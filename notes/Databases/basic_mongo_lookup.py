from pymongo import MongoClient

# Connect to MongoDB
client = MongoClient('mongodb://localhost:27017/')
db = client['homeowners_db']

# Drop existing collections
db.homeowners.drop()
db.houses.drop()

# Insert sample homeowner data
homeowners = [
    {"name": "Alice", "age": 31, "house_id": 6},
    {"name": "Bob", "age": 32, "house_id": 3},
    {"name": "Jane", "age": 25, "house_id": 4}
]
db.homeowners.insert_many(homeowners)

# Insert sample house data
houses = [
    {"_id": 6, "year": 1904},
    {"_id": 4, "year": 1965},
    {"_id": 1, "year": 1965}
]
db.houses.insert_many(houses)

# Perform a $lookup (similar to LEFT OUTER JOIN)
pipeline = [
    {
        "$lookup": {
            "from": "houses",           # collection to join with
            "localField": "house_id",   # field from homeowners collection
            "foreignField": "_id",      # field from houses collection
            "as": "house_info"          # array field to store the joined data
        }
    }
]

# Execute the aggregation pipeline and print results
results = db.homeowners.aggregate(pipeline)
print("\nResults of $lookup aggregation:")
for doc in results:
    print(doc)
