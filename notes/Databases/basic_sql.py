import sqlite3

# Create connection and cursor
conn = sqlite3.connect('homeowners.db')
cursor = conn.cursor()

# Drop tables if they exist
cursor.execute('DROP TABLE IF EXISTS homeowners')
cursor.execute('DROP TABLE IF EXISTS houses')

# Create the homeowners table
cursor.execute('''
CREATE TABLE IF NOT EXISTS homeowners (
    name TEXT,
    age INTEGER,
    house_id INTEGER
)''')

# Insert the sample data
cursor.execute('''
INSERT INTO homeowners (name, age, house_id) VALUES
    ('Alice', 31, 6),
    ('Bob', 32, 3),
    ('Jane', 25, 4)
''')

# Create the houses table
cursor.execute('''
CREATE TABLE IF NOT EXISTS houses (
    id INTEGER,
    year INTEGER
)''')

# Insert the sample data
cursor.execute('''
INSERT INTO houses (id, year) VALUES
    (6, 1904),
    (4, 1965),
    (1, 1965)
''')

# Commit the changes
conn.commit()


cursor = conn.cursor()
# Print homeowners table
print("Homeowners table:")
cursor.execute('SELECT * FROM homeowners')
for row in cursor.fetchall():
    print(row)

print("\nHouses table:")
cursor.execute('SELECT * FROM houses') 
for row in cursor.fetchall():
    print(row)

print("CROSS JOIN of homeowners and houses:")
cursor.execute('''
SELECT * FROM homeowners CROSS JOIN houses''')
for row in cursor.fetchall():
    print(row)


print("INNER JOIN of homeowners and houses:")
cursor.execute('''
SELECT * FROM homeowners INNER JOIN houses ON homeowners.house_id = houses.id''')
for row in cursor.fetchall():
    print(row)


print("LEFT OUTER JOIN of homeowners and houses:")
cursor.execute('''
SELECT * FROM homeowners LEFT OUTER JOIN houses ON homeowners.house_id = houses.id''')
for row in cursor.fetchall():
    print(row)


print("RIGHT OUTER JOIN of homeowners and houses:")
cursor.execute('''
SELECT * FROM homeowners RIGHT OUTER JOIN houses ON homeowners.house_id = houses.id''')
for row in cursor.fetchall():
    print(row)

# Close the connection
conn.close()
