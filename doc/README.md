# Verifizierte Implementierung einer Mapping-Datenbank in Coq
## Deutsche Kurzfassung
Aktuell verbreitete Betriebssystemkerne sind zu komplex, um sie vollständig zu testen.
Doch gerade Fehler im Systemkern stellen ein großes Sicherheitsrisiko dar, da sie die Umgehung der meisten anderen Sicherheitsmaßnahmen ermöglichen. 
Microkerne versuchen deshalb, möglichst viele Funktionen außerhalb des Kerns zu implementieren und damit die Komplexität des sicherheitskritischen Teils zu minimieren.

Selbst dann können jedoch nicht alle möglichen Fälle getestet werden.
In dieser Arbeit wird deshalb Coq zur formalen Verifikation eingesetzt.
Es wird eine verifizierte Implementierung von AVL-Bäumen entwickelt, die als finite Maps viele Anwendungsmöglichkeiten besitzen.
Durch die Verifikation wurden mehrere Fehler in der Implementierung gefunden, doch die Beweise garantieren, dass keine weiteren Fehler existieren.

Darauf aufbauend wird ein Modell einer Mapping-Datenbank entwickelt, wobei wichtige Eigenschaften bewiesen werden.
So wird die Korrektheit dieser zentralen Komponente sichergestellt, die der Verwaltung der Rechte von Prozessen eines Microkern-basierten Systems dient.

# Verified implementation of a mapping database in coq #

## English abstract
Commonly used system kernels are too complex to be fully tested.
However, bugs in the kernel are a high security risk, since they can lead to the circumvention of most other security measures.
Microkernels therefore try to implement as many functions as possible outside of the kernel, thereby reducing the complexitiy of the security-critical part.

Even then, not all cases can be tested.
To remedy this, the work uses Coq in order to perform formal verification.
I develop a verified implementation of AVL trees, which have many applications as finite maps.
Through the verification, multiple bugs were found in the implementation.
The proofs guarantee that no further bugs exist.

The formalization of AVL trees is used to develop a mapping database and prove important properties.
Those properties imply the correctness of this central component, which manages the rights of processes in a microkernel-based system.
