import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices

open Matrix
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviGen

variable {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
  (X Y : Matrix (Fin n) (Fin r) A)

def prX (d : Fin r → A) : Matrix (Fin n) (Fin n) A := X * diagonal d * cT s Y * J

def prY (d : Fin r → A) : Matrix (Fin n) (Fin n) A := Y * diagonal d * cT s X * J

def onPart (Q g : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := 1 - Q + g * Q

def ind (I : Set (Fin r)) : Fin r → A := I.indicator fun _ => 1

end GlobalTheory.CompanionTheory.LeviGen

open Matrix
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviGen

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

section Basic

variable (s) in
theorem cT_add' {m p : Type} (M N : Matrix m p A) : cT s (M + N) = cT s M + cT s N := by
  ext; simp [cT]

variable (s) in
theorem cT_sub' {m p : Type} (M N : Matrix m p A) : cT s (M - N) = cT s M - cT s N := by
  ext; simp [cT]

theorem cT_cT (hs : ∀ a, s (s a) = a) {m p : Type} (M : Matrix m p A) : cT s (cT s M) = M := by
  ext; simp [cT, hs]

variable (s) in
theorem cT_diagonal (d : Fin r → A) : cT s (diagonal d) = diagonal (fun i => s (d i)) := by
  ext i j; by_cases h : i = j <;> simp [cT, diagonal_apply, h, eq_comm]

theorem diag_diag (d e : Fin r → A) {m : Type} (M : Matrix (Fin r) m A) :
    diagonal d * (diagonal e * M) = diagonal (d * e) * M := by
  rw [← Matrix.mul_assoc, diagonal_mul_diagonal]; rfl

end Basic

section Frame

variable (hxx : cT s X * J * X = 0) (hyy : cT s Y * J * Y = 0) (hxy : cT s X * J * Y = 1)
  (hyx : cT s Y * J * X = 1)

include hyx in
theorem prX_mul_prX (d e : Fin r → A) : prX s J X Y d * prX s J X Y e = prX s J X Y (d * e) := by
  have h : ∀ {m : Type} (M : Matrix (Fin r) m A), cT s Y * (J * (X * M)) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  simp only [prX, Matrix.mul_assoc, h, diag_diag]

include hxy in
theorem prY_mul_prY (d e : Fin r → A) : prY s J X Y d * prY s J X Y e = prY s J X Y (d * e) := by
  have h : ∀ {m : Type} (M : Matrix (Fin r) m A), cT s X * (J * (Y * M)) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hxy, Matrix.one_mul]
  simp only [prY, Matrix.mul_assoc, h, diag_diag]

include hyy in
theorem prX_mul_prY (d e : Fin r → A) : prX s J X Y d * prY s J X Y e = 0 := by
  have h : ∀ {m : Type} (M : Matrix (Fin r) m A), cT s Y * (J * (Y * M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyy, Matrix.zero_mul]
  simp only [prX, prY, Matrix.mul_assoc, h, Matrix.mul_zero]

include hxx in
theorem prY_mul_prX (d e : Fin r → A) : prY s J X Y d * prX s J X Y e = 0 := by
  have h : ∀ {m : Type} (M : Matrix (Fin r) m A), cT s X * (J * (X * M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, Matrix.zero_mul]
  simp only [prX, prY, Matrix.mul_assoc, h, Matrix.mul_zero]

include hyx in
theorem prX_mul_X (d : Fin r → A) : prX s J X Y d * X = X * diagonal d := by
  simp only [prX, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (cT s Y), hyx, Matrix.mul_one]

include hyy in
theorem prX_mul_Y (d : Fin r → A) : prX s J X Y d * Y = 0 := by
  simp only [prX, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (cT s Y), hyy, Matrix.mul_zero, Matrix.mul_zero]

include hxx in
theorem prY_mul_X (d : Fin r → A) : prY s J X Y d * X = 0 := by
  simp only [prY, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (cT s X), hxx, Matrix.mul_zero, Matrix.mul_zero]

include hxy in
theorem prY_mul_Y (d : Fin r → A) : prY s J X Y d * Y = Y * diagonal d := by
  simp only [prY, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (cT s X), hxy, Matrix.mul_one]

end Frame

theorem diagonal_add' (d e : Fin r → A) : diagonal (d + e) = diagonal d + diagonal e := (diagonal_add d e).symm
theorem diagonal_sub' (d e : Fin r → A) : diagonal (d - e) = diagonal d - diagonal e := by
  ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
theorem prX_add (d e : Fin r → A) : prX s J X Y (d + e) = prX s J X Y d + prX s J X Y e := by
  simp only [prX, diagonal_add', Matrix.mul_add, Matrix.add_mul]
theorem prX_sub (d e : Fin r → A) : prX s J X Y (d - e) = prX s J X Y d - prX s J X Y e := by
  simp only [prX, diagonal_sub', Matrix.mul_sub, Matrix.sub_mul]
theorem prY_add (d e : Fin r → A) : prY s J X Y (d + e) = prY s J X Y d + prY s J X Y e := by
  simp only [prY, diagonal_add', Matrix.mul_add, Matrix.add_mul]
theorem prY_sub (d e : Fin r → A) : prY s J X Y (d - e) = prY s J X Y d - prY s J X Y e := by
  simp only [prY, diagonal_sub', Matrix.mul_sub, Matrix.sub_mul]
theorem prX_zero : prX s J X Y 0 = 0 := by simp [prX]
theorem prY_zero : prY s J X Y 0 = 0 := by simp [prY]

theorem cT_prX_mul (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (d : Fin r → A) :
    cT s (prX s J X Y d) * J = J * prY s J X Y (fun i => s (d i)) := by
  simp only [prX, prY, Formalism.UG.cT_mul, cT_cT hs, hJ, cT_diagonal, Matrix.mul_assoc]

theorem cT_prY_mul (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (d : Fin r → A) :
    cT s (prY s J X Y d) * J = J * prX s J X Y (fun i => s (d i)) := by
  simp only [prX, prY, Formalism.UG.cT_mul, cT_cT hs, hJ, cT_diagonal, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.LeviGen

open Matrix
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviGen

variable {A : Type} [CommRing A] {s : A →+* A} {n : ℕ} {J : Matrix (Fin n) (Fin n) A}

section OnPart

variable {Q Q' G H : Matrix (Fin n) (Fin n) A}

theorem onPart_add (h0 : Q * Q' = 0) (hc : G * Q' = Q' * G) :
    onPart Q G * onPart Q' G = onPart (Q + Q') G := by
  have h1 : Q * (G * Q') = 0 := by rw [hc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  simp only [onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, h0, h1, Matrix.mul_zero]
  abel

theorem onPart_mul (hQ : Q * Q = Q) (hc : H * Q = Q * H) : onPart Q G * onPart Q H = onPart Q (G * H) := by
  have h1 : Q * (H * Q) = H * Q := by rw [hc, ← Matrix.mul_assoc, hQ]
  simp only [onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hQ, h1]
  abel

theorem onPart_one_left : onPart (1 : Matrix (Fin n) (Fin n) A) G = G := by simp [onPart]

theorem onPart_one_right : onPart Q (1 : Matrix (Fin n) (Fin n) A) = 1 := by simp [onPart]

theorem comm_inv (hc : G * Q = Q * G) (hGH : G * H = 1) (hHG : H * G = 1) : H * Q = Q * H := by
  calc H * Q = H * Q * (G * H) := by rw [hGH, Matrix.mul_one]
    _ = H * (Q * G) * H := by simp only [Matrix.mul_assoc]
    _ = H * (G * Q) * H := by rw [hc]
    _ = Q * H := by rw [← Matrix.mul_assoc H G, hHG, Matrix.one_mul]

theorem onPart_inv (hQ : Q * Q = Q) (hc : G * Q = Q * G) (hGH : G * H = 1) (hHG : H * G = 1) :
    onPart Q G * onPart Q H = 1 := by
  rw [onPart_mul hQ (comm_inv hc hGH hHG), hGH, onPart_one_right]

theorem onPart_unitary (hQ : Q * Q = Q) (hQJ : cT s Q * J = J * Q) (hc : G * Q = Q * G)
    (hu : cT s G * J * G = J) (hGH : G * H = 1) (hHG : H * G = 1) :
    cT s (onPart Q G) * J * onPart Q G = J := by
  have hJH : cT s G * J = J * H := by
    calc cT s G * J = cT s G * J * (G * H) := by rw [hGH, Matrix.mul_one]
      _ = J * H := by rw [← Matrix.mul_assoc, hu]
  have hHQ := comm_inv hc hGH hHG
  have e : cT s (onPart Q G) * J = J * onPart Q H := by
    rw [onPart, cT_add', cT_sub', Formalism.UG.cT_one, Formalism.UG.cT_mul]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, onPart, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
    rw [hQJ, Matrix.mul_assoc, hJH, ← Matrix.mul_assoc, hQJ, Matrix.mul_assoc, hHQ]
  rw [e, Matrix.mul_assoc, onPart_mul hQ hc, hHG, onPart_one_right, Matrix.mul_one]

end OnPart

section FrameComm

theorem comm_of_frame {m : ℕ} {Z W : Matrix (Fin n) (Fin m) A} (hWZ : cT s W * J * Z = 1) {G H : Matrix (Fin n) (Fin n) A}
    (hu : cT s G * J * G = J) (hGH : G * H = 1) (hHG : H * G = 1) {B C : Matrix (Fin m) (Fin m) A}
    (hZ : G * Z = Z * B) (hW : G * W = W * C) : G * (Z * cT s W * J) = Z * cT s W * J * G := by
  have hJH : cT s G * J = J * H := by
    calc cT s G * J = cT s G * J * (G * H) := by rw [hGH, Matrix.mul_one]
      _ = J * H := by rw [← Matrix.mul_assoc, hu]
  have s1 : cT s W * J * H = cT s C * (cT s W * J) := by
    rw [Matrix.mul_assoc, ← hJH, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hW, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have s2 : cT s W * J = cT s C * (cT s W * J) * G := by
    rw [← s1, Matrix.mul_assoc, hHG, Matrix.mul_one]
  have s3 : cT s C * B = 1 := by
    calc cT s C * B = cT s C * (cT s W * J * Z) * B := by rw [hWZ, Matrix.mul_one]
      _ = cT s C * (cT s W * J) * (Z * B) := by simp only [Matrix.mul_assoc]
      _ = cT s C * (cT s W * J) * (G * Z) := by rw [hZ]
      _ = cT s C * (cT s W * J) * G * Z := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← s2, hWZ]
  have s4 : B * cT s C = 1 := mul_eq_one_comm.1 s3
  have s5 : cT s W * J * G = B * (cT s W * J) := by
    conv_rhs => rw [s2]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, s4, Matrix.one_mul]
  calc G * (Z * cT s W * J) = G * Z * (cT s W * J) := by simp only [Matrix.mul_assoc]
    _ = Z * (B * (cT s W * J)) := by rw [hZ]; simp only [Matrix.mul_assoc]
    _ = Z * (cT s W * J * G) := by rw [s5]
    _ = Z * cT s W * J * G := by simp only [Matrix.mul_assoc]

theorem frame_of_comm {m : ℕ} {Z W : Matrix (Fin n) (Fin m) A} (hWZ : cT s W * J * Z = 1) {G : Matrix (Fin n) (Fin n) A}
    (hc : G * (Z * cT s W * J) = Z * cT s W * J * G) : G * Z = Z * (cT s W * J * G * Z) := by
  calc G * Z = G * (Z * (cT s W * J * Z)) := by rw [hWZ, Matrix.mul_one]
    _ = G * (Z * cT s W * J) * Z := by simp only [Matrix.mul_assoc]
    _ = Z * cT s W * J * G * Z := by rw [hc]
    _ = Z * (cT s W * J * G * Z) := by simp only [Matrix.mul_assoc]

end FrameComm

end GlobalTheory.CompanionTheory.LeviGen

open Matrix
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviGen

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

variable (s J X Y) in

def prj (d : Fin r → A) : Matrix (Fin n) (Fin n) A := prX s J X Y d + prY s J X Y d

variable (s J X Y) in

def IsComm (G : Matrix (Fin n) (Fin n) A) (d : Fin r → A) : Prop :=
  G * prX s J X Y d = prX s J X Y d * G ∧ G * prY s J X Y d = prY s J X Y d * G

section Comm

variable {G : Matrix (Fin n) (Fin n) A}

theorem isComm_zero : IsComm s J X Y G 0 := by simp [IsComm, prX_zero, prY_zero]

theorem IsComm.add {d e : Fin r → A} (hd : IsComm s J X Y G d) (he : IsComm s J X Y G e) : IsComm s J X Y G (d + e) := by
  refine ⟨?_, ?_⟩
  · rw [prX_add, Matrix.mul_add, Matrix.add_mul, hd.1, he.1]
  · rw [prY_add, Matrix.mul_add, Matrix.add_mul, hd.2, he.2]

theorem IsComm.sub {d e : Fin r → A} (hd : IsComm s J X Y G d) (he : IsComm s J X Y G e) : IsComm s J X Y G (d - e) := by
  refine ⟨?_, ?_⟩
  · rw [prX_sub, Matrix.mul_sub, Matrix.sub_mul, hd.1, he.1]
  · rw [prY_sub, Matrix.mul_sub, Matrix.sub_mul, hd.2, he.2]

theorem IsComm.mul (hxy : cT s X * J * Y = 1) (hyx : cT s Y * J * X = 1) {d e : Fin r → A} (hd : IsComm s J X Y G d)
    (he : IsComm s J X Y G e) : IsComm s J X Y G (d * e) := by
  refine ⟨?_, ?_⟩
  · rw [← prX_mul_prX hyx, ← Matrix.mul_assoc, hd.1, Matrix.mul_assoc, he.1, Matrix.mul_assoc]
  · rw [← prY_mul_prY hxy, ← Matrix.mul_assoc, hd.2, Matrix.mul_assoc, he.2, Matrix.mul_assoc]

theorem IsComm.comm_prj {d : Fin r → A} (hd : IsComm s J X Y G d) : G * prj s J X Y d = prj s J X Y d * G := by
  rw [prj, Matrix.mul_add, Matrix.add_mul, hd.1, hd.2]

theorem IsComm.inv {H : Matrix (Fin n) (Fin n) A} (hGH : G * H = 1) (hHG : H * G = 1) {d : Fin r → A}
    (hd : IsComm s J X Y G d) : IsComm s J X Y H d := ⟨comm_inv hd.1 hGH hHG, comm_inv hd.2 hGH hHG⟩

variable (hxx : cT s X * J * X = 0) (hyy : cT s Y * J * Y = 0) (hxy : cT s X * J * Y = 1)
  (hyx : cT s Y * J * X = 1)
include hxx hyy hxy hyx

theorem prj_mul_prj (d e : Fin r → A) : prj s J X Y d * prj s J X Y e = prj s J X Y (d * e) := by
  simp only [prj, Matrix.mul_add, Matrix.add_mul, prX_mul_prX hyx, prY_mul_prY hxy, prX_mul_prY hyy, prY_mul_prX hxx,
    add_zero, zero_add]

theorem isComm_onPart {d e : Fin r → A} (he : IsComm s J X Y G e) :
    IsComm s J X Y (onPart (prj s J X Y d) G) e := by
  have c1 : prj s J X Y d * prX s J X Y e = prX s J X Y e * prj s J X Y d := by
    simp only [prj, Matrix.mul_add, Matrix.add_mul, prX_mul_prX hyx, prY_mul_prX hxx, prX_mul_prY hyy, mul_comm d e]
  have c2 : prj s J X Y d * prY s J X Y e = prY s J X Y e * prj s J X Y d := by
    simp only [prj, Matrix.mul_add, Matrix.add_mul, prY_mul_prY hxy, prY_mul_prX hxx, prX_mul_prY hyy, mul_comm d e]
  refine ⟨?_, ?_⟩
  · simp only [GlobalTheory.CompanionTheory.LeviGen.onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, c1]
    rw [← Matrix.mul_assoc (prX s J X Y e) G, ← he.1, Matrix.mul_assoc]
  · simp only [GlobalTheory.CompanionTheory.LeviGen.onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, c2]
    rw [← Matrix.mul_assoc (prY s J X Y e) G, ← he.2, Matrix.mul_assoc]

end Comm

theorem cT_prj_mul (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) {d : Fin r → A} (hd : ∀ i, s (d i) = d i) :
    cT s (prj s J X Y d) * J = J * prj s J X Y d := by
  have e : (fun i => s (d i)) = d := funext hd
  rw [prj, cT_add', Matrix.add_mul, cT_prX_mul hs hJ, cT_prY_mul hs hJ, e, Matrix.mul_add, add_comm]

theorem exists_unit_of_comm {m : ℕ} {Z W : Matrix (Fin n) (Fin m) A} (hWZ : cT s W * J * Z = 1)
    {G H : Matrix (Fin n) (Fin n) A} (hGH : G * H = 1) (hc : G * (Z * cT s W * J) = Z * cT s W * J * G)
    (hc' : H * (Z * cT s W * J) = Z * cT s W * J * H) : ∃ B : (Matrix (Fin m) (Fin m) A)ˣ, G * Z = Z * B.1 := by
  have e1 := frame_of_comm hWZ hc
  have e2 := frame_of_comm hWZ hc'
  have hB : (cT s W * J * G * Z) * (cT s W * J * H * Z) = 1 := by
    calc (cT s W * J * G * Z) * (cT s W * J * H * Z) = cT s W * J * (G * Z) * (cT s W * J * H * Z) := by
          simp only [Matrix.mul_assoc]
      _ = cT s W * J * (G * (Z * cT s W * J) * H) * Z := by simp only [Matrix.mul_assoc]
      _ = cT s W * J * Z * (cT s W * J * Z) := by
          rw [hc, Matrix.mul_assoc (Z * cT s W * J), hGH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hWZ, Matrix.one_mul]
  exact ⟨⟨_, _, hB, mul_eq_one_comm.1 hB⟩, e1⟩

end GlobalTheory.CompanionTheory.LeviGen

namespace GlobalTheory.CompanionTheory.LeviGen

variable {A : Type} [CommRing A] {r : ℕ}

theorem ind_apply (I : Set (Fin r)) (i : Fin r) [Decidable (i ∈ I)] : (ind I i : A) = if i ∈ I then 1 else 0 := by
  unfold ind; rw [Set.indicator_apply]

theorem ind_mul_self (I : Set (Fin r)) : (ind I : Fin r → A) * ind I = ind I := by
  classical
  funext i; simp only [Pi.mul_apply, ind_apply]; split_ifs <;> simp

theorem map_ind (s : A →+* A) (I : Set (Fin r)) (i : Fin r) : s (ind I i) = ind I i := by
  classical
  rw [ind_apply]; split_ifs <;> simp

@[simp] theorem ind_empty : (ind (∅ : Set (Fin r)) : Fin r → A) = 0 := by
  funext i; simp [ind]

end GlobalTheory.CompanionTheory.LeviGen
