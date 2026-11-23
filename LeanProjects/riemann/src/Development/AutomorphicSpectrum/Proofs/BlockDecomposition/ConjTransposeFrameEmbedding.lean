import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Ring

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def emb0 (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) : Matrix m m S :=
  1 + V * (x - 1) * P

structure IsFrame (c : S →+* S) (J : Matrix m m S) (K : Matrix n n S) (a : S) (V : Matrix m n S)
    (P : Matrix n m S) : Prop where
  pv : P * V = 1
  jv : J * V = a • (cT c P * K)
  vj : cT c V * J = a • (K * P)

theorem cT_add (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X + Y) = cT c X + cT c Y := by
  ext i j; simp [cT]

theorem cT_sub (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X - Y) = cT c X - cT c Y := by
  ext i j; simp [cT]

theorem frame_embedding_one (V : Matrix m n S) (P : Matrix n m S) : emb0 V P 1 = 1 := by simp [emb0]

theorem embed_mul {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x y : Matrix n n S) :
    emb0 V P (x * y) = emb0 V P x * emb0 V P y := by
  have e : V * (x - 1) * P * (V * (y - 1) * P) = V * ((x - 1) * (y - 1)) * P := by
    calc V * (x - 1) * P * (V * (y - 1) * P) = V * (x - 1) * (P * V) * (y - 1) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [emb0, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e]
  have e2 : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  rw [e2]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

def embHom {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) : Matrix n n S →* Matrix m m S where
  toFun := emb0 V P
  map_one' := frame_embedding_one V P
  map_mul' := embed_mul h

theorem det_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    (emb0 V P x).det = x.det := by
  have e : emb0 V P x = 1 + V * ((x - 1) * P) := by rw [emb0, Matrix.mul_assoc]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]
  simp

theorem projection_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    P * emb0 V P x * V = x := by
  have e : P * (1 + V * (x - 1) * P) * V = P * V + (P * V) * (x - 1) * (P * V) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [emb0, e, h]
  simp

theorem conj_transpose_frame_embedding (c : S →+* S) (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) :
    cT c (emb0 V P x) = 1 + cT c P * (cT c x - 1) * cT c V := by
  rw [emb0, cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]

theorem frame_embedding_form_defect {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (x : Matrix n n S) :
    cT c (emb0 V P x) * J * emb0 V P x = J + a • (cT c P * (cT c x * K * x - K) * P) := by
  have hvjv : cT c V * J * V = a • K := by
    rw [h.vj, Matrix.smul_mul, Matrix.mul_assoc, h.pv, Matrix.mul_one]
  set A := x - 1 with hA
  set B := cT c x - 1 with hB
  have hx : x = A + 1 := by rw [hA]; abel
  have hcx : cT c x = B + 1 := by rw [hB]; abel
  have e1 : cT c x * K * x - K = K * A + B * K + B * K * A := by
    rw [hcx, hx]; noncomm_ring
  have t1 : J * (V * A * P) = a • (cT c P * (K * A) * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.jv]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have t2 : cT c P * B * cT c V * J = a • (cT c P * (B * K) * P) := by
    rw [Matrix.mul_assoc _ (cT c V) J, h.vj]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have t3 : cT c P * B * cT c V * J * (V * A * P) = a • (cT c P * (B * K * A) * P) := by
    calc cT c P * B * cT c V * J * (V * A * P) = cT c P * B * (cT c V * J * V) * A * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hvjv]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [conj_transpose_frame_embedding, ← hB, emb0, ← hA, e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_add]
  rw [t3, t2, t1]
  abel

theorem frame_embedding_unitary {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {x : Matrix n n S} (hx : cT c x * K * x = K) :
    cT c (emb0 V P x) * J * emb0 V P x = J := by
  rw [frame_embedding_form_defect h, hx]; simp

theorem unitary_of_frame_embedding {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a b : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (hab : b * a = 1) {x : Matrix n n S}
    (hx : cT c (emb0 V P x) * J * emb0 V P x = J) : cT c x * K * x = K := by
  rw [frame_embedding_form_defect h] at hx
  have h0 : a • (cT c P * (cT c x * K * x - K) * P) = 0 := by simpa using hx
  have hvp : cT c V * cT c P = 1 := by rw [← cT_mul, h.pv, cT_one]
  have h1 : a • (cT c x * K * x - K) = 0 := by
    have := congrArg (fun Y => cT c V * Y * V) h0
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    have e : cT c V * (cT c P * (cT c x * K * x - K) * P) * V =
        (cT c V * cT c P) * (cT c x * K * x - K) * (P * V) := by simp only [Matrix.mul_assoc]
    rwa [e, hvp, h.pv, Matrix.one_mul, Matrix.mul_one] at this
  have h2 : cT c x * K * x - K = 0 := by
    have := congrArg (fun Y => b • Y) h1
    simpa [smul_smul, hab] using this
  exact sub_eq_zero.1 h2

theorem fix_left {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {L : Matrix m m S} (hL : L * J = 1) {g : Matrix m m S}
    (hg : cT c g * J * g = J) (hq : g * (1 - V * P) = 1 - V * P) : (1 - V * P) * g = 1 - V * P := by
  set q := 1 - V * P with hqd
  have hsym : cT c q * J = J * q := by
    have e1 : cT c q = 1 - cT c P * cT c V := by rw [hqd, cT_sub, cT_one, cT_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, hqd, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, h.vj,
      ← Matrix.mul_assoc J, h.jv]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hstar : cT c q * cT c g = cT c q := by rw [← cT_mul, hq]
  have h1 : J * q * g = J * q := by
    rw [← hsym]
    calc cT c q * J * g = cT c q * cT c g * J * g := by rw [hstar]
      _ = cT c q * (cT c g * J * g) := by simp only [Matrix.mul_assoc]
      _ = cT c q * J := by rw [hg]
  calc q * g = L * (J * q * g) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    _ = q := by rw [h1, ← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem frame_embedding_projection {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) {g : Matrix m m S}
    (h1 : g * (1 - V * P) = 1 - V * P) (h2 : (1 - V * P) * g = 1 - V * P) :
    emb0 V P (P * g * V) = g := by
  set p := V * P with hp
  have hpp : p * p = p := by
    calc p * p = V * (P * V) * P := by simp only [hp, Matrix.mul_assoc]
      _ = p := by rw [h, Matrix.mul_one]
  have a1 : g * p = g - 1 + p := by
    have : g - g * p = 1 - p := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
    rw [show g * p = g - (g - g * p) by abel, this]; abel
  have a2 : p * g = g - 1 + p := by
    have : g - p * g = 1 - p := by rw [← h2, Matrix.sub_mul, Matrix.one_mul]
    rw [show p * g = g - (g - p * g) by abel, this]; abel
  have e : V * (P * g * V - 1) * P = p * g * p - p := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hp]
    simp only [Matrix.mul_assoc]
  rw [emb0, e, a2, Matrix.add_mul, Matrix.sub_mul, a1, hpp, Matrix.one_mul]
  abel

theorem IsFrame.map {S' : Type} [CommRing S'] {c : S →+* S} {c' : S' →+* S'} (f : S →+* S')
    (hf : ∀ s, f (c s) = c' (f s)) {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) :
    IsFrame c' (J.map f) (K.map f) (f a) (V.map f) (P.map f) := by
  have hc : ∀ {p q : Type} (X : Matrix p q S), cT c' (X.map f) = (cT c X).map f := by
    intro p q X; ext i j; simp [cT, hf]
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul (f := f)).symm
  have hs : ∀ {p q : Type} (X : Matrix p q S), f a • X.map f = (a • X).map f := by
    intro p q X; ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, h.pv]; simp [Matrix.map_one]
  · rw [hm, h.jv, hc, hm, hs]
  · rw [hc, hm, h.vj, hm, hs]

theorem frame_embedding_map {S' : Type} [CommRing S'] (f : S →+* S') (V : Matrix m n S) (P : Matrix n m S)
    (x : Matrix n n S) : (emb0 V P x).map f = emb0 (V.map f) (P.map f) (x.map f) := by
  have h1 : ∀ {k : Type} [DecidableEq k], (1 : Matrix k k S).map f = 1 := fun {k} _ =>
    Matrix.map_one f (map_zero f) (map_one f)
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      (X * Y).map f = X.map f * Y.map f := fun X Y => Matrix.map_mul (f := f)
  have hs : (x - 1).map f = x.map f - 1 := by
    have : (x - 1).map f = x.map f - (1 : Matrix n n S).map f := by
      ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [this, h1]
  have ha : ∀ X Y : Matrix m m S, (X + Y).map f = X.map f + Y.map f := fun X Y => by
    ext i j; simp
  rw [emb0, emb0, ha, h1, hm, hm, hs]

end Ring

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
