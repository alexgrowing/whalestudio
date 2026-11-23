import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PairingClass

section Mat

variable {E : Type} [CommRing E] {n : ℕ}

def UT (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1

def IntM (O : Subring E) (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, A i j ∈ O

lemma diag_mul {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]
  · simp

lemma UT.mul {A B : Matrix (Fin n) (Fin n) E} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun i j h => ?_, fun i => by rw [diag_mul hA.1 hB.1, hA.2, hB.2, one_mul]⟩
  have h1 : A.BlockTriangular id := fun i j h => hA.1 i j h
  have h2 : B.BlockTriangular id := fun i j h => hB.1 i j h
  exact (h1.mul h2) h

lemma IntM.mul {O : Subring E} {A B : Matrix (Fin n) (Fin n) E} (hA : IntM O A) (hB : IntM O B) :
    IntM O (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)

lemma UT.inv {A : Matrix (Fin n) (Fin n) E} (hA : UT A) :
    ∃ B, UT B ∧ A * B = 1 ∧ B * A = 1 ∧ ∀ O : Subring E, IntM O A → IntM O B := by
  have h1 : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular h1]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have h2 : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h1
  have h3 : ∀ i j, j < i → A⁻¹ i j = 0 := fun i j h => h2 h
  refine ⟨A⁻¹, ⟨h3, fun i => ?_⟩, Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu, ?_⟩
  · have := diag_mul hA.1 h3 i
    rw [Matrix.mul_nonsing_inv A hu, hA.2, one_mul] at this
    rw [← this]; simp
  · intro O hO i j
    let A₀ : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
    have hA₀ : O.subtype.mapMatrix A₀ = A := by ext i j; rfl
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, ← hA₀, ← RingHom.map_adjugate]
    exact (A₀.adjugate i j).2

def Tied (O : Subring E) (θ : E) (A A' : Matrix (Fin n) (Fin n) E) : Prop :=
  UT A ∧ UT A' ∧ IntM O A ∧ IntM O A' ∧ ∃ C, IntM O C ∧ A' = A + θ • C

lemma Tied.mul {O : Subring E} {θ : E} {A A' B B' : Matrix (Fin n) (Fin n) E}
    (hA : Tied O θ A A') (hB : Tied O θ B B') : Tied O θ (A * B) (A' * B') := by
  obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hA
  obtain ⟨b1, b2, b3, b4, D, hD, e2⟩ := hB
  refine ⟨a1.mul b1, a2.mul b2, a3.mul b3, a4.mul b4, A * D + C * B', fun i j => ?_, ?_⟩
  · exact O.add_mem (a3.mul hD i j) (hC.mul b4 i j)
  · have h : A * B' = A * B + θ • (A * D) := by rw [e2, mul_add, Matrix.mul_smul]
    rw [e1, add_mul, smul_add, Matrix.smul_mul, ← add_assoc, ← h]

lemma Tied.inv {O : Subring E} {θ : E} {A A' : Matrix (Fin n) (Fin n) E} (hA : Tied O θ A A') :
    ∃ B B', Tied O θ B B' ∧ A * B = 1 ∧ B * A = 1 ∧ A' * B' = 1 ∧ B' * A' = 1 := by
  obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hA
  obtain ⟨B, b1, b2, b3, b4⟩ := a1.inv
  obtain ⟨B', c1, c2, c3, c4⟩ := a2.inv
  refine ⟨B, B', ⟨b1, c1, b4 O a3, c4 O a4, -(B' * C * B), fun i j => ?_, ?_⟩, b2, b3, c2, c3⟩
  · exact O.neg_mem (((c4 O a4).mul hC).mul (b4 O a3) i j)
  · have h : θ • C = A' - A := by rw [e1]; abel
    rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, h, mul_sub, sub_mul, c3, one_mul,
      mul_assoc, b2, mul_one]
    abel

lemma tied_iff_span (O : Subring E) (θ : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ O) ∧
      ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ O) ∧
      (∀ a b, A a b - A' a b ∈ Submodule.span O {θ})) ↔ Tied O θ A A' := by
  constructor
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, h⟩
    choose c hc using fun a b => Submodule.mem_span_singleton.1 (h a b)
    refine ⟨⟨a1, a2⟩, ⟨b1, b2⟩, a3, b3, Matrix.of fun a b => -(c a b : E), fun a b => O.neg_mem (c a b).2, ?_⟩
    ext a b
    have := hc a b
    rw [Subring.smul_def, smul_eq_mul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination this
  · rintro ⟨a, b, a3, b3, C, hC, e⟩
    refine ⟨⟨a.1, a.2, a3⟩, ⟨b.1, b.2, b3⟩, fun i j => Submodule.mem_span_singleton.2
      ⟨⟨-C i j, O.neg_mem (hC i j)⟩, ?_⟩⟩
    rw [Subring.smul_def, smul_eq_mul, e]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

lemma tied_iff_mul (O : Subring E) (θ : E) (A A' : Matrix (Fin n) (Fin n) E) :
    ((∀ i j, A i j ∈ O ∧ A' i j ∈ O ∧ ∃ c ∈ O, A' i j - A i j = θ * c) ∧
      (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1)) ↔ Tied O θ A A' := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose c hc hc' using fun a b => (h1 a b).2.2
    refine ⟨⟨fun i j h => (h2 i j h).1, fun i => (h3 i).1⟩, ⟨fun i j h => (h2 i j h).2, fun i => (h3 i).2⟩,
      fun i j => (h1 i j).1, fun i j => (h1 i j).2.1, Matrix.of c, hc, ?_⟩
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination hc' a b
  · rintro ⟨a, b, a3, b3, C, hC, e⟩
    refine ⟨fun i j => ⟨a3 i j, b3 i j, C i j, hC i j, ?_⟩, fun i j h => ⟨a.1 i j h, b.1 i j h⟩,
      fun i => ⟨a.2 i, b.2 i⟩⟩
    rw [e]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

variable {V : Type} [AddCommGroup V] [Module E V]

def act (g : Fin n → V) (A : Matrix (Fin n) (Fin n) E) : Fin n → V := fun j => ∑ i, A i j • g i

lemma act_act (g : Fin n → V) (A B : Matrix (Fin n) (Fin n) E) : act (act g A) B = act g (A * B) := by
  funext j
  simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma map_act (s : V ≃ₗ[E] V) (g : Fin n → V) (A : Matrix (Fin n) (Fin n) E) :
    (fun i => s (act g A i)) = act (fun i => s (g i)) A := by
  funext j
  simp [act]

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma cT_mul (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j
  simp [cT, Matrix.mul_apply, mul_comm]

lemma cT_one (L : LocE F E) {n : ℕ} : cT L (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  simp [cT, Matrix.one_apply, eq_comm]

lemma Zhat_act (H : HermSp M V) (f f' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    H.Zhat (act f A) (act f' A') = cT M.L A * H.Zhat f f' * A' := by
  ext a b
  simp only [HermSp.Zhat, act, Matrix.of_apply, Matrix.mul_apply, cT, CoordExist.h_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [H.h_herm, CoordExist.h_sum_left, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← H.h_herm]

lemma unitary_of_mem {Fr : LocNG.FrameD H r} {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : LocNG.IsUnitary H g := by
  unfold LocNG.FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro x y; rfl
  | mul a b _ _ ha hb => intro x y; exact (ha _ _).trans (hb x y)
  | inv a _ ha =>
    intro x y
    have := ha (a⁻¹ x) (a⁻¹ y)
    rw [← this]
    simp [LinearEquiv.coe_inv]

lemma pull {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V)
    (f : Fin (r + 1) → V) (f₁ : Fin (r + 1) → S.V) (hf : ∀ a, f₁ a = c.e (f a))
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : ∀ j, c.grp g (f₁ j) = ∑ i, s i j • f₁ i) :
    (fun j => g (f j)) = act f s := by
  funext j
  apply c.e.injective
  have := h j
  simp only [hf, CoordUnip.grp_apply] at this
  rw [this]
  simp [act]

theorem mem_class_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d₁ d : LocNG.Datum P) (t₁ t : Term V M r), LocNG.IsTermOver P d₁ t₁ → LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t₁.f t₁.f' ∈ c1 → (H.Zhat t.f t.f' ∈ c1 ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d₁ d t₁ t ht₁ ht Y0 c1 hc1 hZ1
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨-, hN, hN', hSt, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨on, on', -⟩ := FrameOnto.unipotent_onto M.L r k S
  obtain ⟨-, stab⟩ := FrameStab.stab_eq M.L r k S
  have hmem : ∀ Y, Y ∈ c1 ↔ ∃ A A', Tied M.L.O (algebraMap F E (LocNG.theta M)) A A' ∧
      Y = cT M.L A * Y0 * A' := by
    intro Y
    rw [hc1]
    constructor
    · rintro ⟨A, A', h1, h2, h3, h4⟩
      exact ⟨A, A', (tied_iff_span _ _ _ _).1 ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨A, A', h, h4⟩
      obtain ⟨h1, h2, h3⟩ := (tied_iff_span _ _ _ _).2 h
      exact ⟨A, A', h1, h2, h3, h4⟩
  have hfr : ∀ {d : LocNG.Datum P} {t : Term V M r}, LocNG.IsTermOver P d t →
      ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, UT u ∧ UT u' ∧ t.f = act P.A.f u ∧ t.f' = act P.B.f u' := by
    rintro d t ⟨-, -, ⟨n, hn, e, -⟩, ⟨n', hn', e', -⟩, -⟩
    obtain ⟨u, hu, h⟩ := on _ ((hN n).1 hn)
    obtain ⟨u', hu', h'⟩ := on' _ ((hN' n').1 hn')
    exact ⟨u, u', hu, hu', e.trans (pull c n _ _ c.f_eq u h), e'.trans (pull c n' _ _ c.f'_eq u' h')⟩
  have hZ0 : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    simp only [Frames.Zh, HermSp.Zhat, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  obtain ⟨a₁, a₁', ha₁, e₁⟩ := (hmem _).1 hZ1
  rw [hmem]
  constructor
  · rintro ⟨a, a', ha, e⟩
    obtain ⟨b₁, b₁', hb₁, p1, -, p1', -⟩ := ha₁.inv
    have hA := hb₁.mul ha
    have eZ : H.Zhat t.f t.f' = cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') := by
      have : cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') =
          cT M.L (a₁ * b₁ * a) * Y0 * (a₁' * b₁' * a') := by
        simp only [e₁, cT_mul, mul_assoc]
      rw [this, p1, p1', one_mul, one_mul, e]
    generalize b₁ * a = A at hA eZ
    generalize b₁' * a' = A' at hA eZ
    obtain ⟨B, B', hB, q1, q2, q1', q2'⟩ := hA.inv
    obtain ⟨u₁, u₁', hu₁, hu₁', f₁, f₁'⟩ := hfr ht₁
    obtain ⟨u, u', hu, hu', f, f'⟩ := hfr ht
    obtain ⟨v, hv, w1, w2, -⟩ := hu₁.inv
    obtain ⟨v', hv', w1', w2', -⟩ := hu₁'.inv
    rw [f, f', f₁, f₁', Zhat_act, Zhat_act, ← hZ0] at eZ
    have key : cT M.L (u * B * v) * S.Zh * (u' * B' * v') = S.Zh := by
      have h1 : cT M.L (u * B * v) * S.Zh * (u' * B' * v') =
          cT M.L (B * v) * (cT M.L u * S.Zh * u') * (B' * v') := by
        simp only [cT_mul, mul_assoc]
      have h2 : cT M.L (B * v) * (cT M.L A * (cT M.L u₁ * S.Zh * u₁') * A') * (B' * v') =
          cT M.L (u₁ * (A * B) * v) * S.Zh * (u₁' * (A' * B') * v') := by
        simp only [cT_mul, mul_assoc]
      rw [h1, eZ, h2, q1, q1', mul_one, mul_one, w1, w1', cT_one, one_mul, mul_one]
    obtain ⟨h, hh, g1, g2⟩ := (stab _ _ ((hu.mul hB.1).mul hv) ((hu'.mul hB.2.1).mul hv')).1 key
    obtain ⟨s, rfl⟩ := c.grp.surjective h
    have k1 := pull c s _ _ c.f_eq _ g1
    have k2 := pull c s _ _ c.f'_eq _ g2
    obtain ⟨z1, z2, z3⟩ := (tied_iff_mul _ _ _ _).2 hA
    refine ⟨s, (hSt s).2 hh, A, A', z1, z2, z3, ?_, ?_⟩
    · refine congrFun (show t.f = act (fun i => s (t₁.f i)) A from ?_)
      rw [f, f₁, map_act, k1, act_act, act_act]
      congr 1
      have : u * B * v * (u₁ * A) = u * (B * (v * u₁) * A) := by simp only [mul_assoc]
      rw [this, w2, mul_one, q2, mul_one]
    · refine congrFun (show t.f' = act (fun i => s (t₁.f' i)) A' from ?_)
      rw [f', f₁', map_act, k2, act_act, act_act]
      congr 1
      have : u' * B' * v' * (u₁' * A') = u' * (B' * (v' * u₁') * A') := by simp only [mul_assoc]
      rw [this, w2', mul_one, q2', mul_one]
  · rintro ⟨s, hs, A, A', z1, z2, z3, g1, g2⟩
    have hA := (tied_iff_mul _ _ _ _).1 ⟨z1, z2, z3⟩
    have k1 : t.f = act (fun i => s (t₁.f i)) A := funext g1
    have k2 : t.f' = act (fun i => s (t₁.f' i)) A' := funext g2
    have hz : H.Zhat (fun i => s (t₁.f i)) (fun i => s (t₁.f' i)) = H.Zhat t₁.f t₁.f' := by
      ext a b
      exact unitary_of_mem hs.1 _ _
    refine ⟨a₁ * A, a₁' * A', ha₁.mul hA, ?_⟩
    rw [k1, k2, Zhat_act, hz, e₁]
    simp only [cT_mul, mul_assoc]

end GlobalTheory.HL.PairingClass
