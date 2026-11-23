import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameChange

theorem coef_zero {ι M R : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι → M}
    (hv : LinearIndependent R v) {s : Set ι} {x : ι} (hx : x ∉ s) {c : R}
    (h : c • v x ∈ Submodule.span R (v '' s)) : c = 0 := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, e⟩ := h
  have h2 : Finsupp.single x c = l := hv (by rw [e, Finsupp.linearCombination_single])
  have h3 := congrArg (fun l : ι →₀ R => l x) h2
  simp only [Finsupp.single_eq_same] at h3
  rw [h3]
  exact (Finsupp.mem_supported' _ _).1 hl x hx

theorem diag_mul {m : ℕ} {R : Type*} [CommRing R] {P Q : Matrix (Fin m) (Fin m) R}
    (hP : P.BlockTriangular id) (hQ : Q.BlockTriangular id) (a : Fin m) :
    (P * Q) a a = P a a * Q a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem sum_mem_spanTo (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j :=
  Submodule.sum_mem _ fun a _ => by
    by_cases h : (a : ℕ) < j
    · exact Submodule.smul_mem _ _ (TermBasic.spanTo_mono S g (by omega) (hg' a))
    · rw [hc a (by omega), zero_smul]; exact Submodule.zero_mem _

theorem coeffs (g : Fin (r + 1) → S.V) (j : ℕ) (v : S.V)
    (hv : v ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) :
    ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) ∧
      v = ∑ a, ((c a : L.O) : E) • g a := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun a ha => (Finsupp.mem_supported' _ _).1 hl a (by simp; omega), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem tri_coeffs {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by
  have hself : ∀ a : Fin (r + 1), g a ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.self_mem S g (by omega)
  have hmem : ∀ a : Fin (r + 1), n (g a) ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.map_mem hg hn _ (hself a)
  have key : ∀ b : Fin (r + 1), ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), (b : ℕ) + 1 ≤ (a : ℕ) → c a = 0) ∧
      z b = ∑ a, ((c a : L.O) : E) • n (g a) := fun b => by
    have h1 : z b ∈ S.spanTo g (b + 1) := by
      rw [hz b]
      exact sum_mem_spanTo S g g hself _ _ fun a ha => hB0 a b (Fin.lt_def.2 (by omega))
    exact coeffs S _ _ _ ((t _ (by omega) _).1 ⟨hzΛ b, h1⟩)
  choose c hc0 hc using key
  refine ⟨Matrix.of fun a b => c b a, fun a b h => hc0 b a (by rw [Fin.lt_def] at h; omega),
    fun b => ?_, fun b => hc b⟩
  show c b b = 1
  apply Subtype.ext
  have e1 : z b - g b ∈ S.spanTo g b := by
    have : z b - g b = ∑ a, (B a b - if a = b then 1 else 0) • g a := by
      rw [hz b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g g hself _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp [hB1]
    · have : b < a := Fin.lt_def.2 (by have := Fin.val_ne_of_ne hab; omega)
      simp [hab, hB0 a b this]
  have e2 : z b - ((c b b : L.O) : E) • n (g b) ∈ S.spanTo g b := by
    have : z b - ((c b b : L.O) : E) • n (g b) =
        ∑ a, (((c b a : L.O) : E) - if a = b then ((c b b : L.O) : E) else 0) • n (g a) := by
      rw [hc b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g _ hmem _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp
    · have := Fin.val_ne_of_ne hab
      simp [hab, hc0 b a (by omega)]
  have e3 : n (g b) - g b ∈ S.spanTo g b := TermBasic.sub_mem hg hn b
  have e4 : (((c b b : L.O) : E) - 1) • g b = (z b - g b) - (z b - ((c b b : L.O) : E) • n (g b)) -
      ((c b b : L.O) : E) • (n (g b) - g b) := by
    simp only [sub_smul, smul_sub, one_smul]; abel
  have h5 := (S.spanTo g b).sub_mem ((S.spanTo g b).sub_mem e1 e2) ((S.spanTo g b).smul_mem ((c b b : L.O) : E) e3)
  rw [← e4] at h5
  have h6 := coef_zero hli (s := {i | (i : ℕ) < b}) (x := b) (by simp) h5
  simpa [sub_eq_zero] using h6

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

theorem frames_congr : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT y x B B' hB0 hB1 hB'0 hB'1 hy hx hyΛ hxΛ
  obtain ⟨-, hW, -, t, t', hli, -, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -, -, hth, -⟩ := hW
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hl1 : LinearIndependent E (S.fr d Λ) := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E (S.fr' d Λ) := hli.comp Sum.inr Sum.inr_injective
  have hlf : LinearIndependent E S.f := by
    have := hl1.map' (S.wit d Λ).1.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f = ⇑((S.wit d Λ).1.symm.toLinearMap) ∘ S.fr d Λ := by
      funext a; simp [Frames.fr]
    rw [e]; exact this
  have hlf' : LinearIndependent E S.f' := by
    have := hl2.map' (S.wit d Λ).2.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f' = ⇑((S.wit d Λ).2.symm.toLinearMap) ∘ S.fr' d Λ := by
      funext a; simp [Frames.fr']
    rw [e]; exact this
  obtain ⟨C, hC0, hC1, hCy⟩ := tri_coeffs S hg hlf hn t y B hB0 hB1 hy hyΛ
  obtain ⟨C', hC'0, hC'1, hC'x⟩ := tri_coeffs S hg' hlf' hn' t' x B' hB'0 hB'1 hx hxΛ
  have hCt : C.BlockTriangular id := fun a b h => hC0 a b h
  have hC't : C'.BlockTriangular id := fun a b h => hC'0 a b h
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_upperTriangular hCt]; simp [hC1]
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (by rw [hdet]; exact isUnit_one)
  have hCit : C⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hCt
  have hCi1 : ∀ a, C⁻¹ a a = 1 := fun a => by
    have h1 := diag_mul hCit hCt a
    rw [Matrix.inv_mul_of_invertible, hC1, mul_one] at h1
    simpa using h1.symm
  set D := C⁻¹ * C' with hD
  have hDt : D.BlockTriangular id := hCit.mul hC't
  have hCD : C * D = C' := by rw [hD, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  choose w hwΛ hw using hth
  refine ⟨Matrix.of fun a b => ((D a b : L.O) : E), fun a b => (D a b).2, fun a b h => ?_, fun a => ?_,
    fun b => ?_⟩
  · simp [hDt h]
  · simp [hD, diag_mul hCit hC't, hCi1, hC'1]
  · have e1 : ∑ a, (Matrix.of fun a b => ((D a b : L.O) : E)) a b • y a =
        ∑ c, ((C' c b : L.O) : E) • (S.wit d Λ).1 (S.f c) := by
      simp only [Matrix.of_apply, hCy, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, ← hCD, Matrix.mul_apply]
      push_cast
      simp only [mul_comm]
    refine ⟨∑ c, ((C' c b : L.O) : E) • w c, Λ.sum_mem fun c _ => Λ.smul_mem (C' c b) (hwΛ c), ?_⟩
    rw [e1, hC'x b, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_sub, hw c, smul_comm]

end GlobalTheory.HL.FrameChange
