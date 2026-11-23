import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open NumberField Matrix GlobalTheory.CuspRep

noncomputable section

open MeasureTheory GroundTheory.Automorphic.FourierWhittaker

namespace GlobalTheory.CuspGeneric.WhitEq

theorem avg_eq_setIntegral {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [m : MeasurableSpace G] [hB : BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (D : Set G)
    (hD : IsAddFundamentalDomain Γ D μ) (h1 : μ D = 1) (Φ : G → ℂ)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    avg Γ Φ = ∫ x in D, Φ x ∂μ := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  have hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 :=
    ⟨(μ, D), inferInstance, hD, h1⟩
  unfold avg
  rw [dif_pos hex]
  obtain ⟨hH, hD', h1'⟩ := hex.choose_spec
  set ν := hex.choose.1
  set D' := hex.choose.2
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc0 : Measure.addHaarScalarFactor ν μ ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hν, h0, zero_smul]
    have hpos : 0 < ν Set.univ := IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩
    rw [this] at hpos
    simp at hpos
  have hac : μ ≪ ν := by
    rw [hν]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have hDμ : IsAddFundamentalDomain Γ D' μ := hD'.mono hac
  have hμD' : μ D' = 1 := by rw [hDμ.measure_eq hD, h1]
  have hc1 : Measure.addHaarScalarFactor ν μ = 1 := by
    have := h1'
    rw [hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hνμ : ν = μ := by rw [hν, hc1, one_smul]
  rw [hνμ]
  exact hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x

def colIx {a k : ℕ} (hk : k < a) : UnipotentBlockColumnIndex a k k ≃ Fin k where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show k = (j : ℕ)
      simp only at h2 h3
      omega
  right_inv i := rfl

theorem blkU_eq_colGL {R : Type} [CommRing R] {a k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) = colGL (n := a) k (fun i => x ((colIx hk).symm i)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j
  rw [uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]
  by_cases hij : (i : ℕ) < k ∧ (j : ℕ) = k
  · have hne : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := by rw [Fin.lt_def]; omega
    rw [Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]
    · rw [if_neg hne, if_neg hne, dif_pos hlt, colX_apply, dif_pos hij.2, Matrix.single_apply_same, zero_add]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        show (j : ℕ) = k
        exact hij.2
    · intro t _ ht
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [add_zero]
      split_ifs with h1 h2
      · rfl
      · rw [colX_apply, dif_neg]
        intro h3
        exact hij ⟨by rw [← h3]; exact h2, h3⟩
      · rfl
    · intro t _
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      apply hij
      have := t.2
      rw [← h1, ← h2]
      omega

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast {k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) x = pair (lastVec k) (fun i => x ((colIx hk).symm i)) := by
  unfold dot pair
  refine Fintype.sum_equiv (colIx hk) _ _ fun t => ?_
  dsimp only
  rw [Equiv.symm_apply_apply]
  rfl

theorem colT_eq_stepCoeff {k : ℕ} (hk : k < a) (f : GA E a → ℂ)
    (hf : ∀ (ξ : Fin k → E) g, f (ratGL E a (colGL k ξ) * g) = f g) (g : GA E a) :
    colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) k f g = stepCoeff k f g := by
  set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)
  have hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ) := fun y => rfl
  set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef
  have hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x := by
    rintro _ ⟨c, rfl⟩ x
    have e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e1]
    have hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g) := by
      change f (posU _ _ * g) = _
      rw [posU_add, mul_assoc]
      change f (blkU _ * _) = _
      rw [← ratGL_blkU, blkU_eq_colGL hk, hf]
      rfl
    have hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) =
        algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
    simp only [Φ]
    rw [hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg,
      GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice
  have hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k) :=
    avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k))
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ
  change avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _
  rw [hA]
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [Φ, hEx, hψ]
  rw [blkU_eq_colGL hk, dot_eLast hk, mul_comm]

theorem whit_partialCoeff (F : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) :
    ∀ m, m + 1 ≤ a → whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) m (partialCoeff F (m + 1)) =
      partialCoeff F 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hk : m + 1 < a := by omega
    rw [whit_succ]
    have hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) =
        partialCoeff F (m + 1) := by
      funext g
      rw [colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g),
        partialCoeff_of_lt F hk]
    rw [hcol]
    exact ih (by omega)

theorem whit_eq_whittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F →
    (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) →
    GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  intro E _ _ a F ha hc hl
  have h := whit_partialCoeff F hl (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha, partialCoeff_self] at h
  rw [h]
  funext g
  exact (whittaker_eq_partialCoeff hc ha g).symm

end GlobalTheory.CuspGeneric.WhitEq
