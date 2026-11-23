import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.NonemptyThetaLOfTied
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FilQuot
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem tiedA_inv_of_theta {y : Per6.BdRp l} (h : Per6.θD l y ≠ 0) : ∃ z, y * z = 1 := by
  have h1 : y ∉ IsLocalRing.maximalIdeal (Per6.BdRp l) := by
    rw [← filq_ker_eq]
    exact h
  exact (IsLocalRing.notMem_maximalIdeal.1 h1).exists_right_inv

variable {P : LocPrime l} {AI : LocAinf l P}

theorem tiedA_fil_iff (P : LocPrime l) (K K' : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD K').Fil a :=
  Set.ext_iff.1 (P.PD_Fil K K' a) x

theorem tiedA_inv (T : LocTied6 l P AI) (K : FinExt l) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) (hy : Per6.θD l y ≠ 0) :
    ∃ u ∈ (P.PD K).Fil 0, x * u = 1 := by
  obtain ⟨z, hz⟩ := tiedA_inv_of_theta hy
  have e := T.eD.apply_symm_apply (algebraMap (Per6.BdRp l) (Per6.BdR l) z)
  refine ⟨_, (tie_fil_zero T K _).2 ⟨z, e⟩, T.eD.injective ?_⟩
  rw [map_mul, e, h, ← map_mul, hz, map_one, map_one]

theorem tiedA_ι_injective (P : LocPrime l) : Function.Injective P.ιB := fun a b h =>
  (P.PD (MainNotions.LocalSituation.botExt l)).ι_inj (((P.PD_ι _ a).trans h).trans (P.PD_ι _ b).symm)

theorem tiedA_φ_injective (P : LocPrime l) : Function.Injective P.φB := fun a b h =>
  (P.PD (MainNotions.LocalSituation.botExt l)).φ_inj (((P.PD_φ _ a).trans h).trans (P.PD_φ _ b).symm)

theorem tiedA_isField (T : LocTied6 l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (Field.toIsField (Per6.BdR l))

variable (K : IntermediateField ℚ_[l] (PadicAlgCl l))

theorem tiedA_grMap_mem {i : ℤ} (x : IsPerfectoidField.fil ℂ_[l] l i)
    (hx : ∀ σ : Gal(PadicAlgCl l/K),
      σ • (x : Per6.BdR l) - x ∈ IsPerfectoidField.fil ℂ_[l] l (i + 1)) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR i x ∈ (cpTwistRep K i).invariants := by
  rw [ContRepresentation.mem_invariants]
  intro σ
  rw [← grMap_tBdR_gal_smul σ x, ← sub_eq_zero, ← map_sub]
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR _).2 (hx σ)

variable [FiniteDimensional ℚ_[l] K]

theorem tiedA_graded_ne {i : ℤ} (hi : i ≠ 0) {x : Per6.BdR l}
    (hxi : x ∈ IsPerfectoidField.fil ℂ_[l] l i)
    (hx : ∀ σ : Gal(PadicAlgCl l/K), σ • x - x ∈ IsPerfectoidField.fil ℂ_[l] l (i + 1)) :
    x ∈ IsPerfectoidField.fil ℂ_[l] l (i + 1) := by
  have h := tiedA_grMap_mem K ⟨x, hxi⟩ hx
  rw [cpTwistRep_invariants_eq_bot K hi, Submodule.mem_bot] at h
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR ⟨x, hxi⟩).1 h

theorem tiedA_graded_zero {x : Per6.BdR l}
    (hxi : x ∈ IsPerfectoidField.fil ℂ_[l] l 0)
    (hx : ∀ σ : Gal(PadicAlgCl l/K), σ • x - x ∈ IsPerfectoidField.fil ℂ_[l] l (0 + 1)) :
    ∃ k : K, x - algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l k) ∈
      IsPerfectoidField.fil ℂ_[l] l (0 + 1) := by
  have hinv := tiedA_grMap_mem K ⟨x, hxi⟩ hx
  rw [cpTwistRep_invariants_zero K] at hinv
  obtain ⟨k, hk⟩ := hinv
  refine ⟨k, ?_⟩
  have hk0 : algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l k) ∈
      IsPerfectoidField.fil ℂ_[l] l 0 :=
    (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨_, rfl⟩
  have hgr0 := grMap_zero_algebraMap (algClToBdR l k) hk0
  rw [thetaAlgHom_algClToBdR] at hgr0
  have hgr : IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0
      ((⟨x, hxi⟩ : IsPerfectoidField.fil ℂ_[l] l 0) - ⟨_, hk0⟩) = 0 := by
    rw [map_sub, hgr0, ← hk, Algebra.linearMap_apply, algebraMap_intermediateField_cp, sub_self]
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR _).1 hgr

end SlopeTestRemainingChoices

theorem tied_field : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied6 l P AI →
    IsField P.R.BdR ∧ IsDomain P.R.B ∧ Function.Injective P.ιB ∧ Function.Injective P.φB ∧
      ∀ (K : FinExt l) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → x ∉ (P.PD K).Fil 1 →
        ∃ y ∈ (P.PD K).Fil 0, x * y = 1 := by
  intro l _ P AI T
  have hF := tiedA_isField T
  have hD : IsDomain P.R.BdR := hF.isDomain
  refine ⟨hF, (tiedA_ι_injective P).isDomain P.ιB.toRingHom, tiedA_ι_injective P,
    tiedA_φ_injective P, fun K x h0 h1 => ?_⟩
  obtain ⟨y, hy⟩ := (tie_fil_zero T K x).1 h0
  refine tiedA_inv T K hy fun h => h1 ((filq_tie_fil T K 1 hy).2 ?_)
  rw [pow_one]
  exact h

theorem tied_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied6 l P AI → (∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2) ∧
    (∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) ∧
    ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR),
      x ∈ (P.PD K).Fil (a + 1) ↔ ∃ y ∈ (P.PD K).Fil a, x = P.ιB P.tB * y := by
  intro l _ P AI T
  refine ⟨fun K => (tiedA_fil_iff P _ K _ _).1 (thetaL T).t_μ,
    fun K => tiedA_inv T K (tie_a T AI.π₁) ?_, fun K a x => ?_⟩
  · rw [filq_θD_π₁, sub_ne_zero]
    exact fun h => AI.ζ_one (Subtype.ext h)
  · refine (tiedA_fil_iff P K _ _ _).trans (((thetaL T).fil_succ_iff_mul_t a x).trans ?_)
    exact exists_congr fun y => and_congr_left fun _ => tiedA_fil_iff P _ K _ _

theorem graded_invariants {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (TT : LocTied6 l P AI) (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ κ ∈ (P.PD K).Fil 0, (∀ g, (P.PD K).actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧
      e - κ ∈ (P.PD K).Fil (n + 1) := by
  have := K.2
  have he' := (TT.fil K n e).1 he
  have hg' : ∀ σ : Gal(PadicAlgCl l/K.1), σ • TT.eD e - TT.eD e ∈ Per6.FilD l (n + 1) := fun σ => by
    have h := (TT.fil K _ _).1 (hg ⟨_, inv_restrictScalars_mem K σ⟩)
    rw [map_sub, P.PD_actdR, TT.actD] at h
    rw [GroundTheory.PAdicHodge.gal_smul_bDeRham_def, inv_galBdRField_eq]
    exact h
  by_cases hn : n = 0
  · subst hn
    obtain ⟨k, hk⟩ := tiedA_graded_zero K.1 he' hg'
    have e1 : TT.eD (algebraMap (Om l) P.R.BdR k) = algebraMap (Per6.BdRp l) (Per6.BdR l)
        (GroundTheory.PAdicHodge.algClToBdR l k) := (tie_o TT _).trans (GaloisCommutant.oD_apply _)
    refine ⟨algebraMap (Om l) P.R.BdR k, (tie_fil_zero TT K _).2 ⟨_, e1⟩, fun g => ?_,
      fun h => absurd rfl h, (TT.fil K _ _).2 ?_⟩
    · rw [P.PD_actdR, P.actQdR_Om, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ k.2]
    · rw [map_sub, e1]
      exact hk
  · refine ⟨0, zero_mem _, fun g => map_zero _, fun _ => rfl, ?_⟩
    rw [sub_zero]
    exact (TT.fil K _ _).2 (tiedA_graded_ne K.1 hn he' hg')

end PositivityTheory.LocInh
