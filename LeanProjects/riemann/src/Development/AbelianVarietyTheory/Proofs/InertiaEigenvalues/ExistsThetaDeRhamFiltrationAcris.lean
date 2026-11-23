import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GlobalTheory.MemLoc GlobalTheory.MemLoc.TiedTheta

theorem theta_fil_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]) (Θ : Formalism.Per.Acris l →+* ℂ_[l]),
      (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      (∀ a, ‖Θ a‖ ≤ 1) ∧
      (∀ z : Formalism.Per.Fl l, Θ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm z)) = sh z) ∧
      ∀ a : Formalism.Per.Acris l, ∃ hm, θ ⟨P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)), hm⟩ = Θ a := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  let S : Subring P.R.BdR := (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom
  have hS : ∀ x, x ∈ S ↔ ∃ y : Formalism.Per.BdRp l, T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y := by
    intro x
    change (∃ y, _ = T.eD x) ↔ _
    exact exists_congr fun y => eq_comm
  have hF0 : ∀ x, x ∈ S ↔ x ∈ Fil P 0 := by
    intro x
    rw [hS]
    change _ ↔ x ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil]
    constructor
    · rintro ⟨y, hy⟩
      rw [hy]
      exact TiedUnif.alg_mem_FilD_zero y
    · intro hx
      obtain ⟨y, hy⟩ := exists_of_mem_FilD_zero hx
      exact ⟨y, hy⟩
  let θ : ↥S →+* ℂ_[l] :=
    { toFun := fun x => thetaExt (T.eD x)
      map_one' := by
        change thetaExt (T.eD 1) = 1
        rw [map_one, ← map_one (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_one]
      map_mul' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) * y)) = thetaExt (T.eD x) * thetaExt (T.eD y)
        rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
      map_zero' := by
        change thetaExt (T.eD 0) = 0
        rw [map_zero, ← map_zero (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_zero]
      map_add' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) + y)) = thetaExt (T.eD x) + thetaExt (T.eD y)
        rw [map_add, hu, hv, ← map_add, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add] }
  have hθ : ∀ (x : ↥S) (y : Formalism.Per.BdRp l), T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y →
      θ x = Formalism.Per.θD l y := by
    intro x y h
    change thetaExt (T.eD x) = _
    rw [h, thetaExt_alg]
  let Θ : Formalism.Per.Acris l →+* ℂ_[l] := (Formalism.Per.θD l).comp C.j
  refine ⟨S, θ, Θ, hF0, fun x => ?_, fun c => ?_, fun a => FundOnto.norm_theta_j_le C a, fun z => ?_,
    fun a => ?_⟩
  · obtain ⟨u, hu⟩ := (hS x).1 x.2
    change θ x = 0 ↔ (x : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hu, hθ x u hu, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · have e : algebraMap ℚ_[l] P.R.BdR c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    obtain ⟨y, hy, hy'⟩ := T.om (algebraMap ℚ_[l] (Om l) c)
    have hm : algebraMap ℚ_[l] P.R.BdR c ∈ S := by
      rw [hS, e]
      exact ⟨y, hy⟩
    refine ⟨hm, ?_⟩
    rw [hθ ⟨_, hm⟩ y (by rw [← hy]; exact congrArg T.eD e), hy']
    rfl
  · change Formalism.Per.θD l (C.j _) = _
    rw [FundOnto.theta_j_alg, FundOnto.theta_tm]
    rfl
  · have hm : P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) ∈ S := by
      rw [hS, hC.ι, RingEquiv.apply_symm_apply, C.ι_j]
      exact ⟨_, rfl⟩
    refine ⟨hm, hθ ⟨_, hm⟩ (C.j a) ?_⟩
    change T.eD (P.ιB _) = _
    rw [hC.ι, RingEquiv.apply_symm_apply, C.ι_j]

end GlobalTheory.PSer
