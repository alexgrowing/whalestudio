import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfFracInv

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedSpan

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem exists_sum_of_isCrys [IsDomain B] (hf : GlobalTheory.RegularRing.FracInv PD)
    (hu : GlobalTheory.RegularRing.LineUnit PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsCrys PD ρ) (y : V ⊗[Qp] B) :
    ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (b i)) (d i) := by
  have hs := (GlobalTheory.RegularRing.isCrys_iff_span PD hf hu ρ).1 h
  have hy : (TensorProduct.comm Qp B V).symm y ∈
      Submodule.span B (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) := hs ▸ Submodule.mem_top
  obtain ⟨m, b, e, he⟩ := Submodule.mem_span_set'.1 hy
  refine ⟨m, b, fun i => TensorProduct.comm Qp B V (e i : B ⊗[Qp] V), fun i => (e i).2, ?_⟩
  have h2 := congrArg (TensorProduct.comm Qp B V) he
  rw [LinearEquiv.apply_symm_apply, map_sum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.Per.TiedIndep.comm_smul (LL := LL) _ _

end Generic

theorem tied_crisSpan : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ h y
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have := LL.2
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  refine exists_sum_of_isCrys (P.PD K) ?_ ?_ ρ h y
  · intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  · intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    rw [e] at hx
    exact ⟨x, by rw [Algebra.smul_def]; exact hx⟩

end GlobalTheory.Per.TiedSpan
