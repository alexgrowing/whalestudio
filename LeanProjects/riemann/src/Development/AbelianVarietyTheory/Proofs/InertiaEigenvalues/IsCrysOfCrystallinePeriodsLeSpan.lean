import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.BKGal

theorem card_le_finrank_of_mem_span {K U W : Type} [Field K] [Field U] [AddCommGroup W] [Module K W]
    [Module U W] (hKU : ∀ c : K, ∃ c' : U, ∀ w : W, c • w = c' • w) (D : Submodule K W) [Module.Finite K D]
    {d : ℕ} (e : Fin d → W) (he : LinearIndependent U e) (hsp : ∀ i, e i ∈ Submodule.span U (D : Set W)) :
    d ≤ Module.finrank K D := by
  classical
  let u := Module.finBasis K D
  let u' := fun i => (u i : W)
  have hle : (D : Set W) ⊆ Submodule.span U (Set.range u') := by
    intro x hx
    have h4 := congrArg Subtype.val (u.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h4
    rw [← h4]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hKU (u.repr ⟨x, hx⟩ i)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h6 := linearIndependent_le_span_aux' _ he (Set.range u') (by
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le.2 hle (hsp i))
  have h7 := Fintype.card_range_le u'
  simp only [Fintype.card_fin] at h6 h7
  exact h6.trans h7

theorem isCrys_of_span_generic {G G' : Type} [Group G] [Group G'] {Qp K₀ K K₀' K' U : Type} [Field Qp] [Field K₀]
    [Field K] [Field K₀'] [Field K'] [Field U]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [IsDomain B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra U B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] [SMulCommClass Qp U B]
    (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (hf : FracInv PD) (hf' : FracInv PD') (hU : ∀ c : K₀, ∃ c' : U, algebraMap K₀ B c = algebraMap U B c')
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (ρ' : Representation LL G' V) (hc : IsCrys PD' ρ')
    (hsp : ∀ m ∈ DcrisK₀ PD' ρ', m ∈ Submodule.span U (DcrisK₀ PD ρ : Set (B ⊗[Qp] V))) : IsCrys PD ρ := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_le₀ PD hf ρ
  obtain ⟨h3, -⟩ := finite_le₀ PD' hf' ρ'
  rw [isCrys_iff_finrank] at hc ⊢
  refine le_antisymm h2 ?_
  let e := Module.finBasisOfFinrankEq K₀' _ hc
  have hB := (indepB PD' hf' ρ' e e.linearIndependent).restrict_scalars' U
  refine card_le_finrank_of_mem_span (U := U) (fun c => ?_) _ _ hB fun i => hsp _ (e i).2
  obtain ⟨c', h⟩ := hU c
  exact ⟨c', fun w => by rw [← algebraMap_smul B c w, h, algebraMap_smul]⟩

theorem isCrys_of_dcris_le_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (LL : FinExt l) (T : QLat LL) (F K'' : FinExt l), IsCrys (P.PD K'') (T.ρ.comp (inclG K'')) → (∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')), m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V))) → IsCrys (P.PD F) (T.ρ.comp (inclG F)) := by
  intro l _ P AI hs LL T F K'' hc hsp
  obtain ⟨Ti⟩ := hs
  haveI := LL.2
  haveI : IsDomain P.R.B := isDomain_of_tied Ti F
  exact isCrys_of_span_generic (U := ↥(MaximalUnramifiedExtension l)) (P.PD F) (P.PD K'') (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti F)
    (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti K'') (fun c => ⟨⟨c.1, c.2.2⟩, rfl⟩) _ _ hc hsp

end GlobalTheory.BKGal
