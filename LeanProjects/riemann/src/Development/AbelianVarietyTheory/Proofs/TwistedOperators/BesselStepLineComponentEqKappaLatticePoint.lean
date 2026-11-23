import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineComp

theorem star_smul_mem_span : ∀ (D : D7) (n : ℕ) (I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), D.host.AAbar * I ≤ D.host.AA * J → ∀ a ∈ D.host.AA, ∀ s ∈ idLat I Λ, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
  intro D n I J Λ hIJ a ha s hs
  have hsa : star a ∈ D.host.AAbar := by
    have e : star a = D.host.conj a := by
      first
      | exact GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.bridge_star_holds D.R D.host a
      | exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host a
      | (apply D.host.φ₀.injective
         have h1 : D.host.φ₀ (D.host.conj a) = starRingEnd ℂ (D.host.φ₀ a) := Formalism.HC.HostAx.conjE_apply _ _ _
         rw [h1]
         haveI := D.host.isCMField_hostE
         exact IsCMField.complexEmbedding_complexConj _ _ _)
    rw [e]; exact Formalism.L2.Pj.conj_mem_AAbar D ha
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    have hm : star a * c ∈ (D.host.AA * J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hIJ (FractionalIdeal.mul_mem_mul hsa hc)
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hm
    rw [smul_smul]
    have key : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (J : Submodule (𝓞 D.host.E) D.host.E)),
        z • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a' ha' j hj =>
        exact Submodule.subset_span ⟨a', ha', j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, by rw [smul_smul]⟩
      | add x x' _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
    exact key _ hm
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem stairRatio_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ), D.host.AAbar * (G.pl.stA sc ^ (σ + 2) * (G.pl.stAbar sc ^ (σ + 2))⁻¹) ≤ D.host.AA * (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) := by
  intro D T L sc G σ
  have hA : (D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  refine le_of_eq ?_
  simp only [shiftId, Places.stA, Places.stAbar, GridData.modul]
  generalize D.host.AA = a at *
  generalize D.host.AAbar = b at *
  generalize ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = n
  generalize ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = m
  rw [pow_succ (a * n⁻¹) (σ + 1), pow_succ (b * m⁻¹) (σ + 1), mul_inv (_ ^ (σ + 1)), mul_inv b, inv_inv]
  calc b * ((a * n⁻¹) ^ (σ + 1) * (a * n⁻¹) * (((b * m⁻¹) ^ (σ + 1))⁻¹ * (b⁻¹ * m)))
      = (b * b⁻¹) * (a * ((a * n⁻¹) ^ (σ + 1) * ((b * m⁻¹) ^ (σ + 1))⁻¹ * (m * n⁻¹))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  refine ⟨_, ?_, (GlobalTheory.T.standardFrameLink_map_inverts_hermitianSkewAdjoint D hq T L μ0 hL sc G W M hM F hF ρ _).symm⟩
  cases ρ with
  | zero => exact GlobalTheory.T.besselStepZero_lineComponent_adjoint_mem_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  | succ σ =>
    exact GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice D _ _ _ _ _ _ (star_smul_mem_span D _ _ _ _ (stairRatio_le G σ)) _
      (GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hq T L μ0 hL sc G W M hM F hF (σ + 1) h u hu)

end GlobalTheory.LineComp

end
