import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoOfInjectiveCodimOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KernelModif

theorem exact_map_of_epi {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (Φ : C ⥤ D)
    [Φ.PreservesZeroMorphisms] (S : ShortComplex C) [PreservesColimit (parallelPair S.f 0) Φ] (hS : S.Exact)
    [Epi S.g] : (S.map Φ).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel Φ)

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (r : ℕ) (F Q : B.X.Modules) (u : F ⟶ Q), GlobalTheory.IsNormalScheme B.X → GlobalTheory.VB.IsVB F r → Q.IsQuasicoherent → Epi u → IsZero (B.genRes.obj Q) → ∃ (B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧ GlobalTheory.VB.IsVB (kernel ((Scheme.Modules.pullback g.f).map u)) r := by
  intro O _ _ _ p _ _ _ B r F Q u hB hF hQ hu hgen
  haveI := hF.isFiniteQC
  obtain ⟨L, hL⟩ := B.exists_isAmpleLB
  obtain ⟨k, G, φ, hG, hφ⟩ := GlobalTheory.FrobFilt.ExtPres.exists_epi_of_isAmpleLB hL (kernel u)
  let S : ShortComplex B.X.Modules := ShortComplex.mk (φ ≫ kernel.ι u) u (by simp)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have e : kernel.lift S.g S.f S.zero = φ := by
      rw [← cancel_mono (kernel.ι S.g), kernel.lift_ι]
    rw [e]
    exact hφ
  haveI : Epi S.g := hu
  have hv : Epi (B.genRes.map S.f) :=
    (exact_map_of_epi B.genRes S hS).epi_f (hgen.eq_of_tgt _ _)
  obtain ⟨B', g, hn, hd, H⟩ := GlobalTheory.ImageDescent.main.2 O p B hB 1 (fun _ => r) (fun _ => k) (fun _ => F) (fun _ => G)
    (fun _ => S.f) (fun _ => ⟨hF, hG, hv⟩)
  refine ⟨B', g, hn, hd, (H 0).of_iso ?_⟩
  let S' := S.map (Scheme.Modules.pullback g.f)
  haveI : Epi (kernel.lift S'.g S'.f S'.zero) :=
    (ShortComplex.exact_iff_epi_kernel_lift S').1 (exact_map_of_epi _ S hS)
  haveI := strongEpi_of_epi (kernel.lift S'.g S'.f S'.zero)
  exact (image.isoStrongEpiMono (kernel.lift S'.g S'.f S'.zero) (kernel.ι S'.g) (kernel.lift_ι _ _ _)).symm

end GlobalTheory.KernelModif
