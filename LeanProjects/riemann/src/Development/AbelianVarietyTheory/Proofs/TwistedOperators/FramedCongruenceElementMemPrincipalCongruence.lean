import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemLatticeCompletionOfSupportedPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeCompletStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlaceIdealMulLatticeCompletionEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegerOutsidePrimePowDvdMaximalIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridModulusExactOrderWitnessStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

open scoped Pointwise

namespace GlobalTheory.LevFrame

theorem gl_smul_pi_one {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] (k₀ : GL n 𝒪[k]) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ • (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) =
      Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) := by
  have A : ∀ h : GL n 𝒪[k], ∀ y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)),
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h • y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) := by
    intro h y hy
    have hy' : ∀ j, ∃ c : 𝒪[k], algebraMap 𝒪[k] k c = y j := fun j => Submodule.mem_one.1 (hy j (Set.mem_univ j))
    choose c hc using hy'
    intro i _
    refine Submodule.mem_one.2 ⟨∑ j, h.1 i j * c j, ?_⟩
    show _ = ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).1 *ᵥ y) i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hc]
    rfl
  refine Submodule.ext fun x => (Submodule.mem_smul_pointwise_iff_exists x _ _).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact A k₀ y hy
  · intro hx
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀⁻¹ • x, A _ x hx, ?_⟩
    rw [map_inv, smul_inv_smul]

set_option maxHeartbeats 2000000 in

theorem gl_mem_lev : All fun {D} _ _ {sc} {G} _ _ => ∀ (X : Node), IsSelfDualC (G.V X) (G.Λ X) → ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) → ∀ (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p (G.V X) n),
  β.IsLat (G.Λ X) (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ k₀ : GL n 𝒪[k],
  (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v) →
  β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) ∈ lev G X := by
  intro D hQ T L μ0 hL sc G W M hM X hsd v hv k _ _ _ _ p hpv hid n _ _ β hlat k₀ hk₀
  set g := β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) with hg
  have hff := GlobalTheory.FrameAt.frame_facts D k p (G.V X) n β
  have hgrp : g ∈ grpAt (G.V X) (· = p.v) := (hff.1 g).2 ⟨_, rfl⟩
  have hinK : InK (G.V X) (G.Λ X) (· = p.v) g := by
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hff.2.2.2.1 (G.Λ X) hsd
    have hΛeq : Λ₀ = Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) :=
      Submodule.ext fun x => (hΛ₀ x).trans (hlat x).symm
    rw [hg, hK, hΛeq]
    exact gl_smul_pi_one k₀
  have hsupp : ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) → ∀ i, y i ∈ idAt D (· = p.v) := fun y hy =>
    (((GlobalTheory.FinPl.localComponents D (· = p.v)).2 (G.V X)).2.2.2 (G.Λ X) y hsd.1).1 hy |>.1
  have hmov : ∀ κ, InK (G.V X) (G.Λ X) (· = p.v) κ → ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) →
      (mt (G.V X) κ - 1) *ᵥ y ∈ latV (G.V X) (G.Λ X) (· = p.v) := by
    intro κ hκ y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hκ.2 y (hsupp y hy)).1 hy) hy
  show g ∈ Lev.levA (G.V X) (G.levCong X)
  refine Lev.mem_levA.2 ⟨GlobalTheory.SplitHecke.Stab.mem_GfC p.split (β.gl_supp _), ?_⟩
  show Lev.finE (G.V X) g ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  refine mem_congLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g hgrp (hmov g hinK) x hx) hx
    rwa [sub_add_cancel] at h1
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g⁻¹ (inv_mem hgrp) (hmov g⁻¹ (inK_inv hinK)) _ hx) hx
    rwa [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h1
  · obtain ⟨⟨m, hm, hm'⟩, m₂, hm₂, hm₂'⟩ := GlobalTheory.T.gridModulus_exact_order_witness G v hv
    refine GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.modul • G.Λ X) g hgrp (fun y hy => ?_) x hx
    have hz := hmov g hinK y hy
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hsplit : (mt (G.V X) g - 1) *ᵥ y = (fun i => p.e * ((mt (G.V X) g - 1) *ᵥ y) i) +
        (fun i => cA D p.e * ((mt (G.V X) g - 1) *ᵥ y) i) := by
      funext i
      rw [Pi.add_apply, ← add_mul, hsum]
      exact (((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 _).1 (hsupp _ hz i)).symm
    rw [hsplit]
    exact add_mem (GlobalTheory.T.frameCongruent_sub_one_mulVec_mem_idealLatticeCompletion D k p (G.V X) (G.Λ X) n β hlat G.modul (G.pl.depth sc v)
      ⟨m, hm, GlobalTheory.T.integer_outside_prime_pow_dvd_maximal_ideal_pow D k p (G.pl.w v) hid _ m hm'⟩ k₀ hk₀ y hy) (GlobalTheory.T.cA_smul_mem_latV_ideal_smul_of_conj_place D k p (G.pl.w v) hid (G.V X) (G.Λ X) G.modul ⟨m₂, hm₂, hm₂'⟩ _ hz)

end GlobalTheory.LevFrame
