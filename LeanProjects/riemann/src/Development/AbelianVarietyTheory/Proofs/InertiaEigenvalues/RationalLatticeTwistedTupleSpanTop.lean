import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem span_preimage_eq_top {L V W ι : Type*} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    (e : L →+* ℂ) (f : V →ₛₗ[e] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun i => f (b i))) (hsp : Submodule.span ℂ (Set.range (fun i => f (b i))) = ⊤)
    (S : Set W) (hS : Submodule.span ℂ S = ⊤) (hsub : ∀ y ∈ S, y ∈ Set.range f) :
    Submodule.span L {x | f x ∈ S} = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let B : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let Φ : W →ₗ[ℂ] ℂ := B.constr ℂ (fun i => e (φ (b i)))
  have key : ∀ x, Φ (f x) = e (φ x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : f (b i) = B i := (Module.Basis.mk_apply hli hsp.ge i).symm
      rw [this]
      exact B.constr_basis ℂ _ i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hΦ : Φ = 0 := by
    refine LinearMap.ext_on hS fun y hy => ?_
    obtain ⟨x, rfl⟩ := hsub y hy
    have : φ x = 0 := hφ (Submodule.subset_span hy)
    rw [key, this, map_zero, LinearMap.zero_apply]
  apply hφ0
  ext x
  have := key x
  rw [hΦ, LinearMap.zero_apply] at this
  exact e.injective (by rw [← this, LinearMap.zero_apply, map_zero])

theorem span_latS : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  intro D w j
  have h := D.what₂.jMt_basis (D.what₂.muTw w) j (Module.Free.chooseBasis _ _)
  exact span_preimage_eq_top D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) _ h.1 h.2 _
    (D.what₂.MtLat (D.what₂.muTw w) j).span_top (fun y hy => D.what₂.MtLat_sub _ _ y hy)

end GlobalTheory.PlaceRead
