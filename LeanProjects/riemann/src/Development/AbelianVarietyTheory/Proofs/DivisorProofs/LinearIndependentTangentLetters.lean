import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagFrame

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] {β : R →+* c.F} {Z : Model Xo c β}
  {Ω : Type} [Field Ω]

theorem ringHom_eq_of_integers {τ τ' : E →+* ℂ} (h : ∀ a : 𝓞 E, τ (a : E) = τ' (a : E)) : τ = τ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem actR_frame (y : FlagPt Z Ω) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) :
    actR Z.t.act a (tanOf (y.tan τ i)) = y.fK (Formalism.L2.Pj.embF c τ (a : E)) • tanOf (y.tan τ i) :=
  tan_ext (y.eig τ i a)

theorem linearIndependent_frame_tau (y : FlagPt Z Ω) (τ : E →+* ℂ) :
    LinearIndependent Ω (fun i => tanOf (y.tan τ i)) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have h0 : ∀ a : 𝓞 E, (tv (0 : TanM (y.y ≫ genι Z) Z.t.G)).left ≫ (Z.t.act.act a).left =
      spMap (epsMul (y.fK (Formalism.L2.Pj.embF c τ (a : E)))) ≫ (tv (0 : TanM (y.y ≫ genι Z) Z.t.G)).left := fun a =>
    congrArg (fun v => (tv v).left)
      (show actR Z.t.act a (0 : TanM (y.y ≫ genι Z) Z.t.G) = y.fK (Formalism.L2.Pj.embF c τ (a : E)) • 0 by simp)
  obtain ⟨a0, -, hu⟩ := y.basis τ _ (isTan_tv 0) h0
  have e1 := hu g ((isComb_iff (fun i => tanOf (y.tan τ i)) g 0).2 hg.symm)
  have e2 := hu 0 ((isComb_iff (fun i => tanOf (y.tan τ i)) 0 0).2 (by simp))
  intro i
  rw [e1, ← e2]
  rfl

theorem linearIndependent_frame (y : FlagPt Z Ω) :
    LinearIndependent Ω (fun l : GlobalTheory.ShFam.Pad.Letter Dw => tanOf (y.tan l.1 l.2)) := by
  classical
  let T : 𝓞 E → Module.End Ω (TanM (y.y ≫ genι Z) Z.t.G) := fun a => actR Z.t.act a
  have hc : ∀ a b, Commute (T a) (T b) := fun a b => by
    show actR Z.t.act a * actR Z.t.act b = actR Z.t.act b * actR Z.t.act a
    rw [← map_mul, ← map_mul, mul_comm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let χ : (E →+* ℂ) → 𝓞 E → Ω := fun τ a => y.fK (Formalism.L2.Pj.embF c τ (a : E))
  have hχ : Function.Injective χ := by
    intro τ τ' h
    refine ringHom_eq_of_integers fun a => ?_
    have h1 := y.fK.injective (congrFun h a)
    exact congrArg Subtype.val h1
  have hind' := hind.comp hχ
  have mem : ∀ τ i, tanOf (y.tan τ i) ∈ ⨅ a, (T a).maxGenEigenspace (χ τ a) := fun τ i => by
    rw [Submodule.mem_iInf]
    intro a
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    exact actR_frame y τ i a
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  rw [Fintype.sum_sigma] at hg
  have hw := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind' Finset.univ
    (fun τ => ∑ i, g ⟨τ, i⟩ • tanOf (y.tan τ i))
    (fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem τ i)) hg
  rintro ⟨τ, i⟩
  exact Fintype.linearIndependent_iff.1 (linearIndependent_frame_tau y τ) (fun i => g ⟨τ, i⟩)
    (hw τ (Finset.mem_univ _)) i

end General

theorem pt_frame_linearIndependent : ∀ (D : D7) (O : Setup D) (y : Pt O.s),
    LinearIndependent Qb (fun l : Pad.Letter O.S.Dw => tanOf (y.tan l.1 l.2)) :=
  fun _ _ y => linearIndependent_frame y

end GlobalTheory.FlagFrame

end
