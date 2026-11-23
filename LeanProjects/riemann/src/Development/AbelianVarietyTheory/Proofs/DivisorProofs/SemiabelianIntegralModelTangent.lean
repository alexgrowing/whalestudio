import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdFib

theorem abMap_bcTan_mem_lieLat : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xO : Sp (𝓞 K) ⟶ X) (xK : Sp K ⟶ X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (φ : Fib K) (m : CubeMap φ.G t.G), FibAt t xK φ m → ∀ (G : Over (Sp (𝓞 K))) [GrpObj G] (hG : IsSemiAbelian G) (θ : φ.P.A.left ⟶ G.left) (hθ : IsGrpPullback φ.P.A G (spMap (algebraMap (𝓞 K) K)) θ) (v : Fin φ.P.g → (epsR K ⟶ φ.P.A)) (hv : IsLieBasis v) (q : TanM xK t.G →ₗ[K] (Fin φ.P.g → K)), IsAbMap φ m v q → ∀ w : TanM xO t.G, q (bcTan (algebraMap (𝓞 K) K) hx w) ∈ (SemiFib.mk φ.P G hG θ hθ v hv).lieLat := by
  intro hP E _ _ _ H X t K _ _ xO xK hx φ m hφ G _ hG θ hθ v hv q hq w
  subst hx
  have h₀ := isGrpPullback_pullback t.G xO
  let ψ : φ.G.left ⟶ ((Over.pullback xO).obj t.G).left :=
    pullback.lift m.F (φ.G.hom ≫ spMap (algebraMap (𝓞 K) K)) (by rw [Category.assoc, hφ.1.1.w])
  have hψ₁ : ψ ≫ pullback.fst t.G.hom xO = m.F := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd t.G.hom xO = φ.G.hom ≫ spMap (algebraMap (𝓞 K) K) := pullback.lift_snd _ _ _
  have hψ : IsGrpPullback φ.G ((Over.pullback xO).obj t.G) (spMap (algebraMap (𝓞 K) K)) ψ :=
    h₀.cancel (hφ.1.congr rfl hψ₁.symm) hψ₂
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := hP.fractionField_of_isGrpPullback (Geo.Tor.IsSemiAbelian.pullback xO t.G t.semi) hG hψ hθ φ.q
  have hw := isTan_tv w
  let w₀ : epsR (𝓞 K) ⟶ (Over.pullback xO).obj t.G :=
    Over.homMk (pullback.lift (tv w).left (spMap (algebraMap _ _)) hw.1) (pullback.lift_snd _ _ _)
  have e₁ : w₀.left ≫ pullback.fst t.G.hom xO = (tv w).left := pullback.lift_fst _ _ _
  have e₂ : w₀.left ≫ pullback.snd t.G.hom xO = spMap (algebraMap _ (DualNumber (𝓞 K))) := pullback.lift_snd _ _ _
  have t₀ : IsTangent w₀ := by
    refine pullback.hom_ext ?_ ?_
    · have e := PolBaseChange.eSec_comm h₀
      unfold eSec at e
      rw [Category.assoc, e₁, hw.2, e]
      exact congrArg (fun z => z.left)
        (MonObj.comp_one (M := t.G) (toUnit (Over.mk xO))).symm
    · rw [Category.assoc, e₂]
      refine Eq.trans ?_ (Over.w η[(Over.pullback xO).obj t.G]).symm
      refine (spMap_comp_spMap _ _).trans ?_
      refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (𝓞 K)))
      congr 1
  obtain ⟨w', hw', hc⟩ := hq (bcTan (algebraMap (𝓞 K) K) rfl w)
  have hd : Formalism.L2.Pj.dualMap (algebraMap (𝓞 K) K) = Chart.dualMapR (algebraMap (𝓞 K) K) :=
    RingHom.ext fun a => by ext <;> simp [Formalism.L2.Pj.dualMap, Chart.dualMapR]
  have hov : IsVecOver (algebraMap (𝓞 K) K) ψ w₀ w' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψ₁, hw', left_bcTan, Category.assoc, e₁, hd]
    · rw [Category.assoc, hψ₂, Category.assoc, e₂, ← Category.assoc, Over.w w']
      refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
      congr 1
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine Submodule.subset_span ⟨w₀ ≫ F, ?_, w' ≫ φ.q, ?_, hc⟩
  · unfold IsTangent at t₀ ⊢
    rw [Over.comp_left, ← Category.assoc, t₀]
    exact congrArg (fun z => z.left) (IsMonHom.one_hom F)
  · unfold IsVecOver at hov ⊢
    rw [Over.comp_left, Over.comp_left, Category.assoc]
    refine (congrArg (w'.left ≫ ·) eF).trans ?_
    rw [← Category.assoc, hov, Category.assoc]

end GlobalTheory.BdFib

end
