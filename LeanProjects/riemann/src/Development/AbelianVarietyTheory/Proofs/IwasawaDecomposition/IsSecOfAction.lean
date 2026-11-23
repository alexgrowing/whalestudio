import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

namespace GlobalTheory.LocM

theorem IsSecOf.act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) [QuasiSeparated t.G.hom] {T : X.Opens} (h : CoordOpen t T) (v : TanM (affPt h.1) t.G)
    (l : Γ(GlobalTheory.LieVB.Lie t.G, T)) (a : 𝓞 E) (hl : IsSecOf h.1 v l) :
    IsSecOf h.1 (actR t.act a v) ((GlobalTheory.VB.act (GlobalTheory.LieVB.lieAct t.act) a).app T l) := by
  intro s
  have := t.act.hom a
  show dualApp l le_rfl ((omegaMap (t.act.act a)).app T s) = _
  rw [hl]
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  let ev (u : TanM (affPt hT) t.G) : Γ(omega t.G, T) →ₗ[Γ(X, T)] Γ(X, T) :=
    { toFun := tanEv t (isTan_tv u) (le_preimage_affPt hT)
      map_add' := tanEv_add t _ _
      map_smul' := fun a s => (tanEv_smul t _ _ a s).trans
        (congrArg (· * _) ((valR_eq _ _ (le_preimage_affPt hT) a).symm.trans (valR_affPt hT a))) }
  refine LinearMap.congr_fun (f := ev v ∘ₗ GlobalTheory.QCoh.appLinear (omegaMap (t.act.act a)) T) (g := ev (actR t.act a v))
    ((hf.basis le_rfl).ext fun b => ?_) s
  rw [IsFrame.basis_apply, GlobalTheory.Twist.resM_self]
  have e : unitSec t.G ≫ (t.act.act a).left = unitSec t.G := congrArg (fun z => z.left) (IsMonHom.one_hom (t.act.act a))
  have hW' : T ≤ unitSec t.G ⁻¹ᵁ ((t.act.act a).left ⁻¹ᵁ W) := fun z hz => by
    have := hW hz
    rw [← e] at this
    exact this
  show tanEv t (isTan_tv v) (le_preimage_affPt hT) ((omegaMap (t.act.act a)).app T (dUnit t.G hW (f b))) =
    tanEv t (isTan_tv (actR t.act a v)) (le_preimage_affPt hT) (dUnit t.G hW (f b))
  refine Eq.trans (congrArg _ (omegaMap_dUnit (t.act.act a) hW hW' le_rfl (f b))) ?_
  have hp := tanEv_dUnit_eq (t := t) (isTan_tv v) (le_preimage_affPt hT) hW'
    (((t.act.act a).left.appLE W ((t.act.act a).left ⁻¹ᵁ W) le_rfl).hom (f b))
  have hq := tanEv_dUnit_eq (isTan_tv (actR t.act a v)) (le_preimage_affPt hT) hW (f b)
  obtain ⟨h₁, h₂⟩ := hp
  have hv : (tv (actR t.act a v)).left = (tv v).left ≫ (t.act.act a).left := by
    rw [tv_actR]
    rfl
  refine (h₂.trans ?_).trans hq.2.symm
  exact congrArg TrivSqZeroExt.snd ((valR_appLE _ _ _ h₁ _).trans (congrArg (fun y => valR y W (f b)) hv.symm))

end GlobalTheory.LocM
