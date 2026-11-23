import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSecOfActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenDecompositionVectorBundle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
  GlobalTheory.LieVB GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.LocM.LieEig

end GlobalTheory.LocM.LieEig

namespace GlobalTheory.LocM.LieEig

theorem spMap_dualMap_resG_self {X : Scheme.{0}} (T : X.Opens) {Y' : Scheme.{0}} (f : Sp (DualNumber Γ(X, T)) ⟶ Y') :
    spMap (Formalism.L2.Pj.dualMap (resG X (le_refl T))) ≫ f = f := by
  have e₁ : resG X (le_refl T) = RingHom.id _ := by
    ext a
    simp [resG]
  have e₂ : Formalism.L2.Pj.dualMap (RingHom.id Γ(X, T)) = RingHom.id _ := by
    ext z <;> simp [Formalism.L2.Pj.dualMap]
  rw [e₁, e₂]
  simp [spMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sec_act {X : Scheme.{0}} {t : SAB H X} [QuasiSeparated t.G.hom] {T : X.Opens} (h : CoordOpen t T)
    (Θ : TanM (affPt h.1) t.G ≃ₗ[Γ(X, T)] Γ(Lie t.G, T)) (hΘ : ∀ v, IsSecOf h.1 v (Θ v)) (a : 𝓞 E)
    (v : TanM (affPt h.1) t.G) : Θ (actR t.act a v) = (VB.act (lieAct t.act) a).app T (Θ v) := by
  have := IsSecOf.eq_resM h le_rfl (GlobalTheory.T.isSecOf_action t h v (Θ v) a (hΘ v)) (hΘ (actR t.act a v))
    (spMap_dualMap_resG_self T _).symm
  rwa [resM_self] at this

theorem exists_tangent_equiv_act {X C : Scheme.{0}} {t : SAB H X} {t' : SAB H C} [QuasiSeparated t'.G.hom] {g : C ⟶ X}
    (m : SABMap t' t g) :
    ∃ Ψ : ∀ (T : C.Opens) (h : CoordOpen t' T) (x : Sp Γ(C, T) ⟶ X), affPt h.1 ≫ g = x →
      (TanM x t.G ≃ₗ[Γ(C, T)] Γ(Lie t'.G, T)),
      (∀ T h x hx T' h' x' hx' (e : T' ≤ T) u u', (tv u').left = spMap (Formalism.L2.Pj.dualMap (resG C e)) ≫ (tv u).left →
        Ψ T' h' x' hx' u' = resM _ e (Ψ T h x hx u)) ∧
      ∀ T h x hx (a : 𝓞 E) u, Ψ T h x hx (actR t.act a u) = (VB.act (lieAct t'.act) a).app T (Ψ T h x hx u) := by
  choose Θ hΘ using fun T (h : CoordOpen t' T) => h.exists_equiv
  refine ⟨fun T h x hx => (pushE m _ hx).symm ≪≫ₗ Θ T h, fun T h x hx T' h' x' hx' e u u' hu => ?_,
    fun T h x hx a u => ?_⟩
  · obtain ⟨v, rfl⟩ := (pushE m _ hx).surjective u
    obtain rfl : pushE m _ hx' (tanOf (isTan_map _ (spMap_affPt h.1 h'.1 e) (isTan_tv v))) = u' :=
      tan_ext (by rw [hu, left_pushE, left_pushE, left_tanOf, Category.assoc])
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (hΘ T h v).eq_resM h e (hΘ T' h' _) rfl
  · simp only [LinearEquiv.trans_apply]
    rw [← sec_act h (Θ T h) (hΘ T h) a]
    refine congrArg (Θ T h) ?_
    have key := pushE_act m (affPt h.1) hx a ((pushE m _ hx).symm u)
    rw [LinearEquiv.apply_symm_apply] at key
    exact (LinearEquiv.symm_apply_eq _).2 key.symm

end GlobalTheory.LocM.LieEig
