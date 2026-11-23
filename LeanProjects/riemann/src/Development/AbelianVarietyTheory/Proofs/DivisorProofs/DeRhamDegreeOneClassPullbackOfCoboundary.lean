import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsBijectiveDegreeOneTwoStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem kaehlerDifferential_map_commutative_pentagon {R₁ R₂ A₁ A₂ A₃ A₄ A₅ : Type} [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [CommRing A₃] [CommRing A₄] [CommRing A₅] [Algebra R₁ A₁] [Algebra R₁ A₂] [Algebra R₁ A₃] [Algebra R₂ A₄]
    [Algebra R₂ A₅] {σ₁ σ₂ : R₁ →+* R₁} {σ₃ σ₄ : R₁ →+* R₂} {σ₅ : R₂ →+* R₂} {a : A₁ →+* A₂} {b : A₂ →+* A₃}
    {c : A₃ →+* A₄} {d : A₁ →+* A₅} {e : A₅ →+* A₄} (ha : SemiHom σ₁ a) (hb : SemiHom σ₂ b) (hc : SemiHom σ₃ c)
    (hd : SemiHom σ₄ d) (he : SemiHom σ₅ e) (h : ∀ x, c (b (a x)) = e (d x)) (x : Ω[A₁⁄R₁]) :
    hc.m1 (hb.m1 (ha.m1 x)) = he.m1 (hd.m1 x) := by
  rw [SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) (fun _ ↦ rfl), SemiHom.oneFormMap_comp_oneFormMap _ _ (ha.comp hb) (fun _ ↦ rfl)]
  exact SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) h x

theorem isPull1_of_pair_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  intro D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg
  unfold IsPull1
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun p ↦ (Λ'.e (Opposite.op p.unop.1.1)).symm (g p), Tot1.ext (fun p q a ↦ ?_) fun p ↦ ?_⟩
  · let B : Type := (Λ'.L.obj (Opposite.op q.unop.1.1)).B
    have e : @HSub.hSub B B B _ (g q) ((Λ'.L.map ((pairFst φ).map a)).φ (g p)) =
        @HSub.hSub B B B _ ((θ.app q).φ (k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a))))
          (k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a))) :=
      congrArg (fun c ↦ c.1 p q a) hg
    have h1 : k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a)) =
        Λ.e (Opposite.op q.unop.1.2) (w.1.1 _ _ ((pairSnd φ).map a)) := hw.1 _ _ _
    have h2 : k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a)) =
        Λ'.e (Opposite.op q.unop.1.1) (w'.1.1 _ _ ((pairFst φ).map a)) := hw'.1 _ _ _
    have h3 := Λ'.nat ((pairFst φ).map a) ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))
    have h4 := hθ q (w.1.1 _ _ ((pairSnd φ).map a))
    apply (Λ'.e (Opposite.op q.unop.1.1)).injective
    refine ((map_sub _ _ _).trans ?_).trans (map_sub _ _ _).symm
    refine (congrArg₂ (fun x y : B ↦ x - y) (AlgEquiv.apply_symm_apply _ _) (h3.trans
      (congrArg _ (AlgEquiv.apply_symm_apply _ _)))).trans (e.trans ?_)
    exact congrArg₂ (fun x y : B ↦ x - y) ((congrArg (θ.app q).φ h1).trans h4) h2
  · let B : Type := K1 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ
    have e : kd0 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ (g p) =
        @HSub.hSub B B B _ (km1 (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (morDP m _)
          (km1 (SemiHom.of_algHom (θ.app p).φ) (θ.app p).dp
          (k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2))))) (k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1))) :=
      congrArg (fun c ↦ c.2 p) hg
    have h1 : k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2)) =
        Submodule.Quotient.mk ((Λ.semi _).m1 (w.1.2 (Opposite.op p.unop.1.2))) := hw.2 _
    have h2 : k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1)) =
        Submodule.Quotient.mk ((Λ'.semi _).m1 (w'.1.2 (Opposite.op p.unop.1.1))) := hw'.2 _
    rw [h1, h2] at e
    apply (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' (Opposite.op p.unop.1.1)).1.1
    have h3 : (Λ'.semi (Opposite.op p.unop.1.1)).m1 (KaehlerDifferential.D D'.R _
        ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))) = KaehlerDifferential.D D'.R _ (g p) :=
      (SemiHom.m1_D _ _).trans (congrArg _ ((Λ'.e _).apply_symm_apply _))
    have h4 := kaehlerDifferential_map_commutative_pentagon (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (semiHom_secPull hφ p.unop)
      (Λ'.semi (Opposite.op p.unop.1.1)) (hθ p) (w.1.2 (Opposite.op p.unop.1.2))
    have h5 : q1 (pairRes φ D'.s) p (w'.1.2 (Opposite.op p.unop.1.1)) = w'.1.2 (Opposite.op p.unop.1.1) :=
      cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) p _
    refine (congrArg Submodule.Quotient.mk h3).trans (e.trans ?_)
    refine (Submodule.Quotient.mk_sub _).symm.trans (congrArg Submodule.Quotient.mk ?_)
    refine Eq.trans ?_ (map_sub _ _ _).symm
    exact congrArg₂ (· - ·) h4 (congrArg (Λ'.semi (Opposite.op p.unop.1.1)).m1 h5.symm)

end GlobalTheory.PDForm
