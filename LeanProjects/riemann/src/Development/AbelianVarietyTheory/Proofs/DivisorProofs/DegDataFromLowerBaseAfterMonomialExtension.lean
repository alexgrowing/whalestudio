import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullFrom

theorem exists_cart_of_pullDeg : ∀ {V V₁ V₂ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing V₂] [IsDomain V₂] (D : DegPre V) (f₁ : V →+* V₁) (f₂ : V₁ →+* V₂) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.P.A.left) (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D'), IsGrpPullback B' D.P.A (spMap f₁) β' → ∃ Φ : D'.P.A.left ⟶ B'.left, IsGrpPullback D'.P.A B' (spMap f₂) Φ ∧ Φ ≫ β' = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁)) ∧ ∀ (a : D'.X) (y : 𝟙_ (Over (Sp V₁)) ⟶ B'), y.left ≫ β' = spMap f₁ ≫ (D.c (hD.xe a)).left → (D'.c a).left ≫ Φ = spMap f₂ ≫ y.left := by
  intro V V₁ V₂ _ _ _ _ _ _ D f₁ f₂ B' _ β' D' hD gp'
  have gp := pull_grp hD
  have hsp : spMap f₂ ≫ spMap f₁ = spMap (f₂.comp f₁) := GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂
  have w₀ : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁))) ≫ D.P.A.hom =
      (D'.P.A.hom ≫ spMap f₂) ≫ spMap f₁ := by
    rw [gp.1.w, Category.assoc, hsp]
  refine ⟨gp'.1.lift _ _ w₀, ?_, gp'.1.lift_fst _ _ w₀, fun a y hy => ?_⟩
  · exact IsGrpPullback.cancel gp' (gp.congr hsp.symm (gp'.1.lift_fst _ _ w₀).symm) (gp'.1.lift_snd _ _ w₀)
  · apply gp'.1.hom_ext
    · rw [Category.assoc, gp'.1.lift_fst, Category.assoc, hy, ← Category.assoc (spMap f₂), hsp]
      exact hD.c_pr a
    · rw [Category.assoc, gp'.1.lift_snd, Category.assoc, Over.w y, ← Category.assoc, Over.w (D'.c a)]
      rfl

theorem degFrom_of_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁i hf₁f hf₁l hκ₁l gp' gp'' sq' sq'' x hx w₁ q hw₁ hPR V₂ _ _ _ f₂ fK I _ s ε hV₂ hf₂i hf₂f hf₂l hfK hq D' hD
  obtain ⟨Φ, gΦ, hΦ, hc₀⟩ := exists_cart_of_pullDeg D.toPre f₁ f₂ B' β' D'.toPre hD gp'
  have hc : ∀ a, (D'.toPre.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left := fun a =>
    hc₀ a _ (by
      have := (hx (hD.xe.trans (e₀.symm.trans e.symm) a)).1
      simpa using this)
  have hΛD : (abelian₂ D.toPre.P.A D.toPre.P.L).IsLB := DVR.linComb_isLB _ D.toPre.P.isLB _ _
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso D.toPre.P.A B' D'.toPre.P.A L.T.B (spMap f₁) (spMap f₂) β' Φ (GlobalTheory.PsiEvenPull.proj hD) β₂ β₂'
    D.toPre.P.L D'.toPre.P.L L.T.M.L gp' gΦ sq' hΦ D.toPre.P.isLB D'.toPre.P.isLB L.T.M.isLB hD.w w₁ hD.w_gen hw₁
  have hsp : spMap f₂ ≫ spMap κ₁ = spMap (f₂.comp κ₁) := GlobalTheory.HalfBC.spMap_comp_spMap' κ₁ f₂
  refine ⟨Wit.ofDeg D'.toPre D'.tau_bimult, AddEquiv.refl _, Wit.refines_ofDeg _ _, Φ ≫ β'', GlobalTheory.HalfBC.sqOf gΦ ≫ β₂', w,
    (IsGrpPullback.comp gΦ gp'').congr hsp rfl, ⟨?_, ?_⟩, hw, fun a => ?_, fun a b => ?_⟩
  · have e₁ : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (fst L.T.B L.T.B).left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.1, ← Category.assoc, e₁, Category.assoc]
  · have e₂ : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (snd L.T.B L.T.B).left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.2, ← Category.assoc, e₂, Category.assoc]
  · refine (congrArg (· ≫ β'') (hc a)).trans ?_
    rw [Category.assoc, (hx _).2, ← Category.assoc, hsp]
    rfl
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.period_relation_pullback_monomial_constants n V D.toPre r e₀ L.T V₁ f₁ κ₁ e B' β₂ β₂' x w₁ q hf₁i hPR V₂ f₂ fK s ε hfK hq D'.toPre hD Φ gΦ hc w hval a b
    refine ⟨k, hk, fun z J J' hJ hJ' => ?_⟩
    refine ((Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').trans ?_
    exact hk' z J J' hJ hJ'

end GlobalTheory.PullFrom
