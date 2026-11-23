import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaScaledThreeValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoCompCartesianHomValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValuesEqOfRigidifiedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TautTransport

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem base_sq : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  intro R V _ _ _ _ f F₀ _ _ F _ _ j hj
  have e₁ : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) := by
    rw [← spMap_comp_spMap']; rfl
  have e₂ : (TF (R := V) F).hom = spMap ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) := by
    rw [← spMap_comp_spMap']; rfl
  rw [e₁, e₂, spMap_comp_spMap', spMap_comp_spMap']
  congr 1
  exact RingHom.ext fun r => hj r

theorem val_tr : ∀ {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀), letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra; ∀ (g₁ : GtPtF D₀ F), g₁.b.left = spMap j ≫ g₀.b.left → (∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) → ∀ (χ : D₀.X) (z : Sp F) J, Good D₀.P.L z J → val (g₁.s χ) (𝟙 _) z J = Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (g₀.s χ) (𝟙 _) (spMap j z) (fun ψ => J (spMap j ≫ ψ))) := by
  intro R _ _ D₀ F₀ F _ _ _ j g₀ g₁ _ hs χ z J hJ
  refine (val_corr hJ (hs χ) (𝟙 (Sp F))).trans ((val_pull hJ (g₀.s χ) (spMap j) (𝟙 (Sp F))).trans ?_)
  have e := (GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap (g₀.s χ) (spMap j) (𝟙 (Sp F₀)) hJ).symm
  rw [Category.comp_id] at e
  rw [Category.id_comp]
  exact e

theorem lamVal_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J₁ J₀ J', Good T.M.L z J₁ → Good D₀.toPre.P.L z J₀ → Good D.P.L z J' → lamVal w' p z J₁ J' = lamVal w (p ≫ sqOf (pull_grp hD)) z J₁ J₀ * ∏ I, gw hD.w (p ≫ lamφ D.P.A I) z (J₀ ((p ≫ lamφ D.P.A I) ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (J' (p ≫ lamφ D.P.A I)) ^ lamε I := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ Z p z J₁ J₀ J' hJ₁ hJ₀ hJ'
  obtain ⟨-, sq₀, gen₀, -⟩ := id h₀
  obtain ⟨-, sq₁, gen₁, -⟩ := id h₁
  obtain ⟨w'', gen'', hval⟩ := GlobalTheory.T.exists_mumfordBundleIso_comp_cartesianHom_values (pull_grp hD) (β₂ := ββ) T.M.isLB D₀.toPre.P.isLB D.P.isLB w hD.w gen₀ hD.w_gen
  have hββ : ββ' = sqOf (pull_grp hD) ≫ ββ := GlobalTheory.LamRigid.square_over_hom_ext
    (by rw [sq₁.1, Category.assoc (sqOf _), sq₀.1, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).1]; simp only [Category.assoc])
    (by rw [sq₁.2, Category.assoc (sqOf _), sq₀.2, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).2]; simp only [Category.assoc])
  subst hββ
  refine (GlobalTheory.T.mumfordBundleIso_values_eq_of_rigidified T.M.isLB D.P.isLB D.P.isAb w' w'' gen₁ gen'' ?_ ?_ Z p z J₁ J' hJ₁ hJ').trans (hval Z p z J₁ J₀ J' hJ₁ hJ₀ hJ')
  · intro T' z' K K' hK hK'
    exact (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D (f.comp ω) (fun i => f (s i)) (hD.xe.trans e) _ _ w' hB h₁ T' 1 z' K K' hK hK').1
  · intro T' z' K K' hK hK'
    obtain ⟨K₀, hK₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := T'.left) z'
    rw [hval _ _ z' K K₀ K' hK hK₀ hK', lift_sqOf]
    have o : pushPt (pull_grp hD).1.w (1 : T' ⟶ D.P.A) = 1 := map_one (pushHom (pull_grp hD) T')
    rw [o, (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n R D₀.toPre ω s e β ββ w D₀.tau_bimult h₀ (Over.mk (T'.hom ≫ spMap f)) 1 z' K K₀ hK hK₀).1, _root_.one_mul]
    rw [prod_lam (1 : T' ⟶ D.P.A) 1 (fun q => gw hD.w q z' (K₀ (q ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (K' q)), _root_.mul_one]
    simp only [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem ag {G : Type*} [CommGroup G] (A B C D v w L τ k Λ : G) (hΛ : Λ = A * B⁻¹ * C⁻¹ * D)
    (hv : w = A⁻¹ * B * C * D⁻¹ * v) (h : w = k * (L * τ)) : v = k * (L * Λ * τ) := by
  subst hΛ
  rw [hv] at h
  rw [← mul_right_inj (A⁻¹ * B * C * D⁻¹), h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tautPt_tr : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', Function.Injective f → D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ (a : Fin T.r → ℤ) (g₀ : GtPtF D₀.toPre F₀) (g : GtPtF D F), TautPt T ω s ε n D₀.toPre e β ββ w F₀ a g₀ → Tr f hD j g₀ g → TautPt T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' F a g := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hf hB h₀ h₁ F₀ _ _ F _ _ j hj a g₀ g hg₀ htr
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  obtain ⟨g₁, ⟨hb₁, hs₁⟩, hpull⟩ := htr
  obtain ⟨hpt₀, hv₀⟩ := hg₀
  have bsq := base_sq f F₀ F j hj
  have hπ := hpull.1
  refine ⟨?_, fun χ => ?_⟩
  · calc g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β = g₁.b.left ≫ β := by
          rw [← hπ]; simp only [Category.assoc]
      _ = spMap j ≫ g₀.b.left ≫ β := by rw [hb₁, Category.assoc]
      _ = spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω ≫ (T.c₀ a).left := by rw [hpt₀]
      _ = _ := by
          rw [← Category.assoc, bsq, Category.assoc, ← Category.assoc (spMap f), spMap_comp_spMap']
  · obtain ⟨k₀, hk₀, hv⟩ := hv₀ (hD.xe χ)
    refine ⟨Units.map j.toMonoidHom k₀, ?_, fun z J₁ J' hJ₁ hJ' => ?_⟩
    · show j (k₀ : F₀) = _
      rw [hk₀, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [map_zpow₀, hj]; rfl
    · obtain ⟨J₀, hJ₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := Sp F) z
      have pv := GlobalTheory.ArcPull.pullGt_val hD hpull χ (𝟙 _) hJ₀ hJ'
      have vt := val_tr j g₀ g₁ hb₁ hs₁ (hD.xe χ) z J₀ hJ₀
      have hv' := hv (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ)) (fun ψ => hJ₁ (spMap j ≫ ψ))
        (fun ψ => hJ₀ (spMap j ≫ ψ))
      have lp := lamVal_pull T ε n R V J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ _
        (lift (DegPre.cF D F χ) g.b).left z J₁ J₀ J' hJ₁ hJ₀ hJ'
      have hpq : spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left =
          (lift (DegPre.cF D F χ) g.b).left ≫ sqOf (pull_grp hD) := by
        apply GlobalTheory.LamRigid.square_over_hom_ext
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).1, ← Category.assoc _ (fst D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
          show spMap j ≫ (TF (R := R) F₀).hom ≫ (D₀.toPre.c (hD.xe χ)).left = ((TF (R := V) F).hom ≫ (D.c χ).left) ≫ _
          rw [Category.assoc, hD.c_pr χ, ← Category.assoc, ← Category.assoc, bsq]
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).2, ← Category.assoc _ (snd D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hb₁, ← hπ]
      have hsp : spMap (RingHom.id F) = 𝟙 (Sp F) := by
        simp [spMap]
      have hgm : gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn (Units.map j.toMonoidHom k₀)) := by
        rw [Category.comp_id, GlobalTheory.ArcSpecialise.gm_unitOn_spMap j k₀ z]
        have := GlobalTheory.ArcSpecialise.gm_unitOn_spMap (RingHom.id F) (Units.map j.toMonoidHom k₀) z
        rw [hsp] at this
        exact this.symm
      have m := congrArg (Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom) hv'
      have lc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (lamVal w (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ))) = lamVal w (spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left) z J₁ J₀ :=
        (GlobalTheory.HalfBC.lamVal_comp w (spMap j) _ z J₁ J₀ hJ₁ hJ₀).symm
      have tc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) ((TF (R := R) F₀).hom ≫ spMap ω) (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ))) = val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) (spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω) z J₁ :=
        GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap _ (spMap j) _ hJ₁
      have gc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (gm (𝟙 (TF (R := R) F₀).left) (spMap j z) ⊤ (unitOn k₀)) = gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) :=
        (GlobalTheory.ConstFam.gm_comp_stalkMap (spMap j) (𝟙 _) z ⊤ trivial _).symm
      rw [← vt, map_mul, map_mul, lc, tc, gc, hpq, hgm] at m
      have tm : spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω = (TF (R := V) F).hom ≫ spMap (f.comp ω) := by
        rw [← Category.assoc, bsq, Category.assoc, spMap_comp_spMap']
      rw [tm] at m
      have hΛ := prod_lam (DegPre.cF D F χ) g.b (fun q => GlobalTheory.ArcPull.om hD.w z J₀ J' q)
      rw [lp]
      simp only [Category.id_comp] at pv
      exact ag _ _ _ _ _ _ _ _ _ _ hΛ pv m

end GlobalTheory.TautTransport
