import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiWZeroPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem rel_on (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty) {K : Type} [Fintype K]
    {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.xK a)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi a) D.rigK)) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (LB.pullGen D.P.L _ _ u (cP D (TW W) a).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi a) (D.rigW W)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ h (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vψ, vρ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    refine congrArg (fun q => val u q z J) ?_
    rw [Category.id_comp]
    exact congrArg (fun q => q.left) (comp_cP D κ a)

end OnW

theorem prod_four {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (f : A ⟶ A) (x : T ⟶ A) {U : Type}
    [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) i) ^
      (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      k (x * (x ≫ f)).left * (k x.left ^ 2)⁻¹ * (k (x ≫ f).left)⁻¹ * k (1 : T ⟶ A).left ^ 2 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ (𝟙 A * f)).left ^ (1 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) * k (x ≫ f).left ^ (-1 : ℤ) *
    k (x ≫ 1).left ^ (2 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg_one, zpow_neg, zpow_ofNat, zpow_ofNat]

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

set_option maxHeartbeats 1000000 in
theorem traceFormTwistIso_of_pullback (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by
  obtain ⟨u, hu, hn, hrel⟩ := h
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have ha : (ιD'.onB.act w0).left ≫ Φ = Φ ≫ (ιD.onB.act w0).left := by
    have a₂ : ((Over.pullback (specOf φ)).map (ιD.onB.act w0)).left ≫ pullback.fst D.P.A.hom (specOf φ) =
        pullback.fst _ _ ≫ (ιD.onB.act w0).left := pullback.lift_fst _ _ _
    show _ ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, a₂, Category.assoc]
  have hψ : ∀ k : Fin 4, (![(padd D'.P.A (𝟙 _) (ιD'.onB.act w0)).left, 𝟙 D'.P.A.left, (ιD'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → _) k ≫ Φ =
      Φ ≫ (![(padd D.P.A (𝟙 _) (ιD.onB.act w0)).left, 𝟙 D.P.A.left, (ιD.onB.act w0).left,
      (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k := by
    have p1 : (pushPt gp.1.w (𝟙 D'.P.A)).left = Φ := Category.id_comp _
    intro k
    fin_cases k
    · have m : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) * pushPt gp.1.w (ιD'.onB.act w0) := map_mul (pushHom gp D'.P.A) _ _
      have q : pushPt gp.1.w (ιD'.onB.act w0) = pushPt gp.1.w (𝟙 D'.P.A) ≫ ιD.onB.act w0 :=
        Over.OverMorphism.ext (by rw [Over.comp_left, p1]; exact ha)
      have m' : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) ≫ (𝟙 D.P.A * ιD.onB.act w0) := by
        rw [m, q, MonObj.comp_mul, Category.comp_id]
      have := congrArg (fun q => q.left) m'
      simp only [Over.comp_left, p1] at this
      exact this
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact ha
    · have m : pushPt gp.1.w (1 : D'.P.A ⟶ D'.P.A) = pushPt gp.1.w (𝟙 D'.P.A) ≫ (1 : D.P.A ⟶ D.P.A) := by
        rw [MonObj.comp_one]; exact map_one (pushHom gp D'.P.A)
      have := congrArg (fun q => q.left) m
      simp only [Over.comp_left, p1] at this
      exact this
  obtain ⟨u', hu', pmu⟩ := exists_pmaps ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB Φ hψ u hu
  have vu : ∀ {T : Over (Spec (CommRingCat.of R'))} (x : T ⟶ D'.P.A) (z : T.left) J J', Good D.P.L z J →
      Good D'.P.L z J' → ∀ Ω : (T ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, Ω x = gw hD.w x.left z (J (x.left ≫ Φ)) (J' x.left)) → val u (x.left ≫ Φ) z J =
        Ω (x * (x ≫ ιD'.onB.act w0)) * (Ω x ^ 2)⁻¹ * (Ω (x ≫ ιD'.onB.act w0))⁻¹ * Ω 1 ^ 2 * val u' x.left z J' :=
    fun x z J J' hJ hJ' Ω hΩ => by
      rw [hΩ, hΩ, hΩ, hΩ]
      exact (pmaps_val hψ pmu x.left z hJ hJ').trans (congrArg₂ (· * ·)
        (prod_four (ιD'.onB.act w0) x (fun q => gw hD.w q z (J (q ≫ Φ)) (J' q))) rfl)
  refine ⟨u', hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun a => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have := ιD'.onB.hom w0
    have e := vu (1 : 𝟙_ _ ⟶ D'.P.A) y J J' hJ hJ' _ (fun _ => rfl)
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have b := val_corr hJ hn (specOf φ)
    rw [val_pull hJ, val_one, ← hD.he] at b
    rw [MonObj.one_comp, _root_.mul_one, e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    have e' := congrArg Additive.ofMul (b.symm.trans e)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ :=
      fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
    have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
      fun χ => val_psiW hD hJ hJ' χ
    have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
      have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
        (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
      have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
        congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
      have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
        (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
      rw [Fintype.prod_unique, zpow_one] at e
      have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
      have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
      rw [b₁, b₂]
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
    have cW : hD.g ≫ (cP D (TW hD.W) (hD.xe a)).left = (cP D' (TK R') a).left ≫ Φ := by
      have hx : (cP D' (TK R') a).left ≫ Φ = jK R' ≫ specOf φ ≫ (D.c (hD.xe a)).left := by
        rw [← hD.c_pr a, ← Category.assoc]; rfl
      rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
    have cl : cP D' (TK R') a ≫ ιD'.onB.act w0 = cP D' (TK R') (w0 • a) := by
      rw [cP, cP, ιD'.c_lin, Category.assoc]
    have key := (val_mul hJ _ _ _).symm.trans ((val_corr hJ
      (rel_on hD.psiW ⟨_, (hD.g y).2⟩ u _ _ (hrel (hD.xe a))) hD.g).trans (val_mul hJ _ _ _))
    rw [val_pull hJ, cW, vu (cP D' (TK R') a) y J J' hJ hJ' Ω (fun _ => rfl), cl, val_tauW _ _ hJ, ← hx, ← map_add,
      vψ, vψ, vψ, vρ, cPoint_add] at key
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    have b : val (LB.pullGen D'.P.L _ _ u' (D'.xK a)) (𝟙 _) y J' = val u' (cP D' (TK R') a).left y J' := by
      rw [val_pull hJ', Category.id_comp]; rfl
    rw [b, val_tau _ hJ']
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul key
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'

end Pull

end PsiWZeroPull

theorem traceFormTwistIso_of_overPullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X]
    [Module O D'.X] (ιD : D.OAct O) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) →
    (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) →
    ∀ w0 : O, Geo.Tor.TraceFormTwistIso D ιD w0 → Geo.Tor.TraceFormTwistIso D' ιD' w0 :=
  fun _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ ιD ιD' hx hact w0 h => PsiWZeroPull.traceFormTwistIso_of_pullback hD ιD ιD' hx hact w0 h

end GlobalTheory
