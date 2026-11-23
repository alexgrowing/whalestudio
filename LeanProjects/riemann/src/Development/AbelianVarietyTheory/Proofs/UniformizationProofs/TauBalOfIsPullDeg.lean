import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TauBalPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem tauW_bal_corr (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b')) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b)
        (LB.pullGen D.P.L _ _ u (lift (cP D (TW W) y) (cP D (TW W) y')).left)) (ψW.tau a' b') := by
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
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ h (𝟙 _))
    refine (val_mul hJ _ _ _).trans ?_
    rw [vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    rw [Category.id_comp, ← Over.comp_left, comp_lift, comp_cP, comp_cP]
    rfl

theorem tauW_bal (ψW : PsiOn D W)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b'))
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) κ.left z J * val₂ u z J (cP D T y) (cP D T y') = val (ψW.tau a' b') κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tauW_bal_corr ψW ⟨_, (κ.left z).2⟩ u a b a' b' y y' h) κ.left)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_pull hJ _ _ _).symm
  rw [← Over.comp_left, comp_lift, comp_cP, comp_cP]
  rfl

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem push_comp (hD : IsPullDeg φ D D') {f : D.P.A ⟶ D.P.A} {f' : D'.P.A ⟶ D'.P.A}
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) {T : Over (Sp R')} (x : T ⟶ D'.P.A) :
    pushPt (pull_grp hD).1.w (x ≫ f') = pushPt (pull_grp hD).1.w x ≫ f := by
  refine Over.OverMorphism.ext ?_
  have h₁ : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) hf
  have h₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  show (x.left ≫ f'.left) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
    (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left
  rw [Category.assoc, ← Category.assoc f'.left, h₁]
  simp only [Category.assoc]
  exact congrArg (fun q => x.left ≫ hD.e.hom.left ≫ q) h₂

theorem push_inj (hD : IsPullDeg φ D D') {T : Over (Sp R')} {x y : T ⟶ D'.P.A}
    (h : pushPt (pull_grp hD).1.w x = pushPt (pull_grp hD).1.w y) : x = y :=
  Over.OverMorphism.ext ((pull_grp hD).1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))

theorem val₂_one {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {K : Type} [Fintype K]
    {ψ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L ψ ε))
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (lift η[A] η[A]).left) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by rw [comp_lift]; rfl
  have := val_corr hJ h₀ (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem ros_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g]
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    {T : Over (Sp R')} {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x y : T ⟶ D'.P.A) :
    val u (lift (pushPt (pull_grp hD).1.w x) (pushPt (pull_grp hD).1.w y)).left z J =
      (∏ i, gw hD.w ((lift x y).left ≫ rosatiφ D'.P.A f' g' i) z
        (J (((lift x y).left ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' ((lift x y).left ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' (lift x y).left z J' := by
  have gp := pull_grp hD
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A), pushPt gp.1.w (x * y) = pushPt gp.1.w x * pushPt gp.1.w y :=
    fun x y => map_mul (pushHom gp _) x y
  have p1 : ∀ {T : Over (Sp R')}, pushPt gp.1.w (1 : T ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB u' hu'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D'.P.A ⊗ D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, gw hD.w (r ≫ rosatiφ D'.P.A f' g' i) z
        (J ((r ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' (r ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let m : (D'.P.A ⊗ D'.P.A).left ⟶ (D.P.A ⊗ D.P.A).left :=
    (lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A))).left
  have hm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A),
      (lift x y).left ≫ m = (lift (pushPt gp.1.w x) (pushPt gp.1.w y)).left := fun {T} x y => by
    let ρ : Over.mk (T.hom ≫ spMap φ) ⟶ Over.mk ((D'.P.A ⊗ D'.P.A).hom ≫ spMap φ) :=
      Over.homMk (lift x y).left (by
        show (lift x y).left ≫ (D'.P.A ⊗ D'.P.A).hom ≫ spMap φ = T.hom ≫ spMap φ
        rw [← Category.assoc, Over.w])
    have r : ∀ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, ρ ≫ pushPt gp.1.w q = pushPt gp.1.w (lift x y ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have : ρ ≫ lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) =
        lift (pushPt gp.1.w x) (pushPt gp.1.w y) := by rw [comp_lift, r, r, lift_fst, lift_snd]
    exact congrArg (fun q => q.left) this
  let e : 𝟙_ (Over (Sp R')) ⟶ D'.P.A ⊗ D'.P.A := lift 1 1
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : e.left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun i => m ≫ rosatiφ D.P.A f g i) (ε := rosatiε)
    (fun V _ k => by
      have p₁ := prod_ros f g (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) k
      have p₂ := prod_ros f' g' (fst D'.P.A D'.P.A) (snd D'.P.A D'.P.A)
        (fun q => k (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
      rw [lift_fst_snd, Over.id_left] at p₂
      simp only [Category.id_comp] at p₂
      rw [← push_comp hD hf, ← push_comp hD hg, ← pm, ← pm] at p₁
      exact p₂.trans p₁.symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hu m) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have p := prod_ros f' g' (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1
        (fun q => gw hD.w q y (I (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (I' q))
      have f₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ f' = 1 :=
        push_inj hD (by rw [push_comp hD hf, p1, MonObj.one_comp])
      have g₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ g' = 1 :=
        push_inj hD (by rw [push_comp hD hg, p1, MonObj.one_comp])
      rw [f₁, g₁, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (val₂_one u' h₀' hI'))).symm
      refine (val_pull hI _ _ _).trans ?_
      rw [hm, p1]
      refine (val₂_one u h₀ (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).trans ?_
      simp) _ (lift x y).left z J hJ
  rw [← hm]
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

set_option maxHeartbeats 1000000 in
theorem tauBal_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g] (hr : RosatiAdj D.P.A D.P.L f g)
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    {a b : D.X → D.X} {a' b' : D'.X → D'.X} (ha : ∀ y, hD.xe (a' y) = a (hD.xe y))
    (hb : ∀ y, hD.xe (b' y) = b (hD.xe y)) (ca : ∀ y, D.c (a y) = D.c y ≫ f) (cb : ∀ y, D.c (b y) = D.c y ≫ g)
    (hB : D.TauBal f g a b) : D'.TauBal f' g' a' b' := by
  intro u' hu' h₀' s s'
  obtain ⟨u, hu, h₀⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  have ca' : cP D' (TK R') (a' s) = cP D' (TK R') s ≫ f' := push_inj hD (by
    rw [push_comp hD hf]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ f) (βc s)).symm)
    rw [ha, cP, ca]; exact (Category.assoc _ _ _).symm)
  have cb' : cP D' (TK R') (b' s') = cP D' (TK R') s' ≫ g' := push_inj hD (by
    rw [push_comp hD hg]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ g) (βc s')).symm)
    rw [hb, cP, cb]; exact (Category.assoc _ _ _).symm)
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let υ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := val₂ u (T := T) y J
  have ros : ∀ p q : TK R' ⟶ D'.P.A, υ (β p) (β q) =
      Ω ((p ≫ f') * q) * (Ω (p ≫ f'))⁻¹ * (Ω q)⁻¹ * (Ω (p * (q ≫ g')))⁻¹ * Ω p * Ω (q ≫ g') * val₂ u' y J' p q :=
    fun p q => (ros_pull hG hD hf hg u hu h₀ u' hu' h₀' (T := TK R') hJ hJ' p q).trans
      (congrArg₂ (· * ·) (prod_ros f' g' p q (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have key : val (hD.psiW.tau (a (hD.xe s)) (hD.xe s')) hD.g y J * υ (cP D T (hD.xe s)) (cP D T (hD.xe s')) =
      val (hD.psiW.tau (hD.xe s) (b (hD.xe s'))) hD.g y J :=
    tauW_bal hD.psiW u _ _ _ _ _ _ (hB u hu h₀ _ _) κ hJ
  rw [← βc, ← βc, ros, ← ha, ← hb, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add, ← map_add,
    vψ, vψ, vψ, vψ, vψ, vψ, cPoint_add, cPoint_add, ca', cb'] at key
  refine (val_mul hJ' _ _ _).trans ?_
  have vu : val (LB.pullGen D'.P.L _ _ u' (D'.pt2 s s')) (𝟙 _) y J' =
      val₂ u' (T := TK R') y J' (cP D' _ s) (cP D' _ s') := by
    rw [val_pull hJ', Category.id_comp]; rfl
  rw [vu, val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Pull

end TauBalPull

theorem tauBal_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → RosatiAdj D.P.A D.P.L f g → f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f → g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g → ∀ (a b : D.X → D.X) (a' b' : D'.X → D'.X), (∀ y, hD.xe (a' y) = a (hD.xe y)) → (∀ y, hD.xe (b' y) = b (hD.xe y)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → D.TauBal f g a b → D'.TauBal f' g' a' b' :=
  fun hG _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ _ hr hf hg _ _ _ _ ha hb ca cb hB =>
    TauBalPull.tauBal_pull hG hD hr hf hg ha hb ca cb hB

end GlobalTheory
