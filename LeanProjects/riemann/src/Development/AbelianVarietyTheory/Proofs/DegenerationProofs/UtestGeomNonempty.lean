import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaGeom
open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

theorem val_powFrame {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (x : T ⟶ A) (e) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) : val (powFrame A L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem val_rigT {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
    (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J (fun _ => J (r ≫ T.hom ≫ eSec A))
    (fun _ => by rw [Category.assoc])]
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem sv_sum {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    ThetaAct.sv (∑ i, c i • v i) r z J = ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) * ThetaAct.sv (v i) r z J := by
  let F : SecM A L k T →+ Z.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v r z J) fun a b => ThetaAct.sv_add a b r z hJ
  exact (map_sum F _ _).trans (Finset.sum_congr rfl fun i _ => ThetaAct.sv_smul _ _ _ _ hJ)

theorem comb_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (t : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T)) :
    (∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (t l).f j) ↔ SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (t l) := by
  have e : ∀ j, (∑ l, c l • SecM.ofSec A (t l)).1 j = ∑ l, liftFun A _ (c l) * (t l).f j := fun j => by
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem genThrough_pow {x : T ⟶ A} {x₀ : T₀ ⟶ G} {e e₀}
    (H : GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => 1) e e₀ τ) (k : ℤ) :
    GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => k)
      (powFrame A L₁ x e k) (powFrame G L₀ x₀ e₀ k) τ := fun Z r z J J' hJ hJ' => by
  rw [val_powFrame, val_powFrame, H Z r z J J' hJ hJ', Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, mul_zpow]

theorem secRel_comb {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤)) {t : I → LB.Sec (LPow A L₁ k T)}
    {t₀ : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (t₀ l)) {σ σ₀}
    (e : SecM.ofSec A σ = ∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l))
    (e₀ : SecM.ofSec G σ₀ = ∑ l, c l • SecM.ofSec G (t₀ l)) : SecRel hp τ hτ w σ σ₀ := fun Z r z J J' hJ hJ' => by
  have a := (congrArg (fun q => ThetaAct.sv q r z J') e).trans (sv_sum _ _ r z hJ')
  have a₀ := (congrArg (fun q => ThetaAct.sv q (r ≫ psi hp τ hτ) z J) e₀).trans (sv_sum _ _ _ z hJ)
  refine a₀.trans (Eq.trans ?_ (congrArg (_ * ·) a).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial _).symm (h l Z r z J J' hJ hJ')

include hτ in
theorem norm_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {n : ℕ} {rig rig₀}
    (hr : GenThrough w (fun _ : PUnit => eSec A) (fun _ : PUnit => eSec G) (fun _ => 1) rig rig₀ f)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ n).left] ![a, -1])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![a, -1])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ (snd T A ^ n).left) ^ (-1 : ℤ)) * val α r z J')
    (H₀ : LB.Gen.Corr L₀ _ _ _ _ (LB.pullGen L₀ _ _ α₀ (ptSecT G 1).left)
      (LB.mulGen L₀ _ _ _ _ (rigT G L₀ rig₀ T₀ a) (rigT G L₀ rig₀ T₀ (-1)))) :
    LB.Gen.Corr L₁ _ _ _ _ (LB.pullGen L₁ _ _ α (ptSecT A 1).left) (rigT A L₁ rig T (a - 1)) := by
  refine corr_of_val hL₁ fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := val_corr hJ H₀ (𝟙 _ ≫ τ)
  have e₁ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ptSecT_snd]; rfl
  have e₂ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A ^ n).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl
  rw [val_pull hJ, val_mul hJ, val_rigT _ _ _ hJ, val_rigT _ _ _ hJ, Category.assoc,
    ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc, H _ _ _ _ _ hJ hJ', e₁, e₂, Category.assoc (𝟙 _) τ, hτ,
    ← Category.assoc (𝟙 _) T.hom f] at q
  have q₂ := hr _ (𝟙 _ ≫ T.hom) y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at q₂
  rw [val_pull hJ', val_rigT _ _ _ hJ']
  erw [q₂] at q
  apply Additive.ofMul.injective
  replace q := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_zpow] at q ⊢
  linear_combination (norm := module) q

end GlobalTheory.ThetaGeom
namespace GlobalTheory.ZH
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaGeom

theorem spMap_appTop_fn {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (a : R) :
    (spMap y).appTop.hom (fn a) = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (y a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem valAt_of_isValueAt {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x}
    {c : F} (h : IsValueAt A.A A.L k t x (powFrame A.A A.L x e k) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)) :
    ValAt t x e c := fun z J hJ => by
  have q := sv_of_isValueAt h (𝟙 _) z hJ
  rw [Category.id_comp] at q
  exact q

theorem utest_geom_nonempty : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), Nonempty u.Geom := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x, hx, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨rig, fr, hrig, vrig, hfr⟩ := GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso o Ω S ρ p y₀ u x hx w hw
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans (congrArg spMap u.fac.symm) ?_)
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, x (n • a) = x a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := hadd 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => by
    rw [hpow, ← pow_mul]
    exact (hfr a).1.1
  choose U hU hU' using fun a => symLift_move hp τ hτ hw hL₀ hL₁ (hx (S.r • a)).symm (hN a) (ρ.U_sym a)
  obtain ⟨r₀, hr₀, -⟩ := thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  obtain ⟨r₁, hr₁, -⟩ := thetaGrp_acts_linearly hL.globalFns _ u.A S.N (TFK (R := u.V) (PadicAlgCl p))
  refine ⟨⟨x, hx, hadd, fun z hz => ?_, GlobalTheory.T.weilPairing_labelledTorsion_uniformTest hL o Ω S ρ p y₀ u x hx, rig, hrig, fr, fun a => (hfr a).1, th,
    fun a z J hJ => ?_, s, fun a i => valAt_of_isValueAt ?_, α, hα,
    norm_move hp τ hτ hL₀ hL₁ vrig vα ρ.α_norm,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero,
    U, hU, fun a i σ => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hsurj z hz
    exact ⟨a, rfl, fun b hb => hinj hb⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (hfr a).2 hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (genThrough_pow τ (hfr a).2 S.N) (hs i) (ρ.ev_val i a)
    rw [spMap_appTop_fn] at h
    exact h
  · have a₀ : IsActOf ρ.P.A ρ.P.L S.N (ρ.U a) (ρ.s i) (SecM.toSec _ (r₀ (ρ.U a) (SecM.ofSec _ (ρ.s i)))) :=
      (hr₀ _ _ _).2 rfl
    let c : S.J → Γ((baseOver (Sp S.R)).left, ⊤) := fun l => fn (algebraMap o S.R (S.ρ a l i))
    have hc : (fun l => τ.appTop.hom (c l)) = fun l => (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom
        (y₀ (algebraMap o S.R (S.ρ a l i))) := funext fun l => spMap_appTop_fn y₀ _
    have a₁ := hU' a _ _ _ (SecM.toSec _ (∑ l, τ.appTop.hom (c l) • SecM.ofSec _ (s l))) (hs i)
      (secRel_comb hp τ hτ c hs rfl ((comb_iff _ _ _).1 (ρ.U_act a i _ a₀))) a₀
    have a₂ := (hr₁ _ _ _).1 a₁
    have a₃ := comb_iff (fun l => τ.appTop.hom (c l)) s σ
    refine (hr₁ _ _ _).trans (Iff.trans ⟨fun h => a₃.2 (h.symm.trans a₂), fun h => a₂.trans (a₃.1 h).symm⟩ ?_)
    exact forall_congr' fun j => Eq.congr_right (Finset.sum_congr rfl fun l _ => by rw [congrFun hc l])

end GlobalTheory.ZH
end
