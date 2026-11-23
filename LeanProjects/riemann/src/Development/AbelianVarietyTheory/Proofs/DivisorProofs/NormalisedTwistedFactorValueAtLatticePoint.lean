import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFacVal

section General

variable {X Y Z : Scheme.{0}}

def pt (q : Y ⟶ X) : Multiplicative (FreeAbelianGroup (Y ⟶ X)) := Multiplicative.ofAdd (FreeAbelianGroup.of q)

def ratSub {L : LB X} (e₀ e₁ : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Subgroup (Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ) where
  carrier := {g | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∏ k, pt (φ k) ^ ε k = g.1 ∧ val t e₁ z J = g.2 * val t e₀ z J}
  one_mem' := ⟨PEmpty, inferInstance, _, _, LB.oneGen L, (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm), Fintype.prod_empty _, by
      rw [val_one, val_one]; exact (_root_.mul_one _).symm⟩
  mul_mem' := by
    rintro g g' ⟨K, _, φ, ε, t, ht, f, v⟩ ⟨K', _, φ', ε', t', ht', f', v'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
      DVR.prod_sum₂ _ f f', ?_⟩
    rw [val_mul hJ, val_mul hJ, v, v']
    exact mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    rintro g ⟨K, _, φ, ε, t, ht, f, v⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, DVR.prod_neg _ _ f, ?_⟩
    rw [val_inv, val_inv, v]
    exact mul_inv _ _

theorem ratSub_eq_one {L : LB X} (hL : L.IsLB) (p : Y ⟶ Z) (e₀ e₁ : Z ⟶ Y) (h₀ : e₀ ≫ p = 𝟙 _) (h₁ : e₁ ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    {g : Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ} (hg : g ∈ ratSub e₀ e₁ hJ) (h : g.1 = 1) :
    g.2 = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, f, v⟩ := hg
  have triv : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = 1 := fun U _ k => by
    let F : Multiplicative (FreeAbelianGroup (Y ⟶ X)) →* U :=
      AddMonoidHom.toMultiplicativeLeft (FreeAbelianGroup.lift fun q => Additive.ofMul (k q))
    have hF : ∀ q, F (pt q) = k q := fun q => by simp [F, pt]
    have := congrArg F (f.trans h)
    simpa only [map_prod, map_zpow, hF, map_one] using this
  have key := gen_unique' hL (φ := φ) (ε := ε) (φ' := fun k => (p ≫ e₀) ≫ φ k) (ε' := ε)
    (fun U _ k => (triv U fun q => k ((p ≫ e₀) ≫ q)).trans (triv U k).symm) p e₀ h₀ hp ht
    (DVR.pullGen_isGen _ _ _ _ ht (p ≫ e₀)) (fun y I hI => by
      rw [val_pull hI, ← Category.assoc, h₀, Category.id_comp]) _ e₁ z J hJ
  rw [val_pull hJ, ← Category.assoc, h₁, Category.id_comp, v] at key
  exact mul_eq_right.1 key

end General

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T B : Over (Spec (CommRingCat.of R))}

theorem prod_tφ (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) (ρ : B ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (B.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ tφ D a β i) ^ tε n j i =
      h ρ.left ^ (n - 1) * h (ρ * DVR.cP D B β).left * (h (DVR.cP D B β).left)⁻¹ * h (1 : B ⟶ D.P.A).left *
        h (ρ ≫ a).left ^ j := by
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ tφ D a β 1 = (ρ * DVR.cP D B β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D B β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : B ⟶ D.P.A).left :=
    congrArg (fun q : B ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

variable (ρ₀ ρ₁ : T ⟶ B) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)

theorem mem_const (κ : B ⟶ TK R) (hκ : ρ₁ ≫ κ = ρ₀ ≫ κ) (χ : D.X) :
    (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine (Subgroup.inv_mem_iff _).1 ⟨PUnit, inferInstance, _, _, LB.pullGen D.P.L _ _ (D.psi χ) κ.left,
    DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _, ?_, ?_⟩
  · rw [Fintype.prod_unique, zpow_neg_one, ← DVR.comp_cP D κ χ]; rfl
  · rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, hκ]
    simp

theorem mem_cub (x x' y : B ⟶ D.P.A) :
    (pt (x * x' * y).left * (pt (x * x').left)⁻¹ * (pt (x * y).left)⁻¹ * (pt (x' * y).left)⁻¹ * pt x.left * pt x'.left *
        pt y.left * (pt (1 : B ⟶ D.P.A).left)⁻¹,
      cubV D.cub z J (ρ₁ ≫ x) (ρ₁ ≫ x') (ρ₁ ≫ y) * (cubV D.cub z J (ρ₀ ≫ x) (ρ₀ ≫ x') (ρ₀ ≫ y))⁻¹) ∈
      ratSub ρ₀.left ρ₁.left hJ :=
  ⟨thK, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ D.cub.isGen _, prod_cub x x' y pt,
    (val_cub D.cub ρ₁ hJ x x' y).trans ((inv_mul_cancel_right _ _).symm.trans
      (congrArg (_ * ·) (val_cub D.cub ρ₀ hJ x x' y).symm))⟩

theorem mem_ros (f g : D.P.A ⟶ D.P.A) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (x y : B ⟶ D.P.A) :
    (pt ((x ≫ f) * y).left * (pt (x ≫ f).left)⁻¹ * (pt y.left)⁻¹ * (pt (x * (y ≫ g)).left)⁻¹ * pt x.left * pt (y ≫ g).left,
      val₂ u z J (ρ₁ ≫ x) (ρ₁ ≫ y) * (val₂ u z J (ρ₀ ≫ x) (ρ₀ ≫ y))⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine ⟨Fin 6, inferInstance, _, _, LB.pullGen D.P.L _ _ u (lift x y).left,
    DVR.pullGen_isGen _ _ _ _ hu _, prod_ros f g x y pt, ?_⟩
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift]
  exact (inv_mul_cancel_right _ _).symm

end Points

theorem mem_of_add {X G : Type} [AddCommGroup X] [CommGroup G] (H : Subgroup G) (l : X → G)
    (hl : ∀ a b, l (a + b) * (l a)⁻¹ * (l b)⁻¹ ∈ H) (n j : ℤ) (β ν δ : X) :
    l (β + (n • ν + j • δ)) * (l β * l ν ^ n * l δ ^ j)⁻¹ ∈ H := by
  let f : X →+ Additive (G ⧸ H) := AddMonoidHom.mk' (fun a => Additive.ofMul (QuotientGroup.mk' H (l a))) (fun a b => by
    have := (QuotientGroup.eq_one_iff _).2 (hl a b)
    rw [← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv, map_inv, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at this
    rw [this, ofMul_mul])
  have e : f (β + (n • ν + j • δ)) = f β + (n • f ν + j • f δ) := by simp only [map_add, map_zsmul]
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [← QuotientGroup.mk'_apply, map_mul, map_inv, map_mul, map_mul, map_zpow, map_zpow, mul_inv_eq_one, _root_.mul_assoc]
  exact congrArg Additive.toMul e

theorem val_fac {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (a a' : D.P.A ⟶ D.P.A)
    (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (n j : ℤ) (ν mu β₀ β₁ : D.X) (hβ : β₁ = β₀ + shift h h' n j ν)
    (u₁ : LB.Gen (LB.LinComb D.P.L (dφ D a ν β₀ β₁) (dε n j))) (hu₁ : IsFac D a h n j ν β₀ β₁ u₁)
    (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    val u₁ ((DegPre.zF D (FractionRing R)).left ≫ (DegPre.trF D (FractionRing R) mu).left) z J =
      (val (D.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n *
        val (D.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) *
      (val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  obtain ⟨ha, ha', hr, hc, hc', hbal⟩ := hE
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  let T : Over (Spec (CommRingCat.of R)) := TF (R := R) (FractionRing R)
  let B : Over (Spec (CommRingCat.of R)) := DegPre.BF D (FractionRing R)
  let ρ₀ : T ⟶ B := DegPre.zF D (FractionRing R)
  let ρ₁ : T ⟶ B := DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu
  let x : B ⟶ D.P.A := DegPre.prB D (FractionRing R)
  let p : B ⟶ T := fst _ _
  let κ : T ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have tx : ∀ χ, DegPre.trF D (FractionRing R) χ ≫ x = x * DVR.cP D B χ := fun χ => lift_snd _ _
  have p₀ : ρ₀ ≫ p = 𝟙 _ := lift_fst _ _
  have p₁ : ρ₁ ≫ p = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (lift_fst _ _)).trans p₀)
  have x₀ : ρ₀ ≫ x = 1 := lift_snd _ _
  have x₁ : ρ₁ ≫ x = DVR.cP D T mu := by
    refine (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (tx mu)).trans ((MonObj.comp_mul _ _ _).trans ?_))
    rw [x₀, DVR.comp_cP, _root_.one_mul]
  have ca : ∀ S χ, DVR.cP D S χ ≫ a = DVR.cP D S (h χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc, Category.assoc]
  have ca' : ∀ S χ, DVR.cP D S χ ≫ a' = DVR.cP D S (h' χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc', Category.assoc]
  have c0 : DVR.cP D B 0 = 1 := by simpa using DVR.cPoint_nsmul D B 0 0
  have s : (𝟙 T : T ⟶ T).left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) (FractionRing R) := Category.id_comp _

  let τ : D.X → D.X → (T.left.presheaf.stalk z)ˣ := fun χ χ' => val (D.tau χ χ') (jFK (R := R) (FractionRing R)) z J
  have tm : ∀ χ χ' b, τ (χ + χ') b * cubV D.cub z J (DVR.cP D T χ) (DVR.cP D T χ') (DVR.cP D T b) = τ χ b * τ χ' b :=
    fun χ χ' b => by have := DVR.tau_mul (𝟙 T) hJ hB χ χ' b; rw [s] at this; exact this
  have ts : ∀ χ χ', τ χ χ' = τ χ' χ := fun χ χ' => by have := DVR.tau_symm (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  let ψ : D.X → (T.left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (jFK (R := R) (FractionRing R)) z J
  let rg : (T.left.presheaf.stalk z)ˣ := val D.rigK (jFK (R := R) (FractionRing R)) z J
  have pa : ∀ χ χ', ψ (χ + χ') = τ χ χ' * ψ χ * ψ χ' * rg := fun χ χ' => by
    have := DVR.UUA.psi_add (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  have tb : τ (h mu) (h ν) * val₂ u (T := T) z J (DVR.cP D T mu) (DVR.cP D T (h ν)) = τ mu (h' (h ν)) := by
    have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ mu (h ν)) κ.left)
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    rw [val_pull hJ, val₂, ← DVR.comp_cP D κ, ← DVR.comp_cP D κ, ← comp_lift]
    rfl
  have r₀ : val₂ u (T := T) z J 1 (DVR.cP D T (h ν)) = 1 := by
    have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ (h ν))).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm

  have mc : ∀ χ, (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    mem_const ρ₀ ρ₁ hJ (p ≫ κ) (by rw [← Category.assoc, ← Category.assoc, p₀, p₁])
  have ml := mem_of_add (ratSub ρ₀.left ρ₁.left hJ) (fun χ => (pt (DVR.cP D B χ * x).left * (pt x.left)⁻¹ *
      (pt (DVR.cP D B χ).left)⁻¹ * pt (1 : B ⟶ D.P.A).left, (τ χ mu)⁻¹)) (fun χ χ' => by
    have m := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B χ) (DVR.cP D B χ') x
    simp only [DVR.comp_cP, x₀, x₁, C.face₃] at m
    convert m using 1
    have t := congrArg Additive.ofMul (tm χ χ' mu)
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, DVR.cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · simp only [Prod.snd_mul, Prod.snd_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at t ⊢
      linear_combination (norm := abel) -t) n j β₀ ν (h' (h ν))
  rw [show β₀ + (n • ν + j • h' (h ν)) = β₁ from hβ.symm] at ml
  have mr := mem_ros ρ₀ ρ₁ hJ a a' u hu x (DVR.cP D B (h ν))
  simp only [DVR.comp_cP, x₀, x₁, r₀, ca'] at mr
  have mk := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B ν) x (DVR.cP D B β₀)
  simp only [DVR.comp_cP, x₀, x₁, C.face₂] at mk
  have f₁ := prod_tφ a n j β₁ x pt
  have f₀ := prod_tφ a n j β₀ (DegPre.trF D (FractionRing R) ν ≫ x) pt
  have mu₁ : (_, val u₁ ρ₁.left z J * (val u₁ ρ₀.left z J)⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    ⟨Fin 5 ⊕ Fin 5, inferInstance, _, _, u₁, hu₁.1, DVR.prod_sum₂ _ f₁ (DVR.prod_neg _ _
      ((Finset.prod_congr rfl fun i _ => by rw [Over.comp_left, Category.assoc]; rfl).trans f₀)),
      (inv_mul_cancel_right _ _).symm⟩
  rw [tx, MonObj.mul_comp, ca] at mu₁
  have key := ratSub_eq_one D.P.isLB p.left ρ₀.left ρ₁.left (congrArg (fun q => q.left) p₀) (congrArg (fun q => q.left) p₁)
    (DVR.surj_appTop D (FractionRing R) hG) hJ
    (mul_mem (mul_mem (mul_mem (mul_mem mu₁ (inv_mem ml)) (zpow_mem mr j)) mk)
      (mul_mem (mul_mem (mul_mem (mul_mem (mc (ν + β₀)) (zpow_mem (mc ν) (n - 1))) (inv_mem (mc β₀)))
        (zpow_mem (mc 0) (1 - n - j))) (zpow_mem (mc (h ν)) j))) (by
      simp only [Prod.fst_mul, Prod.fst_inv, Prod.pow_fst, DVR.cPoint_add, c0, _root_.mul_comm (DVR.cP D B _) x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have v₀ := hu₁.2 z J hJ
  simp only [Prod.snd_mul, Prod.snd_inv, Prod.pow_snd] at key
  show val u₁ ρ₁.left z J = ψ (ν + mu) ^ n * ψ (h (ν + mu)) ^ j * τ (ν + mu) β₀ * rg ^ (n + j) *
    (ψ mu ^ n * ψ (h mu) ^ j * τ mu β₁ * rg ^ (n + j))⁻¹
  change val u₁ ρ₀.left z J = ψ ν ^ n * ψ (h ν) ^ j * τ ν β₀ * rg ^ (n + j) at v₀
  rw [map_add, pa, pa]
  rw [v₀, ts β₁, ts β₀, ts (h' (h ν)), ← tb, ts (h mu)] at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  have t := congrArg Additive.ofMul (tm ν mu β₀)
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, smul_add, smul_neg] at k t ⊢
  linear_combination (norm := module) k - t

theorem val_fac_at_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ :=
  fun _ _ _ _ _ D a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ =>
    val_fac D.toPre D.tau_bimult a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ

end GlobalTheory.TwFacVal
