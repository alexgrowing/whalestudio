import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslCP

open GlobalTheory.CubTransport GlobalTheory.UU

section Gen
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_transl_gen (hL : L.IsLB) (τ : X ⟶ X) {K : Type} [Fintype K] {φ' φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hc : ∀ k, φ' k ≫ τ = φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb (L.pull τ) φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good L z J → Good (L.pull τ) z J' →
        val t r z J = (∏ k, gw (pullIso L τ) (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ τ)) (J' (r ≫ φ' k)) ^ ε k) *
          val t' r z J' := by
  have hc' : ∀ k, φ' k ≫ τ = 𝟙 Y ≫ φ k := fun k => (hc k).trans (Category.id_comp _).symm
  obtain ⟨a, ha, H⟩ := exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL τ)) hL (pull_isLB hL τ) (𝟙 Y) hc' t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  have e := val_pmaps hc' H r hJ hJ'
  rwa [Category.comp_id] at e

theorem gw_pullIso_self (hL : L.IsLB) (τ : X ⟶ X) (f : Y ⟶ X) (y : Y) {j : L.ι} (hj : τ (f y) ∈ L.U j) :
    gw (pullIso L τ) f y j (fun _ => j) = 1 :=
  gm_self (pull_isLB hL τ) f y (mem_pull.2 hj)

theorem gw_pullIso_good (hL : L.IsLB) (τ : X ⟶ X) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (f : Z ⟶ X) : gw (pullIso L τ) f z (J (f ≫ τ)) (fun _ => J (f ≫ τ)) = 1 :=
  gw_pullIso_self hL τ f z (hJ (f ≫ τ))

theorem good_pull {Z : Scheme.{0}} (τ : X ⟶ X) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (L.pull τ) z (fun r _ => J (r ≫ τ)) := fun r => mem_pull.2 (hJ (r ≫ τ))

end Gen

section Grp
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem comp_transl (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (toUnit T), Category.comp_id]

theorem toUnit_comp_inv (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) (T : Over S) : (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := by
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ha])
  rw [← GrpObj.comp_inv, this]

theorem eSec_eq_one_left : eSec G = (1 : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]; rfl

theorem toUnit_left' (T : Over S) (a : 𝟙_ (Over S) ⟶ G) : (toUnit T ≫ a).left = T.hom ≫ a.left := by
  rw [Over.comp_left, Rosenlicht.toUnit_left]

end Grp

section Main
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem transl_comp_inv (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) :
    ((toUnit G ≫ a) * 𝟙 G).left ≫ (ι[G]).left = (ι[G]).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have i1 : ι[G] = (𝟙 G)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have e : ((toUnit G ≫ a) * 𝟙 G) ≫ ι[G] = ι[G] ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, toUnit_unique (ι[G] ≫ toUnit G) (toUnit G),
      Category.comp_id, mul_inv, toUnit_comp_inv a ha, i1]
  rw [← Over.comp_left, ← Over.comp_left, e]

theorem exists_symL (P : CP G) (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) (fun k => ![(ι[G]).left, 𝟙 G.left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]),
      t.IsGen ∧ ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
        val t x.left z J = val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹ := by
  have hm := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen ((toUnit G ≫ a) * 𝟙 G).left)
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen (G.hom ≫ a.left)))
  have hi : (G.hom ≫ a.left) ≫ (ι[G]).left = G.hom ≫ a.left := by
    have : a ≫ ι[G] = a := by rw [← Hom.inv_def]; exact inv_eq_of_mul_eq_one_left (by rw [← pow_two, ha])
    rw [Category.assoc, ← Over.comp_left, this]
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := fun k => ![(ι[G]).left, 𝟙 G.left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left)
    (ε' := ![1, -1]) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hi, Category.comp_id, Category.id_comp, transl_comp_inv a ha]
      simp only [zpow_one, zpow_neg, inv_inv, mul_inv_cancel, inv_mul_cancel, _root_.mul_one]) _ hm
  refine ⟨t, ht, fun T x z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, comp_transl, ← Category.assoc, Over.w x,
    toUnit_left']
end Main

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lift_tripleCoordinates_eq_id : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
  ext <;> simp [x3]

theorem exists_cubL (P : CP G) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (fun I => thφ G (x3 G) I ≫ ((toUnit G ≫ a) * 𝟙 G).left) thε), t.IsGen ∧
      ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
        val t (lift x (lift y u)).left z J =
          cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹ := by
  have hm := DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.pullGen_isGen P.L.L (thφ G (x3 G)) thε P.c.t P.c.isGen
      (lift (x3 G 0) (lift (x3 G 1) ((toUnit (G3 G) ≫ a) * x3 G 2))).left)
    (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen P.L.L (thφ G (x3 G)) thε P.c.t P.c.isGen (lift (x3 G 0) (lift (x3 G 1) (toUnit (G3 G) ≫ a))).left))
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := fun I => thφ G (x3 G) I ≫ ((toUnit G ≫ a) * 𝟙 G).left) (ε' := thε) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      refine (congrArg₂ (· * ·) (prod_cub _ _ _ h) (congrArg (·⁻¹) (prod_cub _ _ _ h))).trans ?_
      have e := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) (fun q => h (q ≫ ((toUnit G ≫ a) * 𝟙 G).left))
      simp only [lift_tripleCoordinates_eq_id, Over.id_left, Category.id_comp, comp_transl] at e
      refine Eq.trans ?_ e.symm
      have c₁ : x3 G 0 * x3 G 1 * ((toUnit (G3 G) ≫ a) * x3 G 2) =
          (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 1 * x3 G 2) := by ac_rfl
      have c₂ : x3 G 0 * ((toUnit (G3 G) ≫ a) * x3 G 2) = (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 2) := by ac_rfl
      have c₃ : x3 G 1 * ((toUnit (G3 G) ≫ a) * x3 G 2) = (toUnit (G3 G) ≫ a) * (x3 G 1 * x3 G 2) := by ac_rfl
      have c₄ : x3 G 0 * x3 G 1 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 1) := by ac_rfl
      have c₅ : x3 G 0 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * x3 G 0 := mul_comm _ _
      have c₆ : x3 G 1 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * x3 G 1 := mul_comm _ _
      rw [c₁, c₂, c₃, c₄, c₅, c₆, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ hm
  refine ⟨t, ht, fun T x y u z J hJ => ?_⟩
  have r₀ : lift x (lift y u) ≫ x3 G 0 = x := by simp [x3]
  have r₁ : lift x (lift y u) ≫ x3 G 1 = y := by simp [x3]
  have r₂ : lift x (lift y u) ≫ x3 G 2 = u := by simp [x3]
  have r₃ : lift x (lift y u) ≫ (toUnit (G3 G) ≫ a) = toUnit T ≫ a := by
    rw [← Category.assoc, toUnit_unique (lift x (lift y u) ≫ toUnit (G3 G)) (toUnit T)]
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)
  refine (congrArg₂ (· * ·) (val_cub P.c _ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub P.c _ hJ _ _ _)))).trans ?_
  rw [r₀, r₁, MonObj.comp_mul, r₂, r₃]
end Cube

section Alg
variable {A U : Type} [CommGroup A] [CommGroup U]

theorem isCub_transl {C : A → A → A → U} (hC : IsCub C) (α : A) :
    IsCub (fun x y u => C x y (α * u) * (C x y α)⁻¹) where
  face x y := by simp only [hC.face, mul_inv_cancel]
  s01 x y u := by rw [hC.s01 x y, hC.s01 x y]
  s12 x y u := by
    have t : ∀ p q, C x p q = C p q x := fun p q => (hC.s01 x p q).trans (hC.s12 p x q)
    have e := hC.coc u α y x
    rw [← t, ← t, ← t, ← t, hC.s12 x (u * α) y, mul_comm u α, hC.s12 x α y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  coc x x' x'' y := by
    have e₁ := hC.coc x x' x'' (α * y)
    have e₂ := hC.coc x x' x'' α
    apply Additive.ofMul.injective
    have e₁' := congrArg Additive.ofMul e₁
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
    linear_combination (norm := abel) e₁' - e₂'

theorem sym_cub_transl (C : A → A → A → U) (σ : A → U) (α : A) (hα : α⁻¹ = α)
    (h : ∀ x y u, C x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) =
      C x y u * σ (x * y * u) * σ x * σ y * σ u) (x y u : A) :
    C x⁻¹ y⁻¹ (α * u⁻¹) * (C x⁻¹ y⁻¹ α)⁻¹ * (σ (α * (x * y)) * (σ α)⁻¹) * (σ (α * (x * u)) * (σ α)⁻¹) *
        (σ (α * (y * u)) * (σ α)⁻¹) =
      C x y (α * u) * (C x y α)⁻¹ * (σ (α * (x * y * u)) * (σ α)⁻¹) * (σ (α * x) * (σ α)⁻¹) *
        (σ (α * y) * (σ α)⁻¹) * (σ (α * u) * (σ α)⁻¹) := by
  have e₁ := h x y (α * u)
  have e₂ := h x y α
  have c₁ : x * (α * u) = α * (x * u) := by ac_rfl
  have c₂ : y * (α * u) = α * (y * u) := by ac_rfl
  have c₃ : x * y * (α * u) = α * (x * y * u) := by ac_rfl
  have c₄ : x * y * α = α * (x * y) := mul_comm _ _
  have c₅ : x * α = α * x := mul_comm _ _
  have c₆ : y * α = α * y := mul_comm _ _
  rw [mul_inv, hα, c₁, c₂, c₃] at e₁
  rw [hα, c₄, c₅, c₆] at e₂
  apply Additive.ofMul.injective
  have e₁' := congrArg Additive.ofMul e₁
  have e₂' := congrArg Additive.ofMul e₂
  simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
  linear_combination (norm := abel) e₁' - e₂'

end Alg

theorem exists_transl : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (a : 𝟙_ (Over S) ⟶ G),
    a ^ 2 = 1 → ∀ ρ : LB.Gen (P.L.L.pull a.left), ρ.IsGen →
    ∃ P' : GlobalTheory.UU.CP G, P'.L.L = P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left ∧
      (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P'.sym x.left z J' =
          val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹) ∧
      (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P'.c z J' x y u = cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹) := by
  intro S G _ _ P a ha ρ hρ
  have hL := P.L.isLB
  have hL' := pull_isLB hL ((toUnit G ≫ a) * 𝟙 G).left
  have hα : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := toUnit_comp_inv a ha

  have hc : ∀ _ : PUnit, eSec G ≫ ((toUnit G ≫ a) * 𝟙 G).left = a.left := fun _ => by
    rw [eSec_eq_one_left, comp_transl, _root_.mul_one, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨rig, hrig, -⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := fun _ : PUnit => eSec G) (φ := fun _ => a.left)
    (ε := fun _ => 1) hc ρ hρ
  let L' : RigLB G := ⟨P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left, rig, hL', hrig⟩

  obtain ⟨s, hs, vs⟩ := exists_symL P a ha
  obtain ⟨s', hs', Vs⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := ![(ι[G]).left, 𝟙 G.left]) (fun _ => rfl) s hs
  obtain ⟨k, hk, vk⟩ := exists_cubL P a
  obtain ⟨k', hk', Vk⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := thφ G (x3 G)) (fun _ => rfl) k hk
  have cubRel : ∀ (T : Over S) (z : T.left) (J) (J'), Good P.L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G,
      cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹ =
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * y * u) *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * y))⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * u))⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (y * u))⁻¹ *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) y *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) u *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) 1)⁻¹ *
        CubTransport.thV (L := L') k' z J' x y u := fun T z J J' hJ hJ' x y u =>
    (vk T x y u z J hJ).symm.trans ((Vk _ _ z J J' hJ hJ').trans
      (congrArg₂ (· * ·) (prod_cub x y u (fun q => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) q z (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' q))) rfl))
  have symRel : ∀ (T : Over S) (z : T.left) (J) (J'), Good P.L.L z J → Good L'.L z J' → ∀ x : T ⟶ G,
      val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹ =
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x)⁻¹ *
        val s' x.left z J' := fun T z J J' hJ hJ' x =>
    (vs T x z J hJ).symm.trans ((Vs _ _ z J J' hJ hJ').trans
      (congrArg₂ (· * ·) (prod_sym x (fun q => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) q z (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' q))) rfl))
  let c' : CubicalStr G L' := cubicalOfVal k' hk' fun T z J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    exact isCub_of_twist (isCub_transl (isCub_cubV P.c hJ) (toUnit T ≫ a)) (MonoidHom.id (T ⟶ G))
      (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left))
      (θ' := CubTransport.thV (L := L') k' z J') (cubRel T z J J' hJ hJ')
  refine ⟨⟨L', c', s', hs', corr_of_val hL' fun y J' hJ' => ?_, fun T x y u z J' hJ' => ?_⟩, rfl,
    fun T x z J J' hJ hJ' => ?_, fun T x y u z J J' hJ hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt hL y
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    have e := symRel (𝟙_ (Over S)) y J J' hJ hJ' 1
    simp only [_root_.mul_one, mul_inv_cancel, inv_one, _root_.one_mul] at e
    rw [Category.id_comp, eSec_eq_one_left]
    exact e.symm
  · obtain ⟨J, hJ⟩ := exists_good_pt hL z
    exact sym_cub_alg (MonoidHom.id (T ⟶ G))
      (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left))
      (θ := fun x y u => cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹)
      (θ' := cubV c' z J') (σ := fun p => val P.sym ((toUnit T ≫ a) * p).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹)
      (σ' := fun p => val s' p.left z J') (cubRel T z J J' hJ hJ') (symRel T z J J' hJ hJ')
      (sym_cub_transl (cubV P.c z J) (fun p => val P.sym p.left z J) _ (hα T) (fun x y u => P.sym_cub T x y u z J hJ) x y u)
  · have eJ : J' = fun r _ => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) := funext fun r => eq_of_heq (hJ' r)
    subst eJ
    have e := symRel T z J _ hJ (good_pull ((toUnit G ≫ a) * 𝟙 G).left hJ) x
    simp only [gw_pullIso_good hL _ hJ, inv_one, _root_.one_mul] at e
    exact e.symm
  · have eJ : J' = fun r _ => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) := funext fun r => eq_of_heq (hJ' r)
    subst eJ
    have e := cubRel T z J _ hJ (good_pull ((toUnit G ≫ a) * 𝟙 G).left hJ) x y u
    simp only [gw_pullIso_good hL _ hJ, inv_one, _root_.one_mul, _root_.mul_one] at e
    exact e.symm

end GlobalTheory.TranslCP
