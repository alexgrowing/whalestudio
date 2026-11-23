import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusCube

open Rosenlicht SplitTorusPoints Geo.Tor

theorem toHom_comp_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z W : Over S} (ρ : W ⟶ Z)
    (t : Z ⟶ splitTorus S X) (a : Multiplicative X) :
    (toHom (ρ ≫ t) a).val = ρ.left.appTop.hom (toHom t a).val := by
  change (coord (ρ ≫ t)).hom _ = _
  rw [coord_comp]; rfl

theorem toHom_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} :
    toHom (1 : Z ⟶ splitTorus S X) = 1 :=
  map_one (splitTorusPointsEquiv S X Z)

theorem exists_form (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of k), ⊤)) (a b d : X), IsUnit c ∧
      ∀ (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X),
        (lift x (lift y u)).left.appTop.hom w = Z.hom.appTop.hom c *
          ((toHom x (Multiplicative.ofAdd a)).val * (toHom y (Multiplicative.ofAdd b)).val *
            (toHom u (Multiplicative.ofAdd d)).val) := by
  let Y := splitTorus (Spec (.of k)) (X × X × X)
  have hp : ∀ j : X →+ X × X × X, ∃ p : Y ⟶ splitTorus (Spec (.of k)) X,
      ∀ (Z : Over (Spec (.of k))) (ρ : Z ⟶ Y) (a : X),
        toHom (ρ ≫ p) (Multiplicative.ofAdd a) = toHom ρ (Multiplicative.ofAdd (j a)) := by
    intro j
    obtain ⟨p, hp⟩ := (toHom_bijective (Z := Y) (X := X)).2
      ((toHom (𝟙 Y)).comp (AddMonoidHom.toMultiplicative j))
    refine ⟨p, fun Z ρ a => Units.ext ?_⟩
    rw [toHom_comp_val, hp]
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  obtain ⟨p₀, h₀⟩ := hp (AddMonoidHom.inl _ _)
  obtain ⟨p₁, h₁⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  obtain ⟨p₂, h₂⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _))
  obtain ⟨c, ⟨a, b, d⟩, hc, e⟩ := torus_units k (X × X × X)
    (hw.map (lift p₀ (lift p₁ p₂)).left.appTop.hom)
  refine ⟨c, a, b, d, hc, fun Z x y u => ?_⟩
  obtain ⟨ρ, hρ⟩ := (toHom_bijective (Z := Z) (X := X × X × X)).2
    ((toHom x).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)) *
      (toHom y).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _))) *
      (toHom u).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  have r₀ : ρ ≫ p₀ = x := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₀ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₁ : ρ ≫ p₁ = y := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₁ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₂ : ρ ≫ p₂ = u := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₂ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have hl : lift x (lift y u) = ρ ≫ lift p₀ (lift p₁ p₂) := by
    rw [comp_lift, comp_lift, r₀, r₁, r₂]
  have hχ : ρ.left.appTop.hom (chi (X × X × X) (a, b, d)) =
      (toHom ρ (Multiplicative.ofAdd (a, b, d))).val := by
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  rw [hl, ← over_appTop_comp, e, map_mul, hχ, hρ, ← appTop_comp_apply, Over.w]
  simp

theorem unit_eq_one (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w)
    (h₀ : (lift (𝟙 _) (lift 1 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₁ : (lift 1 (lift (𝟙 _) 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₂ : (lift 1 (lift 1 (𝟙 _)) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X) :
    (lift x (lift y u)).left.appTop.hom w = 1 := by
  obtain ⟨c, a, b, d, hc, H⟩ := exists_form k X w hw
  rw [H] at h₀ h₁ h₂
  simp only [toHom_one, MonoidHom.one_apply, Units.val_one, _root_.mul_one, _root_.one_mul]
    at h₀ h₁ h₂
  have ha : a = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₀.trans (map_one _).symm)
  have hb : b = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₁.trans (map_one _).symm)
  have hd : d = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₂.trans (map_one _).symm)
  subst ha hb hd
  have hc1 : c = 1 := torus_const_injective k X (by simpa using h₀)
  rw [H, hc1]
  simp

section Val

variable {X Y : Scheme.{0}} (L : LB X)

def HasVal (form : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V)
    (f : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → L.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ (∀ (V : Type) [CommGroup V] (h : (Y ⟶ X) → V), ∏ k, h (φ k) ^ ε k = form V h) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t r z J = f Z r z J

variable {L}

theorem HasVal.mul {F F' : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f f'}
    (h : HasVal L F f) (h' : HasVal L F' f') :
    HasVal L (fun V _ k => F V k * F' V k) (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', a', b'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t',
    DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (a V k) (a' V k))
  · rw [val_mul hJ, b Z r z J hJ, b' Z r z J hJ]

theorem HasVal.inv {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) : HasVal L (fun V _ k => (F V k)⁻¹) (fun Z r z J => (f Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, a]
  · rw [val_inv, b Z r z J hJ]

theorem hasVal_pull (θ : LB.Gen (L.pull (𝟙 X))) (hθ : θ.IsGen) (p : Y ⟶ X) :
    HasVal L (fun _ _ k => k p) (fun _ r z J =>
      val (L := L) (φ := fun _ : PUnit => 𝟙 X) (ε := fun _ => 1) θ (r ≫ p) z J) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L (fun _ : PUnit => 𝟙 X) (fun _ => 1) θ p,
    DVR.pullGen_isGen _ _ _ _ hθ p, fun V _ k => by simp, fun Z r z J hJ => val_pull hJ _ _ _⟩

theorem HasVal.exists_unit (hL : L.IsLB) {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) (hF : ∀ (V : Type) [CommGroup V] (k : (Y ⟶ X) → V), F V k = 1) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (f Z r z J).val = gs (𝟙 Z) z ⊤ (r.appTop.hom w.val) := by
  obtain ⟨K, _, φ, ε, u, hu, a, b⟩ := h
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (a V k).trans ((hF V k).trans (Fintype.prod_empty _).symm)) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← b Z r z J hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans
    ((gs_unit r z ⊤ trivial _).symm.trans ?_)
  refine Eq.trans ?_ (gs_pull (𝟙 Z) r z ⊤ trivial _).symm
  rw [Category.id_comp]

end Val

theorem exists_ratio {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (c : CubicalStr G L) (θ : LB.Gen (L.L.pull (𝟙 G.left))) (hθ : θ.IsGen) :
    ∃ w : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left)
      (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      ∀ v : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, (∀ a, v a = val (L := L.L)
        (φ := fun _ : PUnit => 𝟙 G.left) (ε := fun _ => 1) θ a.left z J) →
      (v (x * y * u) * v x * v y * v u *
        (cubV c z J x y u * v (x * y) * v (x * u) * v (y * u) * v 1)⁻¹).val =
        gs (𝟙 T.left) z ⊤ ((lift x (lift y u)).left.appTop.hom w.val) := by
  let p₀ := x3 G 0
  let p₁ := x3 G 1
  let p₂ := x3 G 2
  have P := fun p : G3 G ⟶ G => hasVal_pull θ hθ p.left
  have hid : lift p₀ (lift p₁ p₂) = 𝟙 _ := by ext <;> simp [p₀, p₁, p₂, x3]
  have C : HasVal L.L (fun _ _ h => h (p₀ * p₁ * p₂).left * (h (p₀ * p₁).left)⁻¹ *
      (h (p₀ * p₂).left)⁻¹ * (h (p₁ * p₂).left)⁻¹ * h p₀.left * h p₁.left *
        h p₂.left * (h (1 : G3 G ⟶ G).left)⁻¹)
      (fun _ r z J => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) :=
    ⟨thK, inferInstance, thφ G (x3 G), thε, c.t, c.isGen, fun V _ h => by
      have := prod_cub p₀ p₁ p₂ h
      rw [hid] at this
      simpa using this, fun _ _ _ _ _ => rfl⟩
  obtain ⟨w, hw⟩ := (((((P (p₀ * p₁ * p₂)).mul (P p₀)).mul (P p₁)).mul (P p₂)).mul
    ((((C.mul (P (p₀ * p₁))).mul (P (p₀ * p₂))).mul (P (p₁ * p₂))).mul (P 1)).inv).exists_unit
    L.isLB (fun V _ k => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T x y u z J hJ v hv => ?_⟩
  refine Eq.trans ?_ (hw _ (lift x (lift y u)).left z J hJ)
  have r₀ : lift x (lift y u) ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y u) ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y u) ≫ p₂ = u := by simp [p₂, x3]
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂, hv]
  rfl

end TorusCube

open TorusCube Geo.Tor in

theorem splitTorus_gen_cubical :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] (i : splitTorus (Spec (CommRingCat.of k)) X ≅ G), IsMonHom i.hom → ∀ (L : RigLB G) (c : CubicalStr G L) (θ : LB.Gen (L.L.pull (𝟙 G.left))), θ.IsGen → ∀ (T : Over (Spec (CommRingCat.of k))) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Geo.Tor.Good L.L z J → let v : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ := fun a => Geo.Tor.val (L := L.L) (φ := fun _ : PUnit => 𝟙 G.left) (ε := fun _ => 1) θ a.left z J; v (x * y * u) * v x * v y * v u = Geo.Tor.cubV c z J x y u * v (x * y) * v (x * u) * v (y * u) * v 1 := by
  intro k _ X _ _ _ G _ _ i hi L c θ hθ T x y u z J hJ v
  obtain ⟨w, hw⟩ := exists_ratio L c θ hθ
  have hT : TwoUniqueSums (X × X × X) := inferInstance
  let m := i.hom ⊗ₘ i.hom ⊗ₘ i.hom
  have hm : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b d : Z ⟶ splitTorus (Spec (.of k)) X),
      (lift a (lift b d)).left.appTop.hom (m.left.appTop.hom w.val) =
        (lift (a ≫ i.hom) (lift (b ≫ i.hom) (d ≫ i.hom))).left.appTop.hom w.val := by
    intro Z a b d
    rw [Rosenlicht.over_appTop_comp]
    simp [m]
  have face : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b d : Z ⟶ G),
      (a = 1 ∨ b = 1 ∨ d = 1) → (lift a (lift b d)).left.appTop.hom w.val = 1 := by
    intro Z a b d h
    refine fn_ext fun q _ => ?_
    choose I hI using fun χ : Z.left ⟶ G.left => exists_chart L.isLB (χ q)
    have C := isCub_cubV c (show Good L.L q I from hI)
    rw [← hw Z a b d q I hI (fun a => val (L := L.L) (φ := fun _ : PUnit => 𝟙 G.left)
      (ε := fun _ => 1) θ a.left q I) (fun _ => rfl), gs_eq _ q ⊤ trivial, map_one, map_one,
      Units.val_eq_one, mul_inv_eq_one]
    rcases h with rfl | rfl | rfl
    · rw [C.face]; simp only [_root_.one_mul, _root_.mul_one]; ac_rfl
    · rw [C.face₂]; simp only [_root_.one_mul, _root_.mul_one]; ac_rfl
    · rw [C.face₃]; simp only [_root_.one_mul, _root_.mul_one]
  have key := unit_eq_one k X (m.left.appTop.hom w.val) (w.isUnit.map _)
    (by rw [hm]; exact face _ _ _ _ (Or.inr (Or.inl (MonObj.one_comp _))))
    (by rw [hm]; exact face _ _ _ _ (Or.inl (MonObj.one_comp _)))
    (by rw [hm]; exact face _ _ _ _ (Or.inl (MonObj.one_comp _)))
    T (x ≫ i.inv) (y ≫ i.inv) (u ≫ i.inv)
  rw [hm] at key
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at key
  have := hw T x y u z J hJ v (fun _ => rfl)
  rw [key, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_eq_one, mul_inv_eq_one] at this
  exact this

end GlobalTheory
