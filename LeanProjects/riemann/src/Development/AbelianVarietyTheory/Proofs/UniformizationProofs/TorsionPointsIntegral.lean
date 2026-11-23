import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace TorsionIntegral

theorem exists_finset_extend {V F : Type} [CommRing V] [Field F] [Algebra V F]
    (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (p : Spec (CommRingCat.of F) ⟶ B.left)
    (hp : p ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ S : Finset F, ∀ (W : Type) [CommRing W] [IsDomain W] [ValuationRing W] [Algebra V W] [Algebra W F]
      [IsScalarTower V W F], Function.Injective (algebraMap W F) →
      (∀ x ∈ S, ∃ a b : W, b ≠ 0 ∧ x * algebraMap W F b = algebraMap W F a) →
      ∃ l : Spec (CommRingCat.of W) ⟶ B.left, Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ l = p ∧
        l ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap V W)) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of V ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap V F) :=
    Spec.map_injective (by rw [Spec.map_comp, hg, ← Category.assoc, hf, hp])
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra V Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType V Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun W _ _ _ _ _ _ hinj hS => ?_⟩
  let K := FractionRing W
  let κ : K →+* F := IsFractionRing.lift hinj
  have hκ : ∀ a, κ (algebraMap W K a) = algebraMap W F a := fun a => IsFractionRing.lift_algebraMap hinj a
  have hV : ∀ r : V, f.hom (g.hom r) = κ (algebraMap W K (algebraMap V W r)) := fun r => by
    rw [hκ, ← IsScalarTower.algebraMap_apply]
    exact congrArg (fun q => q.hom r) hgf
  have hr : ∀ a, f.hom a ∈ κ.range := fun a => by
    have ha : a ∈ Algebra.adjoin V (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, b, hb, e⟩ := hS _ (Finset.mem_image_of_mem _ hx)
      refine ⟨algebraMap W K a / algebraMap W K b, ?_⟩
      rw [map_div₀, hκ, hκ, ← e, mul_div_cancel_right₀ _ ((map_ne_zero_iff _ hinj).2 hb)]
    | algebraMap r => exact ⟨_, (hV r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let e : K ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b h => κ.injective (congrArg Subtype.val h), κ.rangeRestrict_surjective⟩
  let f' : Γ(B.left, U) →+* K := e.symm.toRingHom.comp (f.hom.codRestrict _ hr)
  have hf' : ∀ a, κ (f' a) = f.hom a := fun a => congrArg Subtype.val (e.apply_symm_apply ⟨f.hom a, hr a⟩)
  have hE : ValuativeCriterion.Existence B.hom := by
    have h : UniversallyClosed B.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let Q : ValuativeCommSq B.hom :=
    { R := W, K := K, i₁ := Spec.map (CommRingCat.ofHom f') ≫ hU.fromSpec,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap V W)),
      commSq := ⟨by
        rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext r
        exact κ.injective ((hf' _).trans (hV r))⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
  refine ⟨l, ?_, h2⟩
  have e₁ : CommRingCat.ofHom (algebraMap W F) = CommRingCat.ofHom (algebraMap W K) ≫ CommRingCat.ofHom κ := by
    ext a; exact (hκ a).symm
  have e₂ : f = CommRingCat.ofHom f' ≫ CommRingCat.ofHom κ := by
    ext a; exact (hf' a).symm
  rw [e₁, Spec.map_comp, Category.assoc, ← hf, e₂, Spec.map_comp, Category.assoc]
  exact congrArg _ h1

def fracUnits {A S : Type} [CommRing A] [CommRing S] (ρ : A →+* S) : Subgroup Sˣ where
  carrier := {v | ∃ a b : A, IsUnit (ρ b) ∧ v.val * ρ b = ρ a}
  one_mem' := ⟨1, 1, by simp, by simp⟩
  mul_mem' := by
    rintro v v' ⟨a, b, hb, e⟩ ⟨a', b', hb', e'⟩
    exact ⟨a * a', b * b', by rw [map_mul]; exact hb.mul hb', by
      rw [map_mul, map_mul, Units.val_mul, ← e, ← e']; ring⟩
  inv_mem' := by
    rintro v ⟨a, b, hb, e⟩
    exact ⟨b, a, e ▸ v.isUnit.mul hb, by rw [← e, Units.inv_mul_cancel_left]⟩

theorem exists_unit_of_pow {A S : Type} [CommRing A] [PreValuationRing A] [CommRing S] {ρ : A →+* S}
    (hρ : Function.Injective ρ) {v : Sˣ} (hv : v ∈ fracUnits ρ) {N : ℕ} (hN : 1 ≤ N) {u : Aˣ}
    (h : ρ u.val = (v ^ N).val) : ∃ u' : Aˣ, ρ u'.val = v.val := by
  obtain ⟨a, b, hb, e⟩ := hv
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
  · have ha : IsUnit (ρ a) := e ▸ v.isUnit.mul hb
    have h1 : v.val * ρ c = 1 := ha.mul_right_cancel (by
      rw [_root_.one_mul, _root_.mul_assoc, ← map_mul, mul_comm c, hc, e])
    have h2 : u.val * c ^ N = 1 := hρ (by
      rw [map_mul, h, map_pow, Units.val_pow_eq_pow_val, ← mul_pow, h1, one_pow, map_one])
    have hu : IsUnit c := (isUnit_pow_iff (by omega)).1 (IsUnit.of_mul_eq_one_right _ h2)
    refine ⟨hu.unit⁻¹, ?_⟩
    calc ρ (hu.unit⁻¹).val = v.val * ρ (c * (hu.unit⁻¹).val) := by
          rw [map_mul, ← _root_.mul_assoc, h1, _root_.one_mul]
      _ = v.val := by rw [hu.mul_val_inv, map_one, _root_.mul_one]
  · have h1 : ρ c = v.val := hb.mul_right_cancel (by rw [e, ← map_mul, mul_comm c, hc])
    have h2 : c ^ N = u.val := hρ (by rw [map_pow, h1, h, Units.val_pow_eq_pow_val])
    have hu : IsUnit c := (isUnit_pow_iff (by omega)).1 (h2 ▸ u.isUnit)
    exact ⟨hu.unit, h1⟩

section Values

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_generic (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z)
    (hd : ∀ (U : Y.Opens) (y : Y), y ∈ U → φ z ∈ U)
    (hi : ∀ (U : Y.Opens), φ z ∈ U → Function.Injective (gm φ z U))
    (he : ∀ ψ ψ' : Y ⟶ X, φ ≫ ψ = φ ≫ ψ' → ψ = ψ')
    {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {ψ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ J, Good L z J → val t φ z J = val t' φ z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine unit_ext fun y hy => congrArg _ ?_
  have hz := hd _ y hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => φ ≫ Sum.elim ψ ψ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (he _ _ e), c₃ a b (he _ _ e), (c₃ b a (he _ _ e).symm).symm, c₂ a b (he _ _ e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := h J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact hi _ hz ((gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm))

theorem exists_gen_of_chart (hL : L.IsLB) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (j₀ : K → L.ι)
    (h₀ : ∀ y, y ∈ LB.wchart L ψ j₀) (u : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L ψ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L ψ j → gm r z (LB.wchart L ψ j) (t.s j) = trF ψ ε r z j j₀ * gm r z ⊤ u := by
  let t : LB.Gen (LB.LinComb L ψ ε) := ⟨fun j =>
    res (le_inf le_rfl (fun y _ => h₀ y) : LB.wchart L ψ j ≤ LB.wchart L ψ j ⊓ LB.wchart L ψ j₀)
      ((LB.LinComb L ψ ε).g j j₀) * res (le_top : LB.wchart L ψ j ≤ ⊤) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L ψ j → gm r z (LB.wchart L ψ j) (t.s j) = trF ψ ε r z j j₀ * gm r z ⊤ u :=
    fun Z r z j hj => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hj _).trans (gm_linComb L ψ ε r z j j₀ hj (h₀ _))) (gm_res r z _ hj _))
  refine ⟨t, fun j j' => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res _ y _ hy _).trans (key _ (𝟙 Y) y j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L ψ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy _).trans (key _ (𝟙 Y) y j' hy.2)))).symm)
  rw [← trF_trans hL ψ ε (𝟙 Y) y hy.1 hy.2 (h₀ _), _root_.mul_assoc]
  rfl

theorem val_trans (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {J J' : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (hJ' : Good L z J') (t : LB.Gen (LB.LinComb L (fun k => φ ≫ ψ k) ε)) (ht : t.IsGen) :
    val t (𝟙 Z) z J = trF ψ ε φ z (fun k => J (φ ≫ ψ k)) (fun k => J' (φ ≫ ψ k)) * val t (𝟙 Z) z J' := by
  rw [val_of t _ z J (fun k => J (φ ≫ ψ k)) (fun k => by rw [Category.id_comp]),
    val_of t _ z J' (fun k => J' (φ ≫ ψ k)) (fun k => by rw [Category.id_comp])]
  refine (gen_trans ht (𝟙 Z) z (j' := fun k => J' (φ ≫ ψ k)) (Set.mem_iInter.2 fun k => hJ (φ ≫ ψ k))
    (Set.mem_iInter.2 fun k => hJ' (φ ≫ ψ k))).trans ?_
  simp only [trF, Category.id_comp]

theorem exists_gen_extend (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {ψ' : K → (Z ⟶ X)}
    (hψ : ∀ k, ψ' k = φ ≫ ψ k) {J₀ : (Z ⟶ X) → L.ι} (hJ₀ : Good L z J₀)
    (h₀ : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q))) (t : LB.Gen (LB.LinComb L ψ' ε)) (ht : t.IsGen)
    (hv : val t (𝟙 Z) z J₀ ∈ (gm φ z ⊤).range) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen ∧ ∀ J, Good L z J → val t' φ z J = val t (𝟙 Z) z J := by
  obtain rfl : ψ' = fun k => φ ≫ ψ k := funext hψ
  obtain ⟨u, hu⟩ := hv
  obtain ⟨t', ht', hv'⟩ := exists_gen_of_chart hL ψ ε (fun k => J₀ (φ ≫ ψ k))
    (fun y => Set.mem_iInter.2 fun k => h₀ _ y) u
  refine ⟨t', ht', fun J hJ => (hv' _ φ z _ (hJ.mem ψ φ)).trans ?_⟩
  rw [hu]
  exact (val_trans φ z ψ ε hJ hJ₀ t ht).symm

theorem val_mem_range (φ : Z ⟶ Y) (z : Z) {J₀ : (Z ⟶ X) → L.ι} (hJ₀ : Good L z J₀)
    (h₀ : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q))) {ψ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L ψ ε)) (r : Y ⟶ Y') : val t (φ ≫ r) z J₀ ∈ (gm φ z ⊤).range := by
  rw [← val_pull hJ₀]
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (fun k => r ≫ ψ k) (fun k => J₀ (φ ≫ r ≫ ψ k)) :=
    fun y _ => Set.mem_iInter.2 fun k => h₀ (r ≫ ψ k) y
  exact ⟨res le _, gm_res φ z le trivial _⟩

theorem exists_good_global (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z) (y₀ : Y) (hy₀ : ∀ (U : Y.Opens) (y : Y), y₀ ∈ U → y ∈ U)
    (he : ∀ ψ ψ' : Y ⟶ X, φ ≫ ψ = φ ≫ ψ' → ψ = ψ') :
    ∃ J₀ : (Z ⟶ X) → L.ι, Good L z J₀ ∧ ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q)) := by
  choose j hj using fun q : Y ⟶ X => exists_chart hL (q y₀)
  have hj' : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (j q) := fun q y => hy₀ (q ⁻¹ᵁ L.U (j q)) y (hj q)
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun q : Y ⟶ X => φ ≫ q) j (fun a b h => congrArg j (he a b h))
    (fun q => hj' q (φ z))
  exact ⟨J, hJ, fun q y => (e q).symm ▸ hj' q y⟩

def germTop (φ : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (φ ⁻¹ᵁ ⊤) z trivial).hom.comp (φ.app ⊤).hom

theorem gm_mem_fracUnits [IsAffine Y] (φ : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : φ z ∈ U) (a : Γ(Y, U)ˣ) :
    gm φ z U a ∈ fracUnits (germTop φ z) := by
  let _ := Y.presheaf.algebra_section_stalk (U := ⊤) ⟨φ z, trivial⟩
  have hl := (isAffineOpen_top Y).isLocalization_stalk ⟨φ z, trivial⟩
  obtain ⟨⟨p, q⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl ((Y.presheaf.germ U (φ z) h).hom a.val)
  have hq := @IsLocalization.map_units _ _ _ _ _ _ hl q
  have k : ∀ x : Γ(Y, ⊤), germTop φ z x = (φ.stalkMap z).hom ((Y.presheaf.germ ⊤ (φ z) trivial).hom x) :=
    fun x => (Scheme.Hom.germ_stalkMap_apply φ ⊤ z trivial x).symm
  refine ⟨p, q, ?_, ?_⟩
  · rw [k]; exact hq.map _
  · rw [k, k, gm_val φ z U h, ← Scheme.Hom.germ_stalkMap_apply, ← map_mul]
    exact congrArg _ e

theorem val_mem_fracUnits [IsAffine Y] (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {ψ' : K → (Z ⟶ X)}
    (hψ : ∀ k, ψ' k = φ ≫ ψ k) {J J' : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hJ' : Good L z J')
    (t : LB.Gen (LB.LinComb L ψ' ε)) (ht : t.IsGen) (hv : val t (𝟙 Z) z J' ∈ fracUnits (germTop φ z)) :
    val t (𝟙 Z) z J ∈ fracUnits (germTop φ z) := by
  obtain rfl : ψ' = fun k => φ ≫ ψ k := funext hψ
  rw [val_trans φ z ψ ε hJ hJ' t ht]
  refine mul_mem (prod_mem fun k _ => zpow_mem ?_ _) hv
  have hm : ψ k (φ z) ∈ L.U (J (φ ≫ ψ k)) ⊓ L.U (J' (φ ≫ ψ k)) := ⟨hJ (φ ≫ ψ k), hJ' (φ ≫ ψ k)⟩
  dsimp only
  rw [← gm_pull φ (ψ k) z _ hm]
  exact gm_mem_fracUnits φ z _ hm _

end Values

section Points

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)

def Restricts (g' : GtPt D T) (g : GtPtF D F) : Prop :=
  φ ≫ g'.b = g.b ∧ ∀ χ J, Good D.P.L z J → val (g'.s χ) φ.left z J = val (g.s χ) (𝟙 _) z J

theorem gtφ_comp {b' : T ⟶ D.P.A} {b : TF (R := R) F ⟶ D.P.A} (hb : φ ≫ b' = b) (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F b χ k = φ.left ≫ DegPre.gtφT D T b' χ k := by
  have e₀ : cP D _ χ * b = φ ≫ (cP D T χ * b') := by rw [MonObj.comp_mul, comp_cP, hb]
  have e₃ : (1 : TF (R := R) F ⟶ D.P.A) = φ ≫ (1 : T ⟶ D.P.A) := (MonObj.comp_one φ).symm
  fin_cases k
  exacts [congrArg (fun q => q.left) e₀, congrArg (fun q => q.left) (comp_cP D φ χ).symm,
    congrArg (fun q => q.left) hb.symm, congrArg (fun q => q.left) e₃]

theorem Restricts.isPullF {g' : GtPt D T} {g : GtPtF D F} (h : Restricts φ z g' g) :
    GtPt.IsPullF F φ.left g' g := by
  refine ⟨congrArg (fun q => q.left) h.1.symm, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  obtain rfl : z = y := Subsingleton.elim (α := PrimeSpectrum F) _ _
  rw [val_pull hJ, Category.id_comp]
  exact (h.2 χ J hJ).symm

variable (hd : ∀ (U : T.left.Opens) (y : T.left), y ∈ U → φ.left z ∈ U)
  (hi : ∀ (U : T.left.Opens), φ.left z ∈ U → Function.Injective (gm φ.left z U))
  (he : ∀ ψ ψ' : T.left ⟶ D.P.A.left, φ.left ≫ ψ = φ.left ≫ ψ' → ψ = ψ')
include hd hi he

theorem Restricts.isZero {g' : GtPt D T} {g : GtPtF D F} (h : Restricts φ z g' g) (h₀ : g.IsZero) : g'.IsZero := by
  obtain ⟨hb, hv⟩ := (isZero_iff g).1 h₀
  refine ⟨Over.OverMorphism.ext (he _ _ (congrArg (fun q => q.left)
    ((h.1.trans hb).trans (MonObj.comp_one φ).symm))), fun χ => corr_of_val_generic D.P.isLB φ.left z hd hi he fun J hJ => ?_⟩
  exact (h.2 χ J hJ).trans ((hv χ z J hJ).trans (val_one _).symm)

theorem Restricts.isAdd {g₁' g₂' g₃' : GtPt D T} {g₁ g₂ g₃ : GtPtF D F} (h₁ : Restricts φ z g₁' g₁)
    (h₂ : Restricts φ z g₂' g₂) (h₃ : Restricts φ z g₃' g₃) (h : g₁.IsAdd g₂ g₃) : g₁'.IsAdd g₂' g₃' := by
  obtain ⟨hb, hv⟩ := (isAdd_iff _ _ _).1 h
  have e : φ ≫ g₃'.b = φ ≫ (g₁'.b * g₂'.b) := by rw [MonObj.comp_mul, h₁.1, h₂.1, h₃.1, hb]
  refine ⟨Over.OverMorphism.ext (he _ _ (congrArg (fun q => q.left) e)),
    fun χ => corr_of_val_generic D.P.isLB φ.left z hd hi he fun J hJ => ?_⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  rw [h₁.2 χ J hJ, h₂.2 χ J hJ, h₃.2 χ J hJ, ← hv χ z J hJ]
  refine congrArg _ ((val_cub D.cub φ hJ (cP D T χ) _ _).trans ?_)
  rw [comp_cP, h₁.1, h₂.1]

variable {J₀ : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ₀ : Good D.P.L z J₀)
  (h₀ : ∀ (q : T.left ⟶ D.P.A.left) (y : T.left), q y ∈ D.P.L.U (J₀ (φ.left ≫ q)))
include hJ₀ h₀

theorem exists_restricts (g : GtPtF D F) (b' : T ⟶ D.P.A) (hb : φ ≫ b' = g.b)
    (hv : ∀ χ, val (g.s χ) (𝟙 _) z J₀ ∈ (gm φ.left z ⊤).range) : ∃ g' : GtPt D T, Restricts φ z g' g := by
  choose s hs vs using fun χ => exists_gen_extend D.P.isLB φ.left z (DegPre.gtφT D T b' χ) DegPre.gtε
    (gtφ_comp φ hb χ) hJ₀ h₀ (g.s χ) (g.isGen χ) (hv χ)
  refine ⟨⟨b', s, hs, corr_of_val_generic D.P.isLB φ.left z hd hi he fun J hJ => ?_,
    fun χ χ' => corr_of_val_generic D.P.isLB φ.left z hd hi he fun J hJ => ?_⟩, hb, vs⟩
  · exact (vs 0 J hJ).trans (((val_corr hJ g.s_zero _).trans (val_one _)).trans (val_one _).symm)
  · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
      ((val_corr hJ (g.mult χ χ') (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [vs χ J hJ, vs χ' J hJ, vs _ J hJ, ← e]
    refine congrArg _ ((val_cub D.cub φ hJ (cP D T χ) (cP D T χ') _).trans ?_)
    rw [comp_cP, comp_cP, hb]
    rfl

omit hd hi he in
theorem th_mem_range (x x' w : T ⟶ D.P.A) : th D z J₀ (φ ≫ x) (φ ≫ x') (φ ≫ w) ∈ (gm φ.left z ⊤).range := by
  have := val_mem_range φ.left z hJ₀ h₀ (ψ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (lift x (lift x' w)).left
  rwa [← Over.comp_left, comp_lift, comp_lift] at this

theorem exists_torsion_extend {N : ℕ} (g : GtPtF D F) (hg : GtTors D N g) (b' : T ⟶ D.P.A) (hb : φ ≫ b' = g.b)
    (S : Set D.X) (hS : Submodule.span ℤ S = ⊤)
    (hv : ∀ χ ∈ S, val (g.s χ) (𝟙 _) z J₀ ^ N ∈ (gm φ.left z ⊤).range → val (g.s χ) (𝟙 _) z J₀ ∈ (gm φ.left z ⊤).range) :
    ∃ g' : GtPt D T, GtPt.IsPullF F φ.left g' g ∧ ∃ h, GtPt.IsNsmul N g' h ∧ h.IsZero := by
  obtain ⟨h, ⟨gs, hz, hs, rfl⟩, hl⟩ := hg
  let π := QuotientGroup.mk' (gm φ.left z ⊤).range
  have hπ : ∀ v, π v = 1 ↔ v ∈ (gm φ.left z ⊤).range := fun v => QuotientGroup.eq_one_iff v
  have chain : ∀ i : Fin (N + 1), φ ≫ b' ^ i.val = (gs i).b ∧
      ∀ χ, π (val ((gs i).s χ) (𝟙 _) z J₀) = π (val (g.s χ) (𝟙 _) z J₀) ^ i.val := by
    intro i
    induction i using Fin.induction with
    | zero =>
      obtain ⟨e, ev⟩ := (isZero_iff _).1 hz
      refine ⟨by rw [e]; exact (congrArg _ (pow_zero _)).trans (MonObj.comp_one φ), fun χ => ?_⟩
      rw [ev χ z J₀ hJ₀, map_one]
      exact (pow_zero _).symm
    | succ i ih =>
      obtain ⟨e, ev⟩ := (isAdd_iff _ _ _).1 (hs i)
      refine ⟨by rw [e, Fin.val_succ, pow_succ, MonObj.comp_mul, hb, ← ih.1, Fin.val_castSucc], fun χ => ?_⟩
      have k := congrArg π (ev χ z J₀ hJ₀)
      have k₁ := (hπ _).2 (th_mem_range φ z hJ₀ h₀ (cP D T χ) (b' ^ i.castSucc.val) b')
      rw [comp_cP, ih.1, hb] at k₁
      rw [map_mul, map_mul, k₁, _root_.mul_one, ih.2] at k
      rw [k, Fin.val_succ, pow_succ, Fin.val_castSucc]
  let f : D.X →+ Additive (_ ⧸ (gm φ.left z ⊤).range) :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (π (val (g.s χ) (𝟙 _) z J₀))) fun χ χ' => by
      have e := ((val_mul hJ₀ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ₀ _ _ _))).symm.trans
        ((val_corr hJ₀ (g.mult χ χ') (𝟙 _)).trans (val_mul hJ₀ _ _ _))
      have k := congrArg π e
      have k₁ := (hπ _).2 (th_mem_range φ z hJ₀ h₀ (cP D T χ) (cP D T χ') b')
      rw [comp_cP, comp_cP, hb] at k₁
      rw [map_mul, map_mul] at k
      exact congrArg Additive.ofMul (((congrArg _ k₁).trans (_root_.mul_one _)).symm.trans k)
  have hf : f.toIntLinearMap = 0 := LinearMap.ext_on hS fun χ hχ => by
    have k := (chain (Fin.last N)).2 χ
    rw [((isZero_iff _).1 hl).2 χ z J₀ hJ₀, map_one, ← map_pow] at k
    exact congrArg Additive.ofMul ((hπ _).2 (hv χ hχ ((hπ _).1 k.symm)))
  have h1 : ∀ χ, π (val (g.s χ) (𝟙 _) z J₀) = 1 := fun χ => LinearMap.congr_fun hf χ
  obtain ⟨g', hg'⟩ := exists_restricts φ z hd hi he hJ₀ h₀ g b' hb fun χ => (hπ _).1 (h1 χ)
  choose gs' hgs' using fun i => exists_restricts φ z hd hi he hJ₀ h₀ (gs i) _ (chain i).1 fun χ =>
    (hπ _).1 (by rw [(chain i).2, h1, one_pow])
  exact ⟨g', hg'.isPullF, gs' (Fin.last N), ⟨gs', (hgs' 0).isZero φ z hd hi he hz,
    fun i => (hgs' _).isAdd φ z hd hi he hg' (hgs' _) (hs i), rfl⟩, (hgs' _).isZero φ z hd hi he hl⟩

end Points

theorem gm_injective {Y Z : Scheme.{0}} [IsAffine Y] [IsIntegral Y] (φ : Z ⟶ Y) (z : Z)
    (hφ : Function.Injective (germTop φ z)) (U : Y.Opens) (h : φ z ∈ U) : Function.Injective (gm φ z U) := by
  let _ := Y.presheaf.algebra_section_stalk (U := ⊤) ⟨φ z, trivial⟩
  have hl := (isAffineOpen_top Y).isLocalization_stalk ⟨φ z, trivial⟩
  have hs : Function.Injective (φ.stalkMap z).hom := (injective_iff_map_eq_zero _).2 fun x hx => by
    obtain ⟨⟨p, q⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl x
    have hq := @IsLocalization.map_units _ _ _ _ _ _ hl q
    have k : germTop φ z p = (φ.stalkMap z).hom (x * _) :=
      (Scheme.Hom.germ_stalkMap_apply φ ⊤ z trivial p).symm.trans (congrArg _ e.symm)
    rw [map_mul, hx, zero_mul] at k
    have hp : p = 0 := hφ (k.trans (map_zero _).symm)
    subst hp
    exact hq.mul_left_eq_zero.1 (e.trans (map_zero _))
  intro a b e
  have e' := congrArg Units.val e
  rw [gm_val φ z U h, gm_val φ z U h, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact Units.ext (germ_injective_of_isIntegral Y (φ z) h (hs e'))

def toStalkField (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem toStalkField_surjective (F : Type) [Field F] (z : Spec (CommRingCat.of F)) :
    Function.Surjective (toStalkField F z) := by
  intro v
  obtain ⟨U, hU, a, rfl⟩ := (Spec (CommRingCat.of F)).presheaf.germ_exist v
  obtain rfl : U = ⊤ := top_unique fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  exact ⟨x, rfl⟩

theorem germTop_specMap {W F : Type} [CommRing W] [Field F] (f : W →+* F) (z : Spec (CommRingCat.of F)) (a : W) :
    germTop (Spec.map (CommRingCat.ofHom f)) z ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a) =
      toStalkField F z (f a) :=
  congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom
    (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

end TorsionIntegral

open TorsionIntegral in

theorem torsion_points_integral :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (N : ℕ), 1 ≤ N →
      ∀ s : Finset (GtPtF D (Kbar V)), (∀ g ∈ s, GtTors D N g) →
      ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W),
        FinExt V W ∧ ∀ g ∈ s, ∃ g' : GtPt D (TA V W), GtPt.IsPullF (Kbar V) φ.left g' g ∧
          ∃ h, GtPt.IsNsmul N g' h ∧ h.IsZero := by
  classical
  intro V _ _ _ ⟨hV₁, hV₂, hV₃⟩ D N hN s hs
  let F := Kbar V
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V)))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).mpr inferInstance
  have := D.P.isAb.proper
  have hT : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algebraMap V F)) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg _ ?_)
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]; rfl
  choose P hP using fun g : GtPtF D F => exists_finset_extend D.P.A g.b.left ((Over.w g.b).trans hT)
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  choose J₁ hJ₁ using fun q : (TF (R := V) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (q z)
  choose x hx using fun (g : GtPtF D F) χ => toStalkField_surjective F z (val (g.s χ) (𝟙 _) z J₁).val
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℤ) (M := D.X))
  obtain ⟨W, hW, -, hc, hfin, hfree, hloc, hfr, -⟩ :=
    exists_complete_dvr_finite_subalgebra V F (s.biUnion fun g => P g ∪ S.image (x g))
  have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
  have hfr' : ∀ g ∈ s, ∀ y ∈ P g ∪ S.image (x g), ∃ a b : W, b ≠ 0 ∧ y * algebraMap W F b = algebraMap W F a := by
    intro g hg y hy
    obtain ⟨a, ha, b, hb, h0, e⟩ := hfr y (Finset.mem_biUnion.2 ⟨g, hg, hy⟩)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => h0 (congrArg Subtype.val h), e⟩
  let φ₀ : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of W) := Spec.map (CommRingCat.ofHom (algebraMap W F))
  let φ : TF (R := V) F ⟶ TA V W := Over.homMk φ₀ (((Spec.map_comp _ _).symm.trans (congrArg _ (by
    rw [IsScalarTower.algebraMap_eq V W F]; rfl))).trans hT.symm)
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv
  have hρ : Function.Injective (germTop φ₀ z) := fun a b e => by
    obtain ⟨a, rfl⟩ := hbij.2 a
    obtain ⟨b, rfl⟩ := hbij.2 b
    exact congrArg _ (hinj ((toStalkField F z).injective
      ((germTop_specMap _ z a).symm.trans (e.trans (germTop_specMap _ z b)))))
  have : PreValuationRing Γ(Spec (CommRingCat.of W), ⊤) :=
    Function.Surjective.preValuationRing (R := W) (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom hbij.2
  have hd : ∀ (U : (Spec (CommRingCat.of W)).Opens) (y : Spec (CommRingCat.of W)), y ∈ U → φ₀ z ∈ U := fun U y hy => by
    refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_) U.isOpen hy
    have ha' : algebraMap W F a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, map_eq_zero_iff _ hinj] at ha'
    exact ha' ▸ zero_mem _
  have he : ∀ ψ ψ' : Spec (CommRingCat.of W) ⟶ D.P.A.left, φ₀ ≫ ψ = φ₀ ≫ ψ' → ψ = ψ' := fun ψ ψ' h => by
    have : IsDominant φ₀ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap W F)).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
    have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
    exact ext_of_isDominant φ₀ h
  obtain ⟨J₀, hJ₀, h₀⟩ := exists_good_global D.P.isLB φ₀ z (IsLocalRing.closedPoint W)
    (fun U y hy => (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hy) he
  refine ⟨W, inferInstance, inferInstance, inferInstance, φ, ⟨hfin, hfree, inferInstance, hloc, hc⟩, fun g hg => ?_⟩
  obtain ⟨l, hl₁, hl₂⟩ := hP g W hinj fun y hy => hfr' g hg y (Finset.mem_union_left _ hy)
  let b' : TA V W ⟶ D.P.A := Over.homMk l hl₂
  have hb : φ ≫ b' = g.b := Over.OverMorphism.ext hl₁
  refine exists_torsion_extend φ z hd (gm_injective φ₀ z hρ) he hJ₀ h₀ g (hs g hg) b' hb S hS ?_
  rintro χ hχ ⟨u, hu⟩
  have hfrac : val (g.s χ) (𝟙 _) z J₀ ∈ fracUnits (germTop φ₀ z) := by
    refine val_mem_fracUnits φ₀ z (DegPre.gtφT D (TA V W) b' χ) _ (gtφ_comp φ hb χ) hJ₀ hJ₁ _ (g.isGen χ) ?_
    obtain ⟨a, b, hb0, e⟩ := hfr' g hg (x g χ) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hχ))
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a, (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b, ?_, ?_⟩
    · rw [germTop_specMap]
      exact (Ne.isUnit ((map_ne_zero_iff _ hinj).2 hb0)).map _
    · rw [germTop_specMap, germTop_specMap, ← e, map_mul, hx]
      rfl
  obtain ⟨u', hu'⟩ := exists_unit_of_pow hρ hfrac hN (u := u)
    ((gm_val φ₀ z ⊤ trivial u).symm.trans (congrArg Units.val hu))
  exact ⟨u', Units.ext ((gm_val φ₀ z ⊤ trivial u').trans hu')⟩

end GlobalTheory
