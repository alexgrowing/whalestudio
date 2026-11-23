import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

namespace GlobalTheory.BiextOfCube

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

private def BxTriv {X : Scheme.{0}} (L : LB X) (Y : Scheme.{0})
    (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h

private theorem BxTriv.mul {X Y : Scheme.{0}} {L : LB X} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    (a : BxTriv L Y F) (b : BxTriv L Y F') : BxTriv L Y (fun U _ h => F U h * F' U h) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', e'⟩ := b
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U h) (e' U h))⟩

private theorem BxTriv.inv {X Y : Scheme.{0}} {L : LB X} {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    (a : BxTriv L Y F) : BxTriv L Y (fun U _ h => (F U h)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := a
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, fun U _ h => ?_⟩
  show _ = (F U h)⁻¹
  rw [← e U h]
  simp only [zpow_neg, Finset.prod_inv_distrib]

private theorem BxTriv.pull {X Y W : Scheme.{0}} {L : LB X} {f : W ⟶ X} (t : (L.pull f).Gen) (ht : t.IsGen)
    (r : Y ⟶ W) {g : Y ⟶ X} (hg : r ≫ f = g) : BxTriv L Y (fun U _ h => h g) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L _ _ t r, DVR.pullGen_isGen _ _ _ _ ht r, fun U _ h => by
    rw [Fintype.prod_unique, zpow_one, hg]⟩

private theorem BxTriv.gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (a : BxTriv L Y F) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = ∏ k, h (φ k) ^ ε k) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', t, ht, e⟩ := a
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => (e U h).trans (hF U h)) t ht
  exact ⟨t', ht'⟩

private theorem bx_norm {X Y W S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    {f : W ⟶ X} (a : (L.pull f).Gen) (ha : a.IsGen) (o : S₀ ⟶ W)
    (h₀ : ∀ (U : Type) [CommGroup U] (h : (S₀ ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = (h (o ≫ f))⁻¹) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ y J, Good L y J → val t' e y J = (val a o y J)⁻¹ := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => by
      refine (DVR.prod_sum₂ (K := K) (K' := K ⊕ PUnit) (U := U) _ (c := ∏ k, h (φ k) ^ ε k) rfl
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := K) (K' := PUnit) (U := U) _
          ((Finset.prod_congr rfl fun k _ => by rw [Category.assoc]; rfl).trans (h₀ U fun q => h (p ≫ q)))
          (c' := h (p ≫ o ≫ f)) (by rw [Fintype.prod_unique, ← Category.assoc]; exact zpow_one _)))).trans ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t (p ≫ e))
      (LB.pullGen L _ _ a (p ≫ o)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ha _))))
  refine ⟨t', ht', fun y J hJ => ?_⟩
  rw [hv _ e y J hJ, val_mul hJ, val_inv, val_mul hJ, val_pull hJ, val_pull hJ, ← Category.assoc, ← Category.assoc,
    he, Category.id_comp, Category.id_comp, mul_inv, mul_inv_cancel_left]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

private theorem bx_lift_mul {T : Over S} (a b c d : T ⟶ A) :
    (lift a b : T ⟶ A ⊗ A) * lift c d = lift (a * c) (b * d) := by
  ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

private theorem bx_lift_one {T : Over S} : (1 : T ⟶ A ⊗ A) = lift 1 1 := by
  ext
  · rw [MonObj.one_comp]; simp
  · rw [MonObj.one_comp]; simp

private theorem bx_prod₁ {T : Over S} (a b c : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 A).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) k) ^ lawε k =
      h (lift (a * b) c).left * (h (lift a c).left)⁻¹ * (h (lift b c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 A 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 A 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 A 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd A (x3 A 0) (x3 A 1) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

private theorem bx_prod₂ {T : Over S} (a b c : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 A).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) k) ^ lawε k =
      h (lift a (b * c)).left * (h (lift a b).left)⁻¹ * (h (lift a c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 A 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 A 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 A 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd A (x3 A 1) (x3 A 2) = b * c := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

private theorem bx_id₃ : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
  ext <;> simp [x3]

private theorem bx_self₁ {U : Type} [CommGroup U] (h : ((G3 A).left ⟶ (G2 A).left) → U) :
    ∏ k, h (law1φ A (x3 A 0) (x3 A 1) (x3 A 2) k) ^ lawε k =
      h (lift (x3 A 0 * x3 A 1) (x3 A 2)).left * (h (lift (x3 A 0) (x3 A 2)).left)⁻¹ *
        (h (lift (x3 A 1) (x3 A 2)).left)⁻¹ := by
  have := bx_prod₁ (x3 A 0) (x3 A 1) (x3 A 2) h
  rw [bx_id₃] at this
  simpa only [Over.id_left, Category.id_comp] using this

private theorem bx_self₂ {U : Type} [CommGroup U] (h : ((G3 A).left ⟶ (G2 A).left) → U) :
    ∏ k, h (law2φ A (x3 A 0) (x3 A 1) (x3 A 2) k) ^ lawε k =
      h (lift (x3 A 0) (x3 A 1 * x3 A 2)).left * (h (lift (x3 A 0) (x3 A 1)).left)⁻¹ *
        (h (lift (x3 A 0) (x3 A 2)).left)⁻¹ := by
  have := bx_prod₂ (x3 A 0) (x3 A 1) (x3 A 2) h
  rw [bx_id₃] at this
  simpa only [Over.id_left, Category.id_comp] using this

private theorem bx_laws {P : LB (A ⊗ A).left} (hP : P.IsLB) (θ : LB.Gen (Theta (A ⊗ A) P)) (hθ : θ.IsGen)
    (a : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen) (ha : a.IsGen)
    (b : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen) (hb : b.IsGen) :
    ∃ (l₁ : LB.Gen (LB.LinComb P (law1φ A (x3 A 0) (x3 A 1) (x3 A 2)) lawε))
      (l₂ : LB.Gen (LB.LinComb P (law2φ A (x3 A 0) (x3 A 1) (x3 A 2)) lawε)), l₁.IsGen ∧ l₂.IsGen ∧
      ∀ y J, Good P y J → val l₁ (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J =
        val l₂ (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J := by
  have Ta : ∀ y : G3 A ⟶ A, BxTriv P (G3 A).left (fun U _ h => h (lift 1 y).left) := fun y =>
    BxTriv.pull a ha y.left (by rw [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id])
  have Tb : ∀ y : G3 A ⟶ A, BxTriv P (G3 A).left (fun U _ h => h (lift y 1).left) := fun y =>
    BxTriv.pull b hb y.left (by rw [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id])
  have Tθ : ∀ x x' y : G3 A ⟶ A ⊗ A, BxTriv P (G3 A).left (fun U _ h =>
      h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : G3 A ⟶ A ⊗ A).left)⁻¹) := fun x x' y =>
    ⟨thK, inferInstance, _, _, LB.pullGen P (thφ (A ⊗ A) (x3 (A ⊗ A))) thε θ (lift x (lift x' y)).left,
      DVR.pullGen_isGen _ _ _ _ hθ _, fun U _ h => prod_cub x x' y h⟩
  obtain ⟨t₁, h₁⟩ := ((Tθ (lift (x3 A 0) 1) (lift (x3 A 1) 1) (lift 1 (x3 A 2))).mul
      (((Tb (x3 A 0 * x3 A 1)).mul (Ta 1)).mul (((Tb (x3 A 0)).mul (Tb (x3 A 1))).mul (Ta (x3 A 2))).inv)).gen hP
      (φ := law1φ A (x3 A 0) (x3 A 1) (x3 A 2)) (ε := lawε) (fun U _ h => by
        rw [bx_self₁]
        simp only [bx_lift_mul, _root_.mul_one, _root_.one_mul, bx_lift_one (T := G3 A)]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
  obtain ⟨t₂, h₂⟩ := ((Tθ (lift (x3 A 0) 1) (lift 1 (x3 A 1)) (lift 1 (x3 A 2))).mul
      (((Ta (x3 A 1 * x3 A 2)).mul (Ta 1)).mul (((Tb (x3 A 0)).mul (Ta (x3 A 1))).mul (Ta (x3 A 2))).inv)).gen hP
      (φ := law2φ A (x3 A 0) (x3 A 1) (x3 A 2)) (ε := lawε) (fun U _ h => by
        rw [bx_self₂]
        simp only [bx_lift_mul, _root_.mul_one, _root_.one_mul, bx_lift_one (T := G3 A)]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
  have o : (1 : 𝟙_ (Over S) ⟶ A).left ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = (lift (1 : 𝟙_ (Over S) ⟶ A) 1).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id]
  obtain ⟨l₁, g₁, v₁⟩ := bx_norm hP t₁ h₁ (G3 A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left (Over.w _) a ha
    (1 : 𝟙_ (Over S) ⟶ A).left (fun U _ h => by
      refine (bx_prod₁ (A := A) (T := 𝟙_ (Over S)) 1 1 1 h).trans (Eq.trans ?_ (congrArg (fun q => (h q)⁻¹) o.symm))
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul])
  obtain ⟨l₂, g₂, v₂⟩ := bx_norm hP t₂ h₂ (G3 A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left (Over.w _) a ha
    (1 : 𝟙_ (Over S) ⟶ A).left (fun U _ h => by
      refine (bx_prod₂ (A := A) (T := 𝟙_ (Over S)) 1 1 1 h).trans (Eq.trans ?_ (congrArg (fun q => (h q)⁻¹) o.symm))
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul])
  exact ⟨l₁, l₂, g₁, g₂, fun y J hJ => (v₁ y J hJ).trans (v₂ y J hJ).symm⟩

private theorem bx_corr {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {T : Over S} (e : 𝟙_ (Over S) ⟶ T)
    (hp : Function.Surjective T.hom.appTop.hom) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (T.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (T.left ⟶ X)} {ε' : K' → ℤ}
    {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (hF : FormEq φ' ε' φ ε) (h : ∀ y J, Good L y J → val u e.left y J = val u' e.left y J) :
    LB.Gen.Corr L φ ε φ' ε' u u' :=
  corr_of_val hL fun y J hJ => gen_unique' hL hF T.hom e.left (Over.w e) hp hu hu' h _ _ y J hJ

private theorem bx_val {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((G3 A).left ⟶ X)} {ε : K → ℤ}
    (l : LB.Gen (LB.LinComb L φ ε)) {T : Over S} (e : 𝟙_ (Over S) ⟶ T) {a b c : T ⟶ A} (ha : e ≫ a = 1)
    (hb : e ≫ b = 1) (hc : e ≫ c = 1) {y} {J} (hJ : Good L y J) :
    val (LB.pullGen L φ ε l (lift a (lift b c)).left) e.left y J =
      val l (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, ha, hb, hc]

private theorem bx_padd {T : Over S} (a b : T ⟶ A) : padd A a b = a * b := rfl

private theorem bx_exist (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (θ : LB.Gen (Theta (A ⊗ A) P)) (hθ : θ.IsGen)
    (a : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen) (ha : a.IsGen)
    (b : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen) (hb : b.IsGen) : Nonempty (IsBiext A P) := by
  obtain ⟨l₁, l₂, g₁, g₂, v⟩ := bx_laws hP θ hθ a ha b hb
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have A₃ := AbelianSchemeGerms.isAbelianScheme_tensor A _ hA A₂
  have s₃ : Function.Surjective (G3 A).hom.appTop.hom := (hG _ _ A₃).2
  have s₄ : Function.Surjective (G4 A).hom.appTop.hom := (hG _ _ (AbelianSchemeGerms.isAbelianScheme_tensor A _ hA A₃)).2
  let e₃ : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  let e₄ : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
  have c₃ : ∀ i, e₃ ≫ x3 A i = 1 := fun i => by fin_cases i <;> simp [e₃, x3]
  have c₄ : ∀ i, e₄ ≫ x4 A i = 1 := fun i => by fin_cases i <;> simp [e₄, x4]
  have d₄ : ∀ i j, e₄ ≫ padd A (x4 A i) (x4 A j) = 1 := fun i j =>
    (MonObj.comp_mul _ _ _).trans (by rw [c₄, c₄, _root_.mul_one])
  have p₁ := fun {T : Over S} (f : T ⟶ G3 A) => DVR.pullGen_isGen _ _ _ _ g₁ f.left
  have p₂ := fun {T : Over S} (f : T ⟶ G3 A) => DVR.pullGen_isGen _ _ _ _ g₂ f.left
  refine ⟨⟨hP, l₁, l₂, g₁, g₂, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine bx_corr hP e₄ s₄ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁ _) (p₁ _)) (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁ _) (p₁ _))
      (fun U _ h => ?_) (fun y J hJ => ?_)
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (bx_prod₁ _ _ _ h) (bx_prod₁ _ _ _ h))).trans
        (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (bx_prod₁ _ _ _ h) (bx_prod₁ _ _ _ h))).symm)
      simp only [bx_padd, _root_.mul_assoc (x4 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (bx_val l₁ e₄ (d₄ _ _) (c₄ _) (c₄ _) hJ)
        (bx_val l₁ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (bx_val l₁ e₄ (c₄ _) (d₄ _ _) (c₄ _) hJ) (bx_val l₁ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).symm
  · refine bx_corr hP e₃ s₃ g₁ (p₁ _) (fun U _ h => ?_)
      (fun y J hJ => (bx_val l₁ e₃ (c₃ _) (c₃ _) (c₃ _) hJ).symm)
    refine (bx_prod₁ _ _ _ h).trans (Eq.trans ?_ (bx_self₁ h).symm)
    rw [_root_.mul_comm (x3 A 1), mul_right_comm]
  · refine bx_corr hP e₄ s₄ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂ _) (p₂ _)) (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂ _) (p₂ _))
      (fun U _ h => ?_) (fun y J hJ => ?_)
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (bx_prod₂ _ _ _ h) (bx_prod₂ _ _ _ h))).trans
        (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (bx_prod₂ _ _ _ h) (bx_prod₂ _ _ _ h))).symm)
      simp only [bx_padd, _root_.mul_assoc (x4 A 1)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (bx_val l₂ e₄ (c₄ _) (d₄ _ _) (c₄ _) hJ)
        (bx_val l₂ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (bx_val l₂ e₄ (c₄ _) (c₄ _) (d₄ _ _) hJ) (bx_val l₂ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).symm
  · refine bx_corr hP e₃ s₃ g₂ (p₂ _) (fun U _ h => ?_)
      (fun y J hJ => (bx_val l₂ e₃ (c₃ _) (c₃ _) (c₃ _) hJ).symm)
    refine (bx_prod₂ _ _ _ h).trans (Eq.trans ?_ (bx_self₂ h).symm)
    rw [_root_.mul_comm (x3 A 2), mul_right_comm]
  · refine bx_corr hP e₄ s₄
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁ _) (p₂ _)) (p₂ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂ _) (p₁ _)) (p₁ _))
      (fun U _ h => ?_) (fun y J hJ => ?_)
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
          (congrArg₂ (· * ·) (bx_prod₂ _ _ _ h) (bx_prod₁ _ _ _ h))) (bx_prod₁ _ _ _ h))).trans
        (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
          (congrArg₂ (· * ·) (bx_prod₁ _ _ _ h) (bx_prod₂ _ _ _ h))) (bx_prod₂ _ _ _ h))).symm)
      simp only [bx_padd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (bx_val l₁ e₄ (c₄ _) (c₄ _) (d₄ _ _) hJ) (bx_val l₂ e₄ (c₄ _) (c₄ _) (c₄ _) hJ)))
        (bx_val l₂ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).trans (Eq.trans ?_
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (bx_val l₂ e₄ (d₄ _ _) (c₄ _) (c₄ _) hJ) (bx_val l₁ e₄ (c₄ _) (c₄ _) (c₄ _) hJ)))
        (bx_val l₁ e₄ (c₄ _) (c₄ _) (c₄ _) hJ))).symm)
      rw [v y J hJ]

end SlopeTestRemainingChoices

end GlobalTheory.BiextOfCube

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem nonempty_isBiext_of_cube_gen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (A ⊗ A).left, P.IsLB → (∃ θ : LB.Gen (Theta (A ⊗ A) P), θ.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Nonempty (IsBiext A P) := by
  intro S A _ _ hA P hP ⟨θ, hθ⟩ ⟨a, ha⟩ ⟨b, hb⟩
  exact BiextOfCube.bx_exist GlobalTheory.firstFiveLaws.1.globalFns hA hP θ hθ a ha b hb

end GlobalTheory
