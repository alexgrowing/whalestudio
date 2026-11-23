import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilUnit

section Rep

variable {X Y Y' : Scheme.{0}} (L : LB X)

def IsVal (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ y J, Good L y J → val t (𝟙 Y) y J = v y J

variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}

theorem IsVal.pull {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (r : Y ⟶ Y') :
    IsVal L (fun _ _ h => ∏ k, h (r ≫ φ k) ^ ε k) (fun y J => val t r y J) :=
  ⟨K, inferInstance, _, ε, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun y J hJ => by rw [val_pull hJ, Category.id_comp]⟩

theorem IsVal.one : IsVal L (Y := Y) (fun _ _ _ => 1) (fun _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, fun i j => by
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _), fun _ _ _ => Fintype.prod_empty _, fun _ _ _ => val_one _⟩

theorem IsVal.mul (a : IsVal L F v) (b : IsVal L F' v') :
    IsVal L (fun U _ h => F U h * F' U h) (fun y J => v y J * v' y J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv y J hJ, hv' y J hJ]

theorem IsVal.inv (a : IsVal L F v) : IsVal L (fun U _ h => (F U h)⁻¹) (fun y J => (v y J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv y J hJ]

theorem IsVal.pow (a : IsVal L F v) (n : ℕ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsVal.one
  | succ n ih => simpa only [pow_succ] using ih.mul a

theorem IsVal.zpow (a : IsVal L F v) (n : ℤ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast] using a.pow k
  · simpa only [zpow_neg, zpow_natCast] using (a.pow k).inv

theorem IsVal.prod {I : Type} {G : I → ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    {u : I → ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ} (a : ∀ i, IsVal L (G i) (u i)) (s : Finset I) :
    IsVal L (fun U _ h => ∏ i ∈ s, G i U h) (fun y J => ∏ i ∈ s, u i y J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using IsVal.one
  | insert d s hd ih => simpa only [Finset.prod_insert hd] using (a d).mul ih

theorem IsVal.exists_unit (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨t', -, hv'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (h1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun y J hJ => ?_⟩
  rw [← hv y J hJ, ← hv' _ _ y J hJ, val_of t' _ y J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res _ y le trivial _)).symm.trans (gs_unit _ y ⊤ trivial _).symm

end Rep

theorem pow_eq_one_of_similitude {A I : Type} [CommGroup A] [Fintype I] [DecidableEq I] (m : ℕ) (hm : m ≠ 0)
    (al : Matrix I I ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix I I ℤ)) (ξ : I → A)
    (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : I) : ξ r ^ m = 1 := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ hm' this.symm
  have h2 : al * al.transpose = (m : ℤ) • (1 : Matrix I I ℤ) := by
    have e : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix I I ℤ)) * al := by
      rw [Matrix.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have e' := congrArg (· * al.adjugate) e
    simp only [Matrix.mul_assoc (_ : Matrix I I ℤ) al al.adjugate, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e'
    exact smul_right_injective _ hd e'
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = ξ r ^ m := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ r', ∏ c, ξ r' ^ (al r' c * al r c) = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
      have := congrFun (congrFun h2 r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, _root_.mul_one, mul_zero] at this
      rw [← this]
      exact (map_prod (zpowersHom A (ξ r')) (fun c => Multiplicative.ofAdd (al r' c * al r c)) Finset.univ).symm
    simp only [this, pow_ite, zpow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true, zpow_natCast]
  rw [← e]
  simp only [hk, one_zpow, Finset.prod_const_one]

theorem exists_normalising_unit : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  intro R _ x m al ξ mu w hm hal hk hmu hw
  haveI := x.P.isAb.comm
  have hξ : ∀ r, ξ r ^ m = 1 := pow_eq_one_of_similitude m hm al hal ξ fun c => by
    simpa only [List.prod_ofFn] using hk c
  have e₁ : ∀ c, eSec (Out.powObj x.P.A 4) ≫ (Out.powPr x.P.A c).left = eSec x.P.A := fun c =>
    congrArg CommaMorphism.left (IsMonHom.one_hom (Out.powPr x.P.A c))
  have e₂ : ∀ r, eSec (Out.powObj x.P.A 4) ≫ (alMap x al r (ξ r)).left = (ξ r).left := fun r => by
    have h1 : ∀ c, η[Out.powObj x.P.A 4] ≫ Out.powPr x.P.A c = 1 := fun c => by
      rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have : η[Out.powObj x.P.A 4] ≫ alMap x al r (ξ r) = ξ r := by
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one, h1, one_zpow, _root_.one_mul]
      rw [← Category.assoc, toUnit_unique (η[_] ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact congrArg CommaMorphism.left this
  have e₃ : ∀ r, (ξ r).left ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A := fun r => by
    have : ξ r ≫ (𝟙 x.P.A) ^ m = η[x.P.A] := by
      rw [MonObj.comp_pow, Category.comp_id, hξ, Hom.one_def, toUnit_unit, Category.id_comp]
    exact congrArg CommaMorphism.left this
  obtain ⟨u, hu⟩ := ((((IsVal.pull hw (eSec (Out.powObj x.P.A 4))).pow (m ^ 2)).mul
    (IsVal.prod (fun r => IsVal.pull hmu (ξ r).left) Finset.univ)).mul
    ((IsVal.pull x.rig_gen (𝟙 _)).zpow (4 - 4 * (m : ℤ) ^ 3)).inv).exists_unit x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e₁, e₂, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₃, Category.comp_id, Category.id_comp, Fintype.prod_unique, zpow_one,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unique, Finset.prod_zpow]
      generalize h (eSec x.P.A) = a
      generalize (∏ r, h (ξ r).left) = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one]
      module)
  let E := RingEquiv.ofBijective _ (cst_bijective (𝟙 (Sp R)) (W := ⊤) rfl)
  refine ⟨Units.map E.symm.toMonoidHom u, fun p J hJ => ?_⟩
  have e : cst (𝟙 (Sp R)) ⊤ (Units.map E.symm.toMonoidHom u : Rˣ) = u.val := E.apply_symm_apply u.val
  rw [e]
  have := hu p J hJ
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul] at this
  exact this

end GlobalTheory.SimilUnit
