import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SympBasis

private theorem sum_inv_mulVec_smul_col_of_det_ne_zero {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (i : ℕ) < g ∧ (j : ℕ) = i + g) : ∑ l, c l * (Out.stdSymp g l j : R) = c i := by
  rw [Finset.sum_eq_single i]
  · unfold Out.stdSymp
    rw [if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := fun h => hl (Fin.ext (by omega))
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

private theorem sum_mul_stdSymp_eq_neg_of_eq_add {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (j : ℕ) < g ∧ (i : ℕ) = j + g) : ∑ l, c l * (Out.stdSymp g l j : R) = - c i := by
  rw [Finset.sum_eq_single i]
  · have h1 : ¬ ((i : ℕ) < g ∧ (j : ℕ) = i + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := by omega
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := fun h => hl (Fin.ext (by omega))
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

theorem eq_of_sum_stdSymp {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by
  funext i
  have hi2 := i.isLt
  by_cases hi : (i : ℕ) < g
  ·
    have h1 := h ⟨i + g, by omega⟩
    rwa [sum_inv_mulVec_smul_col_of_det_ne_zero a i _ ⟨hi, rfl⟩, sum_inv_mulVec_smul_col_of_det_ne_zero b i _ ⟨hi, rfl⟩] at h1
  ·
    have h1 := h ⟨i - g, by omega⟩
    rw [sum_mul_stdSymp_eq_neg_of_eq_add a i _ ⟨by simp; omega, by simp; omega⟩,
      sum_mul_stdSymp_eq_neg_of_eq_add b i _ ⟨by simp; omega, by simp; omega⟩] at h1
    exact neg_inj.mp h1

theorem rel_prod {M U : Type} [CommMonoid M] [CommGroup U] (W : M → U → Prop) (h1 : W 1 1)
    (hm : ∀ x x' c c', W x c → W x' c' → W (x * x') (c * c')) {J : Type} (s : Finset J) (p : J → M) (u : J → U)
    (a : J → ℕ) (hp : ∀ i, W (p i) (u i)) : W (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, u i ^ a i) := by
  classical
  have hpow : ∀ i (n : ℕ), W (p i ^ n) (u i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact hm _ _ _ _ ih (hp i)
  refine Finset.induction_on s (by simpa using h1) ?_
  intro j t hj ih
  rw [Finset.prod_insert hj, Finset.prod_insert hj]
  exact hm _ _ _ _ (hpow j (a j)) ih

private theorem zpow_finset_sum_divisor {U : Type} [CommGroup U] (z : U) {I : Type} (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem injective_of_pairing {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by
  classical

  have hone : ∀ y, y ^ k = 1 → W 1 y 1 := by
    intro y hy
    obtain ⟨c, hc, huniq⟩ := hu 1 y (one_pow k) hy
    have h2 : W 1 y (c * c) := by simpa using hm 1 1 y c c hc hc
    have hcc : c * c = c := huniq _ h2
    have hc1 : c = 1 := by simpa using hcc
    rw [hc1] at hc
    exact hc

  let e : (Fin (2 * g) → ZMod k) → Fin (2 * g) → ℤ := fun c j => ∑ i, Out.stdSymp g i j * ((c i).val : ℤ)
  have hW : ∀ (c : Fin (2 * g) → ZMod k) j, W (∏ i, p i ^ (c i).val) (p j) (z ^ e c j) := by
    intro c j
    have h := rel_prod (fun x v => W x (p j) v) (hone _ (hp j))
      (fun x x' v v' hx hx' => hm x x' (p j) v v' hx hx') Finset.univ p
      (fun i => z ^ Out.stdSymp g i j) (fun i => (c i).val) (fun i => hw i j)
    have hz' : (∏ i, (z ^ Out.stdSymp g i j) ^ (c i).val) = z ^ e c j := by
      simp only [e, zpow_finset_sum_divisor]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
    simpa only [hz'] using h
  have htors : ∀ c : Fin (2 * g) → ZMod k, (∏ i, p i ^ (c i).val) ^ k = 1 := by
    intro c
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hp i, one_pow]
  intro c c' hcc
  have hcc' : (∏ i, p i ^ (c i).val) = ∏ i, p i ^ (c' i).val := hcc
  have key : ∀ j, z ^ e c j = z ^ e c' j := by
    intro j
    obtain ⟨w, _, huniq⟩ := hu _ (p j) (htors c) (hp j)
    have h1 := huniq _ (hW c j)
    have h2 := huniq _ (hcc' ▸ hW c' j)
    rw [h1, h2]
  apply eq_of_sum_stdSymp (R := ZMod k) c c'
  intro j
  have hd : ((e c j : ℤ) : ZMod k) = ((e c' j : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hz.zpow_eq_one_iff_dvd, zpow_sub, key j, mul_inv_cancel]
  simpa [e, mul_comm] using hd

private theorem comp_list_prod_eq_prod_map_comp_over {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T)
    (l : List (T ⟶ A)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons x l ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem comp_linComb {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  rw [comp_list_prod_eq_prod_map_comp_over, List.map_ofFn]
  simp [Function.comp_def, MonObj.comp_pow]

end GlobalTheory.SympBasis

namespace GlobalTheory

open SympBasis in

theorem symplectic_system_torsion_basis :
    Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  intro hL K₀ _ P k ze pt hk hze hpt hw K _ _ x y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  have : NeZero k := ⟨hk0⟩
  have hsep : IsSeparated P.A.hom := by
    obtain ⟨_, _, _, _⟩ := P.isAb
    infer_instance

  let h : Over.mk x ⟶ Out.baseOver (Sp K₀) := Over.homMk x (by simp)

  have hpre : ∀ s s' : Out.baseOver (Sp K₀) ⟶ P.A, h ≫ s = h ≫ s' → s = s' := by
    intro s s' hss
    have : IsReduced (Out.baseOver (Sp K₀)).left := inferInstanceAs (IsReduced (Sp K₀))
    have : IsDominant (X := Sp K) (Y := (Out.baseOver (Sp K₀)).left) x :=
      inferInstanceAs (IsDominant (X := Sp K) (Y := Sp K₀) x)
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated P.A.hom ?_ x ?_
    · rw [Over.w s, Over.w s']
    · simpa [h] using congrArg CommaMorphism.left hss

  have hzu : IsPrimitiveRoot (unitOn ze) k := by
    unfold unitOn
    refine hze.map_of_injective (Units.map_injective ?_)
    exact Function.LeftInverse.injective
      (g := (Scheme.ΓSpecIso (CommRingCat.of K₀)).hom.hom) fun a => by simp

  obtain ⟨hu, hm, -, -⟩ := hL.weil (Sp K₀) P k (Out.baseOver (Sp K₀))
  have hinj0 := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L (k : ℤ) a b c) k hu
    (fun a a' b c c' => hm a a' b c c') pt hpt (unitOn ze) hzu hw

  have hlin : ∀ c : Fin (2 * P.g) → ZMod k,
      Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) = h ≫ ∏ i, pt i ^ (c i).val := by
    intro c
    rw [← SympBasis.comp_linComb]
    unfold Out.linComb
    rw [List.prod_ofFn]
  have htors : ∀ c : Fin (2 * P.g) → ZMod k,
      (Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val)) ^ k = 1 := by
    intro c
    rw [hlin, ← MonObj.comp_pow, ← Finset.prod_pow,
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt i, one_pow]]
    exact MonObj.comp_one _
  let Φ : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c => ⟨_, htors c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' hcc
    have h1 : Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) =
        Out.linComb (fun i => h ≫ pt i) (fun i => (c' i).val) := congrArg Subtype.val hcc
    rw [hlin, hlin] at h1
    exact hinj0 (hpre _ _ h1)

  have hkK : ((k : ℕ) : K) ≠ 0 := by
    have hc : ((k : ℕ) : K) = (Spec.preimage x).hom (k : K₀) := by simp
    rw [hc]
    exact (map_ne_zero_iff _ (Spec.preimage x).hom.injective).2 hk
  have hcard := (hL.mulN (Sp K₀) P k (Nat.one_le_iff_ne_zero.2 hk0)).2.2.2.2 K x hkK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc,
    fun c' hc' => hbij.1 (Subtype.ext (hc'.trans (congrArg Subtype.val hc).symm))⟩

end GlobalTheory
