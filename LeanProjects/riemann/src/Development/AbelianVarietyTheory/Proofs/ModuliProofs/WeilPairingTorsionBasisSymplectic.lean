import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinCombStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormTorsion

theorem rel_prod {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hm : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) :
    ∀ (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ), (∀ i, R (y i) (c i)) →
      R (List.ofFn fun i => y i ^ a i).prod (∏ i, c i ^ a i) := by
  first
  | exact @_root_.GlobalTheory.RelationPowers.rel_prod_pow
  | exact _root_.GlobalTheory.RelationPowers.rel_prod_pow
  | (apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationPowers.rel_prod_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationPowers.rel_prod_pow ..)

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_linComb (hW : Out.WeilSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ) {n : ℕ}
    (y : Fin n → (Out.baseOver (Sp K) ⟶ P.A)) (z : Out.baseOver (Sp K) ⟶ P.A) (hz : z ^ k = 1)
    (e : Fin n → ℤ) (a : Fin n → ℕ) (h : ∀ i, Out.WeilIs P.A P.L k (y i) z (unitOn (ζ ^ e i))) :
    Out.WeilIs P.A P.L k (Out.linComb y a) z (unitOn (ζ ^ ∑ i, (a i : ℤ) * e i)) := by
  obtain ⟨hu, hm, -, -⟩ := hW (Sp K) P k (Out.baseOver (Sp K))
  have h1 : Out.WeilIs P.A P.L k 1 z 1 := by
    obtain ⟨c, hc, hc'⟩ := hu 1 z (one_pow k) hz
    have h2 := hm _ _ _ _ _ hc hc
    rw [_root_.mul_one] at h2
    have : c = 1 := mul_eq_left.1 (hc' _ h2)
    exact this ▸ hc
  have H := rel_prod (fun x (c : Kˣ) => Out.WeilIs P.A P.L k x z (unitOn c))
    (by
      have : unitOn (1 : Kˣ) = 1 := map_one _
      show Out.WeilIs P.A P.L k 1 z (unitOn 1)
      rw [this]; exact h1)
    (fun x x' c c' hx hx' => by
      have : unitOn (c * c') = unitOn c * unitOn c' := map_mul _ _ _
      show Out.WeilIs P.A P.L k (x * x') z (unitOn (c * c'))
      rw [this]; exact hm _ _ _ _ _ hx hx') n y (fun i => ζ ^ e i) a h
  have e' : ∏ i, (ζ ^ e i) ^ a i = ζ ^ ∑ i, (a i : ℤ) * e i := by
    have key : ∀ t : Finset (Fin n), ∏ i ∈ t, (ζ ^ e i) ^ a i = ζ ^ ∑ i ∈ t, (a i : ℤ) * e i := fun t => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add, ← zpow_natCast, ← zpow_mul,
          _root_.mul_comm (e b)]
    exact key _
  rw [← e']
  exact H

theorem weilIs_symm_zpow {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ)
    {x y : Out.baseOver (Sp K) ⟶ P.A} {e : ℤ} (h : Out.WeilIs P.A P.L k x y (unitOn (ζ ^ e))) :
    Out.WeilIs P.A P.L k y x (unitOn (ζ ^ (-e))) := by
  have : unitOn (ζ ^ (-e)) = (unitOn (ζ ^ e))⁻¹ := by
    rw [zpow_neg]; exact map_inv _ _
  rw [this]
  exact GlobalTheory.CommPairing.weilIs_symm P.isLB h

theorem injective_stdSymp (g k : ℕ) :
    Function.Injective (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k)) := by
  intro x x' h
  apply GlobalTheory.injective_toBilin'_stdSymp (R := ZMod k) g
  ext a
  have := congrFun h a
  simpa [Matrix.toBilin'_apply, Pi.single_apply] using this

theorem exists_matrix_form : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  intro hL hL2 g N k Mat
  classical
  refine ⟨fun i j => Function.invFun
    (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k))
    (fun a => -(((Out.stdSymp g a j : ℤ) : ZMod k) * N +
      (∑ i, Mat i a * -(∑ l, Mat l j * ((Out.stdSymp g l i : ℤ) : ZMod k))) * N)) i, ?_⟩
  intro K _ _ P pt ζ f s hk hζ hB hpt hf hM hs
  refine ⟨hB.pos, fun j => ?_⟩
  haveI : NeZero k := ⟨fun e => hk (by simp [e])⟩
  haveI := hs.isMonHom
  have tors : ∀ (u : P.A ⟶ P.A) [IsMonHom u] i, (pt i ≫ u) ^ k = 1 := fun u _ i => by
    have := congrArg (IsMonHom.monoidHom u _) (hB.pow_eq_one i)
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨c, hc, -⟩ := hB.existsUnique (tors s j)
  rw [← hc]
  congr 1
  funext i
  congr 1
  refine congrFun (?_ : c = _) i
  rw [← Function.leftInverse_invFun (injective_stdSymp g k) c]
  congr 1
  funext a
  have w₁ := weilIs_linComb hL.weil P k ζ pt (pt a) (hB.pow_eq_one a) _ (fun i => (c i).val) (fun i => hpt i a)
  rw [hc] at w₁
  have w₂ : ∀ i, Out.WeilIs P.A P.L k (pt i) (pt j ≫ f)
      (unitOn (ζ ^ (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i))) := fun i => by
    rw [hM.comp_eq j]
    exact weilIs_symm_zpow P k ζ (weilIs_linComb hL.weil P k ζ pt (pt i) (hB.pow_eq_one i) _ _ (fun l => hpt l i))
  have w₃ := weilIs_linComb hL.weil P k ζ pt _ (tors f j) _ (fun i => (Mat i a).val) w₂
  rw [← hM.comp_eq a] at w₃
  have eφ : (fun i : Fin 2 => ((![𝟙 P.A, f] : Fin 2 → (P.A ⟶ P.A)) i).left) = ![𝟙 P.A.left, f.left] := by
    funext i; fin_cases i <;> rfl
  have w₄ := GlobalTheory.T.weilPairing_of_polarisationForm_linComb hL hL2 K P (Fin 2) ![𝟙 P.A, f] ![(N : ℤ), (N : ℤ)] s k (pt a) (pt j)
    ![ζ ^ Out.stdSymp g a j, ζ ^ ∑ i, ((Mat i a).val : ℤ) * (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i)] hk
    (fun i => by
      fin_cases i
      · exact (inferInstance : IsMonHom (𝟙 P.A))
      · exact hf)
    (by rw [eφ]; exact hs) (hB.pow_eq_one a) (hB.pow_eq_one j)
    (fun i => by
      fin_cases i
      · show Out.WeilIs P.A P.L k (pt a ≫ 𝟙 _) (pt j ≫ 𝟙 _) _
        rw [Category.comp_id, Category.comp_id]
        exact hpt a j
      · exact w₃)
  rw [Fin.prod_univ_two] at w₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at w₄
  rw [← zpow_mul, ← zpow_mul, ← zpow_add] at w₄
  have w₅ := weilIs_symm_zpow P k ζ w₄
  have e := unitOn_inj (((hL.weil (Sp K) P k _).1 _ _ (tors s j) (hB.pow_eq_one a)).unique w₁ w₅)
  rw [← mul_inv_eq_one, ← zpow_sub, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at e
  push_cast at e
  simp only [ZMod.natCast_zmod_val] at e
  exact sub_eq_zero.1 e

end GlobalTheory.FormTorsion
