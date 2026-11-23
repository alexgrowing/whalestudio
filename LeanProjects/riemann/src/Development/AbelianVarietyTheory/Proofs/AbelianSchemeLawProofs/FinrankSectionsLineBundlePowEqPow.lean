import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FinrankGrowthBounds

open Filter Topology

theorem le_of_pow_le_mul_pow {a b C : ℕ} (hb : 1 ≤ b) (h : ∀ k : ℕ, a ^ k ≤ C * b ^ k) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (1 : ℝ) < a / b := by rw [one_lt_div hb']; exact_mod_cast hab
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop (C : ℝ)).exists
  rw [div_pow, lt_div_iff₀ (pow_pos hb' k)] at hk
  have := h k
  have h2 : ((a : ℝ)) ^ k ≤ C * b ^ k := by exact_mod_cast this
  linarith

theorem le_of_frequently {a b g : ℕ} (h : ∀ M : ℕ, ∃ n, M ≤ n ∧ a * n ^ g ≤ b * (n + 8) ^ g) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  have ht : Tendsto (fun n : ℕ => (b : ℝ) * (1 + 8 / (n : ℝ)) ^ g) atTop (𝓝 ((b : ℝ) * (1 + 0) ^ g)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 8)).pow g).const_mul _
  have hlt : (b : ℝ) * (1 + 0) ^ g < a := by simpa using hab
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_lt_const hlt)
  obtain ⟨n, hn, hle⟩ := h (M + 1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := hM n (by omega)
  have h2 : (1 + 8 / (n : ℝ)) = (n + 8) / n := by field_simp
  rw [h2, div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hn0 g)] at h1
  have h3 : (a : ℝ) * n ^ g ≤ b * (n + 8) ^ g := by exact_mod_cast hle
  linarith

theorem eq_pow_of_growth (h : ℕ → ℕ) (g : ℕ) (G : ℕ → Prop) (hG : ∀ m, G m ∨ G (m + 1))
    (hG0 : ¬ G 0) (h1 : h 1 = 1)
    (hmono : Monotone h) (hrel : ∀ n j, G n → 1 ≤ j → h (n ^ 2 * j) = h (n ^ 2) * h j)
    (N c C : ℕ) (hN : 1 ≤ N)
    (hgr : ∀ t, 1 ≤ t → t ^ g ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ g) (j : ℕ) (hj : 1 ≤ j) :
    h j = j ^ g := by
  have hpos : ∀ n, G n → 1 ≤ n := fun n hn => Nat.pos_of_ne_zero fun e => hG0 (e ▸ hn)
  have hit : ∀ n, G n → ∀ i, 1 ≤ i → ∀ k, h ((n ^ 2) ^ k * i) = h (n ^ 2) ^ k * h i := by
    intro n hn i hi k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hpos n hn
      rw [pow_succ' (n ^ 2), Nat.mul_assoc, hrel n _ hn (Nat.mul_pos (by positivity) hi), ih]
      ring
  have hsq : ∀ n, G n → h (n ^ 2) = (n ^ 2) ^ g := by
    intro n hn
    have hn1 := hpos n hn
    apply le_antisymm
    · refine le_of_pow_le_mul_pow (C := C) (Nat.pos_of_ne_zero (by positivity)) fun k => ?_
      have e := hit n hn 1 le_rfl k
      rw [h1, Nat.mul_one, Nat.mul_one] at e
      rw [← e, ← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      refine le_trans (hmono (Nat.le_mul_of_pos_left _ hN)) (hgr _ (Nat.pos_of_ne_zero (by positivity))).2
    · have hd : 1 ≤ h (n ^ 2) := h1 ▸ hmono (Nat.pos_of_ne_zero (by positivity))
      refine le_of_pow_le_mul_pow (C := c * h N) hd fun k => ?_
      have e := hit n hn N hN k
      have := (hgr ((n ^ 2) ^ k) (Nat.pos_of_ne_zero (by positivity))).1
      rw [mul_comm N, e] at this
      rw [← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      calc _ ≤ _ := this
        _ = _ := by ring
  have hbig : ∀ M, ∃ n, M ≤ n ∧ G n := fun M => (hG M).elim (fun x => ⟨M, le_rfl, x⟩)
    fun x => ⟨M + 1, by omega, x⟩
  apply le_antisymm
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig M
    have hn1 := hpos n hn
    refine ⟨n, hMn, ?_⟩
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m + 1 ≤ m' ∧ m' ≤ m + 2 ∧ G m' :=
      (hG (m + 1)).elim (fun x => ⟨_, le_rfl, by omega, x⟩) fun x => ⟨_, by omega, le_rfl, x⟩
    have hnj : 1 ≤ n * j := Nat.mul_pos hn1 hj
    have l3 : m ≤ n * j := by
      by_contra hc
      push Not at hc
      have : n ^ 2 * j ≤ (n * j) * (n * j) := by nlinarith [Nat.mul_le_mul_left (n ^ 2 * j) hj]
      nlinarith
    have l4 : m' ^ 2 ≤ n * (j * (n + 8)) := by nlinarith
    have l5 : h (n ^ 2 * j) ≤ h (m' ^ 2) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := l5.trans (Nat.pow_le_pow_left l4 g)
    rw [pow_two, mul_pow, mul_pow, mul_pow, Nat.mul_assoc] at l6
    rw [mul_comm]
    exact Nat.le_of_mul_le_mul_left l6 (by positivity)
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig (M + 2)
    have hn1 := hpos n hn
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    have l3 : n ≤ m := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left (n ^ 2) hj]
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m' ≤ m ∧ m ≤ m' + 1 ∧ G m' :=
      (hG (m - 1)).elim (fun x => ⟨_, by omega, by omega, x⟩) fun x => ⟨_, by omega, by omega, x⟩
    have hm1 := hpos m' hm'
    refine ⟨m', by omega, ?_⟩
    have l4 : n ^ 2 * j ≤ m' * (m' + 8) := by nlinarith
    have l5 : h (m' ^ 2) ≤ h (n ^ 2 * j) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := Nat.pow_le_pow_left l4 g
    rw [mul_pow, mul_pow] at l6
    rw [pow_two m', mul_pow] at l5
    have l7 : (n ^ 2) ^ g * (j ^ g * m' ^ g) ≤ (n ^ 2) ^ g * (h j * (m' + 8) ^ g) :=
      calc _ = ((n ^ 2) ^ g * j ^ g) * m' ^ g := by ring
        _ ≤ (m' ^ g * (m' + 8) ^ g) * m' ^ g := Nat.mul_le_mul_right _ l6
        _ = (m' ^ g * m' ^ g) * (m' + 8) ^ g := by ring
        _ ≤ ((n ^ 2) ^ g * h j) * (m' + 8) ^ g := Nat.mul_le_mul_right _ l5
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left l7 (by positivity)

theorem finite_index {R : Type*} [Field R] {M I : Type*} [AddCommGroup M] [Module R M]
    [Nontrivial M] [Module.Finite R (I → M)] : Finite I := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : LinearIndependent R (fun i : I => (Pi.single i m : I → M)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single i] at this
    · simpa [hm] using this
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · exact fun x => (x hi).elim
  exact this.finite

theorem finrank_eq_mul {R : Type*} [CommRing R] (hR : IsField R) {I A M B M' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] [AddCommGroup B] [Module R B]
    [AddCommGroup M'] [Module R M'] [Module.Finite R A] [Module.Finite R M']
    (hM : Module.finrank R M = 1) (e : A ≃ₗ[R] (I → M)) (e' : B ≃ₗ[R] (I → M')) :
    Module.finrank R B = Module.finrank R A * Module.finrank R M' := by
  letI := hR.toField
  haveI : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hM
  haveI : Module.Finite R M := Module.finite_of_finrank_eq_succ hM
  haveI : Module.Finite R (I → M) := Module.Finite.equiv e
  haveI : Finite I := finite_index (R := R) (M := M)
  letI := Fintype.ofFinite I
  rw [e.finrank_eq, e'.finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [hM]

theorem sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {M : LB X} (s : LB.Sec M) {i₀ : M.ι}
    (h₀ : s.f i₀ ≠ 0) (i : M.ι) [hi : Nonempty (M.U i)] : s.f i ≠ 0 := by
  intro hz
  have hi₀ : Nonempty (M.U i₀) := by
    by_contra hn
    have e : M.U i₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hn ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ(X, M.U i₀) := by rw [e]; infer_instance
    exact h₀ (Subsingleton.elim _ _)
  haveI : Nonempty (M.U i₀ ⊓ M.U i : X.Opens) := by
    obtain ⟨a⟩ := hi₀
    obtain ⟨b⟩ := hi
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (M.U i₀).isOpen (M.U i).isOpen ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
    exact ⟨⟨x, hx⟩⟩
  have hc := s.compat i₀ i
  rw [hz, map_zero, mul_zero] at hc
  apply h₀
  apply map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i₀ ⊓ M.U i ≤ M.U i₀))
  simpa using hc

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

theorem lpow_g_add (a b : ℤ) (i j : Fin 1 → L.ι) :
    (LPow A L (a + b) T).g i j =
      (show Γ((T ⊗ A).left, (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j)ˣ from
        (LPow A L a T).g i j) *
      (show Γ((T ⊗ A).left, (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j)ˣ from
        (LPow A L b T).g i j) := by
  simp only [LPow, LB.LinComb, zpow_add, Finset.prod_mul_distrib]
  rfl

noncomputable def mulSec (a b : ℤ) (s : SecM A L b T) :
    SecM A L a T →ₗ[Γ(T.left, ⊤)] SecM A L (a + b) T where
  toFun f := ⟨fun i => (show Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i) from f.1 i) *
      (show Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i) from s.1 i), by
    intro i j
    have hf := f.2 i j
    have hs := s.2 i j
    rw [lpow_g_add A L T a b i j]
    refine (map_mul _ _ _).trans ?_
    refine (congrArg₂ (fun x y : Γ((T ⊗ A).left,
      (LPow A L (a + b) T).U i ⊓ (LPow A L (a + b) T).U j) => x * y) hf hs).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) (Units.val_mul _ _).symm (map_mul _ _ _).symm)
    exact mul_mul_mul_comm _ _ _ _⟩
  map_add' f f' := Subtype.ext (funext fun i =>
    add_mul (R := Γ((T ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd T A).left) i)) (f.1 i) (f'.1 i) (s.1 i))
  map_smul' c f := Subtype.ext (funext fun i => _root_.mul_assoc (liftHom A _ c) _ _)

theorem mulSec_injective [IsIntegral (T ⊗ A).left] (a b : ℤ) (s : SecM A L b T) (hs : s ≠ 0) :
    Function.Injective (mulSec A L T a b s) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨i₀, h₀⟩ : ∃ i, s.1 i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hs (Subtype.ext (funext hc))
  refine Subtype.ext (funext fun i => ?_)
  by_cases hi : Nonempty ((LPow A L b T).U i)
  · have h1 : (SecM.toSec A s).f i ≠ 0 := sec_ne_zero (SecM.toSec A s) (i₀ := i₀) h₀ i
    have h2 := congrFun (congrArg Subtype.val hf) i
    haveI : IsDomain Γ((T ⊗ A).left, (LPow A L b T).U i) := inferInstance
    exact (mul_eq_zero (M₀ := Γ((T ⊗ A).left, (LPow A L b T).U i)).1 h2).resolve_right h1
  · have e : (LPow A L a T).U i = ⊥ := by
      ext x
      exact ⟨fun hx => (hi ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ((T ⊗ A).left, (LPow A L a T).U i) := by rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem isField_base (K : Type) [Field K] :
    IsField Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

theorem finrank_sections_lineBundlePow_eq_pow : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → GlobalSectionsRankAlgClosed := by
  intro hint hone hrel hgrow _ K _ _ P
  obtain ⟨hfin, N, c, C, hN, -, hgr⟩ := hgrow K P
  have hF := isField_base K
  haveI : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) := hF.nontrivial
  haveI : GeometricallyIntegral P.A.hom := hint _ _ _ P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) _ _ _
      (IsPullback.of_hasPullback (𝟙 (Spec (CommRingCat.of K))) P.A.hom).flip
  have h1 := hone K P
  haveI : Nontrivial (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) :=
    Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨s, hs⟩ := exists_ne (0 : SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K))))
  intro n hn
  refine eq_pow_of_growth (fun j : ℕ => Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) P.g (fun m => (m : K) ≠ 0)
      ?_ (by simp) h1 ?_ ?_ N c C hN hgr n hn
  · intro m
    by_cases hm : (m : K) = 0
    · right
      simp [hm]
    · exact Or.inl hm
  · refine monotone_nat_of_le_succ fun j => ?_
    haveI : Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L ((j : ℤ) + 1) (baseOver (Spec (CommRingCat.of K)))) := hfin (j + 1)
    exact LinearMap.finrank_le_finrank_of_injective (mulSec_injective P.A P.L _ (j : ℤ) 1 s hs)
  · intro m j hm hj
    obtain ⟨e⟩ := hrel K P m 1 hm le_rfl
    obtain ⟨e'⟩ := hrel K P m j hm hj
    rw [Nat.mul_one] at e
    haveI := hfin (m ^ 2)
    haveI := hfin j
    exact finrank_eq_mul hF h1 e e'

end GlobalTheory.FinrankGrowthBounds
