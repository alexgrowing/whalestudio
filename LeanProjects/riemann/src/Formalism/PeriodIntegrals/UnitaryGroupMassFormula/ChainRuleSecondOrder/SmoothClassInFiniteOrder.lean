import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf

open Matrix Finset

noncomputable section

namespace PI.ComplexConjugateDerivative

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Good (Φ : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  (∀ f₁ f₂ : B.Mat k r → E, (∀ h ∈ B.GV k r, f₁ h = f₂ h) → ∀ g ∈ B.GV k r, Φ f₁ g = Φ f₂ g) ∧
  (∀ f₁ f₂ : B.Mat k r → E, SS k r f₁ → SS k r f₂ → ∀ g ∈ B.GV k r, Φ (f₁ + f₂) g = Φ f₁ g + Φ f₂ g) ∧
  (∀ (c : ℝ) (f : B.Mat k r → E), SS k r f → ∀ g ∈ B.GV k r, Φ (c • f) g = c • Φ f g)

theorem good_id : Good (k := k) (r := r) (E := E) id :=
  ⟨fun _ _ h g hg => h g hg, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem good_comp {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {b : Bool} {X : B.Mat k r}
    (hX : B.inLie k r X) : Good (fun f => Φ (D b X f)) := by
  refine ⟨fun f₁ f₂ h g hg => hΦ.1 _ _ (fun y hy => D_congr h hy hX) g hg, fun f₁ f₂ h₁ h₂ g hg => ?_,
    fun c f hf g hg => ?_⟩
  · show Φ (D b X (f₁ + f₂)) g = Φ (D b X f₁) g + Φ (D b X f₂) g
    rw [hΦ.1 _ (D b X f₁ + D b X f₂) (fun y hy => D_add h₁ h₂ hy hX) g hg]
    exact hΦ.2.1 _ _ (ss_D h₁ hX) (ss_D h₂ hX) g hg
  · show Φ (D b X (c • f)) g = c • Φ (D b X f) g
    rw [hΦ.1 _ (c • D b X f) (fun y hy => D_smul c hf hy hX) g hg]
    exact hΦ.2.2 c _ (ss_D hf hX) g hg

theorem good_sum {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {N : ℕ} (c : Fin N → ℝ)
    (h : Fin N → B.Mat k r → E) (hh : ∀ i, SS k r (h i)) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Φ (∑ i, c i • h i) g = ∑ i, c i • Φ (h i) g := by
  have h0 : Φ 0 g = 0 := by
    have := hΦ.2.2 0 0 ss_zero g hg
    simpa only [zero_smul] using this
  have key : ∀ s : Finset (Fin N),
      SS k r (∑ i ∈ s, c i • h i) ∧ Φ (∑ i ∈ s, c i • h i) g = ∑ i ∈ s, c i • Φ (h i) g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact ⟨ss_zero, h0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨ss_add (ss_smul _ (hh a)) ih.1, ?_⟩
      rw [hΦ.2.1 _ _ (ss_smul _ (hh a)) ih.1 g hg, hΦ.2.2 _ _ (hh a) g hg, ih.2]
  exact (key univ).2

def ev : List Bool → List (B.Mat k r) → (B.Mat k r → E) → (B.Mat k r → E)
  | b :: ks, X :: xs, f => D b X (ev ks xs f)
  | _, _, f => f

theorem ss_ev : ∀ (ks : List Bool) (xs : List (B.Mat k r)) {f : B.Mat k r → E},
    (∀ X ∈ xs, B.inLie k r X) → SS k r f → SS k r (ev ks xs f)
  | [], _, _, _, hf => by simpa [ev] using hf
  | _ :: _, [], _, _, hf => by simpa [ev] using hf
  | b :: ks, X :: xs, f, hxs, hf => by
    show SS k r (D b X (ev ks xs f))
    exact ss_D (ss_ev ks xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY)) hf) (hxs X List.mem_cons_self)

theorem rw_eq_ev (v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.Rw v F = ev (List.replicate v.length false) v F := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show Formalism.REAL.RdV X (B.Rw v F) = D false X (ev (List.replicate v.length false) v F)
    rw [ih]; rfl

theorem dLR_eq_ev (u v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.dLR u v F = ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F := by
  induction u with
  | nil => exact rw_eq_ev v F
  | cons X u ih =>
    show B.LdV X (B.dLR u v F) = D true X (ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F)
    rw [ih]; rfl

def bsum {N : ℕ} (e : Fin N → B.Mat k r) : List Bool → (List (B.Mat k r) → ℝ) → ℝ
  | [], Ψ => Ψ []
  | _ :: ks, Ψ => ∑ i, bsum e ks (fun β => Ψ (e i :: β))

theorem bsum_mul {N : ℕ} (e : Fin N → B.Mat k r) (a : ℝ) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), bsum e ks (fun β => a * Ψ β) = a * bsum e ks Ψ
  | [], _ => rfl
  | _ :: ks, Ψ => by
    simp only [bsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => bsum_mul e a ks _

theorem bsum_mono {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ₁ Ψ₂ : List (B.Mat k r) → ℝ),
      (∀ β : List (B.Mat k r), β.length = ks.length → (∀ x ∈ β, ∃ i, x = e i) → Ψ₁ β ≤ Ψ₂ β) →
      bsum e ks Ψ₁ ≤ bsum e ks Ψ₂
  | [], _, _, h => h [] rfl (by simp)
  | _ :: ks, Ψ₁, Ψ₂, h => by
    simp only [bsum]
    refine Finset.sum_le_sum fun i _ => bsum_mono e ks _ _ fun β hβ hβe => h (e i :: β) (by simp [hβ]) ?_
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · exact ⟨i, hx⟩
    · exact hβe x hx

theorem bsum_nonneg {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), (∀ β, 0 ≤ Ψ β) → 0 ≤ bsum e ks Ψ
  | [], _, h => h []
  | _ :: ks, Ψ, h => by
    simp only [bsum]
    exact Finset.sum_nonneg fun i _ => bsum_nonneg e ks _ fun β => h _

theorem expand {N : ℕ} (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ i, B.inLie k r (e i)) (hc : ∀ X, B.inLie k r X → X = ∑ i, c i X • e i) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), xs.length = ks.length →
      (∀ X ∈ xs, B.inLie k r X ∧ ∀ i, |c i X| ≤ K) →
      ∀ (Φ : (B.Mat k r → E) → (B.Mat k r → E)), Good Φ → ∀ f, SS k r f → ∀ g ∈ B.GV k r,
        ‖Φ (ev ks xs f) g‖ ≤ K ^ xs.length * bsum e ks (fun β => ‖Φ (ev ks β f) g‖) := by
  intro ks
  induction ks with
  | nil =>
    intro xs hlen _ Φ _ f _ g _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    simp [ev, bsum]
  | cons b ks ih =>
    intro xs hlen hxs Φ hΦ f hf g hg
    cases xs with
    | nil => simp at hlen
    | cons X xs =>
      have hlen' : xs.length = ks.length := by simpa using hlen
      have hX := hxs X List.mem_cons_self
      have hxs' : ∀ Y ∈ xs, B.inLie k r Y ∧ ∀ i, |c i Y| ≤ K :=
        fun Y hY => hxs Y (List.mem_cons_of_mem _ hY)
      have hh : SS k r (ev ks xs f) := ss_ev ks xs (fun Y hY => (hxs' Y hY).1) hf
      have hexp : ∀ g' ∈ B.GV k r,
          D b X (ev ks xs f) g' = (∑ i, c i X • D b (e i) (ev ks xs f)) g' := by
        intro g' hg'
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply]
        exact D_letter hh hg' he hX.1 (hc X hX.1)
      have step1 : Φ (ev (b :: ks) (X :: xs) f) g = ∑ i, c i X • Φ (D b (e i) (ev ks xs f)) g := by
        show Φ (D b X (ev ks xs f)) g = _
        rw [hΦ.1 _ _ hexp g hg]
        exact good_sum hΦ _ _ (fun i => ss_D hh (he i)) hg
      rw [step1]
      calc ‖∑ i, c i X • Φ (D b (e i) (ev ks xs f)) g‖
          ≤ ∑ i, ‖c i X • Φ (D b (e i) (ev ks xs f)) g‖ := norm_sum_le _ _
        _ ≤ ∑ i, K * (K ^ xs.length * bsum e ks (fun β => ‖Φ (D b (e i) (ev ks β f)) g‖)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hX.2 i)
            (ih xs hlen' hxs' (fun f' => Φ (D b (e i) f')) (good_comp hΦ (he i)) f hf g hg)
            (norm_nonneg _) hK
        _ = K ^ (X :: xs).length * bsum e (b :: ks) (fun β => ‖Φ (ev (b :: ks) β f) g‖) := by
          rw [List.length_cons]
          simp only [bsum, ev]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

def lieSub (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := fun {X Y} hX hY => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
    show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [hX', hY', add_zero]
  zero_mem' := by
    show (0 : B.Mat k r)ᴴ * Hpk k r + Hpk k r * 0 = 0
    simp
  smul_mem' := fun a X hX => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (a • X)ᴴ * Hpk k r + Hpk k r * (a • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]

theorem basis_exists (k r : ℕ) : ∃ (N : ℕ) (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) (K : ℝ),
    0 ≤ K ∧ (∀ i, B.unitLie k r (e i)) ∧ (∀ X, B.inLie k r X → X = ∑ i, c i X • e i) ∧
    (∀ X, B.unitLie k r X → ∀ i, |c i X| ≤ K) := by
  classical
  have : FiniteDimensional ℝ (B.Mat k r) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  let bs := Module.finBasis ℝ (lieSub k r)
  let N := Module.finrank ℝ (lieSub k r)
  let s : Fin N → ℝ := fun i => max 1 ‖((bs i : lieSub k r) : B.Mat k r)‖
  have hs1 : ∀ i, 1 ≤ s i := fun i => le_max_left _ _
  have hs0 : ∀ i, 0 < s i := fun i => lt_of_lt_of_le one_pos (hs1 i)
  have hb : ∀ i : Fin N, ∃ C, 0 < C ∧ ∀ x : lieSub k r, ‖bs.coord i x‖ ≤ C * ‖x‖ :=
    fun i => (LinearMap.toContinuousLinearMap (bs.coord i)).bound
  choose C hC0 hC using hb
  let K : ℝ := ∑ i, C i * s i
  refine ⟨N, fun i => (s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r),
    fun i X => if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0, K, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i).le (hs0 i).le
  · intro i
    refine ⟨(lieSub k r).smul_mem (s i)⁻¹ (bs i).2, fun p q => ?_⟩
    show ‖((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r)) p q‖ ≤ 1
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hs0 i)),
      inv_mul_le_iff₀ (hs0 i), mul_one]
    exact le_trans (Matrix.norm_entry_le_entrywise_sup_norm _) (le_max_right _ _)
  · intro X hX
    have h1 := congrArg Subtype.val (bs.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = (if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0) • ((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r))
    rw [dif_pos hX, smul_smul, mul_assoc, mul_inv_cancel₀ (hs0 i).ne', mul_one]
  · intro X hX i
    show |(if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0)| ≤ K
    rw [dif_pos hX.1, abs_mul, abs_of_pos (hs0 i)]
    have hXn : ‖(⟨X, hX.1⟩ : lieSub k r)‖ ≤ 1 := by
      show ‖X‖ ≤ 1
      exact (Matrix.norm_le_iff zero_le_one).2 hX.2
    have hrep : |bs.repr ⟨X, hX.1⟩ i| ≤ C i := by
      rw [← Module.Basis.coord_apply, ← Real.norm_eq_abs]
      calc ‖bs.coord i ⟨X, hX.1⟩‖ ≤ C i * ‖(⟨X, hX.1⟩ : lieSub k r)‖ := hC i _
        _ ≤ C i * 1 := mul_le_mul_of_nonneg_left hXn (hC0 i).le
        _ = C i := mul_one _
    calc |bs.repr ⟨X, hX.1⟩ i| * s i ≤ C i * s i := mul_le_mul_of_nonneg_right hrep (hs0 i).le
      _ ≤ K := Finset.single_le_sum (f := fun j => C j * s j)
          (fun j _ => mul_nonneg (hC0 j).le (hs0 j).le) (Finset.mem_univ i)

open Classical in

def cst {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0

theorem cst_spec {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖B.dLR u v F g‖ ≤ cst hF u v := by
  unfold cst
  rw [dif_pos ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg

def termT {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cst hF (β.take a) (β.drop a)) 0)

theorem smooth_class_in_finite_order : C2.SmoothClassInFiniteOrder := by
  intro k r E _ _ A F hF m
  obtain ⟨N, e, c, K, hK, he, hc, hcK⟩ := basis_exists k r
  have hF0 : SS k r F := hF.1
  have hT : ∀ a b, 0 ≤ termT e K hF a b := fun a b =>
    mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)
  unfold B.InCC B.CCle
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termT e K hF a b, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hg₀U, hf', hfe⟩ := hF0 g₀ hg₀
    exact ⟨U, f', hU, hg₀U, hf'.of_le (by exact_mod_cast le_top), hfe⟩
  · intro u v hu hv hlen g hg
    have h1 := one_le_gN hg
    have hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K := by
      intro X hX
      rcases List.mem_append.1 hX with h | h
      · exact ⟨(hu X h).1, hcK X (hu X h)⟩
      · exact ⟨(hv X h).1, hcK X (hv X h)⟩
    have hexp := expand e c hK (fun i => (he i).1) hc
      (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) (by simp) hxs id good_id F hF0 g hg
    simp only [id] at hexp
    rw [← dLR_eq_ev, List.length_append] at hexp
    have hw : B.gN g ^ (A - C2.B0 r * (m : ℝ)) ≤ B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) := by
      apply Real.rpow_le_rpow_of_exponent_le h1
      have hB : 0 ≤ C2.B0 r := by unfold C2.B0; positivity
      have : ((u.length : ℝ) + v.length) ≤ m := by exact_mod_cast hlen
      nlinarith
    have hgN0 : 0 ≤ B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) :=
      Real.rpow_nonneg (le_trans zero_le_one h1) _
    calc B.gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖B.dLR u v F g‖
        ≤ B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖B.dLR u v F g‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ ≤ B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) *
          (K ^ (u.length + v.length) * bsum e (List.replicate u.length true ++ List.replicate v.length false)
            (fun β => ‖ev (List.replicate u.length true ++ List.replicate v.length false) β F g‖)) :=
          mul_le_mul_of_nonneg_left hexp hgN0
      _ = K ^ (u.length + v.length) * bsum e (List.replicate u.length true ++ List.replicate v.length false)
            (fun β => B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) *
              ‖ev (List.replicate u.length true ++ List.replicate v.length false) β F g‖) := by
          rw [bsum_mul]; ring
      _ ≤ termT e K hF u.length v.length := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK _)
          apply bsum_mono
          intro β hβlen hβe
          have hl : β.length = u.length + v.length := by simpa using hβlen
          have hsplit : ev (List.replicate u.length true ++ List.replicate v.length false) β F =
              B.dLR (β.take u.length) (β.drop u.length) F := by
            rw [dLR_eq_ev, List.take_append_drop, List.length_take, List.length_drop,
              min_eq_left (by omega), show β.length - u.length = v.length by omega]
          rw [hsplit]
          have hunit : ∀ X ∈ β, B.unitLie k r X := fun X hX => by
            obtain ⟨i, rfl⟩ := hβe X hX
            exact he i
          refine le_trans ?_ (le_max_left _ _)
          have := cst_spec hF (β.take u.length) (β.drop u.length)
            (fun X hX => hunit X (List.mem_of_mem_take hX)) (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg
          rwa [List.length_take, List.length_drop, min_eq_left (by omega),
            show β.length - u.length = v.length by omega] at this
      _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termT e K hF a b := by
          refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), termT e K hF a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hT a b) (Finset.mem_range.2 (show u.length < m + 1 by omega)))
          exact Finset.single_le_sum (f := fun b => termT e K hF u.length b) (fun b _ => hT _ b)
            (Finset.mem_range.2 (show v.length < m + 1 by omega))

end PI.ComplexConjugateDerivative
