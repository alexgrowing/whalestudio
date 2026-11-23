import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListSumSplittings

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftToRightConversion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma inv_eq_iota {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hgU : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hgU, hpk_sq']

lemma cv_LR {X g : Mat k r} (hg : g ∈ GV k r) (t : ℝ) :
    cv true X t g = cv false (-(g⁻¹ * X * g)) t g := by
  have hdu := WeylGroupFacts.isUnit_of_uh hg
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdu
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdu
  have hc : g * (g⁻¹ * X * g) * g⁻¹ = X := by
    simp only [Matrix.mul_assoc, hgi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
  have e : g * ((t : ℂ) • -(g⁻¹ * X * g)) * g⁻¹ = -((t : ℂ) • X) := by
    rw [smul_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hc]
  show NormedSpace.exp (-((t : ℂ) • X)) * g = g * NormedSpace.exp ((t : ℂ) • -(g⁻¹ * X * g))
  rw [← e, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdu, Matrix.mul_one]

def cT (i : J k r) (X : Mat k r) (g : Mat k r) : ℂ := ((kc i (-(Hpk k r * gᴴ * Hpk k r * X * g)) : ℝ) : ℂ)

lemma L_to_R {H : Mat k r → E} {X g : Mat k r} (hX : inLie k r X) (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H)
    (hg : g ∈ GV k r) : op true X H g = ∑ i, cT i X g • op false (Lt i) H g := by
  have hY : inLie k r (-(g⁻¹ * X * g)) := inLie_neg (inLie_conj hg hX)
  have e1 : op true X H g = op false (-(g⁻¹ * X * g)) H g := by
    unfold op; congr 1; funext t; rw [cv_LR hg t]
  rw [e1, op_expand false hY hH hg, inv_eq_iota hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

lemma kc_add (i : J k r) (Z Z' : Mat k r) : kc i (Z + Z') = kc i Z + kc i Z' := by
  unfold kc; rw [co_add]; ring

lemma kc_smul (i : J k r) (c : ℝ) (Z : Mat k r) : kc i (c • Z) = c * kc i Z := by
  unfold kc; rw [co_smul]; ring

def coL (j : J k r) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := ((co g j : ℝ) : ℂ)
  map_add' x y := by rw [co_add]; push_cast; rfl
  map_smul' c x := by rw [co_smul]; simp [Complex.real_smul]

def qL (i : J k r) (X : Mat k r) (j : J k r) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := ((kc i (-(Hpk k r * gᴴ * Hpk k r * X * Eb j)) : ℝ) : ℂ)
  map_add' x y := by
    rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, neg_add, kc_add]
    exact Complex.ofReal_add _ _
  map_smul' c x := by
    have e : Hpk k r * (c • x)ᴴ * Hpk k r * X * Eb j = c • (Hpk k r * xᴴ * Hpk k r * X * Eb j) := by
      rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e, ← smul_neg, kc_smul]
    simp [Complex.real_smul]

lemma cT_eq (i : J k r) (X g : Mat k r) : cT i X g = ∑ j, coL j g * qL i X j g := by
  have hs : -(Hpk k r * gᴴ * Hpk k r * X * g) = ∑ j, co g j • (-(Hpk k r * gᴴ * Hpk k r * X * Eb j)) := by
    have h1 : Hpk k r * gᴴ * Hpk k r * X * g = Hpk k r * gᴴ * Hpk k r * X * Mv (co g) := by rw [Mv_co]
    rw [h1, Mv_sum, Matrix.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, smul_neg]
  unfold cT
  rw [hs, kc_sum]
  push_cast
  rfl

lemma polyClass_cT (i : J k r) (X : Mat k r) : PolyClass 2 (cT i X) := by
  have e : cT i X = fun g => ∑ j, coL j g * qL i X j g := funext (cT_eq i X)
  rw [e]
  exact polyClass_sum _ _ _ fun j _ => polyClass_mul (polyClass_lin (coL j)) (polyClass_lin (qL i X j))

theorem LtoR : ∀ u : List (Mat k r), (∀ X ∈ u, inLie k r X) →
    ∃ L : List ((Mat k r → ℂ) × List (Mat k r)),
      (∀ p ∈ L, PolyClass (2 * u.length) p.1 ∧ p.2.length ≤ u.length ∧ ∀ Y ∈ p.2, unitLie k r Y) ∧
      ∀ H : Mat k r → E, CkOn ((u.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
        u.foldr LdV H g = (L.map fun p => p.1 g • Rw p.2 H g).sum := by
  intro u
  induction u with
  | nil =>
    intro _
    refine ⟨[(fun _ => 1, [])], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨polyClass_const 1, le_rfl, by simp⟩
    · intro H _ g _
      simp [Rw]
  | cons Y u ih =>
    intro hu
    have hY : inLie k r Y := hu Y List.mem_cons_self
    obtain ⟨L', hL'1, hL'2⟩ := ih fun X hX => hu X (List.mem_cons_of_mem _ hX)
    refine ⟨L'.flatMap fun p => (op true Y p.1, p.2) ::
      ((Finset.univ.toList : List (J k r)).map fun i => ((fun g => p.1 g * cT i Y g), Lt i :: p.2)), ?_, ?_⟩
    · intro q hq
      rw [List.mem_flatMap] at hq
      obtain ⟨p, hp, hq⟩ := hq
      obtain ⟨hp1, hp2, hp3⟩ := hL'1 p hp
      rcases List.mem_cons.1 hq with h | h
      · subst h
        refine ⟨polyClass_mono (by rw [List.length_cons]; omega) (polyClass_op hp1 true hY),
          by show p.2.length ≤ (Y :: u).length; rw [List.length_cons]; omega, hp3⟩
      · rw [List.mem_map] at h
        obtain ⟨i, -, rfl⟩ := h
        refine ⟨?_, by show (Lt i :: p.2).length ≤ (Y :: u).length; rw [List.length_cons, List.length_cons]; omega, ?_⟩
        · have := polyClass_mul hp1 (polyClass_cT i Y)
          rwa [show 2 * u.length + 2 = 2 * (Y :: u).length by rw [List.length_cons]; ring] at this
        · intro Z hZ
          rcases List.mem_cons.1 hZ with h | h
          · rw [h]; exact Lt_unit i
          · exact hp3 Z h
    · intro H hH g hg
      have hH' : CkOn ((u.length : ℕ) : ℕ∞) (GV k r) H := ckOn_mono (by simp) hH
      have hC1 : ∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.1 := fun p hp => ckOn_top_nat (hL'1 p hp).1.1 1
      have hC2 : ∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Rw p.2 H) := by
        intro p hp
        obtain ⟨-, hp2, hp3⟩ := hL'1 p hp
        rw [right_word_eq_word]
        exact smooth_on_of_word_derivatives _ (allLie_lr' (by simp) fun X hX => (hp3 X hX).1) 1
          (ckOn_mono (by simp [length_lr]; omega) hH)
      show op true Y (u.foldr LdV H) g = _
      rw [op_congr true hY (hL'2 H hH') g hg]
      rw [op_listSumF hY (fun p g' => p.1 g' • Rw p.2 H g') L'
        (fun p hp => ckOn_mulF (f := p.1) (H := Rw p.2 H) (hC1 p hp) (hC2 p hp)) g hg]
      rw [list_sum_flatMap]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      rw [op_smulF true hY (hC1 p hp) (hC2 p hp) hg, L_to_R hY (hC2 p hp) hg]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      congr 1
      rw [Finset.sum_map_toList, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      rfl

lemma tw_word {A c : ℝ} {m : ℕ} {F : Mat k r → E} (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F)
    (hR : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ GV k r, gN g ^ A * ‖Rw v F g‖ ≤ c)
    (u v : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, unitLie k r X)
    (hl : u.length + v.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GV k r, gN g ^ (A - 2 * (m : ℝ)) * ‖dLR u v F g‖ ≤ C := by
  obtain ⟨L, hL1, hL2⟩ := LtoR (E := E) u hu
  have hH : CkOn ((u.length : ℕ) : ℕ∞) (GV k r) (Rw v F) := by
    rw [right_word_eq_word]
    exact smooth_on_of_word_derivatives _ (allLie_lr' (by simp) fun X hX => (hv X hX).1) _
      (ckOn_mono (by simp [length_lr]; omega) hF)
  have hexC : ∀ p : (Mat k r → ℂ) × List (Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (PolyClass (2 * u.length) p.1 → ∀ g ∈ GV k r, ‖p.1 g‖ ≤ C * gN g ^ (2 * u.length)) := by
    intro p
    by_cases hp : PolyClass (2 * u.length) p.1
    · obtain ⟨C, h0, h⟩ := hp.2 [] (by simp [AllLie])
      exact ⟨C, h0, fun _ g hg => by simpa [W_nil] using h g hg⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose CP hCP0 hCP using hexC
  refine ⟨(L.map fun p => CP p * max c 0).sum,
    list_sum_nonneg _ _ fun p _ => mul_nonneg (hCP0 p) (le_max_right _ _), fun g hg => ?_⟩
  have e : dLR u v F g = (L.map fun p => p.1 g • Rw (p.2 ++ v) F g).sum := by
    rw [show dLR u v F = u.foldr LdV (Rw v F) from rfl, hL2 (Rw v F) hH g hg]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Rw, List.foldr_append]
  rw [e]
  have hgp := gN_pos hg
  have hq : 0 ≤ gN g ^ (A - 2 * (m : ℝ)) := gN_rpow_nonneg g _
  calc gN g ^ (A - 2 * (m : ℝ)) * ‖(L.map fun p => p.1 g • Rw (p.2 ++ v) F g).sum‖
      ≤ gN g ^ (A - 2 * (m : ℝ)) * (L.map fun p => ‖p.1 g • Rw (p.2 ++ v) F g‖).sum :=
        mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hq
    _ = (L.map fun p => gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 g • Rw (p.2 ++ v) F g‖).sum :=
        (list_sum_mul_left _ _ _).symm
    _ ≤ (L.map fun p => CP p * max c 0).sum := by
        refine list_sum_le _ _ _ fun p hp => ?_
        obtain ⟨hpP, hpl, hpu⟩ := hL1 p hp
        have hunit : ∀ X ∈ p.2 ++ v, unitLie k r X := by
          intro X hX
          rcases List.mem_append.1 hX with h | h
          · exact hpu X h
          · exact hv X h
        have hlen : (p.2 ++ v).length ≤ m := by simp; omega
        have hRw := (hR (p.2 ++ v) hunit hlen g hg).trans (le_max_left c 0)
        have hP := hCP p hpP g hg
        have hpow : gN g ^ (A - 2 * (m : ℝ)) * gN g ^ (2 * u.length) ≤ gN g ^ A := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hgp]
          apply rpow_mono_G hg
          have : ((2 * u.length : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
            have h2 : 2 * u.length ≤ 2 * m := by omega
            exact_mod_cast h2
          linarith
        have hnR := norm_nonneg (Rw (p.2 ++ v) F g)
        have hpw : 0 ≤ gN g ^ (2 * u.length) := pow_nonneg hgp.le _
        rw [norm_smul]
        calc gN g ^ (A - 2 * (m : ℝ)) * (‖p.1 g‖ * ‖Rw (p.2 ++ v) F g‖)
            ≤ gN g ^ (A - 2 * (m : ℝ)) * ((CP p * gN g ^ (2 * u.length)) * ‖Rw (p.2 ++ v) F g‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP hnR) hq
          _ = CP p * ((gN g ^ (A - 2 * (m : ℝ)) * gN g ^ (2 * u.length)) * ‖Rw (p.2 ++ v) F g‖) := by ring
          _ ≤ CP p * (gN g ^ A * ‖Rw (p.2 ++ v) F g‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hnR) (hCP0 p)
          _ ≤ CP p * max c 0 := mul_le_mul_of_nonneg_left hRw (hCP0 p)

theorem twoSided : C2.TwoSided := by
  intro k r E _ _ A m F c hF hR
  have hex : ∀ w' : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧ (LRt (w'.map Prod.fst) →
      (∀ y ∈ w', unitLie k r y.2) → w'.length ≤ m →
      ∀ g ∈ GV k r, gN g ^ (A - 2 * (m : ℝ)) * ‖W w' F g‖ ≤ C) := by
    intro w'
    by_cases h : LRt (w'.map Prod.fst) ∧ (∀ y ∈ w', unitLie k r y.2) ∧ w'.length ≤ m
    · obtain ⟨a, b, hab⟩ := h.1
      obtain ⟨u, v, -, rfl⟩ := of_tags w' a b hab
      have hu : ∀ X ∈ u, unitLie k r X := fun X hX =>
        h.2.1 (true, X) (by simp only [lr, List.mem_append, List.mem_map]; exact Or.inl ⟨X, hX, rfl⟩)
      have hv : ∀ X ∈ v, unitLie k r X := fun X hX =>
        h.2.1 (false, X) (by simp only [lr, List.mem_append, List.mem_map]; exact Or.inr ⟨X, hX, rfl⟩)
      obtain ⟨C, hC0, hC⟩ := tw_word hF hR u v (fun X hX => (hu X hX).1) hv
        (by rw [← length_lr]; exact h.2.2)
      exact ⟨C, hC0, fun _ _ _ g hg => by rw [← dLR_eq]; exact hC g hg⟩
    · exact ⟨0, le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Cw hCw0 hCw using hex
  set K := Kc k r with hK
  have hK1 : 1 ≤ K := one_le_Kc
  let pat : ℕ → ℕ → List Bool := fun a b => List.replicate a true ++ List.replicate b false
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    K ^ (a + b) * ((bw (k := k) (r := r) (pat a b)).map Cw).sum, hF, ?_⟩
  intro u v hu hv hl g hg
  set w := lr u v with hwdef
  set n := u.length + v.length with hn
  have hwl : w.length = n := length_lr u v
  have hwu : ∀ y ∈ w, unitLie k r y.2 := by
    intro y hy
    simp only [hwdef, lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  have hwL : AllLie w := fun y hy => (hwu y hy).1
  have hexp := W_expand w hwL F (ckOn_mono (by rw [hwl]; exact hl) hF) g hg
  rw [dLR_eq, hexp]
  have hgp : 0 ≤ gN g ^ (A - 2 * (m : ℝ)) := gN_rpow_nonneg g _
  have hterm : ∀ p ∈ expW w, gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 • W p.2 F g‖ ≤ K ^ n * Cw p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := expW_mem w p hp
    have hc := expW_coef w hwu p hp
    rw [hwl] at hc
    have htag : LRt (p.2.map Prod.fst) := by
      have e := expW_snd w
      have : p.2 ∈ bw (w.map Prod.fst) := by rw [← e]; exact List.mem_map_of_mem hp
      refine ⟨u.length, v.length, ?_⟩
      rw [hwdef, lr_tags] at this
      exact bw_tags _ _ this
    have hb := hCw p.2 htag h2 (by rw [h1, hwl]; exact hl) g hg
    rw [norm_smul, Real.norm_eq_abs]
    calc gN g ^ (A - 2 * (m : ℝ)) * (|p.1| * ‖W p.2 F g‖)
        = |p.1| * (gN g ^ (A - 2 * (m : ℝ)) * ‖W p.2 F g‖) := by ring
      _ ≤ K ^ n * Cw p.2 :=
          mul_le_mul hc hb (mul_nonneg hgp (norm_nonneg _)) (pow_nonneg (by linarith) _)
  calc gN g ^ (A - 2 * (m : ℝ)) * ‖((expW w).map fun p => p.1 • W p.2 F g).sum‖
      ≤ gN g ^ (A - 2 * (m : ℝ)) * ((expW w).map fun p => ‖p.1 • W p.2 F g‖).sum :=
        mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hgp
    _ = ((expW w).map fun p => gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 • W p.2 F g‖).sum :=
        (list_sum_mul_left _ _ _).symm
    _ ≤ ((expW w).map fun p => K ^ n * Cw p.2).sum := list_sum_le _ _ _ hterm
    _ = K ^ n * ((bw (pat u.length v.length)).map Cw).sum := by
        rw [list_sum_mul_left]
        congr 1
        have e := expW_snd w
        rw [hwdef, lr_tags] at e
        rw [← e, List.map_map]
        rfl
    _ ≤ ∑ b ∈ Finset.range (m + 1), K ^ (u.length + b) * ((bw (pat u.length b)).map Cw).sum := by
        refine Finset.single_le_sum (f := fun b => K ^ (u.length + b) * ((bw (pat u.length b)).map Cw).sum)
          (fun b _ => mul_nonneg (pow_nonneg (by linarith) _)
            (list_sum_nonneg _ _ fun w' _ => hCw0 w')) (Finset.mem_range.2 (by omega))
    _ ≤ _ := by
        refine Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1),
            K ^ (a + b) * ((bw (pat a b)).map Cw).sum)
          (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (pow_nonneg (by linarith) _)
            (list_sum_nonneg _ _ fun w' _ => hCw0 w')) (Finset.mem_range.2 (by omega))

end Formalism.FourierDecayAlt.P.LeftToRightConversion

namespace Formalism.FourierDecayAlt.P

theorem two_sided_derivative_rule : C2.TwoSided := LeftToRightConversion.twoSided

end Formalism.FourierDecayAlt.P
