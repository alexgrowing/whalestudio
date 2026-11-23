import Mathlib

open MvPolynomial

namespace GlobalTheory
namespace UnramifiedHensel

theorem exists_relation_gradient {R A k ι : Type} [CommRing R] [CommRing A] [Field k]
    [Fintype ι] [DecidableEq ι] (ev : MvPolynomial ι R →+* A) (hev : Function.Surjective ev)
    (red : A →+* k) (hred : ∀ c : k, ∃ w : R, red (ev (C w)) = c)
    (h : ∀ φ : A →+* DualNumber k, (∀ a, (φ a).fst = red a) → (∀ w, (φ (ev (C w))).snd = 0) →
      ∀ i, (φ (ev (X i))).snd = 0) (i : ι) :
    ∃ G : MvPolynomial ι R, ev G = 0 ∧
      ∀ j, red (ev (pderiv j G)) = if j = i then 1 else 0 := by
  let Γ : Submodule k (ι → k) :=
    { carrier := {γ | ∃ G : MvPolynomial ι R, ev G = 0 ∧ ∀ j, red (ev (pderiv j G)) = γ j}
      add_mem' := by
        rintro a b ⟨G, hG, ha⟩ ⟨H, hH, hb⟩
        exact ⟨G + H, by simp [hG, hH], fun j => by simp [ha, hb]⟩
      zero_mem' := ⟨0, by simp, fun j => by simp⟩
      smul_mem' := by
        rintro c a ⟨G, hG, ha⟩
        obtain ⟨w, hw⟩ := hred c
        refine ⟨C w * G, by simp [hG], fun j => ?_⟩
        rw [pderiv_C_mul]
        simp [ha, hw] }
  suffices hΓ : Γ = ⊤ by
    have : (fun j => if j = i then (1 : k) else 0) ∈ Γ := by rw [hΓ]; trivial
    exact this
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  let v : ι → k := fun j => f (Pi.single j 1)
  have hfv : ∀ γ : ι → k, f γ = ∑ j, γ j * v j := by
    intro γ
    conv_lhs => rw [pi_eq_sum_univ' γ]
    simp [v, map_sum]
  let ψ : MvPolynomial ι R →+* DualNumber k :=
    eval₂Hom ((TrivSqZeroExt.inlHom k k).comp (red.comp (ev.comp C)))
      (fun j => (TrivSqZeroExt.inl (red (ev (X j))) + TrivSqZeroExt.inr (v j) : DualNumber k))
  have hψ : ∀ F, (ψ F).fst = red (ev F) ∧
      (ψ F).snd = ∑ j, red (ev (pderiv j F)) * v j := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp [hp.1, hp.2, hq.1, hq.2, add_mul, Finset.sum_add_distrib]
    | mul_X p n hp =>
      have h1 : (ψ (X n)).fst = red (ev (X n)) := by simp [ψ]
      have h2 : (ψ (X n)).snd = v n := by simp [ψ]
      refine ⟨by simp [hp.1, h1], ?_⟩
      rw [map_mul, DualNumber.snd_mul, hp.1, hp.2, h1, h2]
      have : ∀ j, red (ev (pderiv j (p * X n))) * v j =
          red (ev (pderiv j p)) * v j * red (ev (X n)) +
            (if j = n then red (ev p) * v n else 0) := by
        intro j
        rw [pderiv_mul, pderiv_X]
        by_cases hj : j = n
        · subst hj; simp; ring
        · simp [hj, Pi.single_apply, Ne.symm hj]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_mul]
      simp [add_comm]
  have hker : RingHom.ker ev ≤ RingHom.ker ψ := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    ext
    · simp [(hψ F).1, hF]
    · rw [(hψ F).2, ← hfv (fun j => red (ev (pderiv j F)))]
      have : f (fun j => red (ev (pderiv j F))) ∈ Γ.map f :=
        Submodule.mem_map_of_mem ⟨F, hF, fun _ => rfl⟩
      rw [hf] at this
      simpa using this
  let φ : A →+* DualNumber k := ev.liftOfSurjective hev ⟨ψ, hker⟩
  have hφ : ∀ F, φ (ev F) = ψ F := fun F => RingHom.liftOfSurjective_comp_apply _ _ _ F
  have hv := h φ (fun a => by obtain ⟨F, rfl⟩ := hev a; rw [hφ, (hψ F).1])
    (fun w => by rw [hφ, (hψ _).2]; simp)
  apply hf0
  ext j
  have := hv j
  rw [hφ] at this
  have h2 : (ψ (X j)).snd = v j := by simp [ψ]
  simpa [v, h2] using this

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]

theorem norm_eval_le_one (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (G : MvPolynomial ι R) : ‖eval₂ c x G‖ ≤ 1 := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq =>
    rw [eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    rw [eval₂_mul, eval₂_X, norm_mul]
    exact mul_le_one₀ hp (norm_nonneg _) (hx n)

theorem norm_sum_le_of_le [Fintype ι] (a : ι → K) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, ‖a i‖ ≤ r) :
    ‖∑ i, a i‖ ≤ r :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr (fun i _ => ha i)

theorem taylor_bound [Fintype ι] [DecidableEq ι] (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1)
    (x y : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hxy : ∀ i, ‖y i - x i‖ ≤ r) (G : MvPolynomial ι R) :
    ‖eval₂ c y G - eval₂ c x G - ∑ j, eval₂ c x (pderiv j G) * (y j - x j)‖ ≤ r * r := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using mul_nonneg hr hr
  | add p q hp hq =>
    have : eval₂ c y (p + q) - eval₂ c x (p + q) -
        ∑ j, eval₂ c x (pderiv j (p + q)) * (y j - x j) =
        (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (eval₂ c y q - eval₂ c x q - ∑ j, eval₂ c x (pderiv j q) * (y j - x j)) := by
      simp only [map_add, eval₂_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    have h1 : ∀ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        eval₂ c x (pderiv j p) * (y j - x j) * x n +
          (if j = n then eval₂ c x p * (y n - x n) else 0) := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hj : j = n
      · subst hj; simp [eval₂_mul]; ring
      · simp [hj, Pi.single_apply, Ne.symm hj, eval₂_mul]; ring
    have hL : ‖∑ j, eval₂ c x (pderiv j p) * (y j - x j)‖ ≤ r := by
      refine norm_sum_le_of_le _ hr fun j => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_eval_le_one c hc x hx _)).trans (hxy j)
    have : eval₂ c y (p * X n) - eval₂ c x (p * X n) -
        ∑ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        y n * (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (y n - x n) * ∑ j, eval₂ c x (pderiv j p) * (y j - x j) := by
      simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul, eval₂_mul, eval₂_X]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hy n)).trans hp
    · rw [norm_mul]
      exact mul_le_mul (hxy n) hL (norm_nonneg _) hr

theorem mem_of_gradient [Fintype ι] [DecidableEq ι] (W : Subring K) (hW : IsClosed (W : Set K))
    (hc : ∀ w ∈ W, ‖w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (h0 : ∀ i, ∃ w ∈ W, ‖x i - w‖ < 1) (G : ι → MvPolynomial ι W)
    (hG : ∀ i, eval₂ W.subtype x (G i) = 0)
    (hd : ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ < 1) (i : ι) :
    x i ∈ W := by
  have hc' : ∀ w : W, ‖W.subtype w‖ ≤ 1 := fun w => hc w w.2
  choose y0 hy0W hy0 using h0
  obtain ⟨ρ, hρ0, hρ1, hρy, hρd⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (∀ i, ‖y0 i - x i‖ ≤ ρ) ∧
      ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ ≤ ρ := by
    refine ⟨max ‖fun i => y0 i - x i‖
      ‖fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖,
      le_max_of_le_left (norm_nonneg _), max_lt ?_ ?_, fun i => le_max_of_le_left ?_,
      fun i j => le_max_of_le_right ?_⟩
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [norm_sub_rev]; exact hy0 i
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [pi_norm_lt_iff one_pos]; exact hd i
    · exact norm_le_pi_norm (fun i => y0 i - x i) i
    · exact (norm_le_pi_norm
        (fun j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) j).trans
        (norm_le_pi_norm
        (fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) i)
  have key : ∀ n : ℕ, ∃ y : ι → W, ∀ i, ‖(y i : K) - x i‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨fun i => ⟨y0 i, hy0W i⟩, fun i => by simpa using hρy i⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨fun i => y i - eval y (G i), fun i => ?_⟩
      have hr : 0 ≤ ρ ^ (n + 1) := pow_nonneg hρ0 _
      have hT := taylor_bound W.subtype hc' x (fun i => (y i : K)) hx (fun i => hc' (y i)) hr hy
        (G i)
      have he : ((eval y (G i) : W) : K) = eval₂ W.subtype (fun i => (y i : K)) (G i) := by
        have := eval₂_comp_left W.subtype (RingHom.id W) y (G i)
        simpa [Function.comp_def] using this
      have : ((y i - eval y (G i) : W) : K) - x i =
          ∑ j, ((if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) * (y j - x j) +
          -(eval₂ W.subtype (fun i => (y i : K)) (G i) - eval₂ W.subtype x (G i) -
            ∑ j, eval₂ W.subtype x (pderiv j (G i)) * (y j - x j)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, hG, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        push_cast
        rw [he]; ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine norm_sum_le_of_le _ (pow_nonneg hρ0 _) fun j => ?_
        rw [norm_mul, pow_succ' ρ (n + 1)]
        exact mul_le_mul (hρd i j) (hy j) (norm_nonneg _) hρ0
      · rw [norm_neg, pow_succ ρ (n + 1)]
        refine hT.trans (mul_le_mul_of_nonneg_left ?_ hr)
        rw [pow_succ]
        exact mul_le_of_le_one_left hρ0 (pow_le_one₀ hρ0 hρ1.le)
  have : x i ∈ closure (W : Set K) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
    obtain ⟨y, hy⟩ := key n
    refine ⟨y i, (y i).2, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine (hy i).trans_lt (lt_of_le_of_lt ?_ hn)
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hρ0 _) hρ1.le
  rwa [hW.closure_eq] at this

end

theorem subset_of_unramified (K : Type) [NormedField K] [IsUltrametricDist K] (W : Subring K)
    (hW : IsClosed (W : Set K)) (hc : ∀ w ∈ W, ‖w‖ ≤ 1)
    (hres : ∀ x : K, ‖x‖ ≤ 1 → ∃ w ∈ W, ‖x - w‖ < 1) (s : Set K) (hs : s.Finite)
    (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (h : ∀ (k : Type) [Field k] (φ : Subring.closure ((W : Set K) ∪ s) →+* DualNumber k),
      (∀ a : Subring.closure ((W : Set K) ∪ s), ‖(a : K)‖ = 1 → (φ a).fst ≠ 0) →
      (∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ W → (φ a).snd = 0) →
      ∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ s → (φ a).snd = 0) :
    s ⊆ (W : Set K) := by
  classical
  haveI : Fintype s := hs.fintype
  let A := Subring.closure ((W : Set K) ∪ s)
  let O := (NormedField.valuation (K := K)).valuationSubring
  have hO : ∀ z : K, z ∈ O ↔ ‖z‖ ≤ 1 := by
    intro z
    simp only [O, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  have hm : ∀ z : O, IsLocalRing.residue O z = 0 ↔ ‖(z : K)‖ < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact Iff.rfl
  have hAO : A ≤ O.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro z (hz | hz)
    · exact (hO z).2 (hc z hz)
    · exact (hO z).2 (hs1 z hz)
  have hWA : W ≤ A := fun z hz => Subring.subset_closure (Or.inl hz)
  let x : s → A := fun i => ⟨i, Subring.subset_closure (Or.inr i.2)⟩
  let ev : MvPolynomial s W →+* A := eval₂Hom (Subring.inclusion hWA) x
  have hevK : ∀ F, ((ev F : A) : K) = eval₂ W.subtype (fun i : s => (i : K)) F := by
    intro F
    have := eval₂_comp_left A.subtype (Subring.inclusion hWA) x F
    exact this
  have hev : Function.Surjective ev := by
    rintro ⟨a, ha⟩
    have : a ∈ (A.subtype.comp ev).range := by
      refine (Subring.closure_le (t := (A.subtype.comp ev).range)).2 ?_ ha
      rintro z (hz | hz)
      · exact ⟨C ⟨z, hz⟩, by simp [ev]⟩
      · exact ⟨X ⟨z, hz⟩, by simp [ev, x]⟩
    obtain ⟨F, hF⟩ := this
    exact ⟨F, Subtype.ext hF⟩
  let inc : A →+* O := Subring.inclusion hAO
  let red : A →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp inc
  have hred0 : ∀ a : A, red a = 0 ↔ ‖(a : K)‖ < 1 := fun a => hm (inc a)
  have hred : ∀ c, ∃ w : W, red (ev (C w)) = c := by
    intro c
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨w, hw, hzw⟩ := hres z ((hO _).1 z.2)
    refine ⟨⟨w, hw⟩, ?_⟩
    symm
    rw [← sub_eq_zero]
    have : IsLocalRing.residue O (z - inc (ev (C ⟨w, hw⟩))) = 0 := by
      rw [hm]
      have : ((inc (ev (C ⟨w, hw⟩)) : O) : K) = w := by
        change ((ev (C ⟨w, hw⟩) : A) : K) = w
        rw [hevK]; simp
      push_cast
      rwa [this]
    rwa [map_sub] at this
  have hG := exists_relation_gradient ev hev red hred (fun φ h1 h2 i => by
    refine h _ φ (fun a ha => ?_) (fun a ha => ?_) _ ?_
    · rw [h1, Ne, hred0, ha]; exact lt_irrefl _
    · have : a = ev (C ⟨a, ha⟩) := Subtype.ext (by rw [hevK]; simp)
      rw [this]; exact h2 _
    · rw [hevK]; simp)
  choose G hG0 hG1 using hG
  intro z hz
  refine mem_of_gradient W hW hc (fun i : s => (i : K)) (fun i => hs1 i i.2)
    (fun i => hres i (hs1 i i.2)) G (fun i => ?_) (fun i j => ?_) ⟨z, hz⟩
  · rw [← hevK, hG0]; rfl
  · have : red ((if j = i then 1 else 0) - ev (pderiv j (G i))) = 0 := by
      rw [map_sub, hG1]; split_ifs <;> simp
    rw [hred0] at this
    rw [← hevK]
    convert this using 2
    split_ifs <;> simp

end UnramifiedHensel
end GlobalTheory
