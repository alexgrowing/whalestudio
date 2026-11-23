import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma tags_map (φ : Bool × Mat k r → Bool × Mat k r) :
    ∀ l : List (Bool × Mat k r), (∀ y ∈ l, (φ y).1 = y.1) → (l.map φ).map Prod.fst = l.map Prod.fst := by
  intro l hl
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hl y (List.mem_cons_self ..), ih fun z hz => hl z (List.mem_cons_of_mem _ hz)⟩

lemma tele {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ ψ : Bool × Mat k r → Bool × Mat k r) :
    ∀ (w pre : List (Bool × Mat k r)), (∀ x ∈ pre, inLie k r x.2 ∧ ‖x.2‖ ≤ K) →
      (∀ x ∈ w, (φ x).1 = x.1 ∧ (ψ x).1 = x.1 ∧ inLie k r (φ x).2 ∧ inLie k r (ψ x).2 ∧
        ‖(φ x).2‖ ≤ K ∧ ‖(ψ x).2‖ ≤ K ∧ ‖(φ x).2 - (ψ x).2‖ ≤ ε) →
      LRt ((pre ++ w).map Prod.fst) → (pre ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (pre ++ w.map φ) F g - W (pre ++ w.map ψ) F g‖ ≤ w.length * (K ^ m * ε * c) := by
  have hCk : ∀ n : ℕ, n ≤ m → CkOn (n : ℕ∞) (GV k r) F := by
    intro n hn g₀ hg₀
    obtain ⟨U, f', hU, hg, hcd, hfe⟩ := h.1 g₀ hg₀
    exact ⟨U, f', hU, hg, hcd.of_le (by exact_mod_cast hn), hfe⟩
  have hsubL : ∀ X Y : Mat k r, inLie k r X → inLie k r Y → inLie k r (X - Y) := by
    intro X Y hX hY
    unfold inLie at hX hY ⊢
    rw [Matrix.conjTranspose_sub, sub_mul, mul_sub]
    calc Xᴴ * Hpk k r - Yᴴ * Hpk k r + (Hpk k r * X - Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) - (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [hX, hY, sub_zero]
  have hpn0 : ∀ l : List (Bool × Mat k r), 0 ≤ pn l := fun l =>
    List.prod_nonneg fun a ha => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; exact norm_nonneg _
  have hpnK : ∀ l : List (Bool × Mat k r), (∀ y ∈ l, ‖y.2‖ ≤ K) → pn l ≤ K ^ l.length := by
    intro l hlK
    induction l with
    | nil => simp [pn]
    | cons y l ih =>
      have h1 := hlK y (List.mem_cons_self ..)
      have h2 := ih fun z hz => hlK z (List.mem_cons_of_mem _ hz)
      have h3 : pn (y :: l) = ‖y.2‖ * pn l := by simp [pn]
      rw [h3, List.length_cons, pow_succ]
      calc ‖y.2‖ * pn l ≤ K * K ^ l.length := mul_le_mul h1 h2 (hpn0 l) (by linarith)
        _ = K ^ l.length * K := mul_comm _ _
  have hgN : ∀ g : Mat k r, 0 ≤ gN g ^ A := fun g => Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) A
  intro w
  induction w with
  | nil =>
    intro pre _ _ _ _ g _
    simp
  | cons x w ih =>
    intro pre hpre hw ht hl g hg
    obtain ⟨hφ1, hψ1, hφL, hψL, hφK, hψK, hε⟩ := hw x (List.mem_cons_self ..)
    have hw' : ∀ y ∈ w, (φ y).1 = y.1 ∧ (ψ y).1 = y.1 ∧ inLie k r (φ y).2 ∧ inLie k r (ψ y).2 ∧
        ‖(φ y).2‖ ≤ K ∧ ‖(ψ y).2‖ ≤ K ∧ ‖(φ y).2 - (ψ y).2‖ ≤ ε :=
      fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hpre' : ∀ y ∈ pre ++ [φ x], inLie k r y.2 ∧ ‖y.2‖ ≤ K := by
      intro y hy
      rcases List.mem_append.mp hy with h' | h'
      · exact hpre y h'
      · rw [List.mem_singleton] at h'; subst h'; exact ⟨hφL, hφK⟩
    have ht' : LRt ((pre ++ [φ x] ++ w).map Prod.fst) := by
      have e : (pre ++ [φ x] ++ w).map Prod.fst = (pre ++ x :: w).map Prod.fst := by simp [hφ1]
      rw [e]; exact ht
    have hl' : (pre ++ [φ x] ++ w).length ≤ m := by simpa using hl
    have ih' := ih (pre ++ [φ x]) hpre' hw' ht' hl' g hg
    have hwψ : (w.map ψ).map Prod.fst = w.map Prod.fst := tags_map ψ w fun y hy => (hw' y hy).2.1
    have hallpre : AllLie pre := fun y hy => (hpre y hy).1
    have hallq : AllLie (w.map ψ) := by
      intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact (hw' z hz).2.2.2.1
    have hlen : pre.length + 1 + w.length ≤ m := by simp at hl; omega
    have hCk' : CkOn ((pre.length + 1 + (w.map ψ).length : ℕ) : ℕ∞) (GV k r) F := by
      rw [List.length_map]; exact hCk _ hlen
    have hDL : inLie k r ((φ x).2 - (ψ x).2) := hsubL _ _ hφL hψL
    have hmid := W_mid_add (F := F) pre (w.map ψ) x.1 hallpre hallq hψL hDL hCk' g hg
    rw [add_sub_cancel] at hmid
    have hφx : φ x = (x.1, (φ x).2) := Prod.ext hφ1 rfl
    have hψx : ψ x = (x.1, (ψ x).2) := Prod.ext hψ1 rfl
    have e1 : pre ++ (x :: w).map φ = pre ++ [φ x] ++ w.map φ := by simp
    have e2 : pre ++ (x :: w).map ψ = pre ++ (x.1, (ψ x).2) :: w.map ψ := by
      rw [List.map_cons, ← hψx]
    have e3 : pre ++ [φ x] ++ w.map ψ = pre ++ (x.1, (φ x).2) :: w.map ψ := by
      rw [List.append_assoc, List.singleton_append, ← hφx]
    have hsplit : W (pre ++ (x :: w).map φ) F g - W (pre ++ (x :: w).map ψ) F g =
        (W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g) +
          W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g := by
      rw [e1, e2, e3, hmid]; abel
    have ht2 : LRt ((pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).map Prod.fst) := by
      have e : (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).map Prod.fst =
          (pre ++ x :: w).map Prod.fst := by
        simp only [List.map_append, List.map_cons, hwψ]
      rw [e]; exact ht
    have hall2 : AllLie (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) := by
      intro y hy
      rcases List.mem_append.mp hy with h' | h'
      · exact hallpre y h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · subst h''; exact hDL
        · exact hallq y h''
    have hl2 : (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).length ≤ m := by simpa using hl
    have hb2 := bound_scaled h _ ht2 hall2 hl2 g hg
    have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
    have hK0 : 0 ≤ K := by linarith
    have hpn2 : pn (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) ≤ K ^ m * ε := by
      have hpre_pn : pn pre ≤ K ^ pre.length := hpnK pre fun y hy => (hpre y hy).2
      have hq_pn : pn (w.map ψ) ≤ K ^ w.length := by
        have h5 := hpnK (w.map ψ) (by
          intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact (hw' z hz).2.2.2.2.2.1)
        simpa using h5
      have e : pn (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) =
          pn pre * (‖(φ x).2 - (ψ x).2‖ * pn (w.map ψ)) := by
        simp [pn, List.map_append, List.prod_append]
      rw [e]
      calc pn pre * (‖(φ x).2 - (ψ x).2‖ * pn (w.map ψ)) ≤ K ^ pre.length * (ε * K ^ w.length) :=
            mul_le_mul hpre_pn (mul_le_mul hε hq_pn (hpn0 _) hε0)
              (mul_nonneg (norm_nonneg _) (hpn0 _)) (pow_nonneg hK0 _)
        _ = K ^ (pre.length + w.length) * ε := by rw [pow_add]; ring
        _ ≤ K ^ m * ε := by
            apply mul_le_mul_of_nonneg_right _ hε0
            exact pow_le_pow_right₀ hK (by omega)
    rw [hsplit]
    have hg0 := hgN g
    calc gN g ^ A * ‖(W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g) +
          W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g‖
        ≤ gN g ^ A * ‖W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g‖ +
          gN g ^ A * ‖W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g‖ := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hg0
      _ ≤ w.length * (K ^ m * ε * c) + K ^ m * ε * c :=
          add_le_add ih' (hb2.trans (by
            have := mul_le_mul_of_nonneg_right hpn2 hc
            linarith))
      _ = ((x :: w).length : ℝ) * (K ^ m * ε * c) := by push_cast [List.length_cons]; ring

section meas

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def adM (p : SS k r) (x : Bool × Mat k r) : Bool × Mat k r := (x.1, cond x.1 (AdL p x.2) (AdR p x.2))

lemma lr_ad (p : SS k r) (u v : List (Mat k r)) :
    lr (u.map (AdL p)) (v.map (AdR p)) = (lr u v).map (adM p) := by
  simp [lr, List.map_append, List.map_map, Function.comp_def, adM]

lemma unit_lr' {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    ∀ x ∈ lr u v, unitLie k r x.2 := by
  intro x hx
  unfold lr at hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

private theorem inLie_conj_of_mem_GV {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

lemma adM_lie {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) {x : Bool × Mat k r} (hx : inLie k r x.2) :
    inLie k r (adM p x).2 := by
  obtain ⟨b, X⟩ := x
  cases b
  · exact inLie_conj_of_mem_GV (JFxDs2.sR_mem hp) hx
  · exact inLie_conj_of_mem_GV (JFxDs2.sL_mem hp) hx

lemma adM_cont (D : RealPlaceData k r Wp Wq) (x : Bool × Mat k r) :
    ContinuousOn (fun p => (adM p x).2) {p : SS k r | D.inSS p} := by
  obtain ⟨b, X⟩ := x
  have hof : ∀ q : SS k r → (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ), Continuous q →
      Continuous fun p => (Matrix.of (q p) : Mat k r) := fun q hq => hq
  have hcL : Continuous fun p : SS k r => sL p := by
    unfold sL; exact (hof _ (by fun_prop)).mul (hof _ (by fun_prop))
  have hcR : Continuous fun p : SS k r => sR p := by
    unfold sR; exact (hof _ (by fun_prop)).mul (hof _ (by fun_prop))
  have hinvOn : ∀ s : SS k r → Mat k r, Continuous s → (∀ p, D.inSS p → s p ∈ GV k r) →
      ContinuousOn (fun p => (s p)⁻¹) {p | D.inSS p} := by
    intro s hs hG p hp
    have hy' : (s p)ᴴ * Hpk k r * s p = Hpk k r := hG p hp
    have hl : (Hpk k r * (s p)ᴴ * Hpk k r) * s p = 1 := by
      simp only [mul_assoc] at hy' ⊢; rw [hy', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
    obtain ⟨u, hu⟩ := Matrix.isUnit_det_of_left_inverse hl
    have hc : ContinuousAt Inv.inv (s p) :=
      continuousAt_matrix_inv _ (by rw [← hu]; exact NormedRing.inverse_continuousAt u)
    exact (hc.comp hs.continuousAt).continuousWithinAt
  cases b
  · show ContinuousOn (fun p => (sR p)⁻¹ * X * sR p) {p | D.inSS p}
    exact ((hinvOn _ hcR fun p hp => JFxDs2.sR_mem hp).mul continuousOn_const).mul hcR.continuousOn
  · show ContinuousOn (fun p => (sL p)⁻¹ * X * sL p) {p | D.inSS p}
    exact ((hinvOn _ hcL fun p hp => JFxDs2.sL_mem hp).mul continuousOn_const).mul hcL.continuousOn

lemma cont_sum {α : Type*} (S : Set (SS k r)) (f : α → SS k r → ℝ) :
    ∀ l : List α, (∀ x ∈ l, ContinuousOn (f x) S) → ContinuousOn (fun p => (l.map (fun x => f x p)).sum) S := by
  intro l hl
  induction l with
  | nil => simpa using continuousOn_const
  | cons y l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hl y (List.mem_cons_self ..)).add (ih fun z hz => hl z (List.mem_cons_of_mem _ hz))

lemma le_sum_map {α : Type*} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (l : List α) {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum := by
  exact List.single_le_sum (fun y hy => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
    exact hf z) _ (List.mem_map_of_mem hx)

theorem bessel_domain_measurable : JFxDs2.JDomMeas := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hF u v hu hv hl g hg
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := cc_nonneg hc
  have hgG : g ∈ GV k r := hg.1
  have hA : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have h2 := lt_of_le_of_lt h1 hThr
    have h3 : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [lt_div_iff₀ h3, zero_mul] at h2
    have : (0 : ℝ) ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
    linarith
  have hwu : ∀ x ∈ lr u v, unitLie k r x.2 := unit_lr' hu hv
  have hwt : LRt ((lr u v).map Prod.fst) := lrt_lr u v
  have hwl : (lr u v).length ≤ m := by rw [length_lr]; exact hl
  have hx : ContinuousOn (fun p => sgs p g) {p : SS k r | D.inSS p} := B6.conjugated_pair_continuous_on D g
  have hxG : ∀ p ∈ {p : SS k r | D.inSS p}, sgs p g ∈ GV k r := fun p hp => B7.sgs_mem D hp hgG
  have hmain : ContinuousOn (fun p => W ((lr u v).map (adM p)) F (sgs p g)) {p : SS k r | D.inSS p} := by
    intro p₀ hp₀
    have hAL : AllLie ((lr u v).map (adM p₀)) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact adM_lie hp₀ (hwu y' hy').1
    have hck : CkOn ((0 : ℕ) : ℕ∞) (GV k r) (W ((lr u v).map (adM p₀)) F) :=
      smooth_on_of_word_derivatives ((lr u v).map (adM p₀)) hAL 0 (ckOn_mono (by simpa using hwl) hc.1)
    have hsec : ContinuousWithinAt (fun p => W ((lr u v).map (adM p₀)) F (sgs p g)) {p : SS k r | D.inSS p} p₀ :=
      ((B6.continuousOn_of_contDiffOn_group hck).comp hx hxG) p₀ hp₀
    let Kf : SS k r → ℝ := fun p => 1 + ((lr u v).map fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖).sum
    let εf : SS k r → ℝ := fun p => ((lr u v).map fun x => ‖(adM p x).2 - (adM p₀ x).2‖).sum
    have hKc : ContinuousOn Kf {p : SS k r | D.inSS p} :=
      continuousOn_const.add (cont_sum _ (fun x p => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (lr u v)
        (fun x _ => (adM_cont D x).norm.add continuousOn_const))
    have hεc : ContinuousOn εf {p : SS k r | D.inSS p} :=
      cont_sum _ (fun x p => ‖(adM p x).2 - (adM p₀ x).2‖) (lr u v)
        (fun x _ => ((adM_cont D x).sub continuousOn_const).norm)
    have hε0 : εf p₀ = 0 := by simp [εf]
    let Bf : SS k r → ℝ := fun p => ((lr u v).length : ℝ) * (Kf p ^ m * εf p * c)
    have hBc : ContinuousWithinAt Bf {p : SS k r | D.inSS p} p₀ :=
      continuousWithinAt_const.mul ((((hKc p₀ hp₀).pow m).mul (hεc p₀ hp₀)).mul continuousWithinAt_const)
    have hB0 : Bf p₀ = 0 := by simp [Bf, hε0]
    have hd : Tendsto (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
      have hBt : Tendsto Bf (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
        have := hBc.tendsto; rwa [hB0] at this
      refine squeeze_zero_norm' ?_ hBt
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hxp := hxG p hp
      have hK1 : 1 ≤ Kf p := le_add_of_nonneg_right (List.sum_nonneg (by
        intro y hy
        obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
        positivity))
      have hT := tele hc hc0 hK1 (adM p) (adM p₀) (lr u v) [] (by simp)
        (by
          intro x hx
          have hmK := le_sum_map (fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (fun _ => by positivity) (lr u v) hx
          have hmε := le_sum_map (fun x => ‖(adM p x).2 - (adM p₀ x).2‖) (fun _ => norm_nonneg _) (lr u v) hx
          refine ⟨rfl, rfl, adM_lie hp (hwu x hx).1, adM_lie hp₀ (hwu x hx).1, ?_, ?_, hmε⟩
          · have := norm_nonneg (adM p₀ x).2
            show ‖(adM p x).2‖ ≤ Kf p
            simp only [Kf]; linarith
          · have := norm_nonneg (adM p x).2
            show ‖(adM p₀ x).2‖ ≤ Kf p
            simp only [Kf]; linarith)
        (by simpa using hwt) (by simpa using hwl) _ hxp
      simp only [List.nil_append] at hT
      have h1 : 1 ≤ gN (sgs p g) ^ A := Real.one_le_rpow (BetaSesquilinearity.gN_ge_one hxp) hA
      calc ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖
          ≤ gN (sgs p g) ^ A * ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) h1
        _ ≤ Bf p := hT
    have hdc : ContinuousWithinAt
        (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        {p : SS k r | D.inSS p} p₀ := by
      have e0 : (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)) p₀ = 0 :=
        sub_self _
      unfold ContinuousWithinAt
      rw [e0]
      exact hd
    refine (hdc.add hsec).congr (fun p _ => ?_) ?_
    · simp
    · simp
  have hΦ : ContinuousOn (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) {p : SS k r | D.inSS p} := by
    have e : (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) =
        fun p => B6.Sd D p (W ((lr u v).map (adM p)) F (sgs p g)) := by
      funext p
      rw [B6.rho_eq, dLR_eq, lr_ad]
    rw [e]
    exact (B6.Sd_continuousOn D).clm_apply hmain
  have := hΦ.aestronglyMeasurable (μ := D.μSS) (B6.measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (B5.ae_inSS D)
  rwa [hr] at this

end meas

end Formalism.FourierDecayAlt.P.JFxDs3
