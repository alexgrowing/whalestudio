import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanInj

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

def SpanFor (A : Type) [Group A] : Prop :=
  ∀ (q : ℕ) (c : (Fin (q + 2) → A) → ℝ), InvS Set.univ c → dc c = 0 →
    ∃ (k : ℕ) (a : Fin k → ℝ) (α : Fin k → Fin (q + 1) → (Additive A →+ ℝ))
      (e : (Fin (q + 1) → A) → ℝ), InvS Set.univ e ∧ c = (∑ i, a i • cupH (α i)) + dc e

variable {G P : Type} [Group G] [Group P]

theorem pull_inv (ρ : P →* G) {n : ℕ} (F : (Fin n → G) → ℝ) (hF : InvS Set.univ F) :
    InvS Set.univ (fun z : Fin n → P => F (fun i => ρ (z i))) := by
  intro g _ y
  simp only [map_mul]
  exact hF _ trivial _

theorem pull_sum (ρ : P →* G) {n k : ℕ} (a : Fin k → ℝ) (α : Fin k → Fin n → (Additive G →+ ℝ)) :
    (fun z : Fin (n + 1) → P => (∑ i, a i • cupH (α i)) (fun j => ρ (z j))) =
      ∑ i, a i • cupH (fun j => (α i j).comp (MonoidHom.toAdditive ρ)) := by
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cupH, AddMonoidHom.comp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [map_mul, map_inv]

theorem sum_append {Y : Type} {k1 k2 : ℕ} (a1 : Fin k1 → ℝ) (a2 : Fin k2 → ℝ) (F1 : Fin k1 → Y → ℝ)
    (F2 : Fin k2 → Y → ℝ) :
    ∑ i, Fin.append a1 a2 i • Fin.append F1 F2 i = (∑ i, a1 i • F1 i) + ∑ i, a2 i • F2 i := by
  rw [Fin.sum_univ_add]
  simp

variable (W : WData G P)

def WData.lR : Additive P →+ ℝ := (Int.castAddHom ℝ).comp W.ℓ

theorem WData.tdecomp (hG : SpanFor G) (q : ℕ) (a : (Fin (q + 1) → G) → ℝ) (ha : InvS Set.univ a)
    (hda : dc a = 0) : ∃ (k : ℕ) (b : Fin k → ℝ) (β : Fin k → Fin (q + 1) → (Additive P →+ ℝ))
      (e : (Fin (q + 1) → P) → ℝ), InvS Set.univ e ∧
        tcup W.lR (fun z : Fin (q + 1) → P => a (fun i => W.ρ (z i))) = (∑ i, b i • cupH (β i)) + dc e := by
  cases q with
  | zero =>
    have hconst : ∀ y : Fin 1 → G, a y = a (fun _ => 1) := by
      intro y
      have := ha (y 0)⁻¹ (Set.mem_univ _) y
      rw [← this]
      congr 1
      funext j
      rw [Fin.fin_one_eq_zero j, inv_mul_cancel]
    refine ⟨1, fun _ => a (fun _ => 1), fun _ => fun _ => W.lR, 0, fun _ _ _ => rfl, ?_⟩
    funext y
    simp [tcup, cupH, hconst, mul_comm, dc]
  | succ q =>
    obtain ⟨k, a', α, eG, heG, hdecomp⟩ := hG q a ha hda
    refine ⟨k, a', fun i => Fin.cons W.lR (fun j => (α i j).comp (MonoidHom.toAdditive W.ρ)),
      (-1 : ℝ) • tcup W.lR (fun z => eG (fun i => W.ρ (z i))), ?_, ?_⟩
    · intro g _ y
      simp only [Pi.smul_apply]
      rw [tcup_inv W.lR Set.univ _ (pull_inv W.ρ eG heG) g (Set.mem_univ _) y]
    · have hpull : (fun z : Fin (q + 2) → P => a (fun i => W.ρ (z i))) =
          (fun z : Fin (q + 2) → P => (∑ i, a' i • cupH (α i)) (fun j => W.ρ (z j))) +
            dc (fun z => eG (fun i => W.ρ (z i))) := by
        funext z
        rw [hdecomp]
        rfl
      rw [hpull, pull_sum, tcup_add, tcup_sum, dc_smul, dc_tcup]
      simp only [tcup_cupH]
      simp

private theorem wData_ps_iota_eq_t_inv_mul (W : WData G P) (g : G) : W.ps (W.ι g) = W.t⁻¹ * W.ι g := by
  simp [WData.ps, W.ρι]

private theorem wData_rho_ps_eq_rho (W : WData G P) (z : P) : W.ρ (W.ps z) = W.ρ z := by
  simp [WData.ps, W.ρι, W.ρt]

private theorem wData_lR_ofMul_iota_eq_zero (W : WData G P) (g : G) : W.lR (Additive.ofMul (W.ι g)) = 0 := by
  simp [WData.lR, W.ℓι]

private theorem wData_lR_ofMul_t_inv_eq_neg_one (W : WData G P) : W.lR (Additive.ofMul W.t⁻¹) = -1 := by
  simp [WData.lR, ofMul_inv, W.ℓt]

private theorem wData_ps_iota_mul_eq_iota_mul_ps (W : WData G P) (h : G) (z : P) : W.ps (W.ι h * z) = W.ι h * W.ps z := by
  have htc : ∀ x : P, W.t⁻¹ * x = x * W.t⁻¹ := by
    intro x
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, W.tc x, mul_assoc, mul_inv_cancel, mul_one]
  simp only [WData.ps, map_mul, W.ρι]
  rw [← mul_assoc, htc, mul_assoc]

private theorem wData_prism_ps_tcup_lR_iota_eq_neg (W : WData G P) {q : ℕ} (Y : (Fin (q + 1) → G) → ℝ)
    (g : Fin (q + 1) → G) :
    prism W.ps (tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i))))
      (fun i => W.ι (g i)) = - Y g := by
  rw [prism_succ]
  have htc : ∀ x : P, W.t⁻¹ * x = x * W.t⁻¹ := by
    intro x
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, W.tc x, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i)))
      (Fin.cons (W.ι (g 0)) fun i => W.ps (W.ι (g i))) = - Y g := by
    simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.tail_cons, wData_rho_ps_eq_rho, W.ρι, wData_ps_iota_eq_t_inv_mul]
    rw [htc, ← mul_assoc, inv_mul_cancel, one_mul, wData_lR_ofMul_t_inv_eq_neg_one]
    simp [W.ρt, W.ρι]
  have h2 : prism W.ps (fun w : Fin (q + 1) → P =>
      tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i))) (Fin.cons (W.ι (g 0)) w))
      (Fin.tail fun i => W.ι (g i)) = 0 := by
    cases q with
    | zero => rw [prism.eq_1]
    | succ q =>
      rw [prism_succ]
      have h0 : (fun w : Fin (q + 1) → P =>
          tcup W.lR (fun z : Fin (q + 2) → P => Y (fun i => W.ρ (z i)))
            (Fin.cons (W.ι (g 0)) (Fin.cons ((Fin.tail fun i => W.ι (g i)) 0) w))) = 0 := by
        funext w
        simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.cons_zero, Fin.tail, Pi.zero_apply]
        rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul]
      rw [h0, prism_zero]
      simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.tail, Pi.zero_apply]
      rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul, sub_zero]
  rw [h1, h2, sub_zero]

private theorem wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero (W : WData G P) {m : ℕ} (F : (Fin (m + 2) → P) → ℝ) (hF : dc F = 0)
    (hps : ∀ g : Fin (m + 2) → G, F (fun i => W.ps (W.ι (g i))) = F (fun i => W.ι (g i))) :
    dc (fun g : Fin (m + 1) → G => prism W.ps F (fun i => W.ι (g i))) = 0 := by
  funext y
  have h := prism_dc W.ps m F (fun i => W.ι (y i))
  rw [hF, prism_zero, Pi.zero_apply, add_zero, hps, sub_self] at h
  exact h

private theorem wData_invS_prism_ps_iota_of_invS (W : WData G P) {n : ℕ} (F : (Fin (n + 1) → P) → ℝ) (hF : InvS Set.univ F) :
    InvS Set.univ (fun g : Fin n → G => prism W.ps F (fun i => W.ι (g i))) := by
  have hF' : InvS (Set.range W.ι) F := fun g _ y => hF g (Set.mem_univ _) y
  have hP := prism_inv W.ps (Set.range W.ι)
    (by rintro _ ⟨h, rfl⟩ z; exact wData_ps_iota_mul_eq_iota_mul_ps W h z) F hF'
  intro h _ y
  simp only [map_mul]
  exact hP (W.ι h) ⟨h, rfl⟩ _

theorem WData.step' (W' : WData G P) (hG : SpanFor G) : SpanFor P := by
  intro q c hc hdc
  let a : (Fin (q + 2) → G) → ℝ := fun g => c (fun i => W'.ι (g i))
  have ha : InvS Set.univ a := by
    intro h _ y
    simp only [a, map_mul]
    exact hc _ (Set.mem_univ _) _
  have hda : dc a = 0 := by
    funext y
    show dc c (fun i => W'.ι (y i)) = 0
    rw [hdc]; rfl
  let A : (Fin (q + 2) → P) → ℝ := fun z => a (fun i => W'.ρ (z i))
  have hAinv : InvS Set.univ A := pull_inv W'.ρ a ha
  have hdA : dc A = 0 := by
    funext y
    show dc a (fun i => W'.ρ (y i)) = 0
    rw [hda]; rfl
  let b : (Fin (q + 1) → G) → ℝ := fun g =>
    prism W'.ps A (fun i => W'.ι (g i)) - prism W'.ps c (fun i => W'.ι (g i))
  have hbinv : InvS Set.univ b := by
    intro h _ y
    simp only [b]
    exact congrArg₂ (fun u v => u - v) (wData_invS_prism_ps_iota_of_invS W' A hAinv h (Set.mem_univ _) y)
      (wData_invS_prism_ps_iota_of_invS W' c hc h (Set.mem_univ _) y)
  have hdb : dc b = 0 := by
    have h1 := wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero W' A hdA (fun g => by simp only [A, wData_rho_ps_eq_rho])
    have h2 := wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero W' c hdc (fun g => by
      simp only [wData_ps_iota_eq_t_inv_mul]
      exact hc _ (Set.mem_univ _) _)
    have : b = (fun g : Fin (q + 1) → G => prism W'.ps A (fun i => W'.ι (g i))) -
        (fun g : Fin (q + 1) → G => prism W'.ps c (fun i => W'.ι (g i))) := rfl
    rw [this, dc_sub, h1, h2, sub_zero]
  let T : (Fin (q + 2) → P) → ℝ := tcup W'.lR (fun z => b (fun i => W'.ρ (z i)))
  have hTinv : InvS Set.univ T := tcup_inv W'.lR Set.univ _ (pull_inv W'.ρ b hbinv)
  have hdT : dc T = 0 := by
    have : dc (fun z : Fin (q + 1) → P => b (fun i => W'.ρ (z i))) = 0 := by
      funext y
      show dc b (fun i => W'.ρ (y i)) = 0
      rw [hdb]; rfl
    simp only [T]
    rw [dc_tcup, this]
    funext y
    simp [tcup]
  have hinv' : InvS Set.univ (c - A - T) := by
    intro h _ y
    simp only [Pi.sub_apply]
    rw [hc h (Set.mem_univ _) y, hAinv h (Set.mem_univ _) y, hTinv h (Set.mem_univ _) y]
  have hdc' : dc (c - A - T) = 0 := by
    rw [dc_sub, dc_sub, hdc, hdA, hdT, sub_zero, sub_zero]
  have hι : ∀ g : Fin (q + 2) → G, (c - A - T) (fun i => W'.ι (g i)) = 0 := by
    intro g
    simp only [Pi.sub_apply, A, a, T, tcup, W'.ρι]
    rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul, sub_self, sub_zero]
  have hpr : ∀ g : Fin (q + 1) → G, prism W'.ps (c - A - T) (fun i => W'.ι (g i)) = 0 := by
    intro g
    rw [prism_sub, prism_sub]
    simp only [Pi.sub_apply, T]
    rw [wData_prism_ps_tcup_lR_iota_eq_neg W' b g]
    simp only [b]
    ring
  obtain ⟨e', he', hce'⟩ := W'.inj q (c - A - T) hinv' hdc' hι hpr
  obtain ⟨k1, a1, α1, eG, heG, hdecA⟩ := hG q a ha hda
  obtain ⟨k2, b2, β2, e2, he2, hdecB⟩ := W'.tdecomp hG q b hbinv hdb
  refine ⟨k1 + k2, Fin.append a1 b2,
    Fin.append (fun i j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ)) β2,
    (fun z => eG (fun i => W'.ρ (z i))) + e2 + e', ?_, ?_⟩
  · intro h _ y
    simp only [Pi.add_apply]
    have h1 : (eG fun i => W'.ρ (h * y i)) = eG fun i => W'.ρ (y i) :=
      pull_inv W'.ρ eG heG h (Set.mem_univ _) y
    rw [h1, he2 h (Set.mem_univ _) y, he' h (Set.mem_univ _) y]
  · have hA' : A = (∑ i, a1 i • cupH (fun j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ))) +
        dc (fun z => eG (fun i => W'.ρ (z i))) := by
      have : A = (fun z : Fin (q + 2) → P => (∑ i, a1 i • cupH (α1 i)) (fun j => W'.ρ (z j))) +
          dc (fun z => eG (fun i => W'.ρ (z i))) := by
        funext z
        show a (fun i => W'.ρ (z i)) = _
        rw [hdecA]
        rfl
      rw [this, pull_sum]
    have hT' : T = (∑ i, b2 i • cupH (β2 i)) + dc e2 := hdecB
    have hsplit : c = A + T + (c - A - T) := by abel
    have hfa : ∀ i, cupH (Fin.append (fun (i : Fin k1) (j : Fin (q + 1)) => (α1 i j).comp (MonoidHom.toAdditive W'.ρ)) β2 i) =
        Fin.append (fun i => cupH (fun j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ))) (fun i => cupH (β2 i)) i := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Fin.append_left, Fin.append_right]
    simp only [hfa]
    rw [hsplit, hce', hA', hT', sum_append, dc_add, dc_add]
    abel

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
