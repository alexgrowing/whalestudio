import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Esk.ExponentialSlopeDerivatives

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def A (δ : ℝ) (y : D.Y) : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}

theorem near_smul (hB : B1b) (δ : ℝ) (g : PG F) (z w : D.Xs) :
    Near δ (g • z : D.Xs) (g • w : D.Xs) ↔ Near δ z w := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [Dat.mk_smulX D γ z, Dat.mk_smulX D γ w]
    simp only [Near, Dat.act, hB.2.2.2.1]

theorem mem_conj (hB : B1b) (δ : ℝ) (g γ : PG F) (y : D.Y) :
    g * γ * g⁻¹ ∈ A D δ (g • y) ↔ γ ∈ A D δ y := by
  simp only [A, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, mul_smul, inv_smul_smul,
    smul_left_cancel_iff, near_smul D hB]

theorem A_conj (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    A D δ (g • y) = (fun γ => g * γ * g⁻¹) '' A D δ y := by
  ext γ'
  constructor
  · intro h
    refine ⟨g⁻¹ * γ' * g, (mem_conj D hB δ g _ y).1 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]
    · show g * (g⁻¹ * γ' * g) * g⁻¹ = γ'
      group
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_conj D hB δ g γ y).2 hγ

theorem conj_inj (g : PG F) : Function.Injective (fun γ : PG F => g * γ * g⁻¹) := by
  intro a b h
  simpa using h

theorem fin_card (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    ((A D δ (g • y)).Finite ↔ (A D δ y).Finite) ∧ (A D δ (g • y)).ncard = (A D δ y).ncard := by
  rw [A_conj D hB δ g y]
  exact ⟨Set.finite_image_iff (conj_inj g).injOn, Set.ncard_image_of_injective _ (conj_inj g)⟩

theorem e01 : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Ht01 [Fintype I] (z : X I) (x : Gf) : D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

end UpperTheory.Esk.ExponentialSlopeDerivatives

open UpperTheory.Esk UpperTheory.Esk.ExponentialSlopeDerivatives

theorem UpperTheory.Esk.pf_Mult : UpperTheory.Esk.B1b → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult := by
  intro hB hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have hcnt : ∀ x' : Gf, ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
      (A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).Finite ∧
      ((A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|) :=
    fun x' => hD.count ((x' : Gf ⧸ D.H)) δ C c hδ hc
  choose C' hC' using hcnt
  have hapos : ∀ x : Gf, 0 < D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H))) := fun x => hD.pos _ e01 _
  have final : ∀ (N Cx P a H K : ℝ), N ≤ Cx * (1 + P) → 0 ≤ P → P * a = H → 0 < a → 0 ≤ H →
      max Cx 0 * (1 + 1 / a) ≤ K → N ≤ K * (1 + H) := by
    intro N Cx P a H K hN hP hPa ha hH hK
    have hP' : P = H / a := eq_div_of_mul_eq ha.ne' hPa
    have h1 : N ≤ max Cx 0 * (1 + P) :=
      hN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h2 : 1 + P ≤ (1 + 1 / a) * (1 + H) := by
      rw [hP']
      have h0 : 0 ≤ 1 / a := by positivity
      have he : (1 + 1 / a) * (1 + H) - (1 + H / a) = H + 1 / a := by ring
      linarith
    have hM : 0 ≤ max Cx 0 := le_max_right _ _
    calc N ≤ max Cx 0 * (1 + P) := h1
      _ ≤ max Cx 0 * ((1 + 1 / a) * (1 + H)) := mul_le_mul_of_nonneg_left h2 hM
      _ = (max Cx 0 * (1 + 1 / a)) * (1 + H) := by ring
      _ ≤ K * (1 + H) := mul_le_mul_of_nonneg_right hK (by linarith)
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))), ?_⟩
  intro y s hs hy
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by
    rw [h2 _ e01 γ₀ y, hγ₀]
  have hn : c₀ ≤ D.Ht ![0, 1] ((γ₀ : PG F) • y).2 (D.rep ((γ₀ : PG F) • y).1) := by
    rw [← e1] at hy
    exact hy
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ hn
  have hb11 : b.val 1 1 ≠ 0 := by
    intro h0
    apply b.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hsm : ∀ ω : D.Om, (b : PG F) • ω = (((D.j b * D.rep ω : Gf) : Gf ⧸ D.H) : D.Om) := by
    intro ω
    conv_lhs => rw [← QuotientGroup.out_eq' ω]
    rfl
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) =
      (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    show (b : PG F) • ((γ₀ : PG F) • y).1 = _
    rw [hsm, hbx]
    exact QuotientGroup.eq.2 (by simpa using hh)
  obtain ⟨f1, c1⟩ := fin_card D hB δ (γ₀ : PG F) y
  obtain ⟨f2, c2⟩ := fin_card D hB δ (b : PG F) ((γ₀ : PG F) • y)
  rw [hy''] at f2 c2
  obtain ⟨hfin, hle⟩ := hC' x' _ hsg
  refine ⟨f1.1 (f2.1 hfin), ?_⟩
  have hHt : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) = D.HtY s y := by
    rw [← hy'', h2 _ e01 b _, hvb, h3 _ e01 _ hb11, e1]
  have hP : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs)
      = (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep ((x' : Gf ⧸ D.H))) :=
    Ht01 D (D.act b ((γ₀ : PG F) • y).2) (D.rep ((x' : Gf ⧸ D.H)))
  have hH : 0 ≤ D.HtY s y := by linarith
  show ((A D δ y).ncard : ℝ) ≤ _
  rw [← c1, ← c2]
  exact final _ _ _ _ _ _ hle (Finset.prod_nonneg fun v _ => abs_nonneg _) (hP.symm.trans hHt) (hapos x') hH
    (Finset.single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))))
      (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (one_div_nonneg.2 (hapos x).le))) hx'S)
