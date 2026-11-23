import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem hcs_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : X) : HasCompactSupport fun y => f (g, y) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(g, y), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem hcs_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : Y) : HasCompactSupport fun y => f (y, g) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, g), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem vp_bdd_on {X : Type*} [TopologicalSpace X] {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V)
    {q : X → (Fin m → SignType) → ℝ} (hq : Continuous q) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖V (q x)‖ ≤ B := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨B, hB⟩ := hV.bdd R
  refine ⟨max B 0, le_max_right _ _, fun x hx => (hB (q x) fun e => ?_).trans (le_max_left _ _)⟩
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (q x) e).trans (hR x hx)

theorem tor2 {n m : ℕ} {d₁ d₂ : GL (Fin n) ℂ} {V : ((Fin m → SignType) → ℝ) → ℂ}
    {p₁ p₂ : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (h₁ : LocFam d₁ V p₁) (h₂ : LocFam d₂ V p₂)
    {t₁ t₂ : GL (Fin n) ℂ} (ht₁ : t₁ ∈ twCent (thC n) d₁) (ht₂ : t₂ ∈ twCent (thC n) d₂) (x₁ x₂ : GL (Fin n) ℂ)
    (z : (Fin m → SignType) → ℝ) : V (p₁ (t₁ * x₁) + p₂ (t₂ * x₂) + z) = V (p₁ x₁ + p₂ x₂ + z) := by
  rw [add_assoc, h₁.tor t₁ ht₁, add_left_comm (p₁ x₁), h₂.tor t₂ ht₂, add_left_comm (p₂ x₂), ← add_assoc]

end PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV PositivityTheory.Rg.BcB.CV.SecondVanishing in
theorem PositivityTheory.Rg.BcB.CV.pf_TwoVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.OneVanish → PositivityTheory.Rg.BcB.CV.TwoVanish := by
  intro hLV hLP hLT hQI hQA hQP hOV n m _ _ μ _ d₁ d₂ ν _ _ f V p₁ p₂ z hm hd₁ hd₂ hfc hfs hcu₁ hcu₂ hV hF₁ hF₂ hz
  obtain ⟨hcl₁, hcomm₁, hθ, hlc, hsc⟩ := hLT n d₁ hd₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n d₂ hd₂
  have := hlc
  have := hsc
  have hc₁ : Continuous fun x => twConj (thC n) x d₁ := by
    show Continuous fun x => x⁻¹ * d₁ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hc₂ : Continuous fun x => twConj (thC n) x d₂ := by
    show Continuous fun x => x⁻¹ * d₂ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hΦc : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) :=
    hfc.comp ((hc₁.comp continuous_fst).prodMk (hc₂.comp continuous_snd))
  have hΦinv : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      f (twConj (thC n) (t * x).1 d₁, twConj (thC n) (t * x).2 d₂) = f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) := by
    intro t ht x
    rw [Prod.fst_mul, Prod.snd_mul, twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).1,
      twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).2]
  obtain ⟨C₁, hC₁, hsub₁⟩ := hLP n d₁ hd₁ (Prod.fst '' tsupport f) (IsCompact.image hfs continuous_fst)
  obtain ⟨C₂, hC₂, hsub₂⟩ := hLP n d₂ hd₂ (Prod.snd '' tsupport f) (IsCompact.image hfs continuous_snd)
  obtain ⟨Bf, hBf⟩ := hfc.bounded_above_of_compact_support hfs
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf (1, 1))
  have hclosed : IsClosed (((twCent (thC n) d₁).prod (twCent (thC n) d₂) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  obtain ⟨A₀, -, hA₀⟩ := hQI (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
    (C₁ ×ˢ C₂) hclosed (hC₁.prod hC₂)
  have hint : ∀ h : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ, Measurable h →
      (∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x, h (t * x) = h x) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C₁ ×ˢ C₂, ‖h x‖ ≤ B) →
      quotLIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
        (fun x => ‖f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x‖ₑ) ≠ ⊤ := by
    intro h hm hinv ⟨B, hB0, hB⟩
    refine (hA₀ (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x) (Bf * B) (mul_nonneg hBf0 hB0)
      (hΦc.measurable.mul hm) (fun t ht x => by rw [hΦinv t ht x, hinv t ht x]) ?_ ?_).1
    · intro x hx
      have hfx : f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ≠ 0 := left_ne_zero_of_mul hx
      have hts : (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ∈ tsupport f :=
        subset_tsupport _ (Function.mem_support.2 hfx)
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := Set.mem_mul.1 (hsub₁ (show twConj (thC n) x.1 d₁ ∈ Prod.fst '' tsupport f from ⟨_, hts, rfl⟩))
      obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := Set.mem_mul.1 (hsub₂ (show twConj (thC n) x.2 d₂ ∈ Prod.snd '' tsupport f from ⟨_, hts, rfl⟩))
      exact Set.mem_mul.2 ⟨(a₁, a₂), Subgroup.mem_prod.2 ⟨ha₁, ha₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext e₁ e₂⟩
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul (hBf _) (hB x hx) (norm_nonneg _) hBf0
  have hq : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 + p₂ x.2 + z :=
    ((hF₁.cont.comp continuous_fst).add (hF₂.cont.comp continuous_snd)).add continuous_const
  have hq' : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 := hF₁.cont.comp continuous_fst
  have hmF : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1 + p₂ x.2 + z) := hV.meas.comp hq.measurable
  have hmB : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1) := hV.meas.comp hq'.measurable
  have hiF : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1 + p₂ (t * x).2 + z) = V (p₁ x.1 + p₂ x.2 + z) := fun t ht x =>
    tor2 hF₁ hF₂ (Subgroup.mem_prod.1 ht).1 (Subgroup.mem_prod.1 ht).2 x.1 x.2 z
  have hiB : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1) = V (p₁ x.1) := fun t ht x => by
    simpa using hF₁.tor t.1 (Subgroup.mem_prod.1 ht).1 x.1 0
  have hIF := hint _ hmF hiF (vp_bdd_on hV hq (hC₁.prod hC₂))
  have hIB := hint _ hmB hiB (vp_bdd_on hV hq' (hC₁.prod hC₂))
  have hsplit := (hQA (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν).2.1
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z))
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1))
    (hΦc.measurable.mul hmF) (hΦc.measurable.mul hmB) hIF hIB

  have hA : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z) -
        f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂
      ((hΦc.measurable.mul hmF).sub (hΦc.measurable.mul hmB))
      (fun t ht x => by simp only [hΦinv t ht x, hiF t ht x, hiB t ht x]) (Or.inl fun ν₁ _ _ x₂ => ?_)
    have h1 := hOV n m μ d₁ ν₁ (fun y => f (y, twConj (thC n) x₂ d₂)) V p₁ (p₂ x₂ + z) hd₁
      (hfc.comp (continuous_id.prodMk continuous_const)) (hcs_right hfs _) (hcu₁ _) hV hF₁
      (by rw [Pi.add_apply, hF₂.zero, hz, add_zero])
    calc _ = quotIntegral μ (twCent (thC n) d₁) ν₁ (fun x => f (twConj (thC n) x d₁, twConj (thC n) x₂ d₂) *
          (V (p₁ x + (p₂ x₂ + z)) - V (p₁ x))) := by
          congr 1; funext x; dsimp only; rw [add_assoc]; ring
      _ = 0 := h1

  have hB : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂ (hΦc.measurable.mul hmB)
      (fun t ht x => by simp only [hΦinv t ht x, hiB t ht x]) (Or.inr fun ν₂ _ _ x₁ => ?_)
    have hne : (fun _ : Fin m => (1 : SignType)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, Nat.pos_of_ne_zero hm⟩
      simp at this
    obtain ⟨W₁, W₂, hW, -⟩ := hF₂.nil _ hne
    have h1 := hLV n μ (fun y => f (twConj (thC n) x₁ d₁, y)) (fun _ => 1) d₂ ν₂ W₁ W₂
      (hfc.comp (continuous_const.prodMk continuous_id)) (hcs_left hfs _) (hcu₂ _) hd₂ hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
      measurable_const (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    calc _ = quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x => V (p₁ x₁) *
          (f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x)) := by
          congr 1; funext x; dsimp only; ring
      _ = V (p₁ x₁) * quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x =>
          f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x) := (hQA _ μ _ ν₂).2.2 _ _
      _ = 0 := by rw [h1, mul_zero]
  rw [hA, hB] at hsplit
  linear_combination -hsplit
