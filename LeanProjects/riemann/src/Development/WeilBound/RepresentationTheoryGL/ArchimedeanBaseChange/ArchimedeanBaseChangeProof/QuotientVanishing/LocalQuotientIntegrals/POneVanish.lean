import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem twConj_mul_left {n : ℕ} (d t x : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    twConj (thC n) (t * x) d = twConj (thC n) x d := by
  rw [mem_twCent] at ht
  simp only [twConj, map_mul]
  calc (t * x)⁻¹ * d * ((thC n) t * (thC n) x) = x⁻¹ * (t⁻¹ * d * (thC n) t) * (thC n) x := by group
    _ = x⁻¹ * d * (thC n) x := by rw [ht]

theorem sle_refl {m : ℕ} (e : Fin m → SignType) : SLe e e := fun _ _ => rfl

def zr {m : ℕ} (z : (Fin m → SignType) → ℝ) (s : Finset (Fin m → SignType)) : (Fin m → SignType) → ℝ :=
  fun e => if e ∈ s then z e else 0

theorem zr_insert {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z (insert e s) = Function.update (y + zr z s) e (y e + z e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr]
  · simp [zr, h]

theorem zr_self {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z s = Function.update (y + zr z s) e (y e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr, he]
  · simp [h]

theorem diff_step {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V) (z : (Fin m → SignType) → ℝ)
    (s : Finset (Fin m → SignType)) (e : Fin m → SignType) (he : e ∉ s) (y y' : (Fin m → SignType) → ℝ)
    (hyy : ∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') :
    V (y + zr z (insert e s)) - V (y + zr z s) = V (y' + zr z (insert e s)) - V (y' + zr z s) := by
  have key : ∀ w : (Fin m → SignType) → ℝ, V (w + zr z (insert e s)) - V (w + zr z s) =
      V (Function.update (w + zr z s) e (w e + z e)) - V (Function.update (w + zr z s) e (w e)) := fun w => by
    rw [← zr_insert z w he, ← zr_self z w he]
  have hee : y e = y' e := hyy e (Or.inl (sle_refl e))
  rw [key y, key y', hee]
  exact hV.diff _ _ e _ _ (fun e' h => by simp only [Pi.add_apply, hyy e' h])

theorem good_V {n m : ℕ} [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] {d : GL (Fin n) ℂ}
    {V : ((Fin m → SignType) → ℝ) → ℂ} {p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (hV : VP V) (hL : LocFam d V p)
    (c : (Fin m → SignType) → ℝ) :
    Measurable (fun x => V (p x + c)) ∧ (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) = V (p x + c)) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c)‖ ≤ B := by
  refine ⟨hV.meas.comp (hL.cont.add continuous_const).measurable, fun t ht x => hL.tor t ht x c, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (f := fun x => p x + c) (hL.cont.add continuous_const).continuousOn
  obtain ⟨B, hB⟩ := hV.bdd M
  refine ⟨B, fun x hx => hB _ fun e => ?_⟩
  have := (norm_le_pi_norm (p x + c) e).trans (hM x hx)
  rwa [Real.norm_eq_abs] at this

end PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB.CV.FirstVanishingAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_OneVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.OneVanish := by
  intro hLV hLP hLT hQI hQA n m _ _ μ _ d ν _ _ f V p z hsep hf hfs hfc hV hL hz0
  obtain ⟨hTc, -, hθc, hlc, hsc⟩ := hLT n d hsep
  have := hlc
  have := hsc
  have htc : Continuous (fun x : GL (Fin n) ℂ => twConj (thC n) x d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul hθc
  obtain ⟨Bf, hBf⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨C', hC', hsub⟩ := hLP n d hsep (tsupport f) hfs
  obtain ⟨A, -, hAI⟩ := hQI (GL (Fin n) ℂ) μ (twCent (thC n) d) ν C' hTc hC'
  have fin : ∀ g : GL (Fin n) ℂ → ℂ, Measurable g → (∀ t ∈ twCent (thC n) d, ∀ x, g (t * x) = g x) →
      (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖g x‖ ≤ B) →
      Measurable (fun x => f (twConj (thC n) x d) * g x) ∧
      quotLIntegral μ (twCent (thC n) d) ν (fun x => ‖f (twConj (thC n) x d) * g x‖ₑ) ≠ ⊤ := by
    intro g hgm hgT hgb
    obtain ⟨Bg, hBg⟩ := hgb C' hC'
    have hm : Measurable (fun x => f (twConj (thC n) x d) * g x) := (hf.comp htc).measurable.mul hgm
    refine ⟨hm, (hAI _ (max Bf 0 * max Bg 0) (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hm ?_ ?_ ?_).1⟩
    · intro t ht x
      rw [twConj_mul_left d t x ht, hgT t ht x]
    · intro x hx
      exact hsub (show twConj (thC n) x d ∈ tsupport f from
        subset_tsupport f (Function.mem_support.2 (left_ne_zero_of_mul hx)))
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul ((hBf _).trans (le_max_left _ _)) ((hBg x hx).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
  have goodsub : ∀ c c' : (Fin m → SignType) → ℝ, Measurable (fun x => V (p x + c) - V (p x + c')) ∧
      (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) - V (p (t * x) + c') = V (p x + c) - V (p x + c')) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c) - V (p x + c')‖ ≤ B := by
    intro c c'
    obtain ⟨h1, h2, h3⟩ := good_V hV hL c
    obtain ⟨h1', h2', h3'⟩ := good_V hV hL c'
    refine ⟨h1.sub h1', fun t ht x => by rw [h2 t ht x, h2' t ht x], fun C hC => ?_⟩
    obtain ⟨B, hB⟩ := h3 C hC
    obtain ⟨B', hB'⟩ := h3' C hC
    exact ⟨B + B', fun x hx => (norm_sub_le _ _).trans (add_le_add (hB x hx) (hB' x hx))⟩
  have h0int : quotIntegral μ (twCent (thC n) d) ν (fun _ => (0 : ℂ)) = 0 := by
    simpa using (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.2 0 (fun _ => 0)
  have main : ∀ s : Finset (Fin m → SignType), quotIntegral μ (twCent (thC n) d) ν
      (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : zr z ∅ = 0 := by funext e; simp [zr]
      simp only [h0, sub_self, mul_zero]
      exact h0int
    · intro e s he ih
      have hFi := fin _ (goodsub (zr z (insert e s)) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hFs := fin _ (goodsub (zr z s) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hdiff : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s))) = 0 := by
        by_cases he0 : e = 0
        · subst he0
          have hzz : zr z (insert 0 s) = zr z s := by
            funext e'
            by_cases h : e' = 0
            · subst h; simp [zr, he, hz0]
            · simp [zr, h]
          simp only [hzz, sub_self, mul_zero]
          exact h0int
        · obtain ⟨W₁, W₂, ⟨hW1, hW12, hp1, hp2⟩, hnil⟩ := hL.nil e he0
          obtain ⟨hm, hTi, hb⟩ := goodsub (zr z (insert e s)) (zr z s)
          exact hLV n μ f (fun x => V (p x + zr z (insert e s)) - V (p x + zr z s)) d ν W₁ W₂ hf hfs hfc hsep
            hW1 hW12 hp1 hp2 hm hb (fun x k hk => by simp only [hL.cpt x k hk]) hTi
            (fun u hu x => diff_step hV z s e he _ _ (fun e' h => hnil u hu x e' h))
      have key : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0))) -
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) :=
        (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.1 _ _ hFi.1 hFs.1 hFi.2 hFs.2
      have hfun : (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s)) := by
        funext x; ring
      rw [hfun, hdiff, ih, sub_zero] at key
      exact key.symm
  have hu : zr z Finset.univ = z := by funext e; simp [zr]
  have := main Finset.univ
  rw [hu] at this
  simpa using this
