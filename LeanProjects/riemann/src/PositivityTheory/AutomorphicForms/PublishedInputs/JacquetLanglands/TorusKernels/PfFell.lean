import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticFixedPointTerms

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem fix_iff (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (s : Fin 2 → F) (γ δ : GL (Fin 2) F) :
    Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val) :=
  (hE F I Gf D hD).2.2.2.2.2.2.2.2.2.2 s γ δ

theorem fix_mk (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (s : Fin 2 → F) (γ : GL (Fin 2) F) :
    Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
  have h := fix_iff D hD hE s γ 1
  simpa using h

theorem isEll_conj (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (γ δ : GL (Fin 2) F) :
    IsEll ((δ : PG F) * (γ : PG F) * (δ : PG F)⁻¹) ↔ IsEll (γ : PG F) := by
  simp only [IsEll, fix_iff D hD hE, fix_mk D hD hE]
  constructor
  · intro h t ht hc
    refine h (t ᵥ* (δ⁻¹).val) ?_ ?_
    · intro h0
      apply ht
      have := congrArg (· ᵥ* δ.val) h0
      simpa [Matrix.vecMul_vecMul] using this
    · simpa [Matrix.vecMul_vecMul] using hc
  · intro h s hs hc
    refine h (s ᵥ* δ.val) ?_ hc
    intro h0
    apply hs
    have := congrArg (· ᵥ* (δ⁻¹).val) h0
    simpa [Matrix.vecMul_vecMul] using this

theorem isEll_conj' (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (δ γ : PG F) :
    IsEll (δ * γ * δ⁻¹) ↔ IsEll γ := by
  have h := isEll_conj D hD hE γ.out δ.out
  have e1 : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have e2 : ((δ.out : GL (Fin 2) F) : PG F) = δ := Quotient.out_eq δ
  rwa [e1, e2] at h

theorem isEll_of_totEll (D : Dat F I Gf) [Nonempty I] (γ : PG F) (h : D.TotEll γ.out) : IsEll γ := by
  intro s hs ⟨c, hc⟩
  set M : Matrix (Fin 2) (Fin 2) F := γ.out.val with hM
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
  have q0 : (c ^ 2 - M.trace * c + M.det) * s 0 = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    linear_combination (M 1 1 - c) * e0 - M 1 0 * e1
  have q1 : (c ^ 2 - M.trace * c + M.det) * s 1 = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    linear_combination (-M 0 1) * e0 + (M 0 0 - c) * e1
  have hq : c ^ 2 - M.trace * c + M.det = 0 := by
    by_contra hne
    apply hs
    funext i
    fin_cases i
    · simpa [hne] using q0
    · simpa [hne] using q1
  have key : (2 * c - M.trace) ^ 2 = M.trace ^ 2 - 4 * M.det := by linear_combination 4 * hq
  obtain ⟨v⟩ := ‹Nonempty I›
  have hv := h v
  have k2 := congrArg (D.σ v) key
  simp only [map_pow, map_sub, map_mul, map_ofNat] at k2
  rw [← hM] at hv
  nlinarith [sq_nonneg (2 * D.σ v c - D.σ v M.trace)]

theorem supp (D : Dat F I Gf) {ι : Type} [Fintype ι] (a : ι → Gf) (γ : PG F) (ω : D.Om)
    (h : D.Te a γ.out (D.rep ω) ≠ 0) : ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨i, ?_⟩
  have hm : (D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * D.rep ω * a i ∈ D.H := by
    by_contra hn
    exact hi (by simp [Dat.ee, hn])
  have e1 : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have e2 : (show D.Om from ((D.rep ω : Gf) : Gf ⧸ D.H)) = ω := Quotient.out_eq ω
  have h2 : γ • ω = ((D.j γ.out * D.rep ω : Gf) : Gf ⧸ D.H) := by
    have h3 := D.mk_smulO γ.out (D.rep ω)
    rw [e1, e2] at h3
    exact h3
  rw [h2]
  refine QuotientGroup.eq.2 ?_
  simpa [_root_.mul_inv_rev, mul_assoc] using hm

end UpperTheory.Esk.EllipticFixedPointTerms

namespace UpperTheory.Esk

open EllipticFixedPointTerms

theorem pf_Fell : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F2 → UpperTheory.Esk.F3 → UpperTheory.Esk.F4 → UpperTheory.Esk.Fell := by
  intro hC4 hE0a hE0c hE0d hE1 hE3 hEcut hFsum hF2 hF3 hF4
  intro F I Gf _ _ _ D hD ι _ a
  classical
  haveI : Nonempty I := by have := hD.two; infer_instance

  obtain ⟨f, hf1, hf2⟩ : ∃ f : D.Cj × D.Om → D.Cj × D.Om, (∀ p, f p ∈ MulAction.orbit (PG F) p) ∧
      (∀ p q, q ∈ MulAction.orbit (PG F) p → f q = f p) :=
    ⟨fun p => Quotient.out (Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) p),
      fun p => MulAction.orbitRel_apply.1 (Quotient.mk_out p),
      fun p q h => congrArg Quotient.out (Quotient.sound (MulAction.orbitRel_apply.2 h))⟩
  have hff : ∀ p, f (f p) = f p := fun p => hf2 p (f p) (hf1 p)
  have hR : ∀ ω, ∃! r, r ∈ Set.range f ∧ r ∈ MulAction.orbit (PG F) ω := by
    intro ω
    refine ⟨f ω, ⟨⟨ω, rfl⟩, hf1 ω⟩, ?_⟩
    rintro r ⟨⟨p, rfl⟩, hr⟩
    rw [← hf2 ω (f p) hr, hff]
  choose Sa hSa using fun i => hF4 F I Gf D hD (a i)
  let Sset : Set (D.Cj × D.Om) := {p | p ∈ Set.range f ∧ D.TotEll (D.el p.1).out ∧
    D.Te a (D.el p.1).out (D.rep p.2) ≠ 0 ∧ Finite (MulAction.stabilizer (PG F) p)}
  have hSfin : Sset.Finite := by
    refine (Set.finite_iUnion fun i => (hSa i).1.image f).subset ?_
    rintro p ⟨⟨q, rfl⟩, htot, hte, -⟩
    obtain ⟨i, hi⟩ := supp D a (D.el (f q).1) (f q).2 hte
    obtain ⟨δ, hδ⟩ := (hSa i).2 (D.el (f q).1) (f q).2 htot hi
    refine Set.mem_iUnion.2 ⟨i, δ • f q, hδ, ?_⟩
    rw [hf2 (f q) (δ • f q) (MulAction.mem_orbit _ δ), hff]
  refine ⟨hSfin.toFinset, fun p hp => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hp
    exact ⟨hp.2.1, hp.2.2.2⟩
  intro k hk b hb
  have hc := hE0c F I Gf ι D k a hk
  let u : PG F → D.Y → ℂ := fun γ y => if IsEll γ then D.kk k a γ y else 0
  have hu_meas : ∀ γ, Measurable (u γ) := by
    intro γ
    by_cases h : IsEll γ
    · simp only [u, h, if_true]; exact hc.2.2.1 γ
    · simp only [u, h, if_false]; exact measurable_const
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hk c₀ hc₀
  have hbd : ∀ y, ∑' γ, ‖u γ y‖ₑ ≤ (C : ℝ≥0∞) := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmink y.2 (D.rep y.1)
    calc ∑' γ, ‖u γ y‖ₑ ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ :=
          ENNReal.summable.tsum_le_tsum (fun γ => by
            by_cases h : IsEll γ
            · have hm : γ ∈ {γ : PG F | ¬ Fix s γ} := h s hs
              simp only [u, h, if_true, Set.indicator_of_mem hm, le_refl]
            · simp [u, h]) ENNReal.summable
      _ = ∑' γ : {γ : PG F | ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
      _ ≤ C := hC y s hs hsy
  have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY < ⊤ := by
    calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY ≤ ∫⁻ y, ENNReal.ofReal (b y) * (C : ℝ≥0∞) ∂D.μY :=
          lintegral_mono fun y => by gcongr; exact hbd y
      _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * C := lintegral_mul_const' _ _ ENNReal.coe_ne_top
      _ < ⊤ := ENNReal.mul_lt_top (hE3 F I Gf D hD b hb) ENNReal.coe_lt_top
  obtain ⟨hb', hFs⟩ := hFsum F I Gf D hD b hb
  obtain ⟨hmeas', hint', hintY, heq⟩ := hFs u hu_meas hfin
  refine ⟨hintY, heq.trans ?_⟩
  obtain ⟨hcount, hsig, hpres, -⟩ := hE0a F I Gf D hD
  haveI : Countable (PG F) := hcount
  haveI : Countable D.Cj := hcount
  haveI : Countable D.Om := hD.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : DiscreteMeasurableSpace (D.Cj × D.Om) := ⟨fun s => s.to_countable.measurableSet⟩
  have stab_le : ∀ p : D.Cj × D.Om, MulAction.stabilizer (PG F) p ≤ MulAction.stabilizer (PG F) p.2 := by
    intro p g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    exact congrArg Prod.snd hg
  choose β hβ using fun p : D.Cj × D.Om => (hEcut F I Gf D hD).2 p.2 (MulAction.stabilizer (PG F) p) (stab_le p)
  have hinv : ∀ (g : PG F) (y : (D.Cj × D.Om) × D.Xs),
      u (D.el (g • y).1.1) ((g • y).1.2, (g • y).2) = u (D.el y.1.1) (y.1.2, y.2) := by
    rintro g ⟨⟨γ, ω⟩, z⟩
    show u (g * D.el γ * g⁻¹) (g • ((ω, z) : D.Y)) = u (D.el γ) (ω, z)
    simp only [u, isEll_conj' D hD hE0d, hc.2.1]
  obtain ⟨hintR, hsum⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres (fun p => b (p.1.2, p.2)) hb'
    (fun p => u (D.el p.1.1) (p.1.2, p.2)) hmeas' hinv hint' (Set.range f) hR β (fun r _ => hβ r)
  let g' : D.Cj × D.Om → ℂ := fun r => ∫ x, β r x • u (D.el r.1) (r.2, x)
  let h' : D.Cj × D.Om → ℂ := fun p => (Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
    (D.Te a ((D.el p.1).out) (D.rep p.2) * D.orb k ((D.el p.1).out))
  have hind : (Set.range f).indicator g' = Sset.indicator h' := by
    funext p
    by_cases hpR : p ∈ Set.range f
    · rw [Set.indicator_of_mem hpR]
      obtain ⟨γ, ω⟩ := p
      have hI := hintR (γ, ω) hpR
      by_cases hS : (γ, ω) ∈ Sset
      · rw [Set.indicator_of_mem hS]
        obtain ⟨-, htot, hte, -⟩ := hS
        have hell := isEll_of_totEll D (D.el γ) htot
        have := (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).2 (β (γ, ω)) (hβ (γ, ω))
        simp only [g', u, hell, if_true]
        exact this
      · rw [Set.indicator_of_notMem hS]
        simp only [g', u]
        by_cases hell : IsEll (D.el γ)
        · simp only [hell, if_true]
          by_cases htot : D.TotEll (D.el γ).out
          · by_cases hte : D.Te a (D.el γ).out (D.rep ω) = 0
            · simp [Dat.kk, Dat.kt, hte]
            · exfalso
              exact hS ⟨hpR, htot, hte, (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).1⟩
          · refine hF2 F I Gf ι D k a hk (D.el γ) ω htot (β (γ, ω)) (hβ (γ, ω)) ?_
            have hI' := hI
            simp only [u, hell, if_true] at hI'
            exact hI'
        · simp [hell]
    · rw [Set.indicator_of_notMem hpR, Set.indicator_of_notMem (fun h => hpR h.1)]
  have h1 : HasSum ((Set.range f).indicator g') (∫ y, (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2)) y •
      (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) y ∂(Measure.count.prod volume)) :=
    (hasSum_subtype_iff_indicator (f := g')).1 hsum
  rw [hind] at h1
  have h2 : HasSum (Sset.indicator h') (∑ p ∈ hSfin.toFinset, Sset.indicator h' p) :=
    hasSum_sum_of_ne_finset_zero fun p hp => Set.indicator_of_notMem (by simpa using hp) _
  have h3 : ∑ p ∈ hSfin.toFinset, Sset.indicator h' p = geo D k a hSfin.toFinset := by
    unfold geo
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Set.indicator_of_mem (by simpa using hp)]
  rw [← h3]
  exact h1.unique h2
