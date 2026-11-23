import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridgeInhab

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_eq_one_of_sub_one {x : k} (hx : valuation k (x - 1) < 1) : valuation k x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (valuation k) (x := x - 1) (y := 1) (by simpa using hx)
  simpa using h

def delta (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) : kˣ →* ℂˣ := μ₁ * GlobalTheory.SmGL.unrChar k (μ₁ ϖ)⁻¹

theorem delta_unit (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) {x : kˣ} (hx : valuation k (x : k) = 1) : delta μ₁ ϖ x = μ₁ x := by
  simp [delta, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]

theorem delta_tame {μ₁ : kˣ →* ℂˣ} (h : IsTame μ₁) (ϖ : kˣ) : IsTame (delta μ₁ ϖ) := by
  intro x hx
  rw [delta_unit μ₁ ϖ (val_eq_one_of_sub_one hx)]
  exact h x hx

def eta (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) (j : ℕ) : kˣ →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ m then μ j * δ⁻¹ else 1

theorem eta_mul (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) {i : ℕ} (hi : i < m) :
    eta μ m δ (i + 1) * δ = μ (i + 1) := by
  rw [eta, if_pos ⟨by omega, by omega⟩, inv_mul_cancel_right]

theorem eta_unram (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ)
    (h : ∀ i, i < m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x) (j : ℕ) : IsUnram (eta μ m δ j) := by
  intro x hx
  unfold eta
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h i (by omega) x hx, mul_inv_cancel]
  · rfl

theorem exists_near {E : Type} [Field E] {ι : E →+* k} (hd : DenseRange ι) (x : k) :
    ∃ a : E, valuation k (ι a - x) < 1 := by
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hU
  exact ⟨a, hy⟩

theorem tame_near {μ : kˣ →* ℂˣ} (h : IsTame μ) {x u : kˣ} (hx : valuation k (x : k) = 1)
    (hu : valuation k ((u : k) - x) < 1) : μ u = μ x := by
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hy : valuation k (((x⁻¹ * u : kˣ) : k) - 1) < 1 := by
    have e : ((x⁻¹ * u : kˣ) : k) - 1 = (x : k)⁻¹ * ((u : k) - x) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hu
  have := h _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

end Loc

section Arith
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem unitV_inv {P : HeightOneSpectrum (𝓞 E)} (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    LocE.unitV χ⁻¹ a = (LocE.unitV χ a)⁻¹ := by
  unfold LocE.unitV
  split_ifs <;> simp

theorem valuation_self (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) :
    LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

theorem locChar_q {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) (cq : K)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (q : E) = cq := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : redP P (1 : E) = 1 := by
    have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
    rw [h3, reduction_coe, map_one]
  have hu : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.locChar
  rw [valuation_self P q hq h0, zpow_one, zpow_one, div_self hqE]
  unfold LocE.unitV
  rw [dif_pos hu]
  have h2 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1]; rfl)
  rw [h2, map_one, Units.val_one, mul_one]

end Arith

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem muAt_unit (hP : P.1 ∉ Pr.vGs) (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
    muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
  unfold muAt
  rw [if_neg hP]
  exact GlobalTheory.LastSteps.locChar_unit _ _ ha

theorem muAt_q (hP : P.1 ∉ Pr.vGs) (i : ℕ) (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal) (h0 : 0 < qOf P.1) :
    muAt Ch sel mu cst i P ((qOf P.1 : ℕ) : X.E) = cst.muq (i + 1) P := by
  unfold muAt
  rw [if_neg hP]
  exact locChar_q _ hq h0 _ _

end Chain

theorem exists_twData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2

  have hunit : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = μ 1 x := by
    intro i hi x hx
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, muAt_unit Ch sel mu cst P hP i hred, muAt_unit Ch sel mu cst P hP 0 hred]
  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = delta (μ 1) ϖ x := by
    intro i hi x hx
    rw [delta_unit _ _ hx]; exact hunit i hi x hx

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, delta (μ 1) ϖ, delta_tame ht1 ϖ, eta μ R.m (delta (μ 1) ϖ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  ·
    intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  ·
    intro a u ha hr hu
    show ((delta (μ 1) ϖ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [delta_unit _ _ hva, hμ1 a u hu, muAt_unit Ch sel mu cst P hP 0 hr, unitV_inv, map_inv₀]
  ·
    intro i hi
    show ((eta μ R.m (delta (μ 1) ϖ) (i + 1) * delta (μ 1) ϖ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, muAt_q Ch sel mu cst P hP i hqmem hqpos]

end GlobalTheory.TwBridgeInhab
