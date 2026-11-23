import Mathlib
import Development.WeilBound.CoreStatements.ThetaDilations.BoundedA
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemma
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core0

section Theta

open GlobalTheory.CompanionTheory.SW.CoefTheta

theorem fourier_coefficient_any : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  intro F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC a ha β N hN hNβ hint D hD
  haveI : Countable F := countable_field
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  obtain ⟨hprob, -, -, hOrth, -⟩ := id hC
  obtain ⟨-, -, hT2, hOc, hOo, -, hmem, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, -, -, hfd⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, horth⟩ := hfd D hD
  have hsb : SB (indL a : (ι → A F) → ℂ) := sb_indL hT2 hOc hOo ha
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC (indL a) hsb 1 1 one_pos one_pos
  obtain ⟨hmeas, hbound⟩ := hCb (fun _ => Complex.I) (by simp) (by simp)
  set s : (ι → F) → Ω → ℂ :=
    fun z ω => thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) z with hs
  have hm : ∀ z, Measurable (s z) := hmeas
  have hwt : wt M (fun _ : InfinitePlace F => Complex.I) = 1 := by simp [wt]
  have hnz : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ := by
    rw [hwt, ENNReal.ofReal_one, one_mul] at hbound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞ := by
    have hle : ∀ ω, ∑' z, ‖s z ω‖ₑ ≤ 1 + ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ := by
      intro ω
      rw [ENNReal.tsum_eq_add_tsum_ite 0]
      refine add_le_add (thTerm_zero_le B ρ P (gf ω) (gi ω) a) (le_of_eq ?_)
      have := tsum_subtype {x : ι → F | x ≠ 0} (fun z => ‖s z ω‖ₑ)
      refine Eq.trans ?_ this.symm
      refine tsum_congr fun z => ?_
      by_cases h : z = 0 <;> simp [h]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hnz⟩
  have hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ) := fun z ω => thTerm_nonneg B ρ P (gf ω) (gi ω) a z
  set Sel : Set (ι → F) := {z | qf (1 / 2 : F) B z = β} with hSel
  haveI : IsFiniteMeasure ((volume : Measure (InfinitePlace F → ℝ)).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hv : Continuous fun x : InfinitePlace F → ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
    simp_rw [ph_neg]
    exact ph_continuous ρ _
  have hvn : ∀ x : InfinitePlace F → ℝ,
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))‖ = 1 := by
    intro x
    rw [ph_neg, ph_norm]
  have hres := fourier_series hm hfin (μ := (volume : Measure (InfinitePlace F → ℝ)).restrict D)
    (u := fun z => ph ρ (qf (1 / 2 : F) B z)) (fun z => ph_continuous ρ _) (fun z x => ph_norm ρ _ x)
    hv hvn Sel ((volume D).toReal : ℂ)
    (by
      intro z hz
      have hz' : qf (1 / 2 : F) B z = β := hz
      have : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 1 := by
        intro x
        rw [ph_neg, ph_mul, hz', add_neg_cancel, ph_zero]
      simp_rw [this]
      simp [setIntegral_const, Measure.real])
    (by
      intro z hz
      by_cases hall : ∀ ω, s z ω = 0
      · exact Or.inr hall
      left
      push_neg at hall
      obtain ⟨ω, hω⟩ := hall
      obtain ⟨r, hr⟩ := integral_of_ne_zero (hOrth ω) hint hmem hω
      obtain ⟨r₀, hr₀⟩ := hNβ
      have hne : qf (1 / 2 : F) B z + -β ≠ 0 := fun h => hz (add_neg_eq_zero.mp h)
      have := horth _ hne ⟨r - r₀, by
        have hsub : ((r - r₀ : 𝓞 F) : F) = (r : F) - (r₀ : F) := map_sub (algebraMap (𝓞 F) F) r r₀
        rw [hsub, hr, hr₀]
        ring⟩
      have hx : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) =
          ph ρ (qf (1 / 2 : F) B z + -β) x := by
        intro x
        rw [ph_neg, ph_mul]
      simp_rw [hx]
      exact this)
  have hth : ∀ (x : InfinitePlace F → ℝ) (ω : Ω),
      theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) =
        ∑' z, ph ρ (qf (1 / 2 : F) B z) x * s z ω := fun x ω =>
    tsum_congr fun z => thTerm_shift P (hOrth ω) _ x z
  have hI : ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun ω =>
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun z => ‖s z ω‖ₑ)
  refine ⟨_, (ENNReal.coe_toNNReal hI).symm, ?_, ?_⟩
  · simp_rw [hth]
    exact hres.1
  · simp_rw [hth]
    rw [hres.2, sum_selected hm hfin hpos Sel]
    rfl

end Theta

section Eis

open GlobalTheory.CompanionTheory.SW.CoefEis

theorem fourier_coeff_eis_any : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → Integrable (fstar ψ (hf F) (Bf B) (muF B lf) φ) lf → Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ x ∈ Oh F, ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → IntegrableOn (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = φ 0 * (∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) φ y * ψ (-(algebraMap F (A F) β) * y) ∂lf) * ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ hΦ hc β N hN hNβ hper D hD
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  have hcount : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  obtain ⟨-, hLcount, hLmem, hLD⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, -⟩ := hLD D hD
  obtain ⟨-, -, -, -, hOopen, -, hOint, -, -, hWopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hψ'⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨hψ1, hψO, -⟩ := hψ' ψ hψ
  obtain ⟨C, hC⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ 1 one_pos
  haveI := hLcount
  haveI : lf.IsAddHaarMeasure := hlf

  set Φ := fstar ψ (hf F) (Bf B) (muF B lf) φ with hΦdef
  set c : (InfinitePlace F → ℝ) → ℂ := fun x => cG B ρ P (fun w => (x w : ℂ) + Complex.I) with hcdef
  set e : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hedef
  let j : F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun b w => ρ w b
      map_zero' := by ext w; simp
      map_add' := fun a b => by ext w; simp }
  have hj : ∀ b w, j b w = ρ w b := fun _ _ => rfl
  have hjinj : Function.Injective j := by
    intro a b hab
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (ρ w).injective (congrFun hab w)
  set al : F →+* A F := algebraMap F (A F) with hal

  have hecont : Continuous e := by
    simp only [hedef]
    fun_prop
  have henorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [hedef]
    have : -(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)
        = ((-(2 * Real.pi * ∑ w, ρ w β * x w) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have headd : ∀ x y, e (x + y) = e x * e y := by
    intro x y
    simp only [hedef, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  have hechar : ∀ b : F, e (-(j b)) = ψ (-(al β) * al b) := by
    intro b
    have h2 : -(al β) * al b = al (-(β * b)) := by simp [hal]
    rw [h2, hψ.2]
    simp only [hedef]
    congr 1
    have h3 : (∑ w, ρ w β * (-(j b)) w) = -((Algebra.trace ℚ F (β * b) : ℚ) : ℝ) := by
      rw [← sum_places_eq_trace F hTR ρ hρ (β * b), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hj]
    rw [h3, map_neg]
    push_cast
    ring

  let H : AddSubgroup F := (latR ρ N).comap j
  have hHmem : ∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F) := by
    intro b
    rw [AddSubgroup.mem_comap, hLmem]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, hjinj ?_⟩
      rw [hr]
      rfl
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have hNal : ∀ n : ℕ, al (n : F) = (n : A F) := fun n => map_natCast _ n

  have hOr : ∀ r : 𝓞 F, al (r : F) ∈ Oh F := fun r => (hOint _).2 ⟨r, rfl⟩
  have heLat : ∀ l ∈ latR ρ N, e l = 1 := by
    intro l hl
    obtain ⟨r, rfl⟩ := (hLmem l).1 hl
    obtain ⟨r0, hr0⟩ := hNβ
    have h4 : (fun w => ρ w ((N : F) * (r : F))) = -(j (-((N : F) * (r : F)))) := by
      ext w
      simp [hj]
    rw [h4, hechar]
    have h5 : -(al β) * al (-((N : F) * (r : F))) = al ((r0 * r : 𝓞 F) : F) := by
      rw [← map_neg, ← map_mul]
      congr 1
      rw [show ((r0 * r : 𝓞 F) : F) = (r0 : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) r0 r, hr0]
      ring
    rw [h5]
    exact hψO _ (hOr _)
  have hap : ∀ b, ∀ h ∈ H, Φ (al (b + h)) = Φ (al b) := by
    intro b h hh
    obtain ⟨r, rfl⟩ := (hHmem h).1 hh
    have : al (b + (N : F) * (r : F)) = al b + (N : A F) * al (r : F) := by
      rw [map_add, map_mul, hNal]
    rw [this]
    exact hper _ (hOr r) _
  have hterm : ∀ (x : InfinitePlace F → ℝ) (b : F),
      eiTerm ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) b = Φ (al b) * c (x + j b) := by
    intro x b
    simp only [eiTerm, hcdef]
    congr 2
    funext w
    simp only [Pi.add_apply, hj]
    push_cast
    ring
  have hbd : ∀ x : InfinitePlace F → ℝ, Summable (fun b => ‖Φ (al b) * c (x + j b)‖) ∧
      ∑' b, ‖Φ (al b) * c (x + j b)‖ ≤ C := by
    intro x
    have h6 := hC (fun w => (x w : ℂ) + Complex.I) (fun w => by simp)
    simp only [hterm] at h6
    have h7 : wt M (fun w => (x w : ℂ) + Complex.I) = 1 := by simp [wt]
    rw [h7, one_mul] at h6
    exact h6
  have hDfin : volume D ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hDfin⟩
  set T : F → (InfinitePlace F → ℝ) → ℂ := fun b x => Φ (al b) * c (x + j b) * e x with hT
  have hTnorm : ∀ b x, ‖T b x‖ = ‖Φ (al b) * c (x + j b)‖ := by
    intro b x
    simp only [hT, norm_mul, henorm, mul_one]
  have hTmeas : ∀ b, AEStronglyMeasurable (T b) (volume.restrict D) := by
    intro b
    have h8 : AEStronglyMeasurable (fun x => c (x + j b)) volume :=
      (hc.comp_add_right (j b)).aestronglyMeasurable
    exact ((h8.const_mul _).mul hecont.aestronglyMeasurable).restrict
  obtain ⟨hInt, hSum, hEq⟩ := tsum_integral_swap F (InfinitePlace F → ℝ) (volume.restrict D) T C hTmeas
    (fun x => by simpa only [hTnorm] using (hbd x).1)
    (fun x => by simpa only [hTnorm] using (hbd x).2)
  have heInt : Integrable e (volume.restrict D) :=
    Integrable.of_bound hecont.aestronglyMeasurable 1 (ae_of_all _ fun x => (henorm x).le)
  have Heisenberg₂ : ∀ x : InfinitePlace F → ℝ,
      eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * e x + ∑' b, T b x := by
    intro x
    simp only [eis, add_mul, hT, hterm, tsum_mul_right]
  refine ⟨?_, ?_⟩
  · have : (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x)
        = fun x => φ 0 * e x + ∑' b, T b x := funext Heisenberg₂
    rw [IntegrableOn, this]
    exact (heInt.const_mul _).add hInt
  · change ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x =
      φ 0 * (∫ x in D, e x) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, Φ y * ψ (-(al β) * y) ∂lf) * ∫ x, c x * e x
    set Ch : ℂ := ∫ x, c x * e x with hCh
    simp only [Heisenberg₂]
    rw [integral_add (heInt.const_mul _) hInt, integral_const_mul, hEq, tsum_cosets F H _ hSum]
    congr 1

    let eH : H ≃ latR ρ N := Equiv.ofBijective (fun h => ⟨j h, h.2⟩) (by
      constructor
      · intro a b hab
        exact Subtype.ext (hjinj (congrArg Subtype.val hab))
      · rintro ⟨l, hl⟩
        obtain ⟨r, rfl⟩ := (hLmem l).1 hl
        exact ⟨⟨(N : F) * (r : F), (hHmem _).2 ⟨r, rfl⟩⟩, rfl⟩)
    have hcoset : ∀ q : F ⧸ H, ∑' h : H, ∫ x in D, T (q.out + (h : F)) x =
        Φ (al q.out) * e (-(j q.out)) * Ch := by
      intro q
      have h10 : ∀ h : H, ∫ x in D, T (q.out + (h : F)) x =
          Φ (al q.out) * ∫ x in D, c (x + (j q.out + ((eH h : latR ρ N) : InfinitePlace F → ℝ))) * e x := by
        intro h
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hT]
        rw [hap _ _ h.2, map_add j, mul_assoc]
        rfl
      simp only [h10]
      rw [tsum_mul_left, eH.tsum_eq (fun l : latR ρ N =>
        ∫ x in D, c (x + (j q.out + (l : InfinitePlace F → ℝ))) * e x),
        unfold_char (InfinitePlace F) (latR ρ N) D hD c e hc hecont henorm headd heLat (j q.out)]
      ring
    simp only [hcoset]
    rw [tsum_mul_right]
    congr 1

    set W : Set (A F) := {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} with hW
    obtain ⟨hcov, hdis⟩ := cosets_of_multiples F N hN H hHmem
    set G : A F → ℂ := fun y => Φ y * ψ (-(al β) * y) with hG
    have hGint : Integrable G lf := by
      refine hΦ.mono ?_ (ae_of_all _ fun y => ?_)
      · refine hΦ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
        exact hψ.1.comp (by fun_prop)
      · simp only [hG, norm_mul, hψ1, mul_one, le_refl]
    have hGper : ∀ y, ∀ w ∈ W, G (y + w) = G y := by
      rintro y w ⟨z, hz, rfl⟩
      obtain ⟨r0, hr0⟩ := hNβ
      have h11 : -(al β) * (y + (N : A F) * z) = -(al β) * y + al (-(r0 : F)) * z := by
        rw [hr0, ← hNal]
        simp only [map_neg, map_mul]
        ring
      have h12 : al (-(r0 : F)) * z ∈ Oh F := by
        rw [show -(r0 : F) = ((-r0 : 𝓞 F) : F) from (map_neg (algebraMap (𝓞 F) F) r0).symm]
        exact Oh_mul_mem F _ _ (hOr _) hz
      simp only [hG]
      rw [hper z hz y, h11, AddChar.map_add_eq_mul, hψO _ h12, mul_one]
    haveI : Countable (F ⧸ H) := Function.Surjective.countable (f := fun b : F => (b : F ⧸ H))
      (fun q => ⟨q.out, QuotientAddGroup.out_eq' q⟩)
    have hsum := hasSum_integral_cosets (A F) (F ⧸ H) lf (fun q => al q.out) W (hWopen N hN) hcov hdis G hGint hGper
    have h13 : ∀ q : F ⧸ H, G (al q.out) = Φ (al q.out) * e (-(j q.out)) := by
      intro q
      simp only [hG, hechar]
    have h14 := hsum.tsum_eq
    simp only [h13] at h14
    rw [tsum_mul_left] at h14
    rw [← h14, ← mul_assoc]
    have h15 := mass_multiples F lf hlf h1 N hN
    have h16 : (((N : ℂ) ^ Module.finrank ℚ F) * (((lf W).toReal : ℝ) : ℂ)) = 1 := by
      rw [mul_comm]
      exact_mod_cast h15
    rw [h16, one_mul]

end Eis

lemma tsum_split {α : Type} (f : α → ℝ≥0∞) (p : α → Prop) (z : α) (hz : p z) :
    ∑' x : {x // p x}, f x.1 = f z + ∑' x : {x // x ≠ z ∧ p x}, f x.1 := by
  classical
  have a1 := tsum_subtype {x | p x} f
  have a2 := tsum_subtype {x | x ≠ z ∧ p x} f
  change ∑' x : ({x | p x} : Set α), f x.1 = f z + ∑' x : ({x | x ≠ z ∧ p x} : Set α), f x.1
  rw [a1, a2, ENNReal.tsum_eq_add_tsum_ite z, Set.indicator_of_mem (show z ∈ {x | p x} from hz)]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = z
  · simp [h]
  · by_cases hp : p x <;> simp [h, hp, Set.indicator]

lemma thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (a : ℕ) :
    thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) 0 = 1 := by
  have hz : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 1 := by
    have : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0 := by
      intro w
      funext i
      simp [Matrix.mulVec, dotProduct]
    simp only [gauss, this]
    simp
  have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  unfold thTerm
  rw [hz, hg, mul_one]
  simp only [indL, Set.indicator_of_mem hm]

theorem core_zero : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a 0 * Dinf (fun _ => 0)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ hF ι _ _ M hc hM B hB hdet ρ hρ P hP hPP _ _ lf hlf h1 Ω _ Pr _ gi gf m1 m2 o1 o2 hcnt
  have hQ : QSetup M B ρ P := ⟨hF, hc, hB, hdet, hρ, hP, hPP⟩
  have hC : CountData M B ρ Pr gf gi := ⟨inferInstance, m1, m2, fun ω => ⟨o2 ω, o1 ω⟩, hcnt⟩
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.standard_adelic_character F).1
  obtain ⟨C, hb⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.bounded_a F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC
  choose! Df d1 d2 d3 d4 d5 using GlobalTheory.T.schur_function_whittaker_equivariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  obtain ⟨Di, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.quadratic_level_set_density F ι M B ρ P hQ hM
  refine ⟨C, Df, Di, fun a ha => ⟨d1 a ha, d2 a ha, d3 a ha⟩, ⟨i1, i2, i3⟩, fun a ha => ?_⟩
  obtain ⟨-, -, -, -, -, -, hint, -, hK, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hs := PositivityTheory.PlacePermOperatorBicommutantSpan.sb_indL (F := F) (ι := ι) ha
  obtain ⟨N₁, p1, n1⟩ := GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ hs
  have hq : Continuous (qf (hf F) (Bf B) : (ι → A F) → A F) := by unfold qf; fun_prop
  obtain ⟨N₂, p2, n2⟩ := hK _ ((hs.2.isCompact.image hq).insert (algebraMap F (A F) 0))
  have hN : 0 < N₁ * N₂ := Nat.mul_pos p1 p2
  have hβN : ∃ r : 𝓞 F, (r : F) = ((N₁ * N₂ : ℕ) : F) * 0 := ⟨0, by simp⟩
  obtain ⟨⟨D, hD⟩, -, -, hvol⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hF ρ hρ _ hN
  obtain ⟨I, e1, j1, e2⟩ := fourier_coefficient_any F ι M B ρ P hQ Ω Pr gf gi hC a ha 0 _ hN hβN (fun y hy => by
    rw [Nat.cast_mul, mul_assoc]
    refine PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₁) (n2 _ (Set.mem_insert_of_mem _ ⟨y, subset_tsupport _ ?_, rfl⟩))
    rw [Function.mem_support, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hy]
    exact one_ne_zero) D hD
  obtain ⟨j2, e3⟩ := fourier_coeff_eis_any F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ hs (d4 a ha) i4 0 _ hN hβN
    (fun x hx y => by
      rw [Nat.cast_mul, mul_assoc]
      exact (n1 _ (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₂) hx)).2 y) D hD
  haveI : IsProbabilityMeasure Pr := hC.1

  have hsplit : ∀ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ =
      1 + ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
        ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ := fun ω => by
    rw [tsum_split (fun x => ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x‖ₑ)
      (fun x => qf (1 / 2 : F) B x = 0) 0 (by simp [qf]), thTerm_zero]
    simp
  have e1' : 1 + ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) := by
    rw [← e1]
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const]
    simp
  have hJtop : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr ≠ ∞ := by
    intro h
    rw [h] at e1'
    simp at e1'
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (J : ℝ≥0∞) :=
    ⟨_, (ENNReal.coe_toNNReal hJtop).symm⟩
  have hIJ : (I : ℝ) = 1 + (J : ℝ) := by
    rw [hJ] at e1'
    have : (1 + J : ℝ≥0) = I := by exact_mod_cast e1'
    rw [← this]
    push_cast
    rfl
  refine ⟨J, Eq.trans (lintegral_congr fun ω => tsum_congr fun x => ?_) hJ, ?_⟩
  · by_cases hx : ∀ i, (a : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F
    · rw [Set.indicator_of_mem (by exact hx), thTerm, indL,
        Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, one_mul, ← ofReal_norm, gauss,
        Complex.norm_exp]
      congr 2
      simp [Finset.mul_sum]
    · rw [Set.indicator_of_notMem (by exact hx), thTerm, indL,
        Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, zero_mul, enorm_zero]
  · have hk : 0 < kap F := inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero F)))
    have hsq : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet))
    set v : ℝ := ((N₁ * N₂ : ℕ) : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹ with hv
    have hv0 : 0 < v := by positivity
    have hvD : volume.real D = v := by rw [Measure.real, (hvol D hD).1, ENNReal.toReal_ofReal hv0.le]
    have hph : ∀ x : InfinitePlace F → ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = 1 := fun x => by simp
    have hind : indL (F := F) (ι := ι) a 0 = 1 := by
      have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
        simp only [Pi.zero_apply, mul_zero]
        exact zero_mem _
      simp only [indL, Set.indicator_of_mem hm]
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D)
      (f := fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) -
        eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)))
      (C := C * (a : ℝ) ^ (Module.finrank ℚ F * M)) (by rw [(hvol D hD).1]; exact ENNReal.ofReal_lt_top) fun x _ => by
        rw [hph, mul_one, mul_one]
        exact (hb a ha x).2
    have hi0 : (fun w => ρ w (0 : F)) = fun _ => (0 : ℝ) := by
      funext w
      exact map_zero _
    have hz0 : algebraMap F (A F) 0 = 0 := map_zero _
    have hD1 : ∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = (v : ℂ) := by
      simp_rw [hph]
      simp [setIntegral_const, hvD]
    rw [integral_sub j1 j2, e2, e3, hD1, hind, d5 a ha, i5, hvD, show (volume D).toReal = v from hvD, hi0, hz0] at h2
    have e4 : ((v : ℝ) : ℂ) * ((I : ℝ) : ℂ) - (1 * ((v : ℝ) : ℂ) + ((N₁ * N₂ : ℕ) : ℂ) ^ Module.finrank ℚ F *
        ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df a 0 : ℝ) : ℂ) *
        ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di (fun _ => 0) : ℝ) : ℂ)) =
        ((v * ((J : ℝ) - kap F ^ (2 * M - 1) * Df a 0 * Di fun _ => 0) : ℝ) : ℂ) := by
      rw [hIJ, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        ← Complex.ofReal_sub, show 2 * M - 1 = 2 * M - 2 + 1 by omega, pow_succ, hv]
      congr 1
      field_simp
      ring
    rw [e4, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, mul_comm v] at h2
    exact le_of_mul_le_mul_right h2 hv0

end GlobalTheory.CompanionTheory.SW.Core0
