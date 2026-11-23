import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth

open Matrix Filter Topology GroundTheory.Heights₂.Heights.Regular
open scoped ContDiff

variable {g : ℕ}

def reCoords (z : Fin g → ℂ) : Fin g ⊕ Fin g → ℝ :=
  Sum.elim (fun k => (z k).re) (fun k => (z k).im)

def ofCoords (v : Fin g ⊕ Fin g → ℝ) : Fin g → ℂ :=
  fun k => (v (.inl k) : ℂ) + Complex.I * (v (.inr k) : ℂ)

def realPeriods (p : Fin g ⊕ Fin g → Fin g → ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.of fun s i => reCoords (p i) s

theorem ofCoords_mulVec (p : Fin g ⊕ Fin g → Fin g → ℂ) (x : Fin g ⊕ Fin g → ℝ) :
    ofCoords (realPeriods p *ᵥ x) = ∑ i, (x i : ℂ) • p i := by
  funext k
  simp only [ofCoords, realPeriods, mulVec, dotProduct, Matrix.of_apply, reCoords, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem im_form (H : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → Fin g → ℂ)
    (Em : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (him : ∀ i j, (p i ⬝ᵥ H *ᵥ star (p j)).im = Em i j) (x y : Fin g ⊕ Fin g → ℝ) :
    ((∑ i, (x i : ℂ) • p i) ⬝ᵥ H *ᵥ star (∑ j, (y j : ℂ) • p j)).im = x ⬝ᵥ Em *ᵥ y := by
  have e : (∑ i, (x i : ℂ) • p i) ⬝ᵥ H *ᵥ star (∑ j, (y j : ℂ) • p j)
      = ∑ i, ∑ j, ((x i * y j : ℝ) : ℂ) * (p i ⬝ᵥ H *ᵥ star (p j)) := by
    simp only [star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum, sum_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have r : x ⬝ᵥ Em *ᵥ y = ∑ i, ∑ j, x i * y j * Em i j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, r]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, him]

theorem ofCoords_inl (k : Fin g) : ofCoords (Pi.single (.inl k) 1) = Pi.single k 1 := by
  funext j
  by_cases h : j = k
  · subst h; simp [ofCoords]
  · simp [ofCoords, Pi.single_apply, h]

theorem ofCoords_inr (k : Fin g) : ofCoords (Pi.single (.inr k) 1) = Pi.single k Complex.I := by
  funext j
  by_cases h : j = k
  · subst h; simp [ofCoords]
  · simp [ofCoords, Pi.single_apply, h]

theorem form_single (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (k l : Fin g) :
    (Pi.single k c : Fin g → ℂ) ⬝ᵥ H *ᵥ star (Pi.single l 1 : Fin g → ℂ) = c * H k l := by
  simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq]

def coordForm (p : Fin g ⊕ Fin g → Fin g → ℂ) (Em : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  ((realPeriods p)⁻¹)ᵀ * Em * (realPeriods p)⁻¹

theorem entry_eq (H : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → Fin g → ℂ)
    (Em : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hE : Em.det ≠ 0)
    (him : ∀ i j, (p i ⬝ᵥ H *ᵥ star (p j)).im = Em i j) :
    (realPeriods p).det ≠ 0 ∧ ∀ k l, H k l =
      (coordForm p Em (.inr k) (.inl l) : ℂ) + Complex.I * (coordForm p Em (.inl k) (.inl l) : ℂ) := by
  have key : ∀ x y, (ofCoords (realPeriods p *ᵥ x) ⬝ᵥ H *ᵥ star (ofCoords (realPeriods p *ᵥ y))).im
      = x ⬝ᵥ Em *ᵥ y := fun x y => by
    rw [ofCoords_mulVec, ofCoords_mulVec]
    exact im_form H p Em him x y
  have hdet : (realPeriods p).det ≠ 0 := by
    intro h
    obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    refine hE (Matrix.exists_vecMul_eq_zero_iff.1 ⟨x, hx, ?_⟩)
    funext j
    have h1 := key x (Pi.single j 1)
    have h0 : ofCoords (0 : Fin g ⊕ Fin g → ℝ) = 0 := by
      funext k; simp [ofCoords]
    rw [hAx, h0, zero_dotProduct, Complex.zero_im, Matrix.dotProduct_mulVec] at h1
    simpa using h1.symm
  refine ⟨hdet, ?_⟩
  have hinv : realPeriods p * (realPeriods p)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
  have key2 : ∀ s t, (ofCoords (Pi.single s 1) ⬝ᵥ H *ᵥ star (ofCoords (Pi.single t 1))).im
      = coordForm p Em s t := fun s t => by
    have h1 := key ((realPeriods p)⁻¹ *ᵥ Pi.single s 1) ((realPeriods p)⁻¹ *ᵥ Pi.single t 1)
    rw [mulVec_mulVec, mulVec_mulVec, hinv, one_mulVec, one_mulVec] at h1
    rw [h1]
    have h2 : coordForm p Em s t = (Pi.single s 1 : Fin g ⊕ Fin g → ℝ) ⬝ᵥ
        coordForm p Em *ᵥ Pi.single t 1 := by simp
    rw [h2, coordForm, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec (Pi.single s 1),
      vecMul_transpose]
  intro k l
  have hre := key2 (.inr k) (.inl l)
  have him' := key2 (.inl k) (.inl l)
  rw [ofCoords_inr, ofCoords_inl, form_single] at hre
  rw [ofCoords_inl k, ofCoords_inl l, form_single] at him'
  rw [← hre, ← him']
  apply Complex.ext <;> simp

theorem contDiffAt_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {m : WithTop ℕ∞} {M : X → Matrix ι ι ℝ} {x : X}
    (h : ∀ i j, ContDiffAt ℝ m (fun y => M y i j) x) : ContDiffAt ℝ m (fun y => (M y).det) x := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  exact (contDiffAt_prod fun i _ => h _ _).const_smul _

theorem contDiffAt_inv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {m : WithTop ℕ∞} {M : X → Matrix ι ι ℝ} {x : X}
    (h : ∀ i j, ContDiffAt ℝ m (fun y => M y i j) x) (hx : (M x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ m (fun y => (M y)⁻¹ i j) x := by
  have h1 : ∀ y, (M y)⁻¹ i j = ((M y).det)⁻¹ * ((M y).updateRow j (Pi.single i 1)).det := by
    intro y
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul]
  simp only [h1]
  refine ((contDiffAt_det h).inv hx).mul (contDiffAt_det fun r s => ?_)
  by_cases hr : r = j
  · subst hr
    simpa using contDiffAt_const
  · simpa [Matrix.updateRow_ne hr] using h r s

theorem exists_section {n a : ℕ} (h : a ≤ n) {u₀ : Fin n → ℂ} (hu : u₀ ∈ Flat.punct n a 1) :
    ∃ σ : (Fin n → ℂ) → Fin n → ℂ, ContDiffAt ℝ ∞ σ u₀ ∧
      ∀ᶠ u in 𝓝 u₀, σ u ∈ logCover h ∧ expCover a (σ u) = u := by
  classical
  have hne : ∀ k : Fin n, k.val < a → u₀ k ≠ 0 := hu.2
  refine ⟨fun u k => if k.val < a then Complex.log (u k / u₀ k) + Complex.log (u₀ k) else u k, ?_, ?_⟩
  · refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k.val < a
    · simp only [if_pos hk]
      have hs : u₀ k / u₀ k ∈ Complex.slitPlane := by
        rw [div_self (hne k hk)]; exact Complex.one_mem_slitPlane
      have hq : ContDiffAt ℝ ∞ (fun u : Fin n → ℂ => u k / u₀ k) u₀ :=
        ((contDiff_apply ℝ ℂ k).div_const _).contDiffAt
      exact (((Complex.contDiffAt_log hs).restrict_scalars ℝ).comp u₀ hq).add contDiffAt_const
    · simp only [if_neg hk]
      exact (contDiff_apply ℝ ℂ k).contDiffAt
  · have hP : ∀ᶠ u in 𝓝 u₀, u ∈ Flat.punct n a 1 := (isOpen_punct n a 1).mem_nhds hu
    have hS : ∀ᶠ u in 𝓝 u₀, ∀ k : Fin n, k.val < a → u k / u₀ k ∈ Complex.slitPlane := by
      refine eventually_all.2 fun k => ?_
      by_cases hk : k.val < a
      · have hc : ContinuousAt (fun u : Fin n → ℂ => u k / u₀ k) u₀ :=
          (continuous_apply k).continuousAt.div_const _
        have hs : u₀ k / u₀ k ∈ Complex.slitPlane := by
          rw [div_self (hne k hk)]; exact Complex.one_mem_slitPlane
        filter_upwards [hc.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hs)] with u hu' _ using hu'
      · exact Eventually.of_forall fun u hk' => absurd hk' hk
    filter_upwards [hP, hS] with u hu' hs
    have hlt : ∀ k : Fin n, ‖u k‖ < 1 := fun k =>
      (norm_le_pi_norm u k).trans_lt (mem_ball_zero_iff.1 hu'.1)
    have hexp : ∀ k : Fin n, k.val < a →
        Complex.exp (Complex.log (u k / u₀ k) + Complex.log (u₀ k)) = u k := fun k hk => by
      rw [Complex.exp_add, Complex.exp_log (div_ne_zero (hu'.2 k hk) (hne k hk)), Complex.exp_log (hne k hk),
        div_mul_cancel₀ _ (hne k hk)]
    refine ⟨⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
    · have hi : (Fin.castLE h i).val < a := i.2
      simp only [if_pos hi]
      by_contra hc
      have h1 := hlt (Fin.castLE h i)
      rw [← hexp _ hi, Complex.norm_exp] at h1
      exact absurd (Real.one_le_exp (not_lt.1 hc)) (not_le.2 h1)
    · simp only [if_neg (not_lt.2 hk)]
      exact hlt k
    · funext k
      by_cases hk : k.val < a
      · simp only [expCover, if_pos hk]
        exact hexp k hk
      · simp only [expCover, if_neg hk]

theorem exists_basis {n a : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) :
    ∃ b : Module.Basis (Fin g ⊕ Fin g) ℤ Λ,
      (Matrix.of fun i j => ((L.E (b i) (b j) : ℤ) : ℝ)).det ≠ 0 := by
  haveI := L.free
  haveI := L.fin
  let e : Fin (2 * g) ≃ Fin g ⊕ Fin g := Fintype.equivOfCardEq (by simp [two_mul])
  let b : Module.Basis (Fin g ⊕ Fin g) ℤ Λ := (Module.finBasisOfFinrankEq ℤ Λ L.rank).reindex e
  refine ⟨b, ?_⟩
  choose c hc using fun i => L.unimod.2 (b.coord i)
  let M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := Matrix.of fun i j => L.E (b i) (b j)
  let C : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := Matrix.of fun i j => b.repr (c i) j
  have hCM : C * M = 1 := by
    ext i j
    have h1 : L.E (c i) (b j) = b.coord i (b j) := by rw [hc]
    have h2 : c i = ∑ k, b.repr (c i) k • b k := (b.sum_repr (c i)).symm
    rw [h2] at h1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, C, M, Matrix.of_apply]
    rw [h1]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hCM
    rw [Matrix.det_mul, h0] at this
    simp at this
  have hmap : (Matrix.of fun i j => ((L.E (b i) (b j) : ℤ) : ℝ)) = (Int.castRingHom ℝ).mapMatrix M := by
    ext i j
    simp [M]
  rw [hmap, ← RingHom.map_det]
  simpa using hdet

theorem isOpen_cover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have e : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w
    simp [logCover]
  rw [e]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (by fun_prop) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (f := fun w : Fin n → ℂ => ‖w k‖) (by fun_prop) continuous_const
    · simp [hk]

theorem contDiffAt_period {n a : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (x : Λ)
    {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : ContDiffAt ℝ ∞ (fun w => L.P w x) w :=
  ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn (isOpen_cover L.a_le) (L.hol x)).contDiffAt
    ((isOpen_cover L.a_le).mem_nhds hw)).restrict_scalars ℝ

theorem contDiffAt_realPeriods {n a : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (b : Fin g ⊕ Fin g → Λ) {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) (s i : Fin g ⊕ Fin g) :
    ContDiffAt ℝ ∞ (fun w => realPeriods (fun i => L.P w (b i)) s i) w := by
  have h := contDiffAt_pi.1 (contDiffAt_period L (b i) hw)
  rcases s with k | k
  · exact Complex.reCLM.contDiff.contDiffAt.comp w (h k)
  · exact Complex.imCLM.contDiff.contDiffAt.comp w (h k)

theorem contDiffAt_H {n a : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    {u₀ : Fin n → ℂ} (hu : u₀ ∈ Flat.punct n a 1) (k l : Fin g) :
    ContDiffAt ℝ ∞ (fun u => L.H u k l) u₀ := by
  obtain ⟨b, hb⟩ := exists_basis L
  obtain ⟨σ, hσ, hev⟩ := exists_section L.a_le hu
  have hw₀ : σ u₀ ∈ logCover L.a_le := hev.self_of_nhds.1
  let Em : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ := Matrix.of fun i j => ((L.E (b i) (b j) : ℤ) : ℝ)
  let p : (Fin n → ℂ) → Fin g ⊕ Fin g → Fin g → ℂ := fun w i => L.P w (b i)
  have hall : ∀ w ∈ logCover L.a_le, (realPeriods (p w)).det ≠ 0 ∧ ∀ k l, L.H (expCover a w) k l =
      (coordForm (p w) Em (.inr k) (.inl l) : ℂ) + Complex.I * (coordForm (p w) Em (.inl k) (.inl l) : ℂ) :=
    fun w hw => entry_eq _ (p w) Em hb fun i j => L.im w hw (b i) (b j)
  have hA : ∀ s i, ContDiffAt ℝ ∞ (fun w => realPeriods (p w) s i) (σ u₀) :=
    fun s i => contDiffAt_realPeriods L b hw₀ s i
  have hB := contDiffAt_inv hA (hall _ hw₀).1
  have hC : ∀ s t, ContDiffAt ℝ ∞ (fun w => coordForm (p w) Em s t) (σ u₀) := by
    intro s t
    simp only [coordForm, Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffAt.sum fun j _ => (ContDiffAt.sum fun i _ => (hB i s).mul contDiffAt_const).mul (hB j t)
  have hc : ∀ s t, ContDiffAt ℝ ∞ (fun w => (coordForm (p w) Em s t : ℂ)) (σ u₀) := fun s t =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC s t)
  have hF : ContDiffAt ℝ ∞ (fun w => (coordForm (p w) Em (.inr k) (.inl l) : ℂ) +
      Complex.I * (coordForm (p w) Em (.inl k) (.inl l) : ℂ)) (σ u₀) :=
    (hc _ _).add (contDiffAt_const.mul (hc _ _))
  refine (ContDiffAt.comp u₀ hF hσ).congr_of_eventuallyEq ?_
  filter_upwards [hev] with u hu'
  have h1 := (hall _ hu'.1).2 k l
  rw [hu'.2] at h1
  exact h1

theorem periodGram_contDiffAt : ∀ (n a₀ g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) →
    ∀ (p q : Fin r), ∀ u ∈ Flat.punct n a₀ 1,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u' => HodgeMetric.periodGram L U u' p q) u := by
  intro n a₀ g r Λ _ L U hU p q u hu
  have hUs : ∀ k, ContDiffAt ℝ ∞ (U k) u := fun k =>
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn Metric.isOpen_ball (hU k)).contDiffAt
      (Metric.isOpen_ball.mem_nhds hu.1)).restrict_scalars ℝ
  have hc : ∀ k i, ContDiffAt ℝ ∞ (fun u' => U k u' i) u := fun k => contDiffAt_pi.1 (hUs k)
  have hs : ∀ k i, ContDiffAt ℝ ∞ (fun u' => (starRingEnd ℂ) (U k u' i)) u := fun k i =>
    (Complex.conjCLE.contDiff (𝕜 := ℝ)).contDiffAt.comp u (hc k i)
  simp only [HodgeMetric.periodGram, Matrix.of_apply, dotProduct, mulVec, Pi.star_apply,
    Complex.star_def]
  refine contDiffAt_const.mul (ContDiffAt.sum fun k _ => (hc q k).mul (ContDiffAt.sum fun l _ => ?_))
  exact (contDiffAt_H L hu k l).mul (hs p l)

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth
