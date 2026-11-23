import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothConv

theorem contDiff_param_integral {X E P : Type} [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P]
    [NormedSpace ℝ P] {e : X → E} (he : MeasurableEmbedding e) {f : X → ℂ} (hf : Integrable f μ) {K : Set E}
    (hK : IsCompact K) (hfK : ∀ x, e x ∉ K → f x = 0) {Φ : P × E → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ fun p => ∫ x, f x * Φ (p, e x) ∂μ := by
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR0, by linarith⟩
  have hf' : Integrable (Function.extend e f 0) (μ.map e) := by
    rw [he.integrable_map_iff]
    have : Function.extend e f 0 ∘ e = f := Function.extend_comp he.injective _ _
    rwa [this]
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℂ) (s := (Set.univ : Set P)) (v := fun _ => (0 : E)) contDiffOn_const
    (f := Function.extend e f 0) (μ := μ.map e) (g := fun p z => (χ (-z) : ℂ) * Φ (p, -z))
    (k := Metric.closedBall 0 (R + 1)) isOpen_univ (isCompact_closedBall _ _) ?_ hf'.locallyIntegrable ?_
  · rw [contDiffOn_univ] at key
    convert key using 2 with p
    rw [convolution_def, he.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [he.injective.extend_apply, zero_sub, neg_neg, ContinuousLinearMap.mul_apply']
    by_cases hx : e x ∈ K
    · rw [χ.one_of_mem_closedBall (hR hx)]; simp
    · simp [hfK x hx]
  · intro p z _ hz
    have : χ (-z) = 0 := by
      apply χ.zero_of_le_dist
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      simpa [χ] using hz.le
    simp [this]
  · refine ContDiff.contDiffOn ?_
    have h1 : ContDiff ℝ ∞ fun q : P × E => ((χ (-q.2) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd.neg)
    exact h1.mul (hΦ.comp (contDiff_fst.prodMk contDiff_snd.neg))

section Entry

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}

def EntrySmoothAt (f : P → Matrix (Fin n) (Fin n) ℂ) (x : P) : Prop :=
  ∀ i j, ContDiffAt ℝ ∞ (fun y => f y i j) x

variable {f g : P → Matrix (Fin n) (Fin n) ℂ} {x : P}

theorem EntrySmoothAt.const (c : Matrix (Fin n) (Fin n) ℂ) : EntrySmoothAt (fun _ => c) x :=
  fun _ _ => contDiffAt_const

theorem EntrySmoothAt.add (hf : EntrySmoothAt f x) (hg : EntrySmoothAt g x) :
    EntrySmoothAt (fun y => f y + g y) x := fun i j => (hf i j).add (hg i j)

theorem EntrySmoothAt.sub (hf : EntrySmoothAt f x) (hg : EntrySmoothAt g x) :
    EntrySmoothAt (fun y => f y - g y) x := fun i j => (hf i j).sub (hg i j)

theorem EntrySmoothAt.smul (c : ℂ) (hf : EntrySmoothAt f x) :
    EntrySmoothAt (fun y => c • f y) x := fun i j => contDiffAt_const.mul (hf i j)

theorem EntrySmoothAt.mul (hf : EntrySmoothAt f x) (hg : EntrySmoothAt g x) :
    EntrySmoothAt (fun y => f y * g y) x := fun i j => by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (hf i k).mul (hg k j)

theorem EntrySmoothAt.conjTranspose (hf : EntrySmoothAt f x) : EntrySmoothAt (fun y => (f y)ᴴ) x :=
  fun i j => Complex.conjCLE.contDiff.contDiffAt.comp x (hf j i)

theorem EntrySmoothAt.det (hf : EntrySmoothAt f x) : ContDiffAt ℝ ∞ (fun y => (f y).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hf _ _)

theorem EntrySmoothAt.inv (hf : EntrySmoothAt f x) (h : (f x).det ≠ 0) :
    EntrySmoothAt (fun y => (f y)⁻¹) x := fun i j => by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine (hf.det.inv h).mul (EntrySmoothAt.det fun k l => ?_)
  by_cases hk : k = j
  · subst hk; simp only [Matrix.updateRow_self]; exact contDiffAt_const
  · simp only [Matrix.updateRow_ne hk]; exact hf k l

end Entry

section Cayley

variable {n : ℕ} (ε : Fin n → Bool)

def adj (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Jm ε * Xᴴ * Jm ε

def cay (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 - X) * (1 + X)⁻¹

def skew (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (X - adj ε X)

theorem adj_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : adj ε (X * Y) = adj ε Y * adj ε X := by
  simp only [adj, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_mul_self, Matrix.one_mul]

theorem adj_one : adj ε 1 = 1 := by simp [adj, Jm_mul_self]

theorem adj_add (X Y : Matrix (Fin n) (Fin n) ℂ) : adj ε (X + Y) = adj ε X + adj ε Y := by
  simp [adj, Matrix.mul_add, Matrix.add_mul]

theorem adj_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : adj ε (X - Y) = adj ε X - adj ε Y := by
  simp [adj, Matrix.mul_sub, Matrix.sub_mul]

theorem adj_adj (X : Matrix (Fin n) (Fin n) ℂ) : adj ε (adj ε X) = X := by
  simp only [adj, conjTranspose_mul, Matrix.mul_assoc, Jm_conjTranspose, conjTranspose_conjTranspose,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_mul_self, Matrix.one_mul]

theorem adj_skew (X : Matrix (Fin n) (Fin n) ℂ) : adj ε (skew ε X) = -skew ε X := by
  have : adj ε (skew ε X) = (2⁻¹ : ℂ) • adj ε (X - adj ε X) := by
    simp only [skew, adj, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
    simp
  rw [this, adj_sub, adj_adj, skew, ← smul_neg, neg_sub]

theorem inUJ_iff (g : Matrix (Fin n) (Fin n) ℂ) : inUJ ε g ↔ adj ε g * g = 1 := by
  constructor
  · intro h; exact (uJInv n ε g h).2
  · intro h
    have := congrArg (Jm ε * ·) h
    simp only [adj, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, Matrix.mul_one] at this
    exact this

theorem inUJ_cay {X : Matrix (Fin n) (Fin n) ℂ} (hX : adj ε X = -X) (h : (1 + X).det ≠ 0) :
    inUJ ε (cay X) := by
  have h1 : (1 + X) * (1 + X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit h)
  rw [inUJ_iff, cay]
  generalize (1 + X)⁻¹ = W at h1
  have h2 := congrArg (adj ε) h1
  rw [adj_mul, adj_add, adj_one, hX] at h2
  rw [adj_mul, adj_sub, adj_one, hX]
  calc _ = adj ε W * (1 + -X) * ((1 + X) * W) := by noncomm_ring
    _ = 1 := by rw [h1, h2, mul_one]

theorem skew_cay {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (h : (1 + g).det ≠ 0) :
    skew ε (cay g) = cay g := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit h)
  rw [inUJ_iff] at hg
  have : adj ε (cay g) = -cay g := by
    rw [cay]
    generalize (1 + g)⁻¹ = W at h1
    have h2 := congrArg (adj ε) h1
    rw [adj_mul, adj_add, adj_one] at h2
    rw [adj_mul, adj_sub, adj_one]
    have h3 : (1 + adj ε g) * (-((1 - g) * W)) = 1 - adj ε g := by
      calc _ = (adj ε g * g + adj ε g) * (-((1 - g) * W)) := by rw [hg]
        _ = -(adj ε g - adj ε g * g) * ((1 + g) * W) := by noncomm_ring
        _ = _ := by rw [h1, hg, mul_one, neg_sub]
    rw [← h3, ← mul_assoc, h2, one_mul]
  rw [skew, this, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  simp

theorem cay_cay {g : Matrix (Fin n) (Fin n) ℂ} (h : (1 + g).det ≠ 0) : cay (cay g) = g := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit h)
  have h2 : (1 + g)⁻¹ * (1 + g) = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit h)
  rw [cay, cay]
  generalize (1 + g)⁻¹ = W at h1 h2
  have h3 : 1 + (1 - g) * W = (2 : ℂ) • W := by
    rw [two_smul]; nth_rewrite 1 [← h1]; noncomm_ring
  have h4 : 1 - (1 - g) * W = (2 : ℂ) • (g * W) := by
    rw [two_smul]; nth_rewrite 1 [← h1]; noncomm_ring
  have h5 : ((2 : ℂ) • W)⁻¹ = (2⁻¹ : ℂ) • (1 + g) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2]; simp
  rw [h3, h4, h5, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc, h2]; simp

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → Matrix (Fin n) (Fin n) ℂ} {x : P}

theorem EntrySmoothAt.adj (hf : EntrySmoothAt f x) : EntrySmoothAt (fun y => adj ε (f y)) x :=
  ((EntrySmoothAt.const _).mul hf.conjTranspose).mul (EntrySmoothAt.const _)

theorem EntrySmoothAt.skew (hf : EntrySmoothAt f x) : EntrySmoothAt (fun y => skew ε (f y)) x :=
  (hf.sub (hf.adj ε)).smul _

theorem EntrySmoothAt.cay (hf : EntrySmoothAt f x) (h : (1 + f x).det ≠ 0) :
    EntrySmoothAt (fun y => cay (f y)) x :=
  ((EntrySmoothAt.const _).sub hf).mul (((EntrySmoothAt.const _).add hf).inv h)

end Cayley

theorem uMat_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ = adj ε (uMat g) := by
  have h1 : adj ε (uMat g) * uMat g = 1 := (inUJ_iff ε _).1 g.2
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    have : uMat g * uMat g⁻¹ = uMat (g * g⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  calc uMat g⁻¹ = adj ε (uMat g) * uMat g * uMat g⁻¹ := by rw [h1, one_mul]
    _ = _ := by rw [mul_assoc, h2, mul_one]

theorem exists_retraction {n : ℕ} {ε : Fin n → Bool} (x : UJ ε) :
    ∃ ρ : (Fin n → Fin n → ℂ) → UJ ε, ∀ᶠ Y in 𝓝 (fun i j => uMat x i j),
      EntrySmoothAt (fun Z => uMat (ρ Z)) Y ∧ ∀ g : UJ ε, (fun i j => uMat g i j) = Y → ρ Y = g := by
  classical
  obtain ⟨hemb, hrange⟩ := uJEmb n ε
  let t : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ := fun Y => uMat x⁻¹ * Matrix.of Y
  have ht : ∀ Y, EntrySmoothAt t Y := fun Y =>
    (EntrySmoothAt.const _).mul fun i j => by simp only [Matrix.of_apply]; fun_prop
  have htg : ∀ g : UJ ε, t (fun i j => uMat g i j) = uMat (x⁻¹ * g) := fun g => rfl
  have htx : t (fun i j => uMat x i j) = 1 := by rw [htg, inv_mul_cancel]; rfl
  have hx1 : (1 + t (fun i j => uMat x i j)).det ≠ 0 := by
    rw [htx, ← two_smul ℂ, Matrix.det_smul]; simp
  have hx2 : (1 + skew ε (cay (t (fun i j => uMat x i j)))).det ≠ 0 := by
    rw [htx]; simp [cay, skew, adj]
  have hev : ∀ᶠ Y in 𝓝 (fun i j => uMat x i j), (1 + t Y).det ≠ 0 ∧ (1 + skew ε (cay (t Y))).det ≠ 0 :=
    (((EntrySmoothAt.const 1).add (ht _)).det.continuousAt.eventually_ne hx1).and
      (((EntrySmoothAt.const 1).add (((ht _).cay hx1).skew ε)).det.continuousAt.eventually_ne hx2)
  have hex : ∀ Y, (1 + skew ε (cay (t Y))).det ≠ 0 → ∃ u : UJ ε, uMat u = cay (skew ε (cay (t Y))) := by
    intro Y hY
    have : cay (skew ε (cay (t Y))) ∈ {g | inUJ ε g} := inUJ_cay ε (adj_skew ε _) hY
    rw [← hrange] at this
    exact this
  let r : (Fin n → Fin n → ℂ) → UJ ε := fun Y =>
    if h : (1 + skew ε (cay (t Y))).det ≠ 0 then (hex Y h).choose else 1
  have hr : ∀ Y, (1 + skew ε (cay (t Y))).det ≠ 0 → uMat (r Y) = cay (skew ε (cay (t Y))) := by
    intro Y hY
    simp only [r, dif_pos hY]
    exact (hex Y hY).choose_spec
  refine ⟨fun Y => x * r Y, ?_⟩
  filter_upwards [hev.eventually_nhds] with Y hY
  have hY0 := hY.self_of_nhds
  constructor
  · have h1 : EntrySmoothAt (fun Z => uMat x * cay (skew ε (cay (t Z)))) Y :=
      (EntrySmoothAt.const _).mul (((((ht Y).cay hY0.1).skew ε)).cay hY0.2)
    intro i j
    refine (h1 i j).congr_of_eventuallyEq ?_
    filter_upwards [hY] with Z hZ
    rw [← hr Z hZ.2]; rfl
  · rintro g rfl
    have h1 := hr _ hY0.2
    have h2 := hY0.1
    rw [htg] at h1 h2
    rw [skew_cay ε (x⁻¹ * g).2 h2, cay_cay h2] at h1
    have h3 : r (fun i j => uMat g i j) = x⁻¹ * g := hemb.injective h1
    rw [h3, mul_inv_cancel_left]

variable (I : AutInst)

def emb (g : I.Ginf) : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ := fun v i j => uMat (g v) i j

theorem isClosedEmbedding_emb : Topology.IsClosedEmbedding (emb I) :=
  Topology.IsClosedEmbedding.piMap (f := fun v (g : UJ (I.ε v)) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ))
    fun v => (uJEmb I.n (I.ε v)).1

theorem exists_contDiff_extension {a : I.Ginf → ℂ} (ha : SmoothInf I a) :
    ∃ A : (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) → ℂ, ContDiff ℝ ∞ A ∧ ∀ g, A (emb I g) = a g := by
  have hemb := isClosedEmbedding_emb I
  obtain ⟨A, hA, hAa⟩ := GlobalTheory.exists_contDiff_extension_of_isClosed hemb.isClosed_range
    (Function.extend (emb I) a 0) (by
      rintro _ ⟨x, rfl⟩
      choose ρ hρ using fun v => exists_retraction (x v)
      have hev : ∀ᶠ Y in 𝓝 (emb I x), ∀ v, EntrySmoothAt (fun Z => uMat (ρ v Z)) (Y v) ∧
          ∀ g : UJ (I.ε v), (fun i j => uMat g i j) = Y v → ρ v (Y v) = g :=
        Filter.eventually_all.2 fun v => ((continuous_apply v).tendsto (emb I x)).eventually (hρ v)
      obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 hev
      let R : (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) → I.Ginf := fun Y v => ρ v (Y v)
      refine ⟨U, fun Y => a (R Y), hUo, hxU, fun Y hY => ContDiffAt.contDiffWithinAt ?_, ?_⟩
      · have h1 : ContDiffAt ℝ ∞ (fun Z => emb I (R Z)) Y := by
          refine contDiffAt_pi.2 fun v => contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
          exact ((hU Y hY v).1 i j).comp Y (contDiffAt_apply ℝ _ v Y)
        have h2 : ContinuousAt R Y := hemb.isInducing.continuousAt_iff.2 h1.continuousAt
        obtain ⟨F, hF, hFa⟩ := ha (R Y)
        exact (ContDiffAt.comp (g := F) Y hF h1).congr_of_eventuallyEq (h2.eventually hFa)
      · rintro _ hy ⟨g, rfl⟩
        rw [hemb.injective.extend_apply]
        congr 1
        funext v
        exact ((hU _ hy v).2 (g v) rfl).symm)
  exact ⟨A, hA, fun g => by rw [hAa _ ⟨g, rfl⟩, hemb.injective.extend_apply]⟩

theorem continuous_of_smoothInf {a : I.Ginf → ℂ} (ha : SmoothInf I a) : Continuous a := by
  obtain ⟨A, hA, hAa⟩ := exists_contDiff_extension I ha
  have : a = A ∘ emb I := funext fun g => (hAa g).symm
  rw [this]
  exact hA.continuous.comp (isClosedEmbedding_emb I).continuous

theorem smoothInf_conv {a F : I.Ginf → ℂ} (ha : SmoothInf I a) (hc : HasCompactSupport a)
    (hF : LocallyIntegrable F (muInf I)) :
    SmoothInf I (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) := by
  intro x
  have hemb := isClosedEmbedding_emb I
  obtain ⟨A, hA, hAa⟩ := exists_contDiff_extension I ha
  obtain ⟨N, hN, hxN⟩ := exists_compact_mem_nhds x
  have hK : IsCompact ((fun p : I.Ginf × I.Ginf => p.1 * p.2) '' (N ×ˢ tsupport a)) :=
    (hN.prod hc).image continuous_mul
  set K := (fun p : I.Ginf × I.Ginf => p.1 * p.2) '' (N ×ˢ tsupport a) with hKdef
  have hint : Integrable (K.indicator F) (muInf I) :=
    (integrable_indicator_iff hK.isClosed.measurableSet).2 (hF.integrableOn_isCompact hK)
  let m : (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) × (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) →
      InfinitePlace I.F → Fin I.n → Fin I.n → ℂ :=
    fun q v i j => (adj (I.ε v) (Matrix.of (q.1 v)) * Matrix.of (q.2 v)) i j
  have hm : ContDiff ℝ ∞ m := by
    refine contDiff_iff_contDiffAt.2 fun q => contDiffAt_pi.2 fun v => contDiffAt_pi.2 fun i =>
      contDiffAt_pi.2 fun j => ?_
    refine EntrySmoothAt.mul (EntrySmoothAt.adj _ fun k l => ?_) (fun k l => ?_) i j <;>
    · simp only [Matrix.of_apply]; fun_prop
  have hmg : ∀ y g, m (emb I y, emb I g) = emb I (y⁻¹ * g) := by
    intro y g
    funext v i j
    change (adj (I.ε v) (uMat (y v)) * uMat (g v)) i j = (uMat (y v)⁻¹ * uMat (g v)) i j
    rw [uMat_inv]
  have key := contDiff_param_integral (muInf I) hemb.measurableEmbedding hint (hK.image hemb.continuous)
    (fun g hg => Set.indicator_of_notMem (fun h => hg ⟨g, h, rfl⟩) _) (hA.comp hm)
  refine ⟨_, key.contDiffAt, ?_⟩
  filter_upwards [hxN] with y hy
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change F g * a (y⁻¹ * g) = K.indicator F g * A (m (emb I y, emb I g))
  rw [hmg, hAa]
  by_cases hg : g ∈ K
  · rw [Set.indicator_of_mem hg]
  · have : a (y⁻¹ * g) = 0 := by
      by_contra h
      exact hg ⟨(y, y⁻¹ * g), ⟨hy, subset_tsupport _ h⟩, mul_inv_cancel_left y g⟩
    simp [this]

theorem smooth_convolution : ∀ (I : AutInst) (a F : I.Ginf → ℂ), SmoothInf I a → HasCompactSupport a →
    LocallyIntegrable F (muInf I) → SmoothInf I (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) ∧
      Continuous (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) :=
  fun I _ _ ha hc hF => ⟨smoothInf_conv I ha hc hF, continuous_of_smoothInf I (smoothInf_conv I ha hc hF)⟩

end GlobalTheory.SmoothConv
