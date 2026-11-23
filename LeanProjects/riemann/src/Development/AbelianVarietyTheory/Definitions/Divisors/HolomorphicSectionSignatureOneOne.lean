import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.AdelLeftInvAndContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDefinite
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Local

open ReciprocityTheory.ChartRestriction.G.FD

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sgn_sq (q a : ℕ) : sgn q a * sgn q a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem OrthFr.det_ne {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : x₀.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det h.2
  rw [det_mul, h0, mul_zero, det_diagonal] at h1
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
  have h2 := sgn_sq q a
  rw [neg_eq_zero, Complex.ofReal_eq_zero] at ha
  simp [ha] at h2

theorem OrthFr.mem {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : x₀ ∈ frDom Hm q := by
  refine ⟨OrthFr.det_ne h, fun i => ?_⟩
  have e : lminor (-(x₀ᴴ * Hm * x₀)) i = ((psgn q i : ℝ) : ℂ) := by
    rw [h.2, diagonal_neg, lminor, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal, psgn,
      ← Fin.prod_univ_eq_prod_range]
    simp
  rw [e, Complex.ofReal_re, psgn, ← Finset.prod_mul_distrib]
  simp [sgn_sq]

theorem mul_mem_frDom {Hm u x : Mt n} {q : ℕ} (hH : Hm.det ≠ 0) (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    u * x ∈ frDom Hm q := by
  have hu' : uᴴ * Hm * u = Hm := hu
  have hd : u.det ≠ 0 := fun h0 => hH (by rw [← hu', det_mul, h0, mul_zero])
  refine ⟨by rw [det_mul]; exact mul_ne_zero hd hx.1, fun i => ?_⟩
  have e : (u * x)ᴴ * Hm * (u * x) = xᴴ * Hm * x := by
    conv_rhs => rw [← hu']
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  exact hx.2 i

theorem torEl_mem {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s : ι → Fin n → ℝ) :
    torEl x₀ s ∈ UG Hm := by
  intro τ
  have hd : IsUnit (x₀ τ).det := (OrthFr.det_ne (h τ)).isUnit
  have h1 : x₀ τ * (x₀ τ)⁻¹ = 1 := mul_nonsing_inv _ hd
  set d : Mt n := diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) with hdd
  have h2 : dᴴ * ((x₀ τ)ᴴ * Hm τ * x₀ τ) * d = (x₀ τ)ᴴ * Hm τ * x₀ τ := by
    rw [(h τ).2, hdd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have : star (Complex.exp ((s τ a : ℂ) * Complex.I)) * Complex.exp ((s τ a : ℂ) * Complex.I) = 1 := by
      rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      simp
    simp only [Pi.star_apply]
    linear_combination (-((sgn (q τ) (a : ℕ) : ℝ) : ℂ)) * this
  show (x₀ τ * d * (x₀ τ)⁻¹)ᴴ * Hm τ * (x₀ τ * d * (x₀ τ)⁻¹) = Hm τ
  calc _ = ((x₀ τ)⁻¹)ᴴ * (dᴴ * ((x₀ τ)ᴴ * Hm τ * x₀ τ) * d) * (x₀ τ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (x₀ τ * (x₀ τ)⁻¹)ᴴ * Hm τ * (x₀ τ * (x₀ τ)⁻¹) := by
        rw [h2]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem HolFn.torus {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {w : ι → Fin n → ℤ}
    {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (s : ι → Fin n → ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    f (u * torEl x₀ s) = torCh w s * f u := by
  obtain ⟨P, hP, hfP⟩ := hf
  have hH : ∀ τ, (Hm τ).det ≠ 0 := fun τ h0 => by
    have h1 := (OrthFr.mem (h τ)).2 (Fin.last n)
    have e : lminor (-((x₀ τ)ᴴ * Hm τ * x₀ τ)) (Fin.last n) = (-((x₀ τ)ᴴ * Hm τ * x₀ τ)).det := rfl
    rw [e, det_neg, det_mul, det_mul, h0] at h1
    simp at h1
  have hm : u * torEl x₀ s ∈ UG Hm := fun τ => by
    have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
    have h2 : (torEl x₀ s τ)ᴴ * Hm τ * torEl x₀ s τ = Hm τ := torEl_mem h s τ
    show (u τ * torEl x₀ s τ)ᴴ * Hm τ * (u τ * torEl x₀ s τ) = Hm τ
    conv_rhs => rw [← h2, ← h1]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have key := hP.2 (fun τ => (u τ * x₀ τ : Mt n)) (fun τ => mul_mem_frDom (hH τ) (hu τ) (OrthFr.mem (h τ)))
    (fun τ => diagonal fun a => Complex.exp ((s τ a : ℂ) * Complex.I))
    (fun τ => ⟨by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _,
      fun a c hac => diagonal_apply_ne _ hac.ne'⟩)
  rw [hfP _ hm, hfP _ hu]
  simp only [diagonal_apply_eq] at key
  refine Eq.trans (congrArg P (funext fun τ => ?_)) key
  show u τ * (x₀ τ * _ * (x₀ τ)⁻¹) * x₀ τ = u τ * x₀ τ * _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ (OrthFr.det_ne (h τ)).isUnit, Matrix.mul_one,
    Matrix.mul_assoc]

theorem weight_eq_zero_of_const {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {w : ι → Fin n → ℤ}
    (hf : HolFn Hm q x₀ w fun _ => 1) (s : ι → Fin n → ℝ) : torCh w s = 1 := by
  have := HolFn.torus h hf s (u := 1) (fun τ => by show (1 : Mt n)ᴴ * _ * 1 = _; simp)
  simpa using this.symm

theorem holFn_const (Hm x₀ : ι → Mt n) (q : ι → ℕ) (z : ℂ) : HolFn Hm q x₀ 0 fun _ => z :=
  ⟨fun _ => z, ⟨differentiableOn_const _, fun _ _ _ _ => by simp⟩, fun _ _ => rfl⟩

def H11 : Unit → Mt 2 := fun _ => !![1, 0; 0, -1]

def x11 : Unit → Mt 2 := fun _ => !![0, 1; 1, 0]

theorem orthFrame_signatureOneOne (τ : Unit) : OrthFr (H11 τ) 1 (x11 τ) := by
  refine ⟨by norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [H11, x11, sgn, Matrix.mul_apply, Fin.sum_univ_two]

theorem ne_zero_of_mem_frameDomain {x : Mt 2} (hx : x ∈ frDom (H11 ()) 1) : x 1 0 ≠ 0 := by
  intro h0
  have h1 := hx.2 1
  have e : lminor (-(xᴴ * H11 () * x)) 1 = -(xᴴ * H11 () * x) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  rw [e] at h1
  simp [psgn, sgn, H11, Matrix.mul_apply, Fin.sum_univ_two, h0] at h1
  nlinarith [mul_self_nonneg (x 0 0).re, mul_self_nonneg (x 0 0).im]

theorem holomorphicSection_signatureOneOne (k : ℤ) : HolSec H11 (fun _ => 1) (fun _ => ![-k, 0]) fun x => x () 1 0 ^ (-k) := by
  refine ⟨fun x hx => ?_, fun x _ b hb => ?_⟩
  · have h0 : x () 1 0 ≠ 0 := ne_zero_of_mem_frameDomain (hx ())
    have h1 : DifferentiableAt ℂ (fun y : Unit → Fin 2 → Fin 2 → ℂ => y () 1 0) x := by fun_prop
    exact (h1.zpow (Or.inl h0)).differentiableWithinAt
  · have h10 : b () 1 0 = 0 := (hb ()).2 1 0 (by decide)
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, Fin.prod_univ_two, mul_zpow, mul_comm]

theorem holomorphicFunction_lowestVector (k : ℤ) : HolFn H11 (fun _ => 1) x11 (fun _ => ![-k, 0]) fun u => u () 1 1 ^ (-k) :=
  ⟨_, holomorphicSection_signatureOneOne k, fun u _ => by simp [x11, Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem norm_lowestCoefficient_le_one (k : ℕ) {u : Unit → Mt 2} (hu : u ∈ UG H11) : ‖u () 1 1 ^ (-(k : ℤ))‖ ≤ 1 := by
  have h : (u ())ᴴ * H11 () * u () = H11 () := hu ()
  have h1 := congrArg Complex.re (congrFun (congrFun h 1) 1)
  simp [H11, Matrix.mul_apply, Fin.sum_univ_two] at h1
  have h2 : 1 ≤ ‖u () 1 1‖ := by
    have : 1 ≤ ‖u () 1 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [mul_self_nonneg (u () 0 1).re, mul_self_nonneg (u () 0 1).im]
    nlinarith [norm_nonneg (u () 1 1)]
  rw [norm_zpow, _root_.zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h2)

theorem exp_one_one (z : ℂ) : (NormedSpace.exp (z • (1 : Mt 1)) : Mt 1) 0 0 = Complex.exp z := by
  have : z • (1 : Mt 1) = diagonal fun _ => z := by
    ext a b
    fin_cases a; fin_cases b; simp
  rw [this, Matrix.exp_diagonal, diagonal_apply_eq, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem der_pow (k : ℕ) (z : ℂ) (u : Unit → Mt 1) :
    der () (z • (1 : Mt 1)) (fun v => v () 0 0 ^ k) u = k * z * u () 0 0 ^ k := by
  have e : (fun t : ℝ => (fun v : Unit → Mt 1 => v () 0 0 ^ k)
      (u * (Pi.mulSingle () (NormedSpace.exp (t • z • (1 : Mt 1))) : Unit → Mt 1))) =
      fun t : ℝ => u () 0 0 ^ k * Complex.exp (k * z * t) := by
    funext t
    have h1 : t • z • (1 : Mt 1) = ((t : ℂ) * z) • (1 : Mt 1) := by
      rw [← smul_assoc, Complex.real_smul]
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Matrix.mul_apply, Fin.sum_univ_one, h1]
    rw [exp_one_one, mul_pow, ← Complex.exp_nat_mul]
    ring_nf
  unfold der
  rw [e]
  have h := (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul ((k : ℂ) * z)).cexp).const_mul (u () 0 0 ^ k)
  refine h.deriv.trans ?_
  simp
  ring

theorem killedFn_pow (k : ℕ) : KilledFn (fun _ : Unit => (1 : Mt 1)) (fun _ => 1) (fun _ _ => (k : ℤ)) fun v => v () 0 0 ^ k := by
  intro τ a c _ u _
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  have e : (1 : Mt 1) * Matrix.single 0 0 1 * (1 : Mt 1)⁻¹ = 1 := by
    ext a b
    fin_cases a; fin_cases b; simp
  have e1 : (1 / 2 : ℂ) • ((1 : Mt 1) + conjH 1 1) = (0 : ℂ) • (1 : Mt 1) := by simp [conjH]
  have e2 : (1 / (2 * Complex.I)) • ((1 : Mt 1) - conjH 1 1) = (-Complex.I) • (1 : Mt 1) := by
    ext a b
    fin_cases a; fin_cases b
    simp [conjH]
    ring
  show derC _ () ((1 : Mt 1) * Matrix.single 0 0 1 * (1 : Mt 1)⁻¹) _ u = _
  rw [e]
  unfold derC
  rw [e1, e2, der_pow, der_pow, if_pos rfl]
  simp only [Int.cast_natCast]
  linear_combination (-(k : ℂ) * u () 0 0 ^ k) * Complex.I_mul_I

end Local

section Adelic

variable {D : D7}

theorem exists_finPair (V : HSp D) (hs : V.SigOK) : ∃ μ 𝓕, FinPair V μ 𝓕 ∧ μ 𝓕 ≠ 0 := by
  obtain ⟨hex, h0, h1⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := volPair_isVolPair V hex
  rw [muQ_univ] at h0 h1
  exact ⟨_, _, ⟨hp.1.1, GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ hp.1.1, hp.2, h1⟩, h0⟩

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩

theorem orthFr_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (hM : HolShape M) (τ : D.what₂.Tau) :
    OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := by
  obtain ⟨-, p, hp, hε⟩ := hM τ
  refine ⟨nNeg_le _, ?_⟩
  have hinv : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have h1 : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      (((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h2, h1, nNeg_shape hp hε]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

end Adelic

section Dict

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member

variable {D : D7}

theorem tauE_inj : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_model (V : HSp D) (ρ : D.what₂.Tau) (x : Mt V.rank) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply, conjTranspose_apply,
    gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

open Classical in

def plOf {β : Type} (b : β) (f : D.what₂.Tau → β) (τ : D.host.E →+* ℂ) : β :=
  if h : ∃ ρ, τ = tauE D ρ then f h.choose else b

theorem plOf_tauE {β : Type} (b : β) (f : D.what₂.Tau → β) (ρ : D.what₂.Tau) : plOf b f (tauE D ρ) = f ρ := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [plOf, dif_pos h, ← tauE_inj h.choose_spec]

theorem goodDict_of_ctx {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {V : HSp D} (C : Ctx Xo c σ V V.rank) (hC : C.OK) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hM : HolShape M) (hq : ∀ ρ, nNeg (M.ε ρ) = Dw.q) (w : D.what₂.Tau → Fin V.rank → ℤ) :
    ∃ θ dict Kf, IsLevelK V l.M Kf ∧
      GoodDict θ M w rfl C.M.X (fun _ τ => plOf 0 w τ.1) dict (fun _ => 1) (fun _ => 1) Kf := by
  have hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (C.M.X k).Ψ ↔ ∃ ρ, τ = tauE D ρ := fun k τ => by
    rw [(hC.base.type k).2, hC.iota.rt, hC.iota.rt0, fix_iff]
  let C' : Ctx Xo c σ V V.rank := { C with x₀ := plOf 1 (x0Mat M) }
  have hC' : C'.OK := by
    refine ⟨hC.iota, hC.pos, hC.lA, hC.good, hC.base, hC.modelW, hC.inf, fun k τ hτ => ?_⟩
    obtain ⟨ρ, rfl⟩ := (hΨ k τ).1 hτ
    have hG : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
    show ReciprocityTheory.ChartRestriction.G.FD.gram _ (C.M.X k).Gm (plOf 1 (x0Mat M) _) = diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)
    rw [hG, plOf_tauE, gram_model, (orthFr_x0Mat M hM ρ).2, (hC.base.type k).1, hq, diagonal_neg, diagonal_transpose]
    simp
  obtain ⟨dict, hd⟩ := GlobalTheory.Member.Ctx.exists_isDict D H Dw l Xo c σ V _ C' hC'
  have hl : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hK : IsLevelK V l.M (PrincLevel.levelGroup V l.M) := fun _ => Iff.rfl
  have hfr : ∀ h k (ρ : D.what₂.Tau) (τ : (C.M.X k).Ψ), τ.1 = tauE D ρ → mat (C'.fr h k) τ =
      Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (C.θ (tauE D ρ)) h * x0Mat M ρ) := by
    intro h k ρ τ hτ
    show Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (C.θ τ.1) h) * plOf 1 (x0Mat M) τ.1 = _
    rw [hτ, plOf_tauE]
    rfl
  refine ⟨fun ρ => C.θ (tauE D ρ), dict, _, hK,
    { inf := fun ρ => hC.inf _
      base := ⟨hΨ, fun k ρ => ((hC.base.type k).1).trans (hq ρ).symm, fun h => ?_⟩
      unif := ⟨C'.th, fun k τ => hC.inf _, GlobalTheory.MemberModel.dictIsUnif_of_isDict D H Dw l Xo c σ V _ C' hC' dict hd _ hK⟩
      model := hC.modelW
      muUnit := ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl,
        (GlobalTheory.MemberModel.dict_invariant D H Dw l Xo c σ V _ C' hC' dict hd _ hK).2.2.2.1⟩
      muCont := continuous_const
      chi := fun k γ _ => hC.base.chi k _ γ
      cNe := fun _ => one_ne_zero
      cBdd := ⟨1, fun _ => norm_one.le⟩
      fin := inferInstance
      levFin := fun k hk => hk.1
      levOpen := ?_
      muK := fun _ _ => rfl
      wt := ⟨0, fun _ _ => by simp, fun k ρ τ hτ a => by rw [hτ, plOf_tauE]; simp⟩ }⟩
  · obtain ⟨γ, hm, he⟩ := hd.1 h
    refine ⟨γ, hm.1, fun ρ τ hτ => ?_, fun u hu => ?_⟩
    · rw [he]
      exact hfr _ _ ρ τ hτ
    · have hm2 := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V _ C' hC' h _ γ hm).2.2.1 u hu
      obtain ⟨δ, hδ, e⟩ := GlobalTheory.MemberModel.dict_eq_of_mark D H Dw l Xo c σ V _ C' hC' dict hd (h * u) _ γ hm2
      refine ⟨δ, hδ, _, e, fun ρ τ hτ => ?_⟩
      rw [mul_assoc γ h u]
      exact hfr _ _ ρ τ hτ
  · have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    let U : Subgroup (GA D V) :=
      { carrier := {k | FinCong V l.M k}
        one_mem' := PrincLevel.finCong_one V l.M
        mul_mem' := fun ha hb => PrincLevel.finCong_mul ha hb
        inv_mem' := fun ha => PrincLevel.finCong_inv ha }
    exact ⟨U, U.isOpen_of_mem_nhds (PrincLevel.finCong_mem_nhds V hl), fun k hk hf => ⟨hf, hk⟩⟩

theorem exists_holModel (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (lam : Fin (D.sp.W j).rank → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hσ : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Mt (D.sp.W j).rank → (H →L[ℂ] H)),
      IsDS (fun a => decide ((a : ℕ) < (D.R.sigW j).1)) lam σ) :
    ∃ (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.W j) S), HolShape M ∧ (∀ ρ, M.lam ρ = lam) ∧
      ∀ ρ, nNeg (M.ε ρ) = (D.R.sigW j).2 := by
  have hr : (D.sp.W j).rank = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    rw [D.sp.W_rank j hj.1 hj.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨H, i1, i2, σ, hσ⟩ := hσ
  set ε : Fin (D.sp.W j).rank → Bool := fun a => decide ((a : ℕ) < (D.R.sigW j).1) with hε
  have hp : (D.R.sigW j).1 ≤ (D.sp.W j).rank := by omega
  have hq : nNeg ε = (D.R.sigW j).2 := by rw [nNeg_shape hp fun _ => rfl]; omega
  have hp' : (Finset.univ.filter fun a => ε a = true).card = (D.R.sigW j).1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (D.sp.W j).rank))) (fun a => ε a = false)
    have h2 : (Finset.univ.filter fun a => ε a = false).card = (D.R.sigW j).2 := hq
    simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hA : ∀ τ : D.what₂.Tau, ∃ A : Mt (D.sp.W j).rank, IsUnit A ∧ Aᴴ * Formalism.REAL.Jm ε * A = gramAt D (D.sp.W j) τ := fun τ => by
    have h1 := D.sp.W_sig j (tauE D τ)
    rw [D.sp.W_sigval j hj.1 hj.2] at h1
    exact GlobalTheory.Published.exists_frame_of_hasSignature h1 ε hp' hq
  choose A hA hG using hA
  choose m hm using hl.2
  let qq : Fin (D.sp.W j).rank → ℚ := fun a => (m a : ℚ) + (((D.sp.W j).rank : ℚ) - 1) / 2
  have hE : IsEnum (Finset.univ.image fun a => (qq a, ε a)) lam ε :=
    ⟨hl.1, qq, fun a => by have := hm a; simp only [qq]; push_cast; linarith, rfl⟩
  exact ⟨_, @DSModel.mk D _ (fun _ => Finset.univ.image fun a => (qq a, ε a)) (fun _ => H) (fun _ => i1) (fun _ => i2)
    (fun _ => σ) (fun _ => lam) (fun _ => ε) A (fun _ => hE) (fun _ => hσ) hA hG,
    fun _ => ⟨hl, _, hp, fun _ => rfl⟩, fun _ => rfl, fun _ => hq⟩

theorem exists_goodDict (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (lam : Fin (D.sp.W j).rank → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hσ : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Mt (D.sp.W j).rank → (H →L[ℂ] H)),
      IsDS (fun a => decide ((a : ℕ) < (D.R.sigW j).1)) lam σ) (w : D.what₂.Tau → Fin (D.sp.W j).rank → ℤ) :
    ∃ (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.W j) S) (θ : InfFam D) (n : ℕ) (X : Fin n → Data D.host.E (D.sp.W j).rank)
      (la : ∀ k, Wt (X k).Ψ _) (dict : _) (Kf : Subgroup (GA D (D.sp.W j))), HolShape M ∧ (∀ ρ, M.lam ρ = lam) ∧ 0 < n ∧
        3 ≤ (D.sp.W j).rank ∧ IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf ∧
        GoodDict θ M w rfl X la dict (fun _ => 1) (fun _ => 1) Kf := by
  obtain ⟨S, M, hM, hlam, hq⟩ := exists_holModel j hj lam hl hσ
  obtain ⟨l, Xo, c, σ, C, hC, h3, hn, hl⟩ := GlobalTheory.Member.Inhab.exists_ctx_ok_at_lift D j hj
  obtain ⟨θ, dict, Kf, hK, hG⟩ := goodDict_of_ctx C hC M hM hq w
  exact ⟨S, M, θ, _, _, _, dict, Kf, hM, hlam, hn, h3, hl ▸ hK, hG⟩

theorem exists_goodDict_last (lam : Fin (D.sp.W D.R.m).rank → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (w : D.what₂.Tau → Fin (D.sp.W D.R.m).rank → ℤ) :
    ∃ (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.W D.R.m) S) (θ : InfFam D) (n : ℕ)
      (X : Fin n → Data D.host.E (D.sp.W D.R.m).rank) (la : ∀ k, Wt (X k).Ψ _) (dict : _)
      (Kf : Subgroup (GA D (D.sp.W D.R.m))), HolShape M ∧ (∀ ρ, M.lam ρ = lam) ∧ 0 < n ∧
        3 ≤ (D.sp.W D.R.m).rank ∧ IsLevelK (D.sp.W D.R.m) (D.host.g 0 * D.host.g 1) Kf ∧
        GoodDict θ M w rfl X la dict (fun _ => 1) (fun _ => 1) Kf := by
  have hm := D.R.two_le_m
  have hj : 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m := ⟨by omega, le_rfl⟩
  refine exists_goodDict _ hj lam hl ?_ w
  have e : (fun a : Fin (D.sp.W D.R.m).rank => decide ((a : ℕ) < (D.R.sigW D.R.m).1)) = fun _ => true := by
    funext a
    have h1 := a.2
    have h2 := D.sp.W_rank _ hj.1 hj.2
    have := D.R.m_add_three_le_k
    refine decide_eq_true ?_
    show (a : ℕ) < D.R.k + D.R.m - 1
    have h3 : (D.sp.W D.R.m).rank = D.R.k + D.R.m - 1 := h2
    omega
  rw [e]
  exact GlobalTheory.CompactDS.exists_isDS_const _ true _ hl

theorem exists_goodDict_of_discreteSeries (h : GlobalTheory.Published.DiscreteSeriesExists) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m)
    (lam : Fin (D.sp.W j).rank → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (w : D.what₂.Tau → Fin (D.sp.W j).rank → ℤ) :
    ∃ (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.W j) S) (θ : InfFam D) (n : ℕ) (X : Fin n → Data D.host.E (D.sp.W j).rank)
      (la : ∀ k, Wt (X k).Ψ _) (dict : _) (Kf : Subgroup (GA D (D.sp.W j))), HolShape M ∧ (∀ ρ, M.lam ρ = lam) ∧ 0 < n ∧
        3 ≤ (D.sp.W j).rank ∧ IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf ∧
        GoodDict θ M w rfl X la dict (fun _ => 1) (fun _ => 1) Kf :=
  exists_goodDict j hj lam hl (GlobalTheory.Published.discreteSeriesExists_iff.1 h _ _ lam hl) w

end Dict

section Forms

variable {D : D7}

set_option maxHeartbeats 1600000 in

theorem exists_isReg (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (h : FinPair V μ 𝓕) : ∃ ρ, IsReg V μ 𝓕 ρ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  have key : ∀ ν : Measure (AutQ V), AutomorphicL2Unitary.quotMeasure (GQ V) μ = ν →
      ∃ ρ : GA D V →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν), (∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))) ∧
        (∀ g F, ‖ρ g F‖ = ‖F‖) ∧ ∀ F, Continuous fun g => ρ g F := by
    rintro ν rfl
    refine ⟨AutomorphicL2Unitary.R (GQ V) μ, fun g F => ?_, fun g F => ?_, fun F => ?_⟩
    · exact AutomorphicL2Unitary.lift_R (Γ := GQ V) (μ := μ) g F
    · exact AutomorphicL2Unitary.norm_R (Γ := GQ V) (μ := μ) g F
    · exact AutomorphicL2Unitary.continuous_R (Γ := GQ V) (μ := μ) F
  have e : AutomorphicL2Unitary.quotMeasure (GQ V) μ = nuQ V μ 𝓕 := AutomorphicL2Unitary.quotMeasure_eq (Γ := GQ V) (μ := μ) h.fd
  obtain ⟨ρ, a, b, c⟩ := key _ e
  exact ⟨ρ, { val := a, iso := b, cont := c }⟩

theorem holForm_const (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (z : ℂ) :
    HolForm θ M 0 J (fun _ => 1) fun _ => z := by
  classical
  exact ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, ⟨‖z‖, fun _ => le_rfl⟩,
    fun _ _ _ => (one_mul _).symm, fun _ => ⟨fun _ => z, holFn_const _ _ _ z, fun _ _ => rfl⟩⟩

theorem mem_GG_iff (V : HSp D) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E V.rank) (hX : ModelW V rfl X) (τ : X.Ψ) (ρ : D.what₂.Tau)
    (hτ : τ.1 = tauE D ρ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ V.rank) :
    ReciprocityTheory.ChartRestriction.G.FD.mat x τ ∈ frDom (gramAt D V ρ) X.p0 ↔ (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (V.rank + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re := by
  have hG : X.Gm = -V.gramᵀ := hX.1
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [ReciprocityTheory.ChartRestriction.G.FD.dmin, hG, hτ, gram_model, ReciprocityTheory.ChartRestriction.G.FD.lminor, ReciprocityTheory.ChartRestriction.G.FD.lminor, ← transpose_submatrix,
    det_transpose]

end Forms

end GlobalTheory.HolDictModel
