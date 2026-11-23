import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartan

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.FockCoef

theorem chain_eq_zero (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (C r : ℝ) (hr : 0 < r)
    (hM : ∀ k t, ‖f k t‖ ≤ C * (k.factorial : ℝ) / r ^ k) (h0 : ∀ k, f k 0 = 0) (t : ℝ) : f 0 t = 0 := by
  have hA : AnalyticOnNhd ℝ (f 0) Set.univ := fun a _ =>
    GlobalTheory.OrbitAnalytic.analyticAt_of_bound f hf C r hr hM a
  have hloc : f 0 =ᶠ[nhds 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with z hz
    have hz' : |z| < r := by simpa [Real.dist_eq] using hz
    have hρ0 : 0 ≤ |z| / r := div_nonneg (abs_nonneg z) hr.le
    have hρ1 : |z| / r < 1 := (div_lt_one hr).mpr hz'
    have hb : ∀ N : ℕ, ‖f 0 z‖ ≤ C * (((N + 1 : ℕ) : ℝ) * (|z| / r) ^ (N + 1)) := by
      intro N
      have h := GlobalTheory.OrbitAnalytic.taylor_bound f hf 0 z N (C * ((N + 1).factorial : ℝ) / r ^ (N + 1)) (hM (N + 1))
      simp only [h0, smul_zero, Finset.sum_const_zero, sub_zero, zero_add] at h
      refine h.trans (le_of_eq ?_)
      have hN : (N.factorial : ℝ) ≠ 0 := by positivity
      have hr' : r ≠ 0 := hr.ne'
      rw [Nat.factorial_succ, div_pow]
      push_cast
      field_simp
    have hlim : Filter.Tendsto (fun N : ℕ => C * (((N + 1 : ℕ) : ℝ) * (|z| / r) ^ (N + 1))) Filter.atTop (nhds 0) := by
      have := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).comp (Filter.tendsto_add_atTop_nat 1)
      simpa using this.const_mul C
    have h1 := ge_of_tendsto' hlim hb
    have h2 := norm_le_zero_iff.mp h1
    simpa using h2
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hloc (Set.mem_univ t)
  simpa using this

theorem family_eq_zero {p q : ℕ} (T : GrpData p q) (hgen : Subgroup.closure (T.expt '' upq p q) = ⊤) {V : Type}
    (D : T.G → V → ℂ) (a : Mat p q → V → V)
    (hder : ∀ Y ∈ upq p q, ∀ g u, HasDerivAt (fun t : ℝ => D (g * T.expt (t • Y)) u) (D g (a Y u)) 0)
    (hb : ∀ Y ∈ upq p q, ∀ u, ∃ C r : ℝ, 0 < r ∧ ∀ k g, ‖D g ((a Y)^[k] u)‖ ≤ C * (k.factorial : ℝ) / r ^ k)
    (h1 : ∀ u, D 1 u = 0) (g : T.G) : ∀ u, D g u = 0 := by
  have step : ∀ g : T.G, (∀ u, D g u = 0) → ∀ Y ∈ upq p q, ∀ t : ℝ, ∀ u, D (g * T.expt (t • Y)) u = 0 := by
    intro g hg Y hY t u
    obtain ⟨C, r, hr, hCr⟩ := hb Y hY u
    have hadd := T.expt_add Y hY
    refine chain_eq_zero (fun k s => D (g * T.expt (s • Y)) ((a Y)^[k] u)) ?_ C r hr (fun k s => hCr k _) ?_ t
    · intro k s
      have h1 := hder Y hY (g * T.expt (s • Y)) ((a Y)^[k] u)
      have h1' : HasDerivAt (fun x : ℝ => D (g * T.expt (s • Y) * T.expt (x • Y)) ((a Y)^[k] u))
          (D (g * T.expt (s • Y)) (a Y ((a Y)^[k] u))) (s - s) := by
        rw [sub_self]
        exact h1
      have h2 := h1'.comp_sub_const s s
      have hfun : (fun x : ℝ => D (g * T.expt (x • Y)) ((a Y)^[k] u)) =
          fun x => D (g * T.expt (s • Y) * T.expt ((x - s) • Y)) ((a Y)^[k] u) := by
        funext x
        have hx : s + (x - s) = x := by ring
        rw [mul_assoc, ← hadd, hx]
      show HasDerivAt (fun x : ℝ => D (g * T.expt (x • Y)) ((a Y)^[k] u))
        (D (g * T.expt (s • Y)) ((a Y)^[k + 1] u)) s
      rw [hfun, Function.iterate_succ_apply']
      exact h2
    · intro k
      show D (g * T.expt ((0 : ℝ) • Y)) ((a Y)^[k] u) = 0
      rw [zero_smul, T.expt_zero, mul_one]
      exact hg _
  have hinv : ∀ Y ∈ upq p q, (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
    intro Y hY
    have := T.expt_add Y hY 1 (-1)
    rw [show ((1 : ℝ) + -1) = 0 by norm_num, zero_smul, T.expt_zero, one_smul] at this
    exact (eq_inv_of_mul_eq_one_right this.symm).symm
  have hP : ∀ x ∈ Submonoid.closure (T.expt '' upq p q ∪ (T.expt '' upq p q)⁻¹),
      ∀ g : T.G, (∀ u, D g u = 0) → ∀ u, D (g * x) u = 0 := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      intro g hg u
      rcases hx with ⟨Y, hY, rfl⟩ | hx
      · simpa using step g hg Y hY 1 u
      · rw [Set.mem_inv] at hx
        obtain ⟨Y, hY, hYx⟩ := hx
        have hx' : x = T.expt ((-1 : ℝ) • Y) := by rw [← hinv Y hY, hYx, inv_inv]
        rw [hx']
        exact step g hg Y hY (-1) u
    | one => intro g hg u; simpa using hg u
    | mul x y _ _ hx hy =>
      intro g hg u
      rw [← mul_assoc]
      exact hy _ (hx g hg) u
  have hg : g ∈ Submonoid.closure (T.expt '' upq p q ∪ (T.expt '' upq p q)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hgen]
    simp
  intro u
  simpa using hP g hg 1 h1 u

section Phi

variable {p q n : ℕ} {G fr : Mn n} {ε : Fin n → Bool} (br : Bool) {e : Ix p q ≃ Fin n}

theorem phi_mul (X Y : Mat p q) : phi br e (X * Y) = phi br e X * phi br e Y := by
  cases br <;> simp [phi, plainMat, barMat, Matrix.submatrix_mul_equiv, Matrix.map_mul]

theorem phi_one : phi br e (1 : Mat p q) = 1 := by
  ext i j
  cases br <;> simp [phi, plainMat, barMat, Matrix.one_apply]

theorem phi_add (X Y : Mat p q) : phi br e (X + Y) = phi br e X + phi br e Y := by
  ext i j
  cases br <;> simp [phi, plainMat, barMat]

theorem phi_zero : phi br e (0 : Mat p q) = 0 := by
  ext i j
  cases br <;> simp [phi, plainMat, barMat]

theorem phi_star (X : Mat p q) : phi br e Xᴴ = (phi br e X)ᴴ := by
  ext i j
  cases br <;> simp [phi, plainMat, barMat, Matrix.conjTranspose_apply]

theorem phi_Jm (hs : SignCompat ε e) : phi br e (TH.Jm p q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  have hs' : ∀ a, ε (e a) = a.isLeft := hs
  cases br <;> rcases a with a | a <;> rcases b with b | b <;>
    simp [phi, plainMat, barMat, TH.Jm, Formalism.UG.Jpq, Formalism.REAL.Jm, hs', Matrix.diagonal_apply, Matrix.one_apply, apply_ite (starRingEnd ℂ)]
  all_goals split_ifs <;> simp

private theorem smul_phi {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (Y : Mat p q) (t : ℝ) :
    t • phi br e Y = phi br e (t • Y) := by
  ext i j
  cases br <;> simp [phi, plainMat, barMat, Complex.real_smul, Complex.conj_ofReal]

private theorem exp_reindex_twisted_operators {p q n : ℕ} (e : Ix p q ≃ Fin n) (M : Mat p q) :
    NormedSpace.exp (Matrix.reindex e e M) = Matrix.reindex e e (NormedSpace.exp M) := by
  let C : Mat p q ≃L[ℂ] Mn n := (Matrix.reindexLinearEquiv ℂ ℂ e e).toContinuousLinearEquiv
  let A := Matrix.reindexAlgEquiv ℂ ℂ e
  have hC : ∀ X, Matrix.reindex e e X = C X := fun X => rfl
  have hA : ∀ X, C X = A X := fun X => rfl
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  simp only [hC]
  rw [C.map_tsum]
  congr 1
  funext k
  rw [hA, hA, map_smul, map_pow]

private theorem exp_map_starRingEnd {p q : ℕ} (M : Mat p q) :
    NormedSpace.exp (M.map (starRingEnd ℂ)) = (NormedSpace.exp M).map (starRingEnd ℂ) := by
  have h : ∀ X : Mat p q, X.map (starRingEnd ℂ) = Xᴴᵀ := fun X => by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

theorem phi_exp (Y : Mat p q) (t : ℝ) : NormedSpace.exp (t • phi br e Y) = phi br e (NormedSpace.exp (t • Y)) := by
  rw [smul_phi]
  cases br <;> simp only [phi, plainMat, barMat, Bool.false_eq_true, ↓reduceIte]
  · exact exp_reindex_twisted_operators e _
  · rw [exp_reindex_twisted_operators, exp_map_starRingEnd]

theorem phiFr_mul (hfr : IsUnit fr) (X Y : Mat p q) : phiFr fr br e (X * Y) = phiFr fr br e X * phiFr fr br e Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  rw [phiFr, phiFr, phiFr, phi_mul,
    show fr⁻¹ * phi br e X * fr * (fr⁻¹ * phi br e Y * fr) = fr⁻¹ * phi br e X * (fr * fr⁻¹) * phi br e Y * fr by
      simp only [Matrix.mul_assoc],
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem phiFr_one (hfr : IsUnit fr) : phiFr fr br e (1 : Mat p q) = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  rw [phiFr, phi_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]

theorem phiFr_exp (hfr : IsUnit fr) (Y : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • phiFr fr br e Y) = phiFr fr br e (NormedSpace.exp (t • Y)) := by
  rw [phiFr, phiFr, ← phi_exp, show t • (fr⁻¹ * phi br e Y * fr) = fr⁻¹ * (t • phi br e Y) * fr by
    rw [Matrix.mul_smul, Matrix.smul_mul]]
  exact Matrix.exp_conj' fr _ hfr

theorem phiFr_mem (hfr : IsUnit fr) (hG : frᴴ * Formalism.REAL.Jm ε * fr = G) (hs : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * TH.Jm p q * g = TH.Jm p q) : phiFr fr br e g ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have key : (phi br e g)ᴴ * Formalism.REAL.Jm ε * phi br e g = Formalism.REAL.Jm ε := by
    rw [← phi_star, ← phi_Jm br hs, ← phi_mul, ← phi_mul, hg]
  show (phiFr fr br e g)ᴴ * G * phiFr fr br e g = G
  subst hG
  have h1 : (fr⁻¹)ᴴ * frᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have h2 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc (phiFr fr br e g)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * phiFr fr br e g
      = frᴴ * ((phi br e g)ᴴ * ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) * phi br e g) * fr := by
        simp only [phiFr, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = frᴴ * Formalism.REAL.Jm ε * fr := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, key]

theorem phiFr_lie (hfr : IsUnit fr) (hG : frᴴ * Formalism.REAL.Jm ε * fr = G) (hs : SignCompat ε e) {Y : Mat p q}
    (hY : Y ∈ upq p q) : (phiFr fr br e Y)ᴴ * G + G * phiFr fr br e Y = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have hY' : Yᴴ * TH.Jm p q + TH.Jm p q * Y = 0 := hY
  have key : (phi br e Y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * phi br e Y = 0 := by
    rw [← phi_star, ← phi_Jm br hs, ← phi_mul, ← phi_mul, ← phi_add, hY', phi_zero]
  subst hG
  have h1 : (fr⁻¹)ᴴ * frᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have h2 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc (phiFr fr br e Y)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) + frᴴ * Formalism.REAL.Jm ε * fr * phiFr fr br e Y
      = frᴴ * ((phi br e Y)ᴴ * ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (fr * fr⁻¹) * phi br e Y) * fr := by
        simp only [phiFr, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, key, Matrix.mul_zero, Matrix.zero_mul]

end Phi

section Fock

variable {p q r s : ℕ} {T₀ : GrpData (p * r + q * s) (p * s + q * r)} {T₁ : GrpData p q} {T₂ : GrpData r s}
  (F : FockData T₀ T₁ T₂)

theorem inner_fock (P Q : Pol p q r s) : ⟪F.ι Q, F.ι P⟫_ℂ = fockIp P Q := by
  have hm : ∀ R : Pol p q r s, F.ι R = ∑ v ∈ R.support, R.coeff v • F.ι (MvPolynomial.monomial v 1) := by
    intro R
    conv_lhs => rw [R.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm P, hm Q, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, F.fockIP, mul_ite, mul_zero]
  unfold fockIp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · push_cast
    ring
  · rw [MvPolynomial.notMem_support_iff.mp h]
    simp

end Fock

section Hilbert

variable {ι Z : Type} {n : ℕ} {G : Mn n} {A : Mn n → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)}
  {ip : (Z → ℂ) → (Z → ℂ) → ℂ} {Θ : Submodule ℂ (Z → ℂ)}

theorem ip_zero (h : L2UnitaryRepresentationData G A pt ip Θ) {E : Z → ℂ} (hE : E ∈ Θ) : ip 0 E = 0 := by
  have h0 := h.ip_lin 1 0 Θ.zero_mem 0 Θ.zero_mem E hE
  simp only [one_smul, add_zero, one_mul] at h0
  linear_combination (-1 : ℂ) * h0

theorem ip_sq_le (h : L2UnitaryRepresentationData G A pt ip Θ) {F E : Z → ℂ} (hF : F ∈ Θ) (hE : E ∈ Θ) :
    ‖ip F E‖ ^ 2 ≤ (ip F F).re * (ip E E).re := by
  have hl : ∀ (z : ℂ), ∀ X ∈ Θ, ∀ Y ∈ Θ, ∀ W ∈ Θ, ip (z • X + Y) W = z * ip X W + ip Y W := h.ip_lin
  have hs : ∀ X ∈ Θ, ∀ Y ∈ Θ, ip Y X = conj (ip X Y) := h.ip_symm
  have hz : ∀ W ∈ Θ, ip 0 W = 0 := fun W hW => ip_zero h hW
  have hsm : ∀ (z : ℂ), ∀ X ∈ Θ, ∀ W ∈ Θ, ip (z • X) W = z * ip X W := by
    intro z X hX W hW
    have := hl z X hX 0 Θ.zero_mem W hW
    rwa [add_zero, hz W hW, add_zero] at this
  have hpos : ∀ X ∈ Θ, 0 ≤ (ip X X).re := by
    intro X hX
    by_cases h0 : X = 0
    · subst h0
      rw [hz 0 Θ.zero_mem]
      simp
    · exact (h.ip_pos X hX h0).le
  have hre : ∀ X ∈ Θ, (ip X X).im = 0 := by
    intro X hX
    have := congrArg Complex.im (hs X hX X hX)
    simp only [Complex.conj_im] at this
    linarith
  by_cases hE0 : E = 0
  · subst hE0
    have hc : ip F 0 = 0 := by rw [hs 0 Θ.zero_mem F hF, hz F hF, map_zero]
    rw [hc]
    simpa using mul_nonneg (hpos F hF) (hpos 0 Θ.zero_mem)
  · have hbpos : 0 < (ip E E).re := h.ip_pos E hE hE0
    have hX : (ip E E) • F + (-ip F E) • E ∈ Θ := Θ.add_mem (Θ.smul_mem _ hF) (Θ.smul_mem _ hE)
    have hexp : ∀ W ∈ Θ, ip ((ip E E) • F + (-ip F E) • E) W = ip E E * ip F W + (-ip F E) * ip E W :=
      fun W hW => by rw [hl _ F hF _ (Θ.smul_mem _ hE) W hW, hsm _ E hE W hW]
    have key := hexp _ hX
    rw [hs _ hX F hF, hs _ hX E hE, hexp F hF, hexp E hE, hs F hF E hE] at key
    have hre' := hpos _ hX
    rw [key] at hre'
    have haim := hre F hF
    have hbim := hre E hE
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_im, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, haim, hbim, mul_zero, zero_mul, sub_zero, add_zero] at hre'
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [hbpos, hre']

private theorem hasDerivAt_fockData_expt_smul {p q r s : ℕ} {T₀ : GrpData (p * r + q * s) (p * s + q * r)} {T₁ : GrpData p q}
    {T₂ : GrpData r s} (F : FockData T₀ T₁ T₂) {Y : Mat p q} (hY : Y ∈ upq p q) (w : Pol p q r s) (t : ℝ) :
    HasDerivAt (fun x : ℝ => F.π (T₁.expt (x • Y), 1) (F.ι w))
      (F.π (T₁.expt (t • Y), 1) (F.ι (fockAct1 p q r s Y w))) t := by
  obtain ⟨-, hder, -⟩ := GlobalTheory.FockEmbExp.fock_derived p q r s T₀ T₁ T₂ F
  have hmul : ∀ s t : ℝ, F.π (T₁.expt ((s + t) • Y), 1) = F.π (T₁.expt (s • Y), 1) * F.π (T₁.expt (t • Y), 1) := by
    intro s t
    rw [T₁.expt_add Y hY, ← map_mul, Prod.mk_mul_mk, mul_one]
  have h1' : HasDerivAt (fun x : ℝ => F.π (T₁.expt (x • Y), 1) (F.ι w)) (F.ι (fockAct1 p q r s Y w)) (t - t) := by
    rw [sub_self]
    exact hder Y hY w
  have h2 := ((F.π (T₁.expt (t • Y), 1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (h1'.comp_sub_const t t)
  have hfun : (fun x : ℝ => F.π (T₁.expt (x • Y), 1) (F.ι w)) = fun x => F.π (T₁.expt (t • Y), 1)
      (F.π (T₁.expt ((x - t) • Y), 1) (F.ι w)) := by
    funext x
    have hx : t + (x - t) = x := by ring
    rw [← ContinuousLinearMap.mul_apply, ← hmul, hx]
  rw [hfun]
  exact h2

end Hilbert

theorem coef_of_side : ∀ (p q r s n : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (ι Z : Type) (G fr : Mn n) (ε : Fin n → Bool) (br : Bool) (e : Ix p q ≃ Fin n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (N : ℝ), 1 ≤ p + q → IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → SignCompat ε e → (m : ℚ) = 2 * c → Side A pt κ (phiFr fr br e) c (fockAct1 p q r s) → L2UnitaryRepresentationData G A pt ip Θ → Fischer pt ip κ N → Coef F A pt ip κ (phiFr fr br e) m N := by
  intro p q r s n T₀ T₁ T₂ F ι Z G fr ε br e A pt ip Θ κ c m N hpq hfr hG hs hm hS hL hF
  have hip : ∀ P Q, ip (pt P) (pt Q) = (N : ℂ) * ⟪F.ι (κ Q), F.ι (κ P)⟫_ℂ := fun P Q => by
    rw [hF.2, ← inner_fock F]
  refine ⟨hF.1, hip, ?_⟩
  intro g P Q
  obtain ⟨hgen, -⟩ := GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan p q hpq T₁
  have hUJ : ∀ x : T₁.G, ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)ᴴ * TH.Jm p q * ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)
      = TH.Jm p q := by
    intro x
    have h : Formalism.UG.cT (starRingEnd ℂ) ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q) * Formalism.UG.Jpq p q *
        ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q) = Formalism.UG.Jpq p q := T₁.cov_mem x
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q) =
        ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)ᴴ := by
      unfold Formalism.UG.cT
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hc] at h
    unfold TH.Jm
    exact h
  have hmemU : ∀ x : T₁.G, phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.QuantumDeterminants.UH G :=
    fun x => phiFr_mem br hfr hG hs (hUJ x)
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by
    have := congrArg (fun y : ℚ => (y : ℂ)) hm
    push_cast at this
    exact this
  let aY : Mat p q → MvPolynomial ι ℂ → MvPolynomial ι ℂ := fun Y P' =>
    κ.symm (fockAct1 p q r s Y (κ P') + ((c : ℂ) * Y.trace) • κ P')
  let D : T₁.G → MvPolynomial ι ℂ → ℂ := fun x P' =>
    ip (A (phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)) (pt P')) (pt Q) -
      (N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m * ⟪F.ι (κ Q), F.π (x, 1) (F.ι (κ P'))⟫_ℂ
  have h1 : ∀ P', D 1 P' = 0 := by
    intro P'
    simp only [D, map_one, Units.val_one, phiFr_one br hfr, hL.one _ (hL.mem P'), _root_.one_zpow, mul_one]
    rw [show ((1 : T₁.G), (1 : T₂.G)) = 1 from rfl, map_one, ContinuousLinearMap.one_apply, hip, sub_self]
  have hder : ∀ Y ∈ upq p q, ∀ x P', HasDerivAt (fun t : ℝ => D (x * T₁.expt (t • Y)) P') (D x (aY Y P')) 0 := by
    intro Y hY x P'
    have hYt : ∀ t : ℝ, t • Y ∈ upq p q := fun t => GlobalTheory.FockEmbExp.smul_mem hY t
    have hhU := hmemU x
    have hh'U := hmemU x⁻¹
    have hhh' : phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q) *
        phiFr fr br e ((T₁.cov x⁻¹ : GL (Ix p q) ℂ) : Mat p q) = 1 := by
      rw [← phiFr_mul br hfr, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, phiFr_one br hfr]
    have hEΘ : A (phiFr fr br e ((T₁.cov x⁻¹ : GL (Ix p q) ℂ) : Mat p q)) (pt Q) ∈ Θ := hL.stable _ hh'U _ (hL.mem Q)
    have hQ : A (phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q))
        (A (phiFr fr br e ((T₁.cov x⁻¹ : GL (Ix p q) ℂ) : Mat p q)) (pt Q)) = pt Q := by
      rw [← hL.mul _ hhU _ hh'U _ (hL.mem Q), hhh', hL.one _ (hL.mem Q)]
    have hXlie := phiFr_lie br hfr hG hs hY
    have hκ : κ (aY Y P') = fockAct1 p q r s Y (κ P') + ((c : ℂ) * Y.trace) • κ P' := by
      simp only [aY, LinearEquiv.apply_symm_apply]
    have hpol : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.PolDer A pt (phiFr fr br e Y) P' (aY Y P') := (hS.der Y hY P' (aY Y P')).mpr hκ
    have hexpU : ∀ t : ℝ, NormedSpace.exp (t • phiFr fr br e Y) ∈ Formalism.QuantumDeterminants.UH G := by
      intro t
      rw [phiFr_exp br hfr Y t, ← T₁.expt_cov _ (hYt t)]
      exact hmemU _
    have hfun1 : ∀ t : ℝ, ip (A (phiFr fr br e ((T₁.cov (x * T₁.expt (t • Y)) : GL (Ix p q) ℂ) : Mat p q)) (pt P')) (pt Q)
        = ip (A (NormedSpace.exp (t • phiFr fr br e Y)) (pt P'))
            (A (phiFr fr br e ((T₁.cov x⁻¹ : GL (Ix p q) ℂ) : Mat p q)) (pt Q)) := by
      intro t
      rw [map_mul, Units.val_mul, T₁.expt_cov _ (hYt t), phiFr_mul br hfr, ← phiFr_exp br hfr Y t,
        hL.mul _ hhU _ (hexpU t) _ (hL.mem P')]
      conv_lhs => rw [← hQ]
      rw [hL.unit _ hhU _ (hL.stable _ (hexpU t) _ (hL.mem P')) _ hEΘ]
    have hfun2 : ∀ t : ℝ, (N : ℂ) * ((T₁.sq (x * T₁.expt (t • Y)) : ℂˣ) : ℂ) ^ m *
        ⟪F.ι (κ Q), F.π (x * T₁.expt (t • Y), 1) (F.ι (κ P'))⟫_ℂ
        = (N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m * (Complex.exp (↑t * ((c : ℂ) * Y.trace)) *
          ⟪F.ι (κ Q), F.π (x, 1) (F.π (T₁.expt (t • Y), 1) (F.ι (κ P')))⟫_ℂ) := by
      intro t
      rw [map_mul, Units.val_mul, GlobalTheory.CoverExp.sq_expt T₁ (hYt t), mul_zpow, ← Complex.exp_int_mul,
        show ((x * T₁.expt (t • Y), (1 : T₂.G))) = (x, 1) * (T₁.expt (t • Y), 1) by simp, map_mul,
        ContinuousLinearMap.mul_apply, Matrix.trace_smul, Complex.real_smul, hmC]
      ring_nf
    have hD : (fun t : ℝ => D (x * T₁.expt (t • Y)) P') = fun t : ℝ => ip (A (NormedSpace.exp (t • phiFr fr br e Y)) (pt P'))
        (A (phiFr fr br e ((T₁.cov x⁻¹ : GL (Ix p q) ℂ) : Mat p q)) (pt Q)) - (N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m *
          (Complex.exp (↑t * ((c : ℂ) * Y.trace)) *
            ⟪F.ι (κ Q), F.π (x, 1) (F.π (T₁.expt (t • Y), 1) (F.ι (κ P')))⟫_ℂ) := by
      funext t
      simp only [D]
      rw [hfun1 t, hfun2 t]
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (↑t * ((c : ℂ) * Y.trace)))
        (Complex.exp (↑(0 : ℝ) * ((c : ℂ) * Y.trace)) * (1 * ((c : ℂ) * Y.trace))) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const ((c : ℂ) * Y.trace)).cexp
    have hin := (hasDerivAt_const (0 : ℝ) (F.ι (κ Q))).inner ℂ
      (((F.π (x, 1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_fockData_expt_smul F hY (κ P') 0))
    have hd := (hL.der _ hXlie P' (aY Y P') hpol _ hEΘ).sub ((hexp.mul hin).const_mul ((N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m))
    rw [hD]
    refine hd.congr_deriv ?_
    rw [← hL.unit _ hhU _ (hL.mem _) _ hEΘ, hQ]
    simp only [D, hκ, map_add, map_smul, inner_add_right, inner_smul_right, inner_zero_left, Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', zero_smul, T₁.expt_zero, Prod.mk_one_one, map_one,
      ContinuousLinearMap.one_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, add_zero]
    ring
  have hb : ∀ Y ∈ upq p q, ∀ P', ∃ C r : ℝ, 0 < r ∧ ∀ k x, ‖D x ((aY Y)^[k] P')‖ ≤ C * (k.factorial : ℝ) / r ^ k := by
    intro Y hY P'
    have hiter : ∀ k, κ ((aY Y)^[k] P') =
        (fun w => fockAct1 p q r s Y w + ((c : ℂ) * Y.trace) • w)^[k] (κ P') := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        simp only [aY, LinearEquiv.apply_symm_apply]
    obtain ⟨C, ρ, hρ, hC⟩ : ∃ C ρ : ℝ, 0 < ρ ∧ ∀ k,
        ‖F.ι ((fun w => fockAct1 p q r s Y w + ((c : ℂ) * Y.trace) • w)^[k] (κ P'))‖ ≤ C * (k.factorial : ℝ) / ρ ^ k := by
      let f : ℕ → ℝ → F.H := fun k t => Complex.exp (↑t * ((c : ℂ) * Y.trace)) •
        F.π (T₁.expt (t • Y), 1) (F.ι ((fun w => fockAct1 p q r s Y w + ((c : ℂ) * Y.trace) • w)^[k] (κ P')))
      have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := by
        intro k t
        have hexp : HasDerivAt (fun t : ℝ => Complex.exp (↑t * ((c : ℂ) * Y.trace)))
            (Complex.exp (↑t * ((c : ℂ) * Y.trace)) * (1 * ((c : ℂ) * Y.trace))) t :=
          ((hasDerivAt_id' t).ofReal_comp.mul_const ((c : ℂ) * Y.trace)).cexp
        have h := hexp.smul (hasDerivAt_fockData_expt_smul F hY
          ((fun w => fockAct1 p q r s Y w + ((c : ℂ) * Y.trace) • w)^[k] (κ P')) t)
        refine h.congr_deriv ?_
        simp only [f, Function.iterate_succ_apply', map_add, map_smul, smul_add, smul_smul, one_mul]
      have hA : AnalyticAt ℝ (f 0) 0 := by
        have h := (GlobalTheory.FockAlg.analyticOnNhd_orbit_pol p q r s T₀ T₁ T₂ F _ (GlobalTheory.FockEmbExp.left_mem hY r s)
          (κ P')).1 0 (Set.mem_univ _)
        have hfun : (fun t : ℝ => F.π (T₁.expt (t • Y), 1) (F.ι (κ P'))) = fun t : ℝ =>
            F.Om (T₀.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
              (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)))) (F.ι (κ P')) := by
          funext t
          rw [← GlobalTheory.FockEmbExp.emb_expt_left F hY t]
          rfl
        have hexpA : AnalyticAt ℝ (fun t : ℝ => Complex.exp (↑t * ((c : ℂ) * Y.trace))) 0 := by
          have h1 : AnalyticAt ℝ (fun t : ℝ => ((t : ℂ) * ((c : ℂ) * Y.trace))) 0 :=
            (Complex.ofRealCLM.analyticAt 0).mul analyticAt_const
          exact (analyticAt_cexp.restrictScalars).comp h1
        have h2 : AnalyticAt ℝ (fun t : ℝ => F.π (T₁.expt (t • Y), 1) (F.ι (κ P'))) 0 := by
          rw [hfun]
          exact h
        exact hexpA.smul h2
      obtain ⟨C, ρ, hρ, hb0⟩ := GlobalTheory.OrbitAnalytic.bound_of_analyticAt f hf 0 hA
      refine ⟨C, ρ, hρ, fun k => ?_⟩
      have h0 : f k 0 = F.ι ((fun w => fockAct1 p q r s Y w + ((c : ℂ) * Y.trace) • w)^[k] (κ P')) := by
        simp only [f, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, zero_smul, T₁.expt_zero,
          Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]
      rw [← h0]
      exact hb0 k
    have hsq : ∀ x : T₁.G, ‖((T₁.sq x : ℂˣ) : ℂ)‖ = 1 := by
      intro x
      have hdet : ‖(((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)).det‖ = 1 := by
        have h := congrArg Matrix.det (hUJ x)
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
        have hJ : (TH.Jm p q).det ≠ 0 := by
          unfold TH.Jm Formalism.UG.Jpq
          rw [Matrix.det_fromBlocks_zero₂₁]
          simp [Matrix.det_neg]
        have h2 : star (((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)).det * (((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)).det = 1 :=
          mul_right_cancel₀ hJ (by linear_combination h)
        rw [Complex.star_def, Complex.conj_mul'] at h2
        have h3 : ‖(((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)).det‖ ^ 2 = 1 := by exact_mod_cast h2
        have h4 := norm_nonneg (((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)).det
        nlinarith
      have h3 := congrArg (‖·‖) (T₁.sq_sq x)
      simp only [norm_pow, hdet] at h3
      have h4 := norm_nonneg ((T₁.sq x : ℂˣ) : ℂ)
      nlinarith
    have hre : ∀ P'' : MvPolynomial ι ℂ, (ip (pt P'') (pt P'')).re = N * ‖F.ι (κ P'')‖ ^ 2 := by
      intro P''
      rw [hip, Complex.re_ofReal_mul]
      congr 1
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (F.ι (κ P''))
    have hN := hF.1
    refine ⟨2 * N * ‖F.ι (κ Q)‖ * C, ρ, hρ, fun k x => ?_⟩
    have hι : ‖F.ι (κ ((aY Y)^[k] P'))‖ ≤ C * (k.factorial : ℝ) / ρ ^ k := by
      rw [hiter]
      exact hC k
    have t1 : ‖ip (A (phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)) (pt ((aY Y)^[k] P'))) (pt Q)‖ ≤
        N * ‖F.ι (κ ((aY Y)^[k] P'))‖ * ‖F.ι (κ Q)‖ := by
      have hcs := ip_sq_le hL (hL.stable _ (hmemU x) _ (hL.mem ((aY Y)^[k] P'))) (hL.mem Q)
      rw [hL.unit _ (hmemU x) _ (hL.mem _) _ (hL.mem _), hre, hre] at hcs
      have hnn : 0 ≤ N * ‖F.ι (κ ((aY Y)^[k] P'))‖ * ‖F.ι (κ Q)‖ :=
        mul_nonneg (mul_nonneg hN.le (norm_nonneg _)) (norm_nonneg _)
      nlinarith [norm_nonneg (ip (A (phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)) (pt ((aY Y)^[k] P'))) (pt Q))]
    have t2 : ‖(N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m * ⟪F.ι (κ Q), F.π (x, 1) (F.ι (κ ((aY Y)^[k] P')))⟫_ℂ‖ ≤
        N * (‖F.ι (κ Q)‖ * ‖F.ι (κ ((aY Y)^[k] P'))‖) := by
      rw [norm_mul, norm_mul, norm_zpow, hsq, _root_.one_zpow, mul_one, Complex.norm_real, Real.norm_of_nonneg hN.le]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans (le_of_eq ?_)) hN.le
      rw [show F.π (x, 1) = F.Om (F.emb (x, 1)) from rfl, F.isom]
    show ‖ip (A (phiFr fr br e ((T₁.cov x : GL (Ix p q) ℂ) : Mat p q)) (pt ((aY Y)^[k] P'))) (pt Q) -
        (N : ℂ) * ((T₁.sq x : ℂˣ) : ℂ) ^ m * ⟪F.ι (κ Q), F.π (x, 1) (F.ι (κ ((aY Y)^[k] P')))⟫_ℂ‖ ≤ _
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add t1 t2
      _ = 2 * N * ‖F.ι (κ Q)‖ * ‖F.ι (κ ((aY Y)^[k] P'))‖ := by ring
      _ ≤ 2 * N * ‖F.ι (κ Q)‖ * (C * (k.factorial : ℝ) / ρ ^ k) :=
        mul_le_mul_of_nonneg_left hι (mul_nonneg (mul_nonneg (by norm_num) hN.le) (norm_nonneg _))
      _ = 2 * N * ‖F.ι (κ Q)‖ * C * (k.factorial : ℝ) / ρ ^ k := by ring
  have := family_eq_zero T₁ hgen D aY hder hb h1 g P
  exact sub_eq_zero.mp this

end GlobalTheory.ArchRec.FockCoef

end
