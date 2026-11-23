import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.WeightsNormal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open scoped Matrix ComplexOrder

section Gram

variable {k : ℕ}

def colMat {ι : Type} (w : ι → Fin k → ℂ) : Matrix (Fin k) ι ℂ := (Matrix.of w)ᵀ

def gramVec {ι : Type} [Fintype ι] (w : ι → Fin k → ℂ) : Matrix ι ι ℂ := (colMat w)ᴴ * colMat w

variable {ρ m : Type} [Fintype ρ] [Fintype m]

def quotCol [DecidableEq ρ] (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) : Matrix (Fin k) m ℂ :=
  colMat u - colMat v * ((gramVec v)⁻¹ * ((colMat v)ᴴ * colMat u))

def quotGram [DecidableEq ρ] (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) : Matrix m m ℂ := (quotCol v u)ᴴ * quotCol v u

theorem gramVec_sum (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) :
    gramVec (Sum.elim v u) = Matrix.fromBlocks (gramVec v) ((colMat v)ᴴ * colMat u)
      ((colMat u)ᴴ * colMat v) (gramVec u) := by
  ext (a | a) (b | b) <;> simp [gramVec, colMat, Matrix.mul_apply]

theorem quotGram_eq [DecidableEq ρ] (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) (hv : IsUnit (gramVec v).det) :
    quotGram v u =
      gramVec u - (colMat u)ᴴ * colMat v * (gramVec v)⁻¹ * ((colMat v)ᴴ * colMat u) := by
  have hH : (gramVec v)ᴴ = gramVec v := by
    simp [gramVec, Matrix.conjTranspose_mul]
  have hinv : ((gramVec v)⁻¹)ᴴ = (gramVec v)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hH]
  have hk : ∀ Y : Matrix ρ m ℂ, (colMat v)ᴴ * (colMat v * ((gramVec v)⁻¹ * Y)) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, show (colMat v)ᴴ * colMat v = gramVec v from rfl,
      Matrix.mul_nonsing_inv _ hv, Matrix.one_mul]
  unfold quotGram quotCol
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hinv]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hk]
  rw [show gramVec u = (colMat u)ᴴ * colMat u from rfl]
  abel

theorem det_gramVec_sum [DecidableEq ρ] [DecidableEq m] (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) (hv : IsUnit (gramVec v).det) :
    (gramVec (Sum.elim v u)).det = (gramVec v).det * (quotGram v u).det := by
  let _ := Matrix.invertibleOfIsUnitDet _ hv
  rw [gramVec_sum, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, quotGram_eq v u hv]

theorem mulVec_colMat_injective {ι : Type} [Fintype ι] {w : ι → Fin k → ℂ} (hw : LinearIndependent ℂ w) :
    Function.Injective (colMat w).mulVec := by
  intro x y hxy
  have h0 : ∑ a, (x - y) a • w a = 0 := by
    funext c
    have := congrFun hxy c
    simp only [colMat, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    rw [sub_eq_zero]
    simpa [mul_comm] using this
  funext a
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hw _ h0 a)

theorem log_det_gramVec_sum [DecidableEq ρ] [DecidableEq m] (v : ρ → Fin k → ℂ) (u : m → Fin k → ℂ) (h : LinearIndependent ℂ (Sum.elim v u)) :
    0 < (gramVec v).det.re ∧
      Real.log (gramVec (Sum.elim v u)).det.re =
        Real.log (gramVec v).det.re + Real.log (quotGram v u).det.re := by
  have hP : (gramVec (Sum.elim v u)).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ (mulVec_colMat_injective h)
  have hv' : LinearIndependent ℂ v := by simpa using h.comp Sum.inl Sum.inl_injective
  have hA : (gramVec v).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (mulVec_colMat_injective hv')
  have hQ : (quotGram v u).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hdA := hA.det_pos
  have hdQ := hQ.det_nonneg
  have hdP := hP.det_pos
  rw [det_gramVec_sum v u (isUnit_iff_ne_zero.2 hdA.ne')] at hdP ⊢
  obtain ⟨a1, a2⟩ := Complex.pos_iff.1 hdA
  obtain ⟨q1, q2⟩ := Complex.nonneg_iff.1 hdQ
  obtain ⟨p1, -⟩ := Complex.pos_iff.1 hdP
  rw [Complex.mul_re, ← a2, ← q2, zero_mul, sub_zero] at p1 ⊢
  have hq : 0 < (quotGram v u).det.re := by
    rcases q1.lt_or_eq with hq | hq
    · exact hq
    · rw [← hq, mul_zero] at p1
      exact absurd p1 (lt_irrefl 0)
  exact ⟨a1, Real.log_mul a1.ne' hq.ne'⟩

end Gram

section Psh

variable {d : ℕ}

theorem isPsh_congr' {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : Set.EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : Set.EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

theorem isPsh_add_re_add_const {U : Set (Fin d → ℂ)} (hU : IsOpen U) {φ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ)
    {G : (Fin d → ℂ) → ℂ} (hG : DifferentiableOn ℂ G U) (c : ℝ) :
    IsPsh U (fun w => φ w + (G w).re + c) := by
  have hcont : ContinuousOn (fun w => (G w).re) U := Complex.continuous_re.comp_continuousOn hG.continuousOn
  refine ⟨(hφ.1.add hcont.upperSemicontinuousOn).add upperSemicontinuousOn_const, fun z w hd => ?_⟩
  obtain ⟨hint, hle⟩ := hφ.2 z w hd
  have hmap : Continuous fun ζ : ℂ => z + ζ • w := continuous_const.add (continuous_id.smul continuous_const)
  have hdiff : DifferentiableOn ℂ (fun ζ : ℂ => G (z + ζ • w)) (closedBall 0 1) := by
    intro ζ hζ
    have hζU : z + ζ • w ∈ U := hd ζ (by simpa using hζ)
    have hGa : DifferentiableAt ℂ G (z + ζ • w) := hG.differentiableAt (hU.mem_nhds hζU)
    have hl : DifferentiableAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const w)
    exact (hGa.comp ζ hl).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => G (z + ζ • w)) (ball 0 |(1 : ℝ)|) := by
    rw [abs_one]
    exact hdiff.diffContOnCl_ball subset_rfl
  have hmean : Real.circleAverage (fun ζ : ℂ => G (z + ζ • w)) 0 1 = G z := by
    have := hdc.circleAverage
    simpa using this
  have hcs : ContinuousOn (fun ζ : ℂ => G (z + ζ • w)) (sphere 0 1) :=
    hdiff.continuousOn.mono sphere_subset_closedBall
  have hciG : CircleIntegrable (fun ζ : ℂ => G (z + ζ • w)) 0 1 := hcs.circleIntegrable zero_le_one
  have hciR : CircleIntegrable (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 :=
    (Complex.continuous_re.comp_continuousOn hcs).circleIntegrable zero_le_one
  have hre : Real.circleAverage (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 = (G z).re := by
    have := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hciG
    rw [hmean] at this
    simpa [Function.comp_def] using this
  have hci2 : CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re) 0 1 := hint.add hciR
  refine ⟨hci2.add (circleIntegrable_const c 0 1), ?_⟩
  have e1 := Real.circleAverage_fun_add hci2 (circleIntegrable_const c 0 1)
  have e2 := Real.circleAverage_fun_add hint hciR
  show φ z + (G z).re + c ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re + c) 0 1
  rw [e1, e2, hre, Real.circleAverage_const]
  linarith

end Psh

section Hodge

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.lieVec (A : HermDatum Em Ψ N j) (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    (x : Fin N → ℂ) : Fin (N - j) → ℂ :=
  fun c => (Real.sqrt (2 * ‖A.emb τ A.ξ‖) : ℂ) * (P⁻¹ *ᵥ x) (tailIdx hj c)

def HermDatum.lieFam (A : HermDatum Em Ψ N j) (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) {ρ : ℕ}
    (v : Fin ρ → Fin N → Em) : Fin ρ → Fin (N - j) → ℂ :=
  fun a => A.lieVec hj P τ (fun b => A.emb τ (v a b))

theorem HermDatum.gramLie_eq (A : HermDatum Em Ψ N j) (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    {ρ : ℕ} (v : Fin ρ → Fin N → Em) : A.gramLie hj P τ v = gramVec (A.lieFam hj P τ v) := by
  ext a b
  simp only [HermDatum.gramLie, gramVec, colMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rfl

def HodgeAlong (A : HermDatum Em Ψ N j) (hj : j ≤ N) {d : ℕ}
    (per : (Fin d → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ) (I : Submodule (𝓞 Em) (Fin N → Em))
    (φ : (Fin d → ℂ) → ℝ) (U : Set (Fin d → ℂ)) : Prop :=
  ∀ (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∃ (m : ℕ) (u : Ψ → Fin m → Fin N → ℂ) (G : (Fin d → ℂ) → ℂ), DifferentiableOn ℂ G U ∧
      (∀ w ∈ U, ∀ τ, LinearIndependent ℂ
        (Sum.elim (A.lieFam hj (per w τ) τ v) fun b => A.lieVec hj (per w τ) τ (u τ b))) ∧
      (∀ w ∈ U, φ w = (1 / 2) * ∑ τ, Real.log
        (gramVec (Sum.elim (A.lieFam hj (per w τ) τ v) fun b => A.lieVec hj (per w τ) τ (u τ b))).det.re +
          (G w).re) ∧
      IsPsh U fun w => ∑ τ, Real.log
        (quotGram (A.lieFam hj (per w τ) τ v) fun b => A.lieVec hj (per w τ) τ (u τ b)).det.re

theorem HermDatum.isPsh_two_mul_sub_log_nz (A : HermDatum Em Ψ N j) (hj : j ≤ N) {d : ℕ}
    {U : Set (Fin d → ℂ)} (hU : IsOpen U) (per : (Fin d → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (I : Submodule (𝓞 Em) (Fin N → Em)) (φ : (Fin d → ℂ) → ℝ) (hI : ∃ ρ v, IsNzFamily I ρ v)
    (hH : HodgeAlong A hj per I φ U) :
    IsPsh U fun w => 2 * φ w - Real.log (A.nz hj (per w) I) := by
  classical
  have key : ∃ (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v ∧ ∀ P : Ψ → Matrix (Fin N) (Fin N) ℂ,
      A.nz hj P I = (∏ τ, (A.gramLie hj (P τ) τ v).det.re) /
        ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) :=
    ⟨hI.choose, hI.choose_spec.choose, hI.choose_spec.choose_spec, fun P => by
      rw [HermDatum.nz, dif_pos hI]⟩
  obtain ⟨ρ, v, hv, hnz⟩ := key
  obtain ⟨m, u, G, hG, hfr, htie, hB⟩ := hH ρ v hv
  have hidx : (0 : ℝ) < ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero hv.2.2.2)
  refine isPsh_congr' (fun w hw => ?_) (isPsh_add_re_add_const hU hB (hG.const_mul 2)
    (Real.log ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)))
  have hsplit := fun τ => log_det_gramVec_sum (A.lieFam hj (per w τ) τ v)
    (fun b => A.lieVec hj (per w τ) τ (u τ b)) (hfr w hw τ)
  have hprod : Real.log (∏ τ, (A.gramLie hj (per w τ) τ v).det.re) =
      ∑ τ, Real.log (gramVec (A.lieFam hj (per w τ) τ v)).det.re := by
    rw [Real.log_prod]
    · simp only [HermDatum.gramLie_eq]
    · intro τ _
      rw [HermDatum.gramLie_eq]
      exact (hsplit τ).1.ne'
  have hsum : ∑ τ, Real.log (gramVec (Sum.elim (A.lieFam hj (per w τ) τ v)
      fun b => A.lieVec hj (per w τ) τ (u τ b))).det.re =
      ∑ τ, Real.log (gramVec (A.lieFam hj (per w τ) τ v)).det.re +
        ∑ τ, Real.log (quotGram (A.lieFam hj (per w τ) τ v) fun b => A.lieVec hj (per w τ) τ (u τ b)).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => (hsplit τ).2
  have hpos : (0 : ℝ) < ∏ τ, (A.gramLie hj (per w τ) τ v).det.re := by
    refine Finset.prod_pos fun τ _ => ?_
    rw [HermDatum.gramLie_eq]
    exact (hsplit τ).1
  show _ = 2 * φ w - Real.log (A.nz hj (per w) I)
  rw [htie w hw, hnz, Real.log_div hpos.ne' hidx.ne', hprod, hsum]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  ring

end Hodge

def PhiISemipositive.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (Em : Type) [Field Em] [NumberField Em] [IsCMField Em]
    (D : FullerData II Ψ K ι Ω E Em) (I : Submodule (𝓞 Em) (Fin D.N → Em)),
    I ≤ D.herm.L → D.herm.IsIso I → D.herm.IsSat I → (∃ ρ v, IsNzFamily I ρ v) →
    ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → (Σ k, ι k) → ℂ), IsOpen U →
      (∀ w ∈ U, g w ∈ mcPts (mCoordIdeal D.y) \ D.Bd) → (∀ p, DifferentiableOn ℂ (fun w => g w p) U) →
      HodgeAlong D.herm (D.j_le.trans (Nat.sub_le _ _)) (fun w => D.per (g w)) I (fun w => phMu D.mu (g w)) U →
      IsPsh U fun w => D.phiI (g w) I

theorem PhiISemipositive.proof : PhiISemipositive.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D I _ _ _ hI d U g hU _ _ hH
  exact D.herm.isPsh_two_mul_sub_log_nz _ hU _ I _ hI hH

end GroundTheory.Heights₂.Heights.NineStatements
