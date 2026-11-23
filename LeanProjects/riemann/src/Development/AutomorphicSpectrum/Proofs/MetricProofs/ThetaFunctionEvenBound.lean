import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSymplecticBasisPrincipalPolarizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianFormPeriodMatrixNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealPartGramInSymplecticGroupStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplierStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaZeroDivisorJetBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NForm

open Matrix in
theorem periodMatrix_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : (periodMatrix X Y).map Complex.im = Y := by
  ext i j; simp [periodMatrix]

open Matrix in
theorem periodMatrix_isSymm {g : ℕ} {X Y : Matrix (Fin g) (Fin g) ℝ} (hX : X.IsSymm) (hY : Y.IsSymm) :
    (periodMatrix X Y).IsSymm := by
  ext i j
  have h1 := congrFun (congrFun hX i) j
  have h2 := congrFun (congrFun hY i) j
  simp only [Matrix.transpose_apply] at h1 h2
  simp [periodMatrix, h1, h2]

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    hermForm Hm (x + y) w = hermForm Hm x w + hermForm Hm y w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w x y : Fin g → ℂ) :
    hermForm Hm w (x + y) = hermForm Hm w x + hermForm Hm w y := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (x w : Fin g → ℂ) :
    hermForm Hm (k • x) w = k * hermForm Hm x w := by
  rw [← Int.cast_smul_eq_zsmul ℂ k x]
  simp [hermForm, smul_dotProduct]

theorem hermForm_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (w x : Fin g → ℂ) :
    hermForm Hm w (k • x) = k * hermForm Hm w x := by
  rw [← Int.cast_smul_eq_zsmul ℂ k x]
  have h : star ((k : ℂ) • x) = (k : ℂ) • star x := by
    ext i; simp
  simp [hermForm, h, Matrix.mulVec_smul, dotProduct_smul]

theorem hermForm_sum_left {g : ℕ} {J : Type} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Finset J)
    (f : J → Fin g → ℂ) (w : Fin g → ℂ) : hermForm Hm (∑ α ∈ s, f α) w = ∑ α ∈ s, hermForm Hm (f α) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_left, ih]

theorem hermForm_sum_right {g : ℕ} {J : Type} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Finset J)
    (f : J → Fin g → ℂ) (w : Fin g → ℂ) : hermForm Hm w (∑ α ∈ s, f α) = ∑ α ∈ s, hermForm Hm w (f α) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right, ih]

theorem hermForm_sum {g : ℕ} {J : Type} [Fintype J] (Hm : Matrix (Fin g) (Fin g) ℂ) (v : J → Fin g → ℂ)
    (m n : J → ℤ) :
    hermForm Hm (∑ α, m α • v α) (∑ β, n β • v β) =
      ∑ α, ∑ β, ((m α * n β : ℤ) : ℂ) * hermForm Hm (v α) (v β) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hermForm_sum_right]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hermForm_zsmul_left, hermForm_zsmul_right]
  push_cast
  ring

theorem mulVec_zsum {g : ℕ} {J : Type} [Fintype J] (h : Matrix (Fin g) (Fin g) ℂ) (v : J → Fin g → ℂ)
    (m : J → ℤ) : h.mulVec (∑ α, m α • v α) = ∑ α, m α • h.mulVec (v α) := by
  calc h.mulVec (∑ α, m α • v α) = Matrix.mulVecLin h (∑ α, m α • v α) := rfl
    _ = ∑ α, Matrix.mulVecLin h (m α • v α) := map_sum _ _ _
    _ = ∑ α, m α • h.mulVec (v α) := Finset.sum_congr rfl fun α _ => by rw [map_zsmul]; rfl

theorem zsum_single {g : ℕ} (m : Fin g → ℤ) :
    (∑ i, m i • (Pi.single i 1 : Fin g → ℂ)) = fun i => (m i : ℂ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_reduced (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hint : ∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k)
    (hdual : ∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) :
    ∃ (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (h : Matrix (Fin g) (Fin g) ℂ)
      (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧ IsReducedImaginaryPart Y ρ ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ x : Λ, h.mulVec (x : Fin g → ℂ) = (fun i => ((bs.repr x (Sum.inl i) : ℤ) : ℂ)) +
        (periodMatrix X Y).mulVec fun i => ((bs.repr x (Sum.inr i) : ℤ) : ℂ)) ∧
      (∀ x y : Λ, (hermForm Hm (x : Fin g → ℂ) (y : Fin g → ℂ)).im =
        ((∑ i, (bs.repr x (Sum.inr i) * bs.repr y (Sum.inl i) -
          bs.repr x (Sum.inl i) * bs.repr y (Sum.inr i)) : ℤ) : ℝ)) := by
  obtain ⟨bs0, hJ0⟩ := GlobalTheory.T.exists_symplectic_basis_principal_polarization g Λ Hm hd hs hH hpos hint hdual
  obtain ⟨h0, X0, Y0, -, hX0, hY0, -, -, -, hG0⟩ := GlobalTheory.T.hermitian_form_period_matrix_normal_form g Hm (fun α => (bs0 α : Fin g → ℂ)) hH hpos hJ0
  have hS := (SiegelCoordinates.intersectionNumber_baseChange g).1 X0 Y0 hX0 hY0
  obtain ⟨bs, ρ, hρ, hρ2, hJ, hfirst, hmin, hdet⟩ :=
    GlobalTheory.T.real_part_gram_in_symplectic_group g Λ Hm bs0 hH hpos hJ0 (by rw [hG0]; exact hS.1) (by rw [hG0]; exact hS.2)
  obtain ⟨h, X, Y, hh, hX, hY, hHh, hin, hinr, -⟩ := GlobalTheory.T.hermitian_form_period_matrix_normal_form g Hm (fun α => (bs α : Fin g → ℂ)) hH hpos hJ
  have hτim : (periodMatrix X Y).map Complex.im = Y := periodMatrix_im X Y
  have hexp : ∀ x : Λ, (x : Fin g → ℂ) = ∑ α, (bs.repr x α) • (bs α : Fin g → ℂ) := fun x => by
    have := congrArg Subtype.val (bs.sum_repr x)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    exact this.symm
  have hYe : ∀ i j, Y⁻¹ i j = (hermForm Hm (bs (Sum.inl i) : Fin g → ℂ) (bs (Sum.inl j) : Fin g → ℂ)).re := by
    intro i j
    rw [hHh, hin, hin, hermForm, GlobalTheory.SiegelNormalForm.form_single, GlobalTheory.CanTh.imInv, hτim]
    simp
  have hred : IsReducedImaginaryPart Y ρ := by
    refine ⟨hρ, hρ2, by rw [hYe]; exact hfirst, fun l hl => ?_, ?_⟩
    · let x : Λ := ∑ i, l i • bs (Sum.inl i)
      have hxc : (x : Fin g → ℂ) = ∑ i, l i • (bs (Sum.inl i) : Fin g → ℂ) := by simp [x]
      have hhx : h.mulVec (x : Fin g → ℂ) = fun i => (l i : ℂ) := by
        rw [hxc, mulVec_zsum]
        simp only [hin]
        exact zsum_single l
      have hx0 : x ≠ 0 := by
        intro e
        rw [e] at hhx
        apply hl
        funext i
        have := congrFun hhx i
        simpa using this.symm
      have := hmin x hx0
      rw [hHh, hhx, hermForm, GlobalTheory.CanTh.imInv, hτim] at this
      convert this using 1
      have hst : star (fun i => (l i : ℂ)) = fun i : Fin g => (l i : ℂ) := by
        ext i; simp
      rw [hst]
      simp only [qf, intVec, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp
    · have : Y⁻¹ = Matrix.of fun i j : Fin g => (hermForm Hm (bs (Sum.inl i) : Fin g → ℂ) (bs (Sum.inl j) : Fin g → ℂ)).re := by
        ext i j; simp [hYe]
      rw [this]
      simpa using hdet
  refine ⟨bs, h, X, Y, ρ, hh, hX, hY, hred, hHh, fun x => ?_, fun x y => ?_⟩
  · rw [hexp x, mulVec_zsum, Fintype.sum_sum_type]
    simp only [hin, hinr]
    rw [zsum_single (fun i => bs.repr x (Sum.inl i))]
    congr 1
    have e : (fun i => ((bs.repr x (Sum.inr i) : ℤ) : ℂ)) = ∑ i, bs.repr x (Sum.inr i) • (Pi.single i 1 : Fin g → ℂ) :=
      (zsum_single (fun i => bs.repr x (Sum.inr i))).symm
    rw [e, mulVec_zsum]
  · rw [hexp x, hexp y, hermForm_sum, Complex.im_sum]
    simp only [Complex.im_sum]
    have hc : ∀ (k : ℤ) (c : ℂ), ((k : ℂ) * c).im = (k : ℝ) * c.im := fun k c => by simp
    simp only [hc, hJ, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply]
    simp only [mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_neg, mul_ite, _root_.mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_neg_distrib]
    push_cast
    rw [Finset.sum_sub_distrib]
    ring

theorem nform : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), 1 ≤ g → (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → (∀ l : a.u.Λ, a.χ l ^ 2 = 1) → ∀ (θ : (Fin g → ℂ) → ℂ) (b : ℝ), a.IsTheta 1 θ → a.IsThetaMeanSquareNorm θ b → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(2 * g) ∧ (∀ w, a.nrm 1 θ w ≤ b * Real.exp (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ∧ ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ), (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) → Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := by
  obtain ⟨C, hC, hB⟩ := ThetaBound.full
  refine ⟨C, hC.le, ?_⟩
  intro S G _ _ P z g a hg hint hdual hsc hsq θ b hθ hL2
  haveI : NeZero g := ⟨by omega⟩
  obtain ⟨hH, hpos, hχn, -⟩ := a.ah
  obtain ⟨bs, h, X, Y, ρ, hh, hX, hY, hR, hHh, hcoord, him⟩ :=
    exists_reduced g a.u.Λ a.Hm a.u.discrete a.u.full hH hpos hint hdual
  have hτim : (periodMatrix X Y).map Complex.im = Y := periodMatrix_im X Y
  have hYs : Y.IsSymm := by
    have := hY.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτs : (periodMatrix X Y).IsSymm := periodMatrix_isSymm hX hYs
  have hτp : ((periodMatrix X Y).map Complex.im).PosDef := by rw [hτim]; exact hY
  have hhu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hh
  have hhi : Function.Injective h.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hhu
  have hxy : ∀ m n : Fin g → ℤ, ∃ x : a.u.Λ,
      h.mulVec (x : Fin g → ℂ) = (fun i => (m i : ℂ)) + (periodMatrix X Y).mulVec (fun i => (n i : ℂ)) ∧
      (∀ i, bs.repr x (Sum.inl i) = m i) ∧ (∀ i, bs.repr x (Sum.inr i) = n i) := by
    intro m n
    have hr : ∀ α, bs.repr (bs.equivFun.symm (Sum.elim m n)) α = Sum.elim m n α := fun α => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨bs.equivFun.symm (Sum.elim m n), ?_, fun i => hr _, fun i => hr _⟩
    rw [hcoord]
    simp only [hr, Sum.elim_inl, Sum.elim_inr]
  have hmem : ∀ lam, lam ∈ a.u.Λ ↔ ∃ m n : Fin g → ℤ,
      h.mulVec lam = (fun i => (m i : ℂ)) + (periodMatrix X Y).mulVec (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · intro hl
      exact ⟨_, _, hcoord ⟨lam, hl⟩⟩
    · rintro ⟨m, n, e⟩
      obtain ⟨x, hx, -, -⟩ := hxy m n
      have : lam = x := hhi (e.trans hx.symm)
      rw [this]
      exact x.2
  obtain ⟨a₀, c₀, ha₀, hc₀, hχ⟩ := GlobalTheory.T.semicharacter_theta_characteristic g a.u.Λ bs a.χ (fun l l' => by
    have := hsc l l'
    rw [show (a.herm l l').im = _ from him l l'] at this
    exact this) hsq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.theta_function_canonical_multiplier g (periodMatrix X Y) h a.Hm a₀ c₀ θ hτs hτp hh hHh hθ.1 (fun m n lam hlam w => by
    obtain ⟨x, hx, hxm, hxn⟩ := hxy m n
    obtain rfl : lam = x := hhi (hlam.trans hx.symm)
    have := hθ.2 x w
    rw [pow_one, hχ x] at this
    have e1 : (fun i => bs.repr x (Sum.inl i)) = m := funext hxm
    have e2 : (fun i => bs.repr x (Sum.inr i)) = n := funext hxn
    rw [e1, e2] at this
    exact this)
  have hb2 := GlobalTheory.T.theta_function_canonical_form g (periodMatrix X Y) h a.Hm a₀ c₀ a.u.Λ θ κ b hτs hτp hh ha₀ hc₀ hmem hHh hκ
    (fun l hl => ⟨a.χ ⟨l, hl⟩, hχn _, fun w => by
      have := hθ.2 ⟨l, hl⟩ w
      rw [pow_one] at this
      exact this⟩) hL2.1 hL2.2
  rw [hτim] at hb2
  have hbpos := hL2.1
  have hDpos : (0 : ℝ) < 2 ^ g * Y.det := mul_pos (by positivity) hY.det_pos
  set β : ℝ := ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) with hβ
  have hβpos : 0 < β := Real.rpow_pos_of_pos hDpos _
  have hβ2 : β ^ 2 = (Real.sqrt (2 ^ g * Y.det))⁻¹ := by
    rw [hβ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, ← Real.rpow_neg hDpos.le]
    norm_num
  have hbκ : b = ‖κ‖ * β := by
    have : b ^ 2 = (‖κ‖ * β) ^ 2 := by rw [mul_pow, hβ2]; exact hb2
    exact (sq_eq_sq₀ hbpos.le (by positivity)).1 this
  have hκpos : 0 < ‖κ‖ := by
    rcases (norm_nonneg κ).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hbκ
      exact absurd hbκ hbpos.ne'
    · exact h0
  have hκ0 : κ ≠ 0 := norm_pos_iff.1 hκpos

  let Hq : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet h hh)).restrictScalars ℝ
  have hHq (w : Fin g → ℂ) : Hq w = h.mulVec w := rfl
  let L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.ofBijective (GlobalTheory.ThetaMean.periodMap (periodMatrix X Y))
      (GlobalTheory.ThetaMean.periodMap_bijective hτp)).trans Hq.symm
  have hLap (p) : h.mulVec (L p) = GlobalTheory.ThetaMean.periodMap (periodMatrix X Y) p := by
    rw [← hHq]
    exact Hq.apply_symm_apply _
  have hcoordL : ∀ w, h.mulVec w = (periodMatrix X Y).mulVec (fun i => (L.symm w (Sum.inr i) : ℂ)) +
      (fun i => (L.symm w (Sum.inl i) : ℂ)) := by
    intro w
    have := hLap (L.symm w)
    rw [L.apply_symm_apply, GlobalTheory.ThetaMean.periodMap_apply, add_comm] at this
    exact this
  have hE := GlobalTheory.T.theta_norm_in_period_coordinates g X Y a₀ c₀ h a.Hm θ κ hX hY hHh hκ
  set E : ℝ := g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g) with hEdef
  have hhalf : ∀ (t : Fin g → ℝ), (∀ i, t i = 0 ∨ t i = 1 / 2) → ∀ i, ∃ m : ℤ, t i = m / 2 := by
    intro t ht i
    rcases ht i with e | e
    · exact ⟨0, by simp [e]⟩
    · exact ⟨1, by simp [e]⟩
  have hbd := (hB g X Y ρ a₀ c₀ hX hY hR (hhalf a₀ ha₀) (hhalf c₀ hc₀)).2
  let d : (Fin g → ℂ) → ℝ := fun w =>
    Metric.infDist (L.symm w (Sum.inr 0) + a₀ 0) (Set.range ((↑) : ℤ → ℝ))
  have hρ : 0 < ρ := hR.pos
  have hnb : ∀ w, a.nrm 1 θ w ≤ b * Real.exp (-(Real.pi / (2 * ρ ^ 2)) * d w ^ 2 + E) := by
    intro w
    have h1 := hE (fun i => L.symm w (Sum.inr i)) (fun i => L.symm w (Sum.inl i)) w (hcoordL w)
    have h2 := hbd (fun i => L.symm w (Sum.inr i)) (fun i => L.symm w (Sum.inl i))
    have h3 : a.nrm 1 θ w = ‖κ‖ * thetaNorm X Y a₀ c₀ (fun i => L.symm w (Sum.inr i))
        (fun i => L.symm w (Sum.inl i)) := h1
    rw [h3, hbκ, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hκpos.le
  refine ⟨ρ, hρ, Real.le_sqrt_of_sq_le hR.sq_le, fun w => ?_, ?_⟩
  · refine (hnb w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hbpos.le)
    have : 0 ≤ Real.pi / (2 * ρ ^ 2) * d w ^ 2 := by positivity
    linarith
  have hnz : ∃ w, θ w ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := Function.ne_iff.1 (GlobalTheory.CanTh.canTh_ne_zero (a := a₀) (b := c₀) hτs hτp)
    obtain ⟨w, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hhu) ζ
    exact ⟨w, by rw [hκ]; exact mul_ne_zero hκ0 hζ⟩
  have hLint : ∀ p, L p ∈ a.u.Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ) := by
    intro p
    rw [hmem, hLap]
    constructor
    · rintro ⟨m, n, e⟩
      refine ⟨Sum.elim m n, (GlobalTheory.ThetaMean.periodMap_bijective hτp).1 ?_⟩
      rw [e, GlobalTheory.ThetaMean.periodMap_apply]
      simp
    · rintro ⟨k, rfl⟩
      refine ⟨fun i => k (Sum.inl i), fun i => k (Sum.inr i), ?_⟩
      rw [GlobalTheory.ThetaMean.periodMap_apply]
      simp
  have hinv : ∀ l ∈ a.u.Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0 := by
    intro l hl w
    have := hθ.2 ⟨l, hl⟩ w
    rw [pow_one] at this
    have hne : a.χ ⟨l, hl⟩ ≠ 0 := fun e => by
      have := hχn ⟨l, hl⟩
      rw [e] at this
      simp at this
    change θ (w + l) = _ at this
    rw [this]
    simp [hne, Complex.exp_ne_zero]
  filter_upwards [GlobalTheory.T.theta_zero_divisor_jet_bound g a.u.Λ θ L (Sum.inr 0) (a₀ 0) hθ.1 hnz hLint hinv (hhalf a₀ ha₀ 0)] with m hm
  intro Ix _ r hr hu
  obtain ⟨hne, hcard⟩ := hm Ix r hr hu
  refine ⟨hne, ?_⟩
  classical
  have hper : ∀ i, Real.pi / (2 * ρ ^ 2) * d (r i) ^ 2 - E ≤ -Real.log (a.nrm 1 θ (r i) / b) := by
    intro i
    have hn0 : 0 < a.nrm 1 θ (r i) := by
      unfold ArchFrame.nrm
      exact mul_pos (norm_pos_iff.2 (hr i).2) (Real.exp_pos _)
    have h1 : a.nrm 1 θ (r i) / b ≤ Real.exp (-(Real.pi / (2 * ρ ^ 2)) * d (r i) ^ 2 + E) := by
      rw [div_le_iff₀ hbpos, mul_comm]
      exact hnb _
    have h2 := (Real.log_le_iff_le_exp (div_pos hn0 hbpos)).2 h1
    linarith
  let A : Finset Ix := Finset.univ.filter fun i => (1 / 4 : ℝ) ≤ d (r i)
  have hA : {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) (Sum.inr 0) + a₀ 0) (Set.range ((↑) : ℤ → ℝ))}.ncard = A.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [A, d]
  rw [hA] at hcard
  have hsum : (A.card : ℝ) / 16 ≤ ∑ i, d (r i) ^ 2 := by
    calc (A.card : ℝ) / 16 = ∑ i ∈ A, (1 / 16 : ℝ) := by simp; ring
      _ ≤ ∑ i ∈ A, d (r i) ^ 2 := Finset.sum_le_sum fun i hi => by
          have : (1 / 4 : ℝ) ≤ d (r i) := (Finset.mem_filter.1 hi).2
          nlinarith
      _ ≤ ∑ i, d (r i) ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => sq_nonneg _
  have hcard' : (Fintype.card Ix : ℝ) ≤ 3 * A.card := by exact_mod_cast hcard
  have hq : 0 < Real.pi / (2 * ρ ^ 2) := by positivity
  calc (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - E)
      = Real.pi / (2 * ρ ^ 2) * ((Fintype.card Ix : ℝ) / 48) - Fintype.card Ix * E := by
        field_simp
        ring
    _ ≤ Real.pi / (2 * ρ ^ 2) * (∑ i, d (r i) ^ 2) - Fintype.card Ix * E := by
        have : (Fintype.card Ix : ℝ) / 48 ≤ ∑ i, d (r i) ^ 2 := by linarith
        nlinarith
    _ = ∑ i, (Real.pi / (2 * ρ ^ 2) * d (r i) ^ 2 - E) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        simp
    _ ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := Finset.sum_le_sum fun i _ => hper i

end GlobalTheory.CompanionTheory.Ar.NForm
