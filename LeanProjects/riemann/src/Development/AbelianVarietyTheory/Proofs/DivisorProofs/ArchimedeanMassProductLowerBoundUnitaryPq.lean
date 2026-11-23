import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassLow

theorem perm_conj' {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix (Fin r) (Fin r) ℂ) :
    permM e * M * (permM e)ᵀ = M.submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, permM]

theorem det_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) (s : realSU Ψ G) (u : UpqT (p ρ) (q ρ))
    (hu : UpqT.mat u * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) :
    (UpqT.mat u).det = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := MassUp.inv_facts hI ρ
  set S := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  set P := permM (e ρ)
  have hS : S.det = 1 := (s.2 (σ ρ)).1
  set M := (Pᵀ * A ρ) * S * mat x (σ ρ) with hM
  have hx : mat x (σ ρ) * M = S * mat x (σ ρ) := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : UpqT.mat u = P * M * Pᵀ := by
    calc UpqT.mat u = UpqT.mat u * (A ρ * (mat x (σ ρ) * Pᵀ)) := by rw [h3, Matrix.mul_one]
      _ = A ρ * (S * mat x (σ ρ)) * Pᵀ := by
        rw [← Matrix.mul_assoc, hu]; simp only [Matrix.mul_assoc]
      _ = P * M * Pᵀ := by
        rw [← hx, ← Matrix.mul_assoc, (hI ρ).2]
  rw [hu', perm_conj', Matrix.det_submatrix_equiv_self, hM, Matrix.det_mul, Matrix.det_mul, hS, mul_one,
    ← Matrix.det_mul, h1, Matrix.det_one]

theorem arith (f r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) :
    (1 / 16 : ℝ) ^ (f * r ^ 2) * (8 * ε) ^ (f * (r ^ 2 - 1)) ≤ (ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1)) ^ f := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (1 / 16 : ℝ) ^ (r ^ 2) * (8 * ε) ^ (r ^ 2 - 1) ≤ ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) := by
    have hrp : (r : ℝ) ^ (r - 1) ≤ 2 ^ (r ^ 2) := by
      have h1 : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (r : ℝ) ^ (r - 1) ≤ ((2 : ℝ) ^ r) ^ (r - 1) := pow_le_pow_left₀ hr0.le h1 _
        _ = 2 ^ (r * (r - 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h8 : (8 : ℝ) ^ (r ^ 2 - 1) ≤ 8 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    rw [le_div_iff₀ (pow_pos hr0 _), mul_pow]
    have hε' : 0 ≤ ε ^ (r ^ 2 - 1) := pow_nonneg hε.le _
    calc (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2 - 1) * ε ^ (r ^ 2 - 1)) * (r : ℝ) ^ (r - 1)
        ≤ (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) * 2 ^ (r ^ 2) := by gcongr
      _ = ((1 / 16 : ℝ) * 8 * 2) ^ (r ^ 2) * ε ^ (r ^ 2 - 1) := by rw [mul_pow, mul_pow]; ring
      _ = ε ^ (r ^ 2 - 1) := by norm_num
  have e1 : (1 / 16 : ℝ) ^ (f * r ^ 2) = ((1 / 16 : ℝ) ^ (r ^ 2)) ^ f := by rw [← pow_mul, mul_comm f]
  have e2 : (8 * ε) ^ (f * (r ^ 2 - 1)) = ((8 * ε) ^ (r ^ 2 - 1)) ^ f := by rw [← pow_mul, mul_comm f]
  rw [e1, e2, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) key f

theorem massLow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))) (ρ₀ : κ), 1 ≤ r → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S ≤ Measure.pi m (π ⁻¹' S ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m ρ₀ hr hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hΨ : 1 ≤ Ψ.card := by
    rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨ρ₀⟩
  have hG : G.det ≠ 0 := MassUp.det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (MassUp.inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set T : Set (∀ ρ, UpqT (p ρ) (q ρ)) := {b | 0 < (UpqT.mat (b ρ₀)).det.im} with hTdef
  have hTo : IsOpen T := isOpen_lt continuous_const
    (Complex.continuous_im.comp ((GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply ρ₀)).matrix_det))
  have hTm : MeasurableSet T := hTo.measurableSet
  set ν := (μ.restrict T).map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := MassUp.exists_lift E r κ p q Ψ G x σ A e hI s
    have hd : (UpqT.mat (b₀ ρ₀)).det = 1 := det_lift hI ρ₀ s (b₀ ρ₀) (hb₀ ρ₀)
    have hpre : (fun b => b₀ * b) ⁻¹' T = T := by
      ext b
      simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Pi.mul_apply]
      rw [show UpqT.mat (b₀ ρ₀ * b ρ₀) = UpqT.mat (b₀ ρ₀) * UpqT.mat (b ρ₀) from rfl, Matrix.det_mul, hd, one_mul]
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀)]
    congr 1
    calc (μ.restrict T).map (fun b => b₀ * b)
        = (μ.restrict ((fun b => b₀ * b) ⁻¹' T)).map (fun b => b₀ * b) := by rw [hpre]
      _ = (μ.map (fun b => b₀ * b)).restrict T := (Measure.restrict_map (measurable_const_mul b₀) hTm).symm
      _ = μ.restrict T := by rw [map_mul_left_eq_self]
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1

  have hup := MassUp.massUp E r κ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro K hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [hν, Measure.map_apply hπm hKm]
    calc μ.restrict T (π ⁻¹' K) ≤ μ (π ⁻¹' K) := Measure.restrict_le_self _
      _ ≤ _ := hup K hKm
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef

  have hplace := fun ρ => GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εu, hεu, hbu⟩ := GlobalTheory.T.riemannianHaar_frameBall_le E r κ p q Ψ G x σ A e hr hI
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εu / 2 with hεdef
  have hεm : ε < min δ εu := half_lt_self (lt_min hδ hεu)
  have hε : 0 < ε := half_pos (lt_min hδ hεu)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεu' : ε < εu := lt_of_lt_of_le hεm (min_le_right _ _)
  have hopen : IsOpen (frBall Ψ G x ε) := by
    have hc' : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc' τ a b) continuous_const
  set L := ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) with hL
  have hlow : ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := by
    rw [hν, Measure.map_apply hπm hopen.measurableSet, Measure.restrict_apply (hπm hopen.measurableSet),
      MassUp.preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε]
    have hsub : Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | (∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε) ∧
        0 < (UpqT.mat u).det.im}) ⊆ Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) |
          ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) ∩ T := by
      intro b hb
      simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hb
      exact ⟨fun ρ _ => (hb ρ).1, (hb ρ₀).2⟩
    refine le_trans ?_ (measure_mono hsub)
    rw [hμ, Measure.pi_pi]
    calc ENNReal.ofReal (L ^ Ψ.card) = ∏ _ρ : κ, ENNReal.ofReal L := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := Finset.prod_le_prod' fun ρ _ => by
          have := hbp ρ ε hε (hεδ ρ)
          rw [hpq ρ] at this
          exact this
  have hupB := hbu ε hε hεu'
  set U := (8 * ε) ^ (Ψ.card * (r ^ 2 - 1)) with hU
  have hcU : L ^ Ψ.card ≤ (c : ℝ) * U := by
    have h1 : ENNReal.ofReal (L ^ Ψ.card) ≤ ENNReal.ofReal ((c : ℝ) * U) := by
      calc ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := hlow
        _ = (c : ℝ≥0∞) * riemHaar Ψ G x (frBall Ψ G x ε) := by
          conv_lhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal U := mul_le_mul_of_nonneg_left hupB (zero_le)
        _ = ENNReal.ofReal ((c : ℝ) * U) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg _) (by positivity))).1 h1
  have hK := arith Ψ.card r ε hr hε
  have hUpos : 0 < U := by positivity
  have hcK : (1 / 16 : ℝ) ^ (Ψ.card * r ^ 2) ≤ c :=
    le_of_mul_le_mul_right (hK.trans hcU) hUpos
  calc ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S
      ≤ (c : ℝ≥0∞) * riemHaar Ψ G x S := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcK
    _ = ν S := by
        conv_rhs => rw [hc]
        rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    _ = μ (π ⁻¹' S ∩ T) := by
        rw [hν, Measure.map_apply hπm hS, Measure.restrict_apply (hπm hS)]

end GlobalTheory.CovTop.VolUp.MassLow
