import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.IsLocOpOfOk
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrixStatement

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def insW (d : SD σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)

section

variable (d : SD σ) (w : InfinitePlace F)

theorem insW_self (z : ℂ) : piInf (d.B.emb w) (insW d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.1, Pi.single_eq_same]

theorem insW_ne {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (insW d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.1, Pi.single_eq_of_ne hw]

theorem insW_fin (z : ℂ) : finOne F • insW d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.2.1]

theorem insW_add (z z' : ℂ) : insW d w (z + z') = insW d w z + insW d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, insW, insW, Pi.single_add, h.2.2.2.1]

end

def insL {d : SD σ} (R : RD d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (insW d w)

section

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

def Supp (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0

theorem cw_insL (v : Fin d.m → Fin d.n → ℂ) : d.cw w (insL R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [SD.cw, insL, Matrix.map_apply, insW_self]

theorem insL_supp (v : Fin d.m → Fin d.n → ℂ) : Supp w (insL R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [SD.cw, insL, Matrix.map_apply, insW_ne d w hw', Matrix.zero_apply]
  · ext i j
    simp only [insL, Matrix.smul_apply, Matrix.map_apply, insW_fin, Matrix.zero_apply]

theorem loc_insL (v : Fin d.m → Fin d.n → ℂ) : R.loc w (insL R w v) = v := by
  unfold RD.loc
  rw [cw_insL, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  ext i j
  simp

theorem insL_add (v v' : Fin d.m → Fin d.n → ℂ) : insL R w (v + v') = insL R w v + insL R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold insL
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, insW_add]

theorem insL_zero : insL R w 0 = 0 := by
  have h := insL_add R w 0 0
  rw [add_zero] at h
  calc insL R w 0 = insL R w 0 + insL R w 0 - insL R w 0 := by abel
    _ = insL R w 0 - insL R w 0 := by rw [← h]
    _ = 0 := sub_self _

theorem insL_loc {Z : Mx F E d.m d.n} (hZ : Supp w Z) : insL R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (insL R w (R.loc w Z)) = d.cw w Z
      rw [cw_insL]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (insL R w (R.loc w Z)) = d.cw w' Z
      rw [(insL_supp R w _).1 w' hw, hZ.1 w' hw]
  · rw [(insL_supp R w _).2, hZ.2]

theorem rest_inv (X Z : Mx F E d.m d.n) (hZ : Supp w Z) :
    (X + Z) - insL R w (R.loc w (X + Z)) = X - insL R w (R.loc w X) := by
  rw [KFock.loc_add' d R w X Z, insL_add, insL_loc R w hZ]
  abel

end

section

variable (d : SD σ)

theorem psi_add_right (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold SD.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, SD.tt, SD.tt, SD.tt, Matrix.trace_add, map_add, mul_add, AddChar.map_add_eq_mul]

theorem psi_add_left (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold SD.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, SD.tt, SD.tt, SD.tt, Matrix.trace_add, map_add, mul_add, AddChar.map_add_eq_mul]

theorem cw_gram (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold SD.gram SD.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]

theorem gram_supp_cmp (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : Supp w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [cw_gram]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [SD.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [SD.cw]
  · unfold SD.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp

theorem psi_zero_gram (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [SD.tt]

end

theorem zeta_ne {d : SD σ} (R : RD d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

section

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem frJ : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (zeta_ne R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]

end

theorem psi_at_w (d : SD σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    simp [Matrix.trace, SD.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]

theorem kernel {d : SD σ} (R : RD d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (insL R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (insL R w u)) = 0 := by
    intro w' hw
    rw [cw_gram, (insL_supp R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (insL R w u) = 0 := by
    unfold SD.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (insL R w u).map (cA σ) = (finOne F • insL R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (insL_supp R w u).2]
    simp
  have e1 : d.cw w (d.gram X (insL R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [cw_gram, cw_loc R w X, cw_insL, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [frJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [psi_at_w d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring

theorem locFT_sw {m n : ℕ} (C s : ℂ) (hs : s ≠ 0) (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSw f) :
    IsSw (fun u => C * ∫ v : Fin m → Fin n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) := by
  obtain ⟨φ, rfl⟩ := hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_fourier_transform_matrix m n C s hs φ
  exact ⟨ψ, hψ⟩

end PositivityTheory.SiegelWeilFormula.KW

end
