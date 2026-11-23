import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def eW (w : InfinitePlace F) : AF F := pairA F (Pi.single w 1) 0

theorem eW_mul_self (w : InfinitePlace F) : eW w * eW w = eW w := by
  apply Prod.ext
  · funext v
    show (eW w).1 v * (eW w).1 v = (eW w).1 v
    by_cases h : v = w
    · subst h
      simp [eW, pairA]
    · simp [eW, pairA, Pi.single_eq_of_ne h]
  · show (eW w).2 * (eW w).2 = (eW w).2
    have : (eW w).2 = 0 := rfl
    rw [this, mul_zero]

theorem finOne_mul_eW (w : InfinitePlace F) : finOne F * eW w = 0 := by
  apply Prod.ext
  · funext v
    show (finOne F).1 v * (eW w).1 v = (0 : AF F).1 v
    have : (finOne F).1 v = 0 := rfl
    rw [this, zero_mul]
    rfl
  · show (finOne F).2 * (eW w).2 = (0 : AF F).2
    have : (eW w).2 = 0 := rfl
    rw [this, mul_zero]
    rfl

theorem piInf_eW {w w' : InfinitePlace F} (τ : EmbOver E w') (z : AE F E) :
    piInf τ (eW w • z) = if w' = w then piInf τ z else 0 := by
  rw [St.piInf_smul]
  by_cases h : w' = w
  · subst h
    simp [eW, pairA]
  · rw [if_neg h]
    simp [eW, pairA, Pi.single_eq_of_ne h]

variable (d : SD σ)

theorem cw_mul (w : InfinitePlace F) {p q r : Type} [Fintype q] (M : Matrix p q (AE F E)) (N : Matrix q r (AE F E)) :
    d.cw w (M * N) = d.cw w M * d.cw w N := by
  simp only [SD.cw]
  exact Matrix.map_mul

theorem cw_one (w : InfinitePlace F) {p : Type} [DecidableEq p] : d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  simp only [SD.cw]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cw_transpose (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w Mᵀ = (d.cw w M)ᵀ := by
  simp only [SD.cw, Matrix.transpose_map]

theorem cw_eW_self (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w (eW w • M) = d.cw w M := by
  ext i j
  simp [SD.cw, piInf_eW]

theorem cw_eW_ne {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w' (eW w • M) = 0 := by
  ext i j
  simp [SD.cw, piInf_eW, h]

theorem finOne_eW_smul (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : finOne F • (eW w • M) = 0 := by
  rw [smul_smul, finOne_mul_eW, zero_smul]

theorem eW_smul_eq_iff (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' := by
  constructor
  · intro h
    rw [← cw_eW_self d w M, h, cw_eW_self]
  · intro h
    apply Place.cw_ext d
    · intro w'
      by_cases hw : w' = w
      · subst hw
        rw [cw_eW_self, cw_eW_self, h]
      · rw [cw_eW_ne d hw, cw_eW_ne d hw]
    · rw [finOne_eW_smul, finOne_eW_smul]

theorem eW_smul_of_supp {w : InfinitePlace F} {p q : Type} {Z : Matrix p q (AE F E)}
    (hZ : ∀ w', w' ≠ w → d.cw w' Z = 0) (hf : finOne F • Z = 0) : eW w • Z = Z := by
  apply Place.cw_ext d
  · intro w'
    by_cases hw : w' = w
    · subst hw
      rw [cw_eW_self]
    · rw [cw_eW_ne d hw, hZ w' hw]
  · rw [finOne_eW_smul, hf]

theorem gram_smul_right (a : AF F) (X Z : Mx F E d.m d.n) : d.gram X (a • Z) = a • d.gram X Z := by
  have : (a • Z).map (cA σ) = a • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  simp only [SD.gram, this, Matrix.mul_smul]

theorem gram_smul_left (a : AF F) (X Z : Mx F E d.m d.n) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [SD.gram, Matrix.transpose_smul, Matrix.smul_mul]

theorem gram_add (X Z : Mx F E d.m d.n) :
    d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) := by
  simp only [SD.gram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.map_add _ (map_add _)]
  abel

theorem cw_eq_one_of (w : InfinitePlace F) {M : Mx F E d.n d.n} (h : eW w • M = eW w • (1 : Mx F E d.n d.n)) :
    d.cw w M = 1 := by
  rw [(eW_smul_eq_iff d w M 1).1 h, cw_one]

namespace Step

variable {d} (R : RD d) (w : InfinitePlace F)

theorem stepN (hT : TAll) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  have hP := hT.2.1 F E σ d
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    have hZe : eW w • Z = Z := eW_smul_of_supp d hZ hf
    have h1 : d.gram X Z = eW w • d.gram X Z := by
      calc d.gram X Z = d.gram X (eW w • Z) := by rw [hZe]
        _ = _ := gram_smul_right d _ X Z
    have h2 : d.gram Z X = eW w • d.gram Z X := by
      calc d.gram Z X = d.gram (eW w • Z) X := by rw [hZe]
        _ = _ := gram_smul_left d _ Z X
    have h3 : d.gram Z Z = eW w • d.gram Z Z := by
      calc d.gram Z Z = d.gram (eW w • Z) Z := by rw [hZe]
        _ = _ := gram_smul_left d _ Z Z
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [gram_add, h1, h2, h3, ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ,
        Matrix.zero_mul, add_zero]
    simp only
    rw [key, hΨ X Z hZ hf]
  · funext X
    rw [(hP Φ hΦ).1 x β hx X, hTΦ]
    simp only [RD.tens, id]
    ring

theorem stepM (hT : TAll) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eW w • a'.1 = eW w • (1 : Mx F E d.n d.n)) :
    R.StepOK w x id (fun Ψ X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hP := hT.2.1 F E σ d
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h1 : d.cw w a'.1 = 1 := cw_eq_one_of d w ha
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, cw_one]
    rwa [cw_mul, h1, Matrix.mul_one] at h2
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ) (fun w' hw' => by rw [cw_mul, hZ w' hw', Matrix.zero_mul])
      (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X
    rw [(hP Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold RD.loc
      rw [cw_mul, cw_transpose, hc, Matrix.transpose_one, Matrix.mul_one]
    simp only [RD.tens, id, hl]
    ring

end Step

end PositivityTheory.SiegelWeilFormula.KAway

end
