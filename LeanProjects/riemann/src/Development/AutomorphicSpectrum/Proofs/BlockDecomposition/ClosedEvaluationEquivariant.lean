import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.TwC
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_false_eq (I T : ℕ) (a : Fin I) :
    ePG I T ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd T a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem ePG_true_eq (I T : ℕ) (b : Fin T) :
    ePG I T ⟨true, b⟩ = Fin.castSucc (Fin.natAdd I b) := by
  apply Fin.ext
  simp [ePG]

theorem colMat_castSucc_last (n : ℕ) (v : Fin n → k) (r : Fin n) :
    colMat k n v (Fin.castSucc r) (Fin.last n) = v r := by
  simp [colMat]

theorem colMat_last_last (n : ℕ) (v : Fin n → k) : colMat k n v (Fin.last n) (Fin.last n) = 0 := by
  simp [colMat]

theorem colMat_of_ne (n : ℕ) (v : Fin n → k) (r : Fin (n + 1)) {c : Fin (n + 1)} (hc : c ≠ Fin.last n) :
    colMat k n v r c = 0 := by
  simp [colMat, hc]

def uG (I T : ℕ) (v : Fin (I + T) → k) : Mir k (I + T) :=
  ⟨unip k (I + T) (Multiplicative.ofAdd v), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uG_add (I T : ℕ) (v w : Fin (I + T) → k) : uG I T (v + w) = uG I T v * uG I T w := by
  apply Subtype.ext
  show unip k (I + T) (Multiplicative.ofAdd (v + w)) = unip k _ _ * unip k _ _
  rw [ofAdd_add, map_mul]

theorem uG_comm (I T : ℕ) (v w : Fin (I + T) → k) : uG I T v * uG I T w = uG I T w * uG I T v := by
  rw [← uG_add, ← uG_add]
  exact congrArg _ (add_comm v w)

theorem uG_mem_H (I T : ℕ) (c : Fin I → k) : uG I T (Fin.append c (0 : Fin T → k)) ∈ HPG k I T := by
  show ((uG I T (Fin.append c (0 : Fin T → k)) : Mir k (I + T)) : GL (Fin (I + T + 1)) k) ∈ parab k (ePG I T)
  rw [mem_parab_iff]
  intro a b x y hab
  obtain ⟨rfl, rfl⟩ : a = true ∧ b = false := by
    cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd hab (by decide)
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨true, x⟩) (ePG I T ⟨false, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨true, x⟩) (ePG I T ⟨false, y⟩) = 0
  rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simp)), zero_add]
  by_cases hy : y = Fin.last I
  · subst hy
    rw [ePG_false_last, ePG_true_eq, colMat_castSucc_last, Fin.append_right]
    rfl
  · exact colMat_of_ne _ _ _ fun e => hy ((ePG_false_eq_last_iff I T y).1 e)

theorem pgProj_snd (I T : ℕ) (c : Fin I → k) :
    (pgProj k I T ⟨uG I T (Fin.append c (0 : Fin T → k)), uG_mem_H I T c⟩).2 = 1 := by
  ext x y
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨true, x⟩) (ePG I T ⟨true, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨true, x⟩) (ePG I T ⟨true, y⟩) = (1 : Matrix _ _ k) x y
  rw [colMat_of_ne _ _ _ (by rw [ePG_true_eq]; exact Fin.castSucc_ne_last _), add_zero]
  by_cases h : x = y
  · subst h; simp
  · rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simpa using h)), Matrix.one_apply_ne h]

theorem pgProj_fst (I T : ℕ) (c : Fin I → k) :
    (((pgProj k I T ⟨uG I T (Fin.append c (0 : Fin T → k)), uG_mem_H I T c⟩).1 : Mir k I) : GL (Fin (I + 1)) k) =
      unip k I (Multiplicative.ofAdd c) := by
  ext x y
  show (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨false, x⟩) (ePG I T ⟨false, y⟩) +
    colMat k (I + T) (Fin.append c (0 : Fin T → k)) (ePG I T ⟨false, x⟩) (ePG I T ⟨false, y⟩) =
    (1 : Matrix _ _ k) x y + colMat k I c x y
  induction y using Fin.lastCases with
  | last =>
    induction x using Fin.lastCases with
    | last => rw [ePG_false_last, colMat_last_last, colMat_last_last]; simp
    | cast a =>
      rw [ePG_false_last, ePG_false_eq, colMat_castSucc_last, colMat_castSucc_last, Fin.append_left,
        Matrix.one_apply_ne (Fin.castSucc_ne_last _), Matrix.one_apply_ne (Fin.castSucc_ne_last _)]
  | cast b =>
    rw [colMat_of_ne _ _ _ (by rw [ePG_false_eq]; exact Fin.castSucc_ne_last _),
      colMat_of_ne _ _ _ (Fin.castSucc_ne_last _)]
    by_cases h : x = Fin.castSucc b
    · subst h; simp
    · rw [Matrix.one_apply_ne ((ePG I T).injective.ne (by simpa using h)), Matrix.one_apply_ne h]

theorem append_split (I T : ℕ) (v : Fin (I + T) → k) :
    v = Fin.append (fun a => v (Fin.castAdd T a)) (0 : Fin T → k) +
      Fin.append (0 : Fin I → k) (fun b => v (Fin.natAdd I b)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp
  · simp

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) : dEmb k i t d = uG (i + 1) (t + 1) (Fin.append 0 d) := rfl

def mv {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin ((i + 1) + (t + 1)) → k :=
  ((m : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v

theorem sEmb_mul_uG (i t : ℕ) (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) :
    sEmb k _ m * uG (i + 1) (t + 1) v = uG (i + 1) (t + 1) (mv m v) * sEmb k _ m := by
  apply Subtype.ext
  exact glEmb_mul_unip' k ((i + 1) + t + 1) (m : GL (Fin ((i + 1) + t + 1)) k) (Multiplicative.ofAdd v)

theorem dEmb_add (i t : ℕ) (d e : Fin (t + 1) → k) : dEmb k i t (d + e) = dEmb k i t d * dEmb k i t e := by
  rw [dEmb_eq, dEmb_eq, dEmb_eq, ← uG_add]
  congr 1
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp

def keyC {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin (i + 1) → k :=
  fun a => mv m v (Fin.castAdd (t + 1) a)

def keyD {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) : Fin (t + 1) → k :=
  fun b => mv m v (Fin.natAdd (i + 1) b)

theorem keyD_last {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) :
    keyD m v (Fin.last t) = v (Fin.last _) := by
  have e : Fin.natAdd (i + 1) (Fin.last t) = Fin.last ((i + 1) + t) := Fin.ext (by simp)
  show mv m v (Fin.natAdd (i + 1) (Fin.last t)) = _
  rw [e]
  exact mulVec_last_of_mem k _ m.2 v

theorem key {i t : ℕ} (m : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + (t + 1)) → k) (d : Fin (t + 1) → k) :
    dEmb k i t d * sEmb k _ m * uG (i + 1) (t + 1) v =
      uG (i + 1) (t + 1) (Fin.append (keyC m v) (0 : Fin (t + 1) → k)) *
        (dEmb k i t (d + keyD m v) * sEmb k _ m) := by
  have hs := append_split (i + 1) (t + 1) (mv m v)
  rw [mul_assoc, sEmb_mul_uG, ← mul_assoc, ← mul_assoc, dEmb_add]
  conv_lhs => rw [hs, uG_add]
  rw [dEmb_eq, dEmb_eq]
  congr 1
  rw [← mul_assoc, ← mul_assoc, uG_comm]
  rfl

theorem det_unip (n : ℕ) (c : Fin n → k) :
    Matrix.GeneralLinearGroup.det (unip k n (Multiplicative.ofAdd c)) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  show (1 + colMat k n c).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    induction x using Fin.lastCases with
    | last => simp [colMat]
    | cast a => simp [colMat, Fin.castSucc_ne_last]
  · intro x y hxy
    have hy : y ≠ Fin.last n := fun e => by
      subst e
      exact absurd (Fin.le_last x) (not_le.2 hxy)
    rw [Matrix.add_apply, colMat_of_ne _ _ _ hy, add_zero]
    exact Matrix.one_apply_ne fun h => by
      subst h
      exact lt_irrefl _ hxy

theorem dpowM_of_unip (n : ℕ) (s : ℝ) (g : Mir k n) (c : Fin n → k)
    (hg : (g : GL (Fin (n + 1)) k) = unip k n (Multiplicative.ofAdd c)) : dpowM n s g = 1 := by
  show absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det (g : GL (Fin (n + 1)) k)) = 1
  rw [hg, det_unip, map_one]

section Fibre
variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

theorem qC_sigX (c : Fin (i + 1) → k) (z : τ.V ⊗[ℂ] σ.V) :
    qC τ σ (sigX τ σ ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩ z) = qC τ σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul a b =>
    set g := (pgProj k (i + 1) (t + 1) ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩) with hgdef
    have hg2 : g.2 = 1 := pgProj_snd _ _ c
    have hg1 : ((g.1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) = unip k (i + 1) (Multiplicative.ofAdd c) :=
      pgProj_fst _ _ c
    have hmem : g.1 ∈ MirUin k (i + 1) := by
      show ((g.1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) ∈ MirU k (i + 1)
      rw [hg1]
      exact ⟨_, rfl⟩
    have e2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ g.1 a = τ.ρ g.1 a := by
      show ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g.1 : ℂˣ) : ℂ) • τ.ρ g.1 a = _
      rw [dpowM_of_unip _ _ _ c hg1, Units.val_one, one_smul]
    have e3 : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ g.2 b = b := by
      rw [hg2, map_one]
      rfl
    have e : sigX τ σ ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩ (a ⊗ₜ b) =
        (τ.ρ g.1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul _ _ _ _ _).trans (congrArg₂ (fun (x : τ.V) (y : σ.V) => x ⊗ₜ[ℂ] y) e2 e3)
    rw [e]
    show LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ _ = LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ _
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨g.1, hmem⟩, a, ?_⟩)
    simp

end Fibre

section Integral

def chi {t : ℕ} (ψ : AddChar k Circle) (d : Fin (t + 1) → k) : ℂ :=
  (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)

theorem chi_add {t : ℕ} (ψ : AddChar k Circle) (d e : Fin (t + 1) → k) :
    chi ψ d = ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) * chi ψ (d + e) := by
  unfold chi
  rw [← Units.val_mul, Pi.add_apply, AddChar.map_add_eq_mul, map_mul, mul_inv, mul_left_comm, mul_inv_cancel, mul_one]

theorem chi_lc {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (chi ψ : (Fin (t + 1) → k) → ℂ) :=
  ((GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous
    (continuous_apply (Fin.last t))).comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))

variable {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem chi_smul_lc {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) : IsLocallyConstant (fun d => chi ψ d • F d) :=
  (chi_lc ψ hψ).comp₂ l (fun a b => a • b)

theorem chi_smul_cs {t : ℕ} (ψ : AddChar k Circle) {F : (Fin (t + 1) → k) → W}
    (c : HasCompactSupport F) : HasCompactSupport (fun d => chi ψ d • F d) :=
  c.mono fun d hd h => hd (by simp [h])

theorem T_smInt {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (T : W →ₗ[ℂ] W') {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d)) =
      @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • T (F d)) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by unfold muD; infer_instance
  rw [← GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T (chi_smul_lc ψ hψ l) (chi_smul_cs ψ c)]
  congr 1
  funext d
  simp

theorem smInt_shift {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {F : (Fin (t + 1) → k) → W}
    (l : IsLocallyConstant F) (c : HasCompactSupport F) (e : Fin (t + 1) → k) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F (d + e)) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) •
        @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by unfold muD; infer_instance
  set θ : ℂ := ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) with hθ
  let T : W →ₗ[ℂ] W := θ • LinearMap.id
  have lΦ := chi_smul_lc ψ hψ l
  have h2 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T lΦ (chi_smul_cs ψ c)
  have h1 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1)) (c := (· + e))
    (φ := T ∘ fun d => chi ψ d • F d) (MeasureTheory.measurePreserving_add_right _ e)
    (lΦ.comp (fun x => T x))
  have h3 : (fun d => chi ψ d • F (d + e)) = (T ∘ fun d => chi ψ d • F d) ∘ (· + e) := by
    funext d
    simp only [Function.comp, T, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [← chi_add]
  rw [h3, h1, h2]
  rfl

theorem shift_abs {t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (T : W →ₗ[ℂ] W')
    {F F' : (Fin (t + 1) → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F)
    (l' : IsLocallyConstant F') (c' : HasCompactSupport F') (e : Fin (t + 1) → k)
    (hpt : ∀ d, T (F' d) = T (F (d + e))) :
    T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F' d)) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) •
        T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => chi ψ d • F d)) := by
  have lq : IsLocallyConstant (fun d => T (F d)) := l.comp (fun x => T x)
  have cq : HasCompactSupport (fun d => T (F d)) := c.comp_left (g := fun x => T x) (map_zero _)
  rw [T_smInt ψ hψ T l' c', T_smInt ψ hψ T l c, ← smInt_shift ψ hψ lq cq e]
  congr 1
  funext d
  rw [hpt]

end Integral

section Main
variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

theorem evX_cInd (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem evX_mul (f : XS τ σ) (h : HPG k (i + 1) (t + 1)) (p : Mir k ((i + 1) + t + 1)) :
    evX f ((h : Mir k ((i + 1) + t + 1)) * p) = sigX τ σ h (evX f p) := f.1.1.2 h p

theorem intC_eq (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ f y = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
      (fun d => chi ψ d • evX f (dEmb k i t d * y)) := rfl

theorem qC_evX (f : XS τ σ) (g y : Mir k ((i + 1) + t + 1)) (c : Fin (i + 1) → k) (e : Fin (t + 1) → k)
    (hk : ∀ d, dEmb k i t d * y * g =
      uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) (d : Fin (t + 1) → k) :
    qC τ σ (evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) (dEmb k i t d * y)) =
      qC τ σ (evX f (dEmb k i t (d + e) * y)) := by
  have h1 : evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) (dEmb k i t d * y) =
      evX f (uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) :=
    (evX_cInd τ σ f g _).trans (congrArg _ (hk d))
  have h2 := evX_mul τ σ f ⟨uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)), uG_mem_H _ _ c⟩
    (dEmb k i t (d + e) * y)
  exact (congrArg (qC τ σ) (h1.trans h2)).trans (qC_sigX τ σ c _)

theorem qC_intC_abs (ψ : AddChar k Circle) (hψ : Continuous ψ) (f f' : XS τ σ) (y : Mir k ((i + 1) + t + 1))
    (e : Fin (t + 1) → k)
    (hpt : ∀ d, qC τ σ (evX f' (dEmb k i t d * y)) = qC τ σ (evX f (dEmb k i t (d + e) * y))) :
    qC τ σ (intC ψ f' y) = ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) • qC τ σ (intC ψ f y) :=
  shift_abs ψ hψ (qC τ σ) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f' y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f' y).2 e hpt

theorem qC_intC_tw (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y g : Mir k ((i + 1) + t + 1))
    (c : Fin (i + 1) → k) (e : Fin (t + 1) → k)
    (hk : ∀ d, dEmb k i t d * y * g =
      uG (i + 1) (t + 1) (Fin.append c (0 : Fin (t + 1) → k)) * (dEmb k i t (d + e) * y)) :
    qC τ σ (intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y) =
      ((Circle.toUnits (ψ (e (Fin.last t))) : ℂˣ) : ℂ) • qC τ σ (intC ψ f y) :=
  qC_intC_abs τ σ ψ hψ f _ y e (qC_evX τ σ f g y c e hk)

end Main

theorem eC_tw_at {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ) (m : Mir k ((i + 1) + t))
    (v : Multiplicative (Fin ((i + 1) + t + 1) → k))
    (hv : unip k ((i + 1) + t + 1) v = ((u : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)) :
    eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) m =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f m := by
  have hu : (u : Mir k ((i + 1) + t + 1)) = uG (i + 1) (t + 1) v.toAdd := Subtype.ext hv.symm
  have hθ : ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) =
      ((Circle.toUnits (ψ (keyD m v.toAdd (Fin.last t))) : ℂˣ) : ℂ) := by
    rw [mirChar_eq k ψ _ u v hv.symm, keyD_last]
    rfl
  have h := qC_intC_tw τ σ ψ hψ f (sEmb k _ m) (u : Mir k ((i + 1) + t + 1)) (keyC m v.toAdd) (keyD m v.toAdd)
    (fun d => by rw [hu]; exact key m v.toAdd d)
  show ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ _ (sEmb k _ m)) =
    ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))
  rw [h, hθ, smul_comm]

theorem eC_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ u f
  have h : ∃ v, unip k ((i + 1) + t + 1) v = ((u : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) := u.2
  exact funext fun m => eC_tw_at ψ hψ τ σ u f m h.choose h.choose_spec

end GlobalTheory.CompanionTheory.BZPhiPG.TwC

end
