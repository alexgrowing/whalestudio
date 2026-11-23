import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.PenPsiInv

open GlobalTheory.CongLevel

section Ext

variable {E : Type} [Field E]

theorem resX_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    resX c (extE c κ v) = κ (resX c v) := by
  rw [extE_apply, map_add, resX_inX]
  abel

theorem atNL_inX {n : ℕ} (c : ℕ) (w : Fin n → E) : atNL E (n + c) n (Loc.inX E n c w) = 0 := by
  unfold atNL
  split_ifs with h
  · rw [LinearMap.proj_apply, inX_apply, dif_neg (lt_irrefl n)]
  · rfl

theorem atNL_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    atNL E (n + c) n (extE c κ v) = atNL E (n + c) n v := by
  rw [extE_apply, map_add, atNL_inX, add_zero]

theorem joinCol_inFr {n' c' n c : ℕ} (f : Sp E n' ≃ₗ[E] Sp E n') (f' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E n' n)
    (y : Sp E n) :
    joinCol (c' := c') (c := c) (inFr f f' x) (f'.symm y) =
      (extE c f'.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x y ∘ₗ (extE c' f).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [extE_inX]
  congr 1
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (extE c' f v) = f (LinearMap.funLeft E E (Fin.castAdd c') v) :=
    resX_extE c' f v
  rw [h1, atNL_extE, map_add, map_smul]
  rfl

end Ext

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem extE_mem_Jat (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Jat (Pr := Pr) sharp j w := by
  have h := (Subgroup.mem_inf.1
    (GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe (Pr := Pr) sharp j w hw hd 1 (one_mem _) κ hκ hr)).2
  rw [Subgroup.mem_comap, inv_one, map_one] at h
  exact h

theorem lamRow_extE (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    lamRow Ch mu sharp j w (extE (cOf R j) κ).toLinearMap = 1 := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have e : (extE (cOf R j) κ).toLinearMap = LinearMap.id + ((qOf w : ℕ) : X.E) •
      (((qOf w : ℕ) : X.E)⁻¹ • ((extE (cOf R j) κ).toLinearMap - LinearMap.id)) := by
    rw [smul_inv_smul₀ hq, add_sub_cancel]
  rw [e]
  refine GlobalTheory.LamRowCong.lamRow_one_add_q Ch mu sharp j w hw _ fun v hv => ?_
  unfold lamYat at hv ⊢
  rw [if_pos hw] at hv ⊢
  exact extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr v hv

theorem muAt_det_extE (i : ℕ) {n : ℕ} (c : ℕ)
    (hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (hκ : κ ∈ GLint X.E n P.1)
    (hr : ∀ x ∈ stdAt X.E n P.1, redV P.1 (κ x) = redV P.1 x) :
    muAt Ch sel mu cst i P ((LinearEquiv.det (extE c κ) : X.Eˣ) : X.E) = 1 := by
  refine GlobalTheory.TwU.MidIndep.muAt_det_cong Ch sel mu cst i P (n + c) 1 le_rfl _ fun v hv => ?_
  rw [pow_one]
  rw [GlobalTheory.DatumLaw.stdAt_eq] at hv ⊢
  exact extE_cong P.1 (qOf P.1) c 0 hd κ hκ hr v hv

end Main

theorem psiAt_one_inFr : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  have hi : s + 2 ≤ R.m := hm.ge
  have hg : f'.symm ∈ GLint X.E (R.N (s + 1)) P.1 := inv_mem hf'
  have hgr : ∀ v ∈ stdAt X.E (R.N (s + 1)) P.1, redV P.1 (f'.symm v) = redV P.1 v := fun v hv => by
    have h := hr' _ ((hg v).2 hv)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp (s + 1) P.1 hP hd _ hg hgr)
    (joinCol x y ∘ₗ (extE (cOf R s) f).toLinearMap)
  have h2 := GlobalTheory.DatumLaw.phiAt_source Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp s P.1 hP hd _ hf hr) (joinCol x y)
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hg hgr, lamRow_extE Ch mu cst.sharp (s + 1) P.1 hP hd _ hg hgr, mul_one, one_mul] at h1
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hf hr, lamRow_extE Ch mu cst.sharp s P.1 hP hd _ hf hr, mul_one, one_mul] at h2
  unfold PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one, joinCol_inFr, h1, h2]

end GlobalTheory.PenPsiInv
