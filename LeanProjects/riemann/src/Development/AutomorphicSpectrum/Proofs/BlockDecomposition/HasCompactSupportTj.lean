import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnifV_of_ordL {w : Pl E} {x : w.adicCompletion E} (h0 : x ≠ 0) (h : ordL x = 1) : IsUnifV E w x := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  unfold ordL at h
  rw [dif_neg hv] at h
  have e : WithZero.unzero hv = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  unfold IsUnifV
  rw [← e, WithZero.coe_unzero]

theorem ordL_eq_zero {w : Pl E} {x : w.adicCompletion E} (h : Valued.v x = 1) : ordL x = 0 := by
  have hv : Valued.v x ≠ 0 := by rw [h]; exact one_ne_zero
  unfold ordL
  rw [dif_neg hv]
  have e : WithZero.unzero hv = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [e]
  simp

theorem det_mem {w : Pl E} {n : ℕ} {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hM : ∀ i j, M i j ∈ Ov E w) : M.det ∈ Ov E w := by
  rw [Matrix.det_apply']
  exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => hM _ _)

theorem v_det {w : Pl E} {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) : Valued.v g.val.det = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hg
  have d1 : Valued.v g.val.det ≤ 1 := det_mem h1
  have d2 : Valued.v (g⁻¹).val.det ≤ 1 := det_mem h2
  have e : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, show g.val * (g⁻¹).val = 1 from g.mul_inv, Matrix.det_one]
  have e' : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by
    rw [← map_mul, e, map_one]
  refine le_antisymm d1 ?_
  calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := e'.symm
    _ ≤ Valued.v g.val.det * 1 := mul_le_mul_right d2 _
    _ = _ := mul_one _

def cMu {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ)

theorem mu_unit {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1 := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  refine hμ _ (ordL_eq_zero ?_)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, map_mul, map_pow,
    v_det h1, v_det h2, one_pow, one_mul]

theorem cMu_mul_left {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (κ * m) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem cMu_mul_right {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (m * κ) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem hasCompactSupport_Tj {w : Pl E} {n : ℕ} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (k : ℕ) :
    HasCompactSupport (Tj ℂ n (Ov E w) ϖ k : GLw n w → ℂ) := by
  have hdet : (diagJ n ϖ k).det ≠ 0 := by
    rw [diagJ, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact h0
    · exact one_ne_zero
  set t : GLw n w := GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ k) hdet with ht
  have hI := GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n
  have hS : IsCompact ((fun p : GLw n w × GLw n w => p.1 * t * p.2) ''
      ((GlobalTheory.LFun.KGL w n : Set (GLw n w)) ×ˢ (GlobalTheory.LFun.KGL w n : Set (GLw n w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  refine HasCompactSupport.intro' hS hS.isClosed fun g hg => ?_
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  exact hg ⟨(x, y), ⟨hx, hy⟩, Units.ext (by simpa [ht] using e.symm)⟩

theorem blk_zero_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    blk h w κ 0 ∈ GlobalTheory.LFun.KGL w n := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  obtain ⟨l1, l2⟩ := GlobalTheory.BCT.CtLevel.lev_KGL_of_unram E a b n h w 1 (fun _ _ => rfl)
  have d1 : GlobalTheory.BCT.CtLevel.dgM h w (κ.1, 1) ∈ GlobalTheory.LFun.KGL w n := by
    have : κ.1 ∈ GlobalTheory.BCT.CtLevel.lev₁ h w (GlobalTheory.LFun.KGL w n) 1 := by rw [l1]; exact h1
    exact this.1.2
  have d2 : GlobalTheory.BCT.CtLevel.dgM h w (1, κ.2) ∈ GlobalTheory.LFun.KGL w n := by
    have : κ.2 ∈ GlobalTheory.BCT.CtLevel.lev₂ h w (GlobalTheory.LFun.KGL w n) 1 := by rw [l2]; exact h2
    exact this.1.2
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
  have e : κ = (κ.1, 1) * (1, κ.2) := by simp
  rw [e, map_mul]
  exact mul_mem d1 d2

theorem ctT_eq {n a b : ℕ} (h : a + b = n) {w : Pl E} (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) :
    RS.ctT h w μ ϖ k = fun m => cMu μ m * phi3 h w (Tj ℂ n (Ov E w) ϖ k) 1 1 m := by
  funext m
  rw [GlobalTheory.CompanionTheory.CtS.ctT_split_eq E n a b h w μ ϖ hw hϖ k m]
  simp [phi3, cMu]

theorem isHecke_ctT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : (w.adicCompletion E)ˣ), IsSplitAt w → ordL (ϖ : w.adicCompletion E) = 1 → (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) → ∀ k : ℕ, IsHecke (K2 a b w) (RS.ctT h w μ (ϖ : w.adicCompletion E) k) := by
  intro E _ _ _ n a b h w μ ϖ hw hord hμ k
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := isUnifV_of_ordL h0 hord
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hf : ∀ k₁ ∈ GlobalTheory.LFun.KGL w n, ∀ k₂ ∈ GlobalTheory.LFun.KGL w n, ∀ g : GLw n w,
      Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k (k₁ * g * k₂) = Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k g :=
    fun k₁ h₁ k₂ h₂ g => hT.1 ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ g
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w n) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) _ hf 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w n) := blk_zero_mem h w (one_mem _)
  rw [ctT_eq h hw μ hϖ k]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ (hasCompactSupport_Tj h0 k) 1 1).mul_left
  · have := hbi κ 1 (blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [cMu_mul_right hμ hκ, this]

end GlobalTheory.CompanionTheory.CtHecke
