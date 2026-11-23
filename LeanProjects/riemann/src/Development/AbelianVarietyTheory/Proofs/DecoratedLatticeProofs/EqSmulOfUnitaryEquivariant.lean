import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EquivariantMapEqSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.BranchMultOne

def blkMat (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if hi : i.1 < n then (if hj : j.1 < n then h ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0)
    else (if j.1 < n then 0 else 1)

def blkPoly (N n : ℕ) (v : Fin N × Fin N) : MvPolynomial (Fin n × Fin n) ℂ :=
  if hi : v.1.1 < n then (if hj : v.2.1 < n then MvPolynomial.X (⟨v.1.1, hi⟩, ⟨v.2.1, hj⟩) else 0)
    else (if v.2.1 < n then 0 else 1)

theorem eval_blkPoly (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (v : Fin N × Fin N) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v) = blkMat N n h v.1 v.2 := by
  simp only [blkPoly, blkMat, Matrix.of_apply]
  split_ifs <;> simp_all

theorem isBlock_blkMat {N n : ℕ} (hN : N = n + 1) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (blkMat N n h) h 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;>
    simp [blkMat, Formalism.L2.Col.Br.iC, Formalism.L2.Col.Br.iL]

theorem eq_blkMat_of_isBlock {N n : ℕ} (hN : N = n + 1) {kt : Matrix (Fin N) (Fin N) ℂ}
    {k : Matrix (Fin n) (Fin n) ℂ} (H : GlobalTheory.BranchFormula.IsBlock hN kt k 1) : kt = blkMat N n k := by
  ext i j
  simp only [blkMat, Matrix.of_apply]
  by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
  · rw [dif_pos hi, dif_pos hj]
    have := H.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_pos hi, dif_neg hj]
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨i.1, hi⟩).1
    rw [ej]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_neg hi, if_pos hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨j.1, hj⟩).2
    rw [ei]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_neg hi, if_neg hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    rw [ei, ej]
    exact H.2.2

theorem pow_toNat_eq (x : ℂ) (hx : x ≠ 0) (c m : ℤ) (hc : 0 ≤ c + m) :
    x ^ (c + m).toNat = x ^ m * x ^ c := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hc, zpow_add₀ hx, mul_comm]

theorem det_eval_mvPolynomialX (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = h.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_ne_zero_of_unitary {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u.det ≠ 0 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact right_ne_zero_of_mul_eq_one h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

open Formalism.BasicNotions

theorem unitary_to_all {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (u : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg)
    (E : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hE : ∀ f : delSq ℂ N lam, E f.1 = (u f).1)
    (hu : ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 →
      ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 →
        k.det ^ lam.detShift • (u f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (u f).1)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.det ≠ 0) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ delSq ℂ N lam) :
    g.det ^ lam.detShift • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g) f) =
      g.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ g (E f) := by
  set a := lam.detShift
  set b := sg.detShift
  set m : ℤ := |a| + |b|
  have ha : 0 ≤ a + m := by
    have := neg_abs_le a; have := abs_nonneg b; omega
  have hb : 0 ≤ b + m := by
    have := neg_abs_le b; have := abs_nonneg a; omega
  have poly : ∀ g' : Matrix (Fin n) (Fin n) ℂ,
      g'.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g') f) =
        g'.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ g' (E f) := by
    intro g'
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef N N f (l ∘ₗ E)
    obtain ⟨P₂, hP₂⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n (E f) l
    let D := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
    let Q := D ^ (a + m).toNat * MvPolynomial.bind₁ (blkPoly N n) P₁ - D ^ (b + m).toNat * P₂
    have hQ : ∀ h : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => h x.1 x.2) Q =
        l (h.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n h) f) -
          h.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ h (E f)) := by
      intro h
      have hbind : MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (MvPolynomial.bind₁ (blkPoly N n) P₁) =
          MvPolynomial.eval (fun v => MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v)) P₁ :=
        MvPolynomial.eval₂Hom_bind₁ _ _ _ P₁
      simp only [Q, D, map_sub, map_mul, map_pow, det_eval_mvPolynomialX, map_smul, smul_eq_mul, hbind, eval_blkPoly]
      rw [← hP₁ (blkMat N n h), ← hP₂ h]
      rfl
    have Q0 : Q = 0 := by
      refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Q fun v hv => ?_
      rw [hQ]
      have hv0 := det_ne_zero_of_unitary hv
      have key := hu v hv (blkMat N n v) (isBlock_blkMat hN v) ⟨f, hf⟩
        ⟨Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n v) f, GlobalTheory.ValueSpaceCoordinates.rowAct_mem_delSq lam _ f hf⟩ rfl
      rw [← hE, ← hE] at key
      rw [pow_toNat_eq _ hv0 a m ha, pow_toNat_eq _ hv0 b m hb, mul_smul, mul_smul, ← smul_sub]
      simp only at key
      rw [key, sub_self, smul_zero, map_zero]
    have := hQ g'
    rw [Q0, map_zero] at this
    exact this.symm
  have h := poly g
  rw [pow_toNat_eq _ hg a m ha, pow_toNat_eq _ hg b m hb, mul_smul, mul_smul] at h
  exact smul_right_injective _ (zpow_ne_zero m hg) h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

theorem eq_smul_of_unitary_equivariant : ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Formalism.L2.Col.Br.Interlace hN lam sg → ∀ t t₀ : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg, (∀ s, s = t ∨ s = t₀ → ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 → ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 → k.det ^ lam.detShift • (s f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (s f).1) → t₀ ≠ 0 → ∃ c : ℂ, t = c • t₀ := by
  intro N n hN lam sg hI t t₀ H h0
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (delSq ℂ N lam)
  let π := (delSq ℂ N lam).linearProjOfIsCompl C hC
  let E : (delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg) → MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    fun u => (delSq ℂ n sg).subtype ∘ₗ u ∘ₗ π
  have hE : ∀ u (f : delSq ℂ N lam), E u f.1 = (u f).1 := fun u f => by
    show (u (π f.1)).1 = (u f).1
    exact congrArg (fun x => (u x).1) (Submodule.linearProjOfIsCompl_apply_left hC f)
  have hN' : Formalism.BasicNotions.nablaSq ℂ N lam = delSq ℂ N lam := Formalism.L2.Col.nablaSq_eq_delSq ℂ lam
  have hn' : Formalism.BasicNotions.nablaSq ℂ n sg = delSq ℂ n sg := Formalism.L2.Col.nablaSq_eq_delSq ℂ sg
  have key : ∀ s, s = E t ∨ s = E t₀ → (∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, s f ∈ Formalism.BasicNotions.nablaSq ℂ n sg) ∧
      ∀ (g : GL (Fin n) ℂ), ∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam,
        s (Formalism.BasicNotions.sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) f) = Formalism.BasicNotions.sqAct ℂ n sg g (s f) := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ : ∃ u, (u = t ∨ u = t₀) ∧ s = E u := by
      rcases hs with hs | hs
      · exact ⟨t, Or.inl rfl, hs⟩
      · exact ⟨t₀, Or.inr rfl, hs⟩
    refine ⟨fun f hf => ?_, fun g f hf => ?_⟩
    · rw [hN'] at hf
      rw [hn', hE u ⟨f, hf⟩]
      exact (u _).2
    · rw [hN'] at hf
      have hb := (GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).transpose
      have hdet : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ).det =
          (g : Matrix (Fin n) (Fin n) ℂ).det := by
        rw [(GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).det, mul_one]
      have hg0 : (g : Matrix (Fin n) (Fin n) ℂ).transpose.det ≠ 0 := by
        rw [Matrix.det_transpose]
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      have main := unitary_to_all hN lam sg u (E u) (hE u) (H u hu) _ hg0 f hf
      rw [← eq_blkMat_of_isBlock hN hb, Matrix.det_transpose] at main
      simp only [Formalism.BasicNotions.sqAct, Formalism.BasicNotions.detPow, map_smul, Units.val_zpow_eq_zpow_val,
        Matrix.GeneralLinearGroup.val_det_apply, hdet]
      exact main
  have hne : ∃ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, E t₀ f ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := hc f.1 (by rw [hN']; exact f.2)
    rw [hE] at this
    simpa using this
  obtain ⟨c, hc⟩ := GlobalTheory.Branching.equivariant_map_eq_smul n N hN.symm lam sg
    ((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.interlace_iff hN lam sg).1 hI) (E t) (E t₀) key hne
  refine ⟨c, LinearMap.ext fun f => Subtype.ext ?_⟩
  have := hc f.1 (by rw [hN']; exact f.2)
  rw [hE, hE] at this
  simpa using this

end GlobalTheory.BranchMultOne
