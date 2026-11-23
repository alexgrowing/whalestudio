import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandGA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GelfandG

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem opPow_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (p q : Fin n → Fin n → Fin n) (s : ℂ)
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E'))
    (hA : ∀ a b h, A a b h = s • EabV ε (p a b) (q a b) h) (j : ℕ) :
    ∀ a b, ∀ g ∈ W, inUJ ε g →
      opPow A j a b f g = (-s) ^ j •
        Lk (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j a b G (g⁻¹ * m)) := by
  induction j with
  | zero =>
    intro a b g hg hgu
    simp only [opPow, pow_zero, one_smul]
    split_ifs
    · exact hf g hg hgu
    · simp
  | succ j ih =>
    intro a b g hg hgu
    have hz : g⁻¹ * m ∈ U := (hWU g hg).2
    simp only [opPow, Finset.sum_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hGd : DifferentiableOn ℂ
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G) U :=
      (GelfandGA.opPow_contDiffOn hU hG _ j c b).differentiableOn (by simp)
    have hF : DifferentiableOn ℂ (fun z => ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G z)) U :=
      ((-s) ^ j • Lk).differentiable.comp_differentiableOn hGd
    have hloc : ∀ g ∈ W, inUJ ε g → opPow A j c b f g = ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G (g⁻¹ * m)) :=
      fun g hg hgu => by rw [ih c b g hg hgu, _root_.smul_apply]
    rw [hA, Pi.smul_apply, eabV_of_local ε hU hF hW hWU hloc _ _ hg hgu,
      CasG.lhol_clm _ _ ((hGd _ hz).differentiableAt (hU.mem_nhds hz)),
      _root_.smul_apply, smul_neg, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

theorem opGelfand_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (p q : Fin n → Fin n → Fin n) (s : ℂ)
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E'))
    (hA : ∀ a b h, A a b h = s • EabV ε (p a b) (q a b) h) (k : ℕ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    opGelfand A k f g = (-s) ^ k •
      Lk (opGelfand (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) k G (g⁻¹ * m)) := by
  unfold opGelfand
  rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => opPow_local ε Lk hU hG hW hWU hf p q s A hA k a a g hg hgu

end GelfandG

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_gelfand (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (k : ℕ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    opGelfand (rightE ε) k (PsiM T μ) g = gval (icShift lam) k • PsiM T μ g ∧
      opGelfand (rightEanti ε) k (PsiM T μ) g = gval (icShift (-lam)) k • PsiM T μ g := by
  have := compactSpace_KG ε
  obtain ⟨U₁, hU₁o, hpos₁, -, hgel⟩ := gelfand_psM T μ lam hμ
  have hUo : IsOpen (U₁ ∩ Ps1.Uset ε) := hU₁o.inter Ps1.isOpen_Uset
  have hpos : posSet n ⊆ U₁ ∩ Ps1.Uset ε := Set.subset_inter hpos₁ Ps1.posSet_subset_Uset
  have hsm : ContDiffOn ℂ ∞ (psM T μ) (U₁ ∩ Ps1.Uset ε) :=
    (GelfandGA.psM_contDiffOn T μ).mono Set.inter_subset_right
  obtain ⟨W, k₀, hWo, hgW, hWV, hloc⟩ := psiM_local T μ hμ _ hUo hpos hg
  have hz : g⁻¹ * toMK k₀ ∈ U₁ ∩ Ps1.Uset ε := (hWV g hgW).2
  have hlocL : ∀ g' ∈ W, inUJ ε g' → PsiM T μ g' =
      ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) (psM T μ (g'⁻¹ * toMK k₀)) :=
    fun g' hg' hgu => hloc g' hg' hgu
  obtain ⟨h1, h2⟩ := hgel _ hz.1 k
  constructor
  · calc opGelfand (rightE ε) k (PsiM T μ) g
        = (-(1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (psM T μ) (g⁻¹ * toMK k₀)) :=
          GelfandG.opGelfand_local ε _ hUo hsm hWo hWV hlocL (fun a _ => a) (fun _ b => b) 1 (rightE ε)
            (fun a b h => (one_smul ℂ _).symm) k hgW hg
      _ = (-(1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (((-1 : ℂ) ^ k * gval (icShift lam) k) • psM T μ (g⁻¹ * toMK k₀)) := by rw [h1]
      _ = gval (icShift lam) k • PsiM T μ g := by
          rw [map_smul, smul_smul, hloc g hgW hg, ← mul_assoc, ← mul_pow]
          congr 1
          norm_num
  · calc opGelfand (rightEanti ε) k (PsiM T μ) g
        = (-(-1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (psM T μ)
              (g⁻¹ * toMK k₀)) :=
          GelfandG.opGelfand_local ε _ hUo hsm hWo hWV hlocL (fun a b => Fin.rev b) (fun a b => Fin.rev a)
            (-1) (rightEanti ε) (fun a b h => (neg_one_smul ℂ _).symm) k hgW hg
      _ = (-(-1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (gval (icShift (-lam)) k • psM T μ (g⁻¹ * toMK k₀)) := by rw [h2]
      _ = gval (icShift (-lam)) k • PsiM T μ g := by
          rw [map_smul, smul_smul, hloc g hgW hg, neg_neg, one_pow, one_mul]
          rfl

end ReciprocityTheory.ChartRestriction.DS.S7
