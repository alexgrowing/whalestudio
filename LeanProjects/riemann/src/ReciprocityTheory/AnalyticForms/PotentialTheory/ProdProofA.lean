import ReciprocityTheory.AnalyticForms.PotentialTheory.FubiniStudyPotentialProductIsPotential
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

namespace ReciprocityTheory.AnForm.M

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

@[simp] theorem appendCLE_apply_castAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e) :
    appendCLE e e' (u, v) (Fin.castAdd e' i) = u i := by
  simp [appendCLE]

@[simp] theorem appendCLE_apply_natAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e') :
    appendCLE e e' (u, v) (Fin.natAdd e i) = v i := by
  simp [appendCLE]

theorem appendCLE_symm_apply (y : Fin (e + e') → ℂ) :
    (appendCLE e e').symm y = (fun i => y (Fin.castAdd e' i), fun i => y (Fin.natAdd e i)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

def pr1L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

def pr2L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e' → ℂ) :=
  (ContinuousLinearMap.snd ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

theorem firstProjection_apply (y : Fin (e + e') → ℂ) : (pr1L y : Fin e → ℂ) = ((appendCLE e e').symm y).1 := rfl
theorem secondProjection_apply (y : Fin (e + e') → ℂ) : (pr2L y : Fin e' → ℂ) = ((appendCLE e e').symm y).2 := rfl

@[simp] theorem firstProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e) :
    (pr1L y : Fin e → ℂ) i = y (Fin.castAdd e' i) := by
  rw [firstProjection_apply, appendCLE_symm_apply]

@[simp] theorem secondProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e') :
    (pr2L y : Fin e' → ℂ) i = y (Fin.natAdd e i) := by
  rw [secondProjection_apply, appendCLE_symm_apply]

def J1 (e e' : ℕ) : Matrix (Fin e) (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.castAdd e' a then 1 else 0

def J2 (e e' : ℕ) : Matrix (Fin e') (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.natAdd e a then 1 else 0

theorem natAdd_ne_castAdd' (a : Fin e) (b : Fin e') : (Fin.natAdd e b : Fin (e + e')) ≠ Fin.castAdd e' a := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem castAdd_ne_natAdd' (a : Fin e) (b : Fin e') : (Fin.castAdd e' a : Fin (e + e')) ≠ Fin.natAdd e b :=
  fun h => natAdd_ne_castAdd' a b h.symm

theorem block_eq (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    (J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e' =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M1 0 0 M2) := by
  ext k l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
    refine Fin.addCases (fun c => ?_) (fun d => ?_) l <;>
    simp [Matrix.mul_apply, J1, J2, Matrix.fromBlocks, ite_mul, mul_ite, Finset.sum_ite_eq, natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem det_block (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    ((J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e').det = M1.det * M2.det := by
  rw [block_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def finsetAppendEquiv (e e' : ℕ) : Finset (Fin e) × Finset (Fin e') ≃ Finset (Fin (e + e')) where
  toFun p := p.1.map (Fin.castAddEmb e') ∪ p.2.map (Fin.natAddEmb e)
  invFun S := (Finset.univ.filter (fun a => Fin.castAdd e' a ∈ S),
    Finset.univ.filter (fun b => Fin.natAdd e b ∈ S))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> ext a <;> simp [natAdd_ne_castAdd', castAdd_ne_natAdd']
  right_inv S := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
      simp [natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem pot_contDiffAt {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x ∈ 𝓝 z :=
    ((A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hz, hzU⟩
  exact ((hP.1 x k).contDiffAt hmem).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

end

end ReciprocityTheory.AnForm.M
