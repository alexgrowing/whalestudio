import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem continuous_block_matrix_three {X : Type*} [TopologicalSpace X] {k j ρ : ℕ}
    {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A22 : X → B.Mat k ρ} {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A31 : X → Matrix (Fin j) (Fin j) ℂ} {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : Continuous A11) (h12 : Continuous A12) (h13 : Continuous A13) (h21 : Continuous A21)
    (h22 : Continuous A22) (h23 : Continuous A23) (h31 : Continuous A31) (h32 : Continuous A32)
    (h33 : Continuous A33) :
    Continuous fun x => blk3 (A11 x) (A12 x) (A13 x) (A21 x) (A22 x) (A23 x) (A31 x) (A32 x) (A33 x) := by
  refine continuous_matrix fun a b => ?_
  unfold blk3
  show Continuous fun x => fromBlocks (fromBlocks (A11 x) (A12 x) (A21 x) (A22 x))
    (fromRows (A13 x) (A23 x)) (fromCols (A31 x) (A32 x)) (A33 x)
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    first
    | exact h11.matrix_elem a' b' | exact h12.matrix_elem a' b' | exact h13.matrix_elem a' b'
    | exact h21.matrix_elem a' b' | exact h22.matrix_elem a' b' | exact h23.matrix_elem a' b'
    | exact h31.matrix_elem a' b' | exact h32.matrix_elem a' b' | exact h33.matrix_elem a' b'

theorem continuous_zjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ) :
    Continuous fun Z' : G.Mat s => ZjH σ d η Z' := by
  unfold ZjH Zj
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_matrix fun a b => ?_
  show Continuous fun Z' : G.Mat s => fromBlocks (headH σ d η.2.1 η.2.2) 0 0 (of Z')
    (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  rcases finSumFinEquiv.symm a with a' | a' <;> rcases finSumFinEquiv.symm b with b' | b'
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_apply_apply a' b'

theorem det_zjH_ne {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (η : XiH p s σ)
    (Z : G.Mat s) (hZ : G.detM Z ≠ 0) : (ZjH σ d η Z).det ≠ 0 := by
  unfold ZjH Zj headH
  simp only [Matrix.det_mul, blk2, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, mul_one]
  unfold wP lowW G.upper
  repeat' apply mul_ne_zero
  all_goals first
    | exact hZ
    | (rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hd i)
    | (have hP : (of fun a b => if σ a = b then (1 : ℂ) else 0) =
          (1 : Matrix (Fin p) (Fin p) ℂ).submatrix σ id := by
         ext a b
         simp [Matrix.one_apply]
       rw [hP, Matrix.det_permute]
       simp)
    | (first | rw [Matrix.det_of_lowerTriangular _ ?_] | rw [Matrix.det_of_lowerTriangular ?_]
       · simp
       · intro i j hij
         have hij' : i < j := hij
         simp [Matrix.one_apply, hij'.ne, not_lt.2 hij'.le])
    | (first | rw [Matrix.det_of_upperTriangular ?_] | rw [Matrix.det_of_upperTriangular _ ?_]
       · simp [G.strictUpper]
       · intro i j hij
         have hij' : j < i := hij
         simp [G.strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le])

theorem rn_mem_of (hR : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  unfold RadicalParam at hR
  obtain ⟨-, hrange, hsub⟩ := hR k j ρ
  have hx : Rn k j ρ x ∈ Rset k j ρ := hrange ▸ Set.mem_range_self x
  exact (hsub hx).1

theorem gaXi_mem_of (hM : SliceMem) (hR : RadicalParam) (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ)
    (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  unfold gaXi
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (rn_mem_of hR _ _ _ _))
      ((hM k (p + s) ρ).1 _ γ (det_zjH_ne σ d hd ξ.2 Z hZ) hγ)) (rn_mem_of hR _ _ _ _)

theorem gaXi_contAt (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) :
    ContinuousAt (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
  have hZj := continuous_zjH σ d ξ.2 (s := s)
  have hdet : ((ZjH σ d ξ.2 Z)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 (det_zjH_ne σ d hd ξ.2 Z hZ)
  have hinvC : ContinuousAt Ring.inverse ((ZjH σ d ξ.2 Z)ᴴ).det := by
    simpa using NormedRing.inverse_continuousAt (Units.mk0 _ hdet)
  have hinv : ContinuousAt (fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ⁻¹) Z :=
    ContinuousAt.comp (g := (Inv.inv : Matrix (Fin (p + s)) (Fin (p + s)) ℂ → _))
      (f := fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ) (continuousAt_matrix_inv _ hinvC)
      hZj.matrix_conjTranspose.continuousAt
  let F : Matrix (Fin (p + s)) (Fin (p + s)) ℂ × Matrix (Fin (p + s)) (Fin (p + s)) ℂ → B.Mat k (p + s + ρ) :=
    fun P => (Rn k (p + s) ρ ξ.1.1)⁻¹ *
      blk3 0 0 (P.2 * G.wMat (p + s)) 0 γ 0 (G.wMat (p + s) * P.1) 0 0 * Rn k (p + s) ρ ξ.1.2
  have hF : Continuous F := by
    refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
    exact continuous_block_matrix_three continuous_const continuous_const
      (continuous_snd.matrix_mul continuous_const) continuous_const continuous_const continuous_const
      (continuous_const.matrix_mul continuous_fst) continuous_const continuous_const
  have : (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) =
      F ∘ fun Z' => (ZjH σ d ξ.2 Z', (ZjH σ d ξ.2 Z')ᴴ⁻¹) := by
    funext Z'; rfl
  rw [this]
  exact hF.continuousAt.comp (hZj.continuousAt.prodMk hinv)

theorem offK : OffK := by
  intro hM hR k p s ρ σ d hd E _ _ H O hO hH ξ Z γ hZ hγ hgO q
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[nhds Z] fun _ => (0 : E) := by
    have h1 : ∀ᶠ Z' in nhds Z, gaXi k ρ σ d ξ Z' γ ∈ O :=
      (gaXi_contAt k p s ρ σ d hd ξ Z γ hZ) (hO.mem_nhds hgO)
    have hdc : Continuous fun Z' : G.Mat s => G.detM Z' := by
      unfold G.detM; exact Continuous.matrix_det continuous_id
    have h2 : ∀ᶠ Z' in nhds Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hH _ (gaXi_mem_of hM hR k p s ρ σ d hd ξ Z' γ h2 hγ) h1
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
  rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
  simp

end PI.UnitaryGroupMassFormula.UsCost
