import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

theorem exists_right_invariant {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ S : Set G, IsOpen S ∧ (1 : G) ∈ S ∧ ∀ s ∈ S, ∀ p : G, f.1.1.1 (p * s) = f.1.1.1 p := by
  have hopen : IsOpen {s : G | GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1} := f.1.2
  refine ⟨_, hopen, ?_, fun s hs p => ?_⟩
  · show GlobalTheory.PRep.ind H ρ 1 f.1.1 = f.1.1
    simp
  · have hs' : GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1 := hs
    exact congrFun (congrArg Subtype.val hs') p

theorem exists_compact_support {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ C : Set G, IsCompact C ∧ ∀ p : G, f.1.1.1 p ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, p = h * c :=
  f.2

section Column

variable (k : Type) [Field k]

def col (n : ℕ) (p : Mir k n) : Fin n → k :=
  fun j => ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc j) (Fin.last n)

theorem last_last (n : ℕ) (p : Mir k n) :
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have h := congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2) (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using h

theorem last_column_entry_product_formula (n : ℕ) (a : Fin n → k) (A : Matrix (Fin n) (Fin n) k)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hP : P (Fin.last n) (Fin.last n) = 1) (j : Fin n) :
    ((1 + colMat k n a) * glEmbMat k n A * P) (Fin.castSucc j) (Fin.last n) =
      a j + (A.mulVec (fun l => P (Fin.castSucc l) (Fin.last n))) j := by
  rw [add_mul, one_mul, GlobalTheory.BZMir.colMat_mul_glEmbMat, add_mul, Matrix.add_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.mulVec,
    dotProduct, hP, Fin.castSucc_ne_last]
  all_goals ring

theorem col_uM_levi_mul (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) (p : Mir k n) :
    col k n (uM k n a * levi k n g * p) = a + (g : Matrix (Fin n) (Fin n) k).mulVec (col k n p) := by
  funext j
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_column_entry_product_formula k n a (g : Matrix (Fin n) (Fin n) k)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_last k n p) j

theorem col_one (n : ℕ) : col k n 1 = 0 := by
  funext j
  simp [GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col, Matrix.one_apply, Fin.castSucc_ne_last]

theorem col_uM_levi (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) :
    col k n (uM k n a * levi k n g) = a := by
  have h := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul k n a g 1
  rwa [mul_one, GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_one, Matrix.mulVec_zero, add_zero] at h

end Column

section Top

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_midV (i t : ℕ) : Continuous (midV k i t) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.castAdd t l)
    simp only [Fin.append_left, Pi.zero_apply]
    exact continuous_const
  | right l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.natAdd i l)
    simp only [Fin.append_right]
    exact continuous_apply l

theorem continuous_col_inv (n : ℕ) : Continuous (fun c : Mir k n => col k n c⁻¹) :=
  continuous_pi fun j =>
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem (Fin.castSucc j) (Fin.last n)

theorem isLocallyConstant_uM {Z : Type} (n : ℕ) (F : Mir k n → Z) (S : Set (Mir k n)) (hS : IsOpen S)
    (h1 : (1 : Mir k n) ∈ S) (hF : ∀ s ∈ S, ∀ p, F (p * s) = F p) (g : GL (Fin n) k) :
    IsLocallyConstant (fun y : Fin n → k => F (uM k n y * levi k n g)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  have hu := (GlobalTheory.T.continuous_levi_unipotent_proj k n).2.1
  set L := GlobalTheory.BZMir.levi k n g
  let φ : (Fin n → k) → GlobalTheory.BZMir.Mir k n := fun y => L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) * L
  have hφ : Continuous φ :=
    (continuous_const.mul (hu.comp (continuous_id.sub continuous_const))).mul continuous_const
  refine ⟨φ ⁻¹' S, hS.preimage hφ, ?_, fun y hy => ?_⟩
  · show L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y₀ - y₀) * L ∈ S
    rw [sub_self, GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, mul_one, inv_mul_cancel]
    exact h1
  · have hadd : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y =
        GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
      congr 1
      abel
    have hy' : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L * φ y := by
      rw [hadd]
      simp only [φ]
      group
    show F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L) = F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L)
    rw [hy']
    exact hF _ hy _

end Top

theorem fibV_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ _ f g
  constructor
  · obtain ⟨S, hS, h1, hSf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_right_invariant _ _ f
    exact (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.isLocallyConstant_uM k (i + t) _ S hS h1 hSf g).comp_continuous
      (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_midV k i t)
  · obtain ⟨C, hC, hCf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_compact_support _ _ f
    let proj : GlobalTheory.BZMir.Mir k (i + t) → Fin t → k := fun c j =>
      -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j))
    have hproj : Continuous proj := continuous_pi fun j =>
      ((continuous_apply (Fin.natAdd i j)).comp
        (continuous_const.matrix_mulVec (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_col_inv k (i + t)))).neg
    refine HasCompactSupport.of_support_subset_isCompact (hC.image hproj) ?_
    intro v hv
    obtain ⟨h, hh, c, hc, hp⟩ := hCf (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) g) hv
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, q, hxq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t ⟨h, hh⟩
    have hxq' : h = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) *
        GlobalTheory.BZMir.levi k (i + t) q := hxq
    have key : GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x = GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v +
        (g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹ := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul, hp, mul_inv_cancel_right, hxq',
        GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi]
    funext j
    have hj := congrFun key (Fin.natAdd i j)
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.topV, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_right, Pi.add_apply, Pi.zero_apply] at hj
    show -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j)) = v j
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact hj.symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

end
