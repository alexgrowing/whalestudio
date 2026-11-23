import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem block_matrix_apply_inl_inl_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem block_matrix_mul_comm_ring {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem one_ll {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
      (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne (fun h' => h (Sum.inl_injective (finSumFinEquiv.injective h'))), Matrix.one_apply_ne h]

theorem one_lr {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 :=
  Matrix.one_apply_ne fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)

variable {S : Finset (Pl D)}

theorem offM_of_N {g : G D n} (hg : g ∈ KOff D n S) {b : Mx D n n} (hb : mat g = blk4 1 b 0 1) : OffM S b := by
  intro i j
  have e : b i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by rw [hb, block_matrix_apply_inl_inr_alt]
  refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [e, LFixTh.kOff_inf hg, one_lr]
  · rw [e, LFixTh.kOff_at hg hv, one_lr]
  · rw [e]; exact (LFixTh.kOff_int hg hv _ _).1

theorem intS_inner (V : HSp D) {S : Finset (Pl D)} (hQ : ∀ i j, IntS S (rat V.gram i j)) {x : Mx D V.rank n}
    (hx : IntOff S x) (i j : Fin n) : IntS S (inner V x x i j) :=
  intS_mul (adj_intS ((intOff_iff x).1 hx)) (intS_mul hQ ((intOff_iff x).1 hx)) i j

theorem fixN (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle), IsWeilSch ψ χ θ V μ ω →
      ∀ g ∈ KOff D n S, IsN g → ∀ Ψ : schwartzA θ V.rank n, (∀ x, ¬ IntOff S x → Ψ.1 x = 0) → ω g Ψ = Ψ := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_off hψ
  obtain ⟨S₂, hS₂⟩ := exists_rat_int V.gram
  refine ⟨S₁ ∪ S₂, fun S hS n θ μ ω χ hω g hg hN Ψ hΨ => ?_⟩
  obtain ⟨b, hb⟩ := hN
  have hQ := hS₂ S (fun v h => hS (Finset.mem_union_right _ h))
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.unip g b hb Ψ x]
  by_cases hx : IntOff S x
  · have h := (hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) _
      (offS_trace (offS_mul_right (offM_of_N hg hb) (intS_inner V hQ hx)))).2
    rw [h, one_mul]
  · rw [hΨ x hx, mul_zero]

end PositivityTheory.Rg.Rsw.L.LFixW

end
