import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasicA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exp_pmat_inUJ {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inUJ ε (NormedSpace.exp (pmat z)) := by
  have h := inUJ_kexp (1 : KG ε) (pmat_inP z)
  have e : toMK (1 : KG ε) = 1 := rfl
  rwa [e, Matrix.one_mul] at h

theorem polarM_inUJ {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : inUJ ε (polarM kz) :=
  inUJ_kexp kz.1 (pmat_inP kz.2)

theorem pmat_injective (ε : Fin n → Bool) : Function.Injective (pmat (ε := ε)) := by
  intro z z' h
  funext ab
  have := congrFun (congrFun h ab.1.1) ab.1.2
  simpa [pmat, dif_pos ab.2] using this

theorem polarM_injective (ε : Fin n → Bool) : Function.Injective (polarM (ε := ε)) := by
  rintro ⟨k, z⟩ ⟨k', z'⟩ h
  obtain ⟨hk, hX⟩ := polar_unique (pmat_inP z) (pmat_inP z')
    (show toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp (pmat z') from h)
  rw [hk, pmat_injective ε hX]

theorem polarM_surj {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    ∃ kz : KG ε × (PCoord ε → ℂ), polarM kz = g := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  refine ⟨(k, fun ab => X ab.1.1 ab.1.2), ?_⟩
  show toMK k * NormedSpace.exp (pmat fun ab : PCoord ε => X ab.1.1 ab.1.2) = _
  rw [pmat_coords X hX]

open scoped Matrix.Norms.L2Operator in
theorem polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

section Emb

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem polarM_continuous (ε : Fin n → Bool) : Continuous (polarM (ε := ε)) := by
  unfold polarM
  exact ((continuous_toM ε).comp (continuous_subtype_val.comp continuous_fst)).mul
    (NormedSpace.exp_continuous.comp ((pmat_continuous ε).comp continuous_snd))

def polarInvK (ε : Fin n → Bool) (g : UJset ε) : KG ε :=
  Classical.choose (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

theorem toMK_polarInvK (ε : Fin n → Bool) (g : UJset ε) :
    toMK (polarInvK ε g) = g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) :=
  Classical.choose_spec (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

def polarInv (ε : Fin n → Bool) (g : UJset ε) : KG ε × (PCoord ε → ℂ) :=
  (polarInvK ε g, fun ab => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2)

theorem polarM_polarInv (ε : Fin n → Bool) (g : UJset ε) : polarM (polarInv ε g) = g.1 := by
  show toMK (polarInvK ε g) * NormedSpace.exp (pmat fun ab : PCoord ε => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2) = g.1
  rw [pmat_coords _ (PolarDecomposition.polar_L_inP (ε := ε) (g := g.1) g.2), toMK_polarInvK]
  exact PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L.symm

theorem polarInv_continuous (ε : Fin n → Bool) : Continuous (polarInv ε) := by
  have hL : Continuous fun g : UJset ε => PolarDecomposition.polar_L g.1 :=
    (polarL_continuousOn ε).comp_continuous continuous_subtype_val (fun g => g.2)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) :=
    (isClosedEmbedding_toM ε).isInducing.comp Topology.IsInducing.subtypeVal
  have hK : Continuous (polarInvK ε) := by
    rw [hind.continuous_iff]
    have : (fun k : KG ε => toMK k) ∘ polarInvK ε =
        fun g : UJset ε => g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) := by
      funext g; exact toMK_polarInvK ε g
    rw [this]
    exact continuous_subtype_val.mul (NormedSpace.exp_continuous.comp hL.neg)
  exact hK.prodMk (continuous_pi fun ab => hL.matrix_elem ab.1.1 ab.1.2)

def polarHomeo (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) ≃ₜ UJset ε where
  toFun kz := ⟨polarM kz, polarM_inUJ kz⟩
  invFun := polarInv ε
  left_inv kz := polarM_injective ε (polarM_polarInv ε ⟨polarM kz, polarM_inUJ kz⟩)
  right_inv g := Subtype.ext (polarM_polarInv ε g)
  continuous_toFun := (polarM_continuous ε).subtype_mk _
  continuous_invFun := polarInv_continuous ε

theorem polarM_isClosedEmbedding (ε : Fin n → Bool) : Topology.IsClosedEmbedding (polarM (ε := ε)) := by
  have h : Topology.IsClosedEmbedding ((Subtype.val : UJset ε → Matrix (Fin n) (Fin n) ℂ) ∘ polarHomeo ε) :=
    (isClosed_inUJ ε).isClosedEmbedding_subtypeVal.comp (polarHomeo ε).isClosedEmbedding
  exact h

end Emb

theorem jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) :=
  pb_jac_continuous ε

end ReciprocityTheory.ChartRestriction.DS
