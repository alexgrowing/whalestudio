import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.StabBoundedSkew

theorem exists_compact_superset_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → ∀ K : Subgroup (UA σ W.J), IsStab (X := W) B K →
    ∃ C : Set (UA σ W.J), IsCompact C ∧ (K : Set (UA σ W.J)) ⊆ C := by
  intro F E _ _ _ _ _ σ B d W r s hB hW K hK
  have hcm : IsCMExt F E σ := hB.cm
  have hJ : W.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hd : (W.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hx : star v ≠ 0 := by simpa using hv
    have := (hW.cartan w).2.2 (star v) hx
    rw [star_star, Matrix.smul_mulVec, hMv, smul_zero, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose Rw hRw using fun w => GlobalTheory.T.cartan_commuting_isometries_bounded _ _ (hW.cartan w)
  set R : ℝ := ∑ w, |Rw w|
  have hlat := hW.lat
  obtain ⟨Cf, hCf, hCfe⟩ := GlobalTheory.StabCompact.exists_compact_entries F E W.L hlat.fg hlat.span_eq_top
  obtain ⟨K', hK', hKe⟩ := GlobalTheory.T.bounded_norm_compact_preimage F E σ hcm B.emb Cf hCf R
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.T.unitary_group_bounded_entries_compact F E σ d W.J hJ K' hK'
  refine ⟨C, hC, fun g hg => ?_⟩
  have hg' := (hK g).1 hg
  refine hCe g fun i j => hKe _ ?_ ?_
  · exact hCfe _ (GlobalTheory.T.lattice_completion_stable_base_change F E d W (mat g) fun z hz => (hg'.2 z hz).1) i j
  · intro w
    have hu0 : ((mat g).map (piInf (B.emb w))).transpose * W.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star = W.J.map (B.emb w).1 := by
      have h2 := congrArg (fun Y : Matrix (Fin d) (Fin d) (AE F E) => Y.map (piInf (B.emb w)))
        (show (mat g).transpose * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2)
      simp only [Matrix.map_mul] at h2
      have e1 : (incM F W.J).map (piInf (B.emb w)) = W.J.map (B.emb w).1 := by
        ext i j
        simp [incM, piInf, compInf, inclR, infEmb_tmul]
      have e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star := by
        ext i j
        simp only [Matrix.map_apply]
        exact GlobalTheory.StabBounded.cA_piInf hcm _ _
      rw [e1] at h2
      rw [← e2, ← Matrix.transpose_map]
      exact h2
    have hu : ((mat g).map (piInf (B.emb w))).transpose * (Complex.I • W.J.map (B.emb w).1) * ((mat g).map (piInf (B.emb w))).map star = Complex.I • W.J.map (B.emb w).1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hu0]
    have hb := hRw w _ hu (hg'.1 w).eq i j
    calc ‖piInf (B.emb w) (mat g i j)‖ = ‖(mat g).map (piInf (B.emb w)) i j‖ := rfl
      _ ≤ Rw w := hb
      _ ≤ |Rw w| := le_abs_self _
      _ ≤ R := Finset.single_le_sum (f := fun w => |Rw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)

end GlobalTheory.StabBoundedSkew
