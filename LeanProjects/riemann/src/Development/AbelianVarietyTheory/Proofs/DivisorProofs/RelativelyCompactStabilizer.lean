import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanCommutingIsometriesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupBoundedEntriesCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedNormCompactPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionStableBaseChangeStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.WeilM GlobalTheory.AdelicU

namespace GlobalTheory.StabBounded

theorem cA_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have e : compInf F E w (cA σ z) = sigR w.Completion σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [piInf, RingHom.comp_apply, e]
  exact (infEmb_sigR h τ _).symm

theorem exists_compact_superset_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∃ C : Set (UA σ X.J), IsCompact C ∧ ((GlobalTheory.StabHaar.stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ⊆ C := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hcm : IsCMExt F E σ := hB.cm
  have hJ : X.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hd : (X.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hx : star v ≠ 0 := by simpa using hv
    have := (hX.cartan w).2.2 (star v) hx
    rw [star_star, hMv, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose Rw hRw using fun w => GlobalTheory.T.cartan_commuting_isometries_bounded _ _ (hX.cartan w)
  set R : ℝ := ∑ w, |Rw w|
  have hlat := hX.lat
  obtain ⟨Cf, hCf, hCfe⟩ := GlobalTheory.StabCompact.exists_compact_entries F E X.L hlat.fg hlat.span_eq_top
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.T.bounded_norm_compact_preimage F E σ hcm B.emb Cf hCf R
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.T.unitary_group_bounded_entries_compact F E σ n X.J hJ K hK
  refine ⟨C, hC, fun g hg => hCe g fun i j => hKe _ ?_ ?_⟩
  · exact hCfe _ (GlobalTheory.T.lattice_completion_stable_base_change F E n X (mat g) fun z hz => (hg.2 z hz).1) i j
  · intro w
    have hu : ((mat g).map (piInf (B.emb w))).transpose * X.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star = X.J.map (B.emb w).1 := by
      have h2 := congrArg (fun Y : Matrix (Fin n) (Fin n) (AE F E) => Y.map (piInf (B.emb w)))
        (show (mat g).transpose * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2)
      simp only [Matrix.map_mul] at h2
      have e1 : (incM F X.J).map (piInf (B.emb w)) = X.J.map (B.emb w).1 := by
        ext i j
        simp [incM, piInf, compInf, inclR, infEmb_tmul]
      have e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star := by
        ext i j
        simp only [Matrix.map_apply]
        exact cA_piInf hcm _ _
      rw [e1] at h2
      rw [← e2, ← Matrix.transpose_map]
      exact h2
    have hb := hRw w _ hu (hg.1 w).eq i j
    calc ‖piInf (B.emb w) (mat g i j)‖ = ‖(mat g).map (piInf (B.emb w)) i j‖ := rfl
      _ ≤ Rw w := hb
      _ ≤ |Rw w| := le_abs_self _
      _ ≤ R := Finset.single_le_sum (f := fun w => |Rw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)

end GlobalTheory.StabBounded
