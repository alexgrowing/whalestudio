import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabiliserArchFiniteDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairUnfoldingLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairUnfoldingOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairUnfoldingMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairStabiliserIntegralStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblKFin

theorem comm_of_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {X : Spc F E n} (a f : UA σ X.J) (ha : a ∈ UAt σ X (evI F)) (hf : f ∈ UAt σ X (sndA F)) : a * f = f * a := by
  let e₀ : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have h₁ : evI F e₀ = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h₂ : sndA F (1 - e₀) = 0 := by
    show (1 - e₀).2 = 0
    show (1 : FiniteAdeleRing (𝓞 F) F) - 1 = 0
    exact sub_self _
  have hx : e₀ • (mat a - 1) = 0 := ha e₀ h₁
  have hy : (1 - e₀) • (mat f - 1) = 0 := hf _ h₂
  have hx' : mat a - 1 = (1 - e₀) • (mat a - 1) := by rw [sub_smul, one_smul, hx, sub_zero]
  have hy' : mat f - 1 = e₀ • (mat f - 1) := by
    rw [sub_smul, one_smul, sub_eq_zero] at hy
    exact hy
  have hxy : (mat a - 1) * (mat f - 1) = 0 := by
    rw [hx', smul_mul_assoc, ← mul_smul_comm, hy, mul_zero]
  have hyx : (mat f - 1) * (mat a - 1) = 0 := by
    rw [hy', smul_mul_assoc, ← mul_smul_comm, hx, mul_zero]
  have hm : mat a * mat f = mat f * mat a := by
    have e1 : mat a * mat f = 1 + (mat a - 1) + (mat f - 1) + (mat a - 1) * (mat f - 1) := by noncomm_ring
    have e2 : mat f * mat a = 1 + (mat a - 1) + (mat f - 1) + (mat f - 1) * (mat a - 1) := by noncomm_ring
    rw [e1, e2, hxy, hyx]
  exact Subtype.ext (Units.ext hm)

theorem doubled_kfin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K₂, Ψ = om₂ (1, k) (e (boxC Φ₁ Φ₂))}) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i _hi co hrat hdiag hanti om₂ hW e hbij hadm hint
    K₂ hK Φ₁ hΦ₁ Φ₂ hΦ₂
  obtain ⟨m, f, g, hfg, hsum⟩ := GlobalTheory.T.doubling_pair_unfolding_lattice F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ co hrat hdiag hanti
    e hbij hadm hint Φ₁ hΦ₁ Φ₂ hΦ₂
  have hsch : e (boxC Φ₁ Φ₂) ∈ schA F (Fin n × Fin (d + d)) := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, g i, (hfg i).2, rfl⟩
  have hmul : ∀ (x y : UA σ W₂.J) Ψ, om₂ (1, x * y) Ψ = om₂ (1, x) (om₂ (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : UA σ Xs.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have hSA : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (e (boxC Φ₁ Φ₂))}) := by
    have hle : Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (e (boxC Φ₁ Φ₂))} ≤
        ⨆ j : Fin m, Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (pureA F (f j) (g j))} := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [hsum, map_sum]
      exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (Submodule.subset_span ⟨a, ha, rfl⟩)
    haveI : ∀ j : Fin m, FiniteDimensional ℂ
        (Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (pureA F (f j) (g j))}) := fun j =>
      GlobalTheory.T.doubling_pair_unfolding_orbit F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ co hrat hdiag hanti om₂ hW (f j) (hfg j).1 (g j) (hfg j).2
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.T.doubling_pair_unfolding_measure F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ co hrat hdiag hanti om₂ hW
    _ hsch
  obtain ⟨S, hS, hcov⟩ := GlobalTheory.T.doubling_pair_stabiliser_integral F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL K₂ hK N hN
  have hle : Submodule.span ℂ {Ψ | ∃ k ∈ K₂, Ψ = om₂ (1, k) (e (boxC Φ₁ Φ₂))} ≤
      ⨆ j : S, (Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (e (boxC Φ₁ Φ₂))}).map (om₂ (1, j.1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨a, ha, f', hf', hf'fin, rfl⟩ := GlobalTheory.T.stabiliser_arch_finite_decomposition F E σ B (d + d) W₂ K₂ hK k hk
    obtain ⟨j, hj, hjN, hjfin⟩ := hcov f' hf' hf'fin
    have hcomm : a * j = j * a := comm_of_at a j ha.1 (hS j hj).2
    have key : om₂ (1, a * f') (e (boxC Φ₁ Φ₂)) = om₂ (1, j) (om₂ (1, a) (e (boxC Φ₁ Φ₂))) := by
      calc om₂ (1, a * f') (e (boxC Φ₁ Φ₂)) = om₂ (1, a * j * (j⁻¹ * f')) (e (boxC Φ₁ Φ₂)) := by
              rw [show a * j * (j⁻¹ * f') = a * f' by group]
        _ = om₂ (1, a * j) (om₂ (1, j⁻¹ * f') (e (boxC Φ₁ Φ₂))) := hmul _ _ _
        _ = om₂ (1, j * a) (e (boxC Φ₁ Φ₂)) := by rw [hfix _ hjN hjfin, hcomm]
        _ = _ := hmul _ _ _
    rw [key]
    exact Submodule.mem_iSup_of_mem ⟨j, hj⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, ha, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.DblKFin

end
