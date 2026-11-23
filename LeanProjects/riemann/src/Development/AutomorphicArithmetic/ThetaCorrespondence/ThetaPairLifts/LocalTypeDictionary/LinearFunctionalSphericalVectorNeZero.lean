import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsLinearFunctionalAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocalStatement

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.VacLinW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem linearFunctional_sphericalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.splitPlace_linearFunctional_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v t b c
  have hcm : IsCMExt F E σ := hPair.base.cm
  obtain ⟨hSB, hne, θ, -, hfix⟩ := hPair.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have htt : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hfix' : ∀ γ ∈ latAtV X W v, (γ.map (piW (t.comp σ)) = 0 ∨ γ.map (piW t) = 0) →
      Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v) (M.vac v) := by
    intro γ hγ h
    have h0 : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ = 0 := by
      rcases h with h | h
      · exact symp_eq_zero_of_comp hcm t (hat γ hγ) h h _ _ _
      · rw [← htt] at h
        exact symp_eq_zero_of_comp hcm (t.comp σ) (hat γ hγ) h h _ _ _
    have := hfix γ hγ
    rwa [h0, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  set f := ι (M.vac v) with hf
  set S : Set (Matrix (Fin n) (Fin d) (Fv F v)) := {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} with hS
  have htr : ∀ A ∈ S, ∀ Y, f (Y + A) = f Y := by
    intro A hA Y
    obtain ⟨γ, hγ, h0, hco⟩ := GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate hcm X W v t b c hb hc A hA
    have := hι.trans γ (hat γ hγ) h0 _ hSB _ hSB (hfix' γ hγ (Or.inl h0)) Y
    rw [hco] at this
    exact this.symm
  have hsupp : ∀ Y, f Y ≠ 0 → Y ∈ S := by
    intro Y hY
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq hcm v t b c Y
    have hψ : ∀ u ∈ latAtV X W v, u.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1 := by
      intro u hu hu0
      have hm := hι.mult u (hat u hu) hu0 _ hSB _ hSB (hfix' u hu (Or.inr hu0)) x hx hx0
      exact (mul_eq_right₀ hY).mp hm.symm
    have hmem : x ∈ latAtV X W v := by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hPair.base hPair.herm hPair.skew v x hx).2
        fun γ hγ => ?_
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl, h₁, h₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hcm X W v t γ hγ
      rw [symp_add_right, symp_eq_zero_of_comp hcm t hx hx0 h₁, zero_add]
      exact hψ γ₂ hγ₂ h₂
    exact GlobalTheory.T.splitPlace_tensorLattice_component_integral X W v t b c hb hc x hmem
  have hf0 : f ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn hSB (zero_mem _) ?_
    rw [map_zero]; exact h
  have hfe : f = f 0 • S.indicator 1 := by
    funext Y
    by_cases hY : Y ∈ S
    · rw [Pi.smul_apply, Set.indicator_of_mem hY, Pi.one_apply, smul_eq_mul, mul_one, ← htr Y hY 0, zero_add]
    · rw [Pi.smul_apply, Set.indicator_of_notMem hY, smul_zero]
      by_contra h
      exact hY (hsupp Y h)
  have hz : f 0 ≠ 0 := by
    intro h
    apply hf0
    rw [hfe, h, zero_smul]
  refine ⟨(f 0)⁻¹ • ι, isLin_smul M B.ψ hι (inv_ne_zero hz), ?_⟩
  rw [LinearMap.smul_apply, ← hf]
  exact (congrArg ((f 0)⁻¹ • ·) hfe).trans (by rw [smul_smul, inv_mul_cancel₀ hz, one_smul])
end GlobalTheory.VacLinW
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearFunctional_sphericalVector_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | exact _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | (intros; apply _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector <;> assumption)
end
