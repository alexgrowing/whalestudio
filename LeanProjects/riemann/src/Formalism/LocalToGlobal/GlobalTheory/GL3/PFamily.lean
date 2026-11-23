import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkChi
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def TaylorCoeffsInNumberField (D : D7) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def NonzeroThetaVectorFamily (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' → e N N' L L' ∈ Th D T L L' ∧ e N N' L L' ≠ 0

def ThetaMeanBound (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  ∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc

def ThetaNormConjugateIndependent (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))

theorem theta_vector_family_iff_parts (D : D7) (T : Tor D) (e : FamE D) : vec22 D T e ↔ NonzeroThetaVectorFamily D T e ∧ TaylorCoeffsInNumberField D e :=
  ⟨fun h => ⟨fun N N' L L' hA => ⟨(h N N' L L' hA).1, (h N N' L L' hA).2.1⟩, fun N N' L L' hA => (h N N' L L' hA).2.2⟩,
    fun h N N' L L' hA => ⟨(h.1 N N' L L' hA).1, (h.1 N N' L L' hA).2, h.2 N N' L L' hA⟩⟩

theorem theta_conditions_iff (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) :
    th22 D T C e ↔ ThetaNormIndependent D T e ∧ ThetaMeanBound D T C e ∧ ThetaNormConjugateIndependent D T e ∧ th22U D T e := Iff.rfl

def EigenvectorPacketProperties {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (C : ℝ) (χ : IdE D → ℂ) : Prop :=
  TaylorCoeffsInNumberField D (B.eNat χ) ∧ ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) ∧ ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) ∧
    B.EqP χ ∧ B.IntP χ ∧ B.MomP χ ∧ B.StrP χ

def LinkBaseNe : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Base D cc δ → δ ≠ 0

def LinkVecE : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK → ∀ χ, IsChi D χ → NonzeroThetaVectorFamily D (tor0 D cc δ) (B.eNat χ)

def LinkThE : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK → ∀ χ, IsChi D χ →
      ThetaNormIndependent D (tor0 D cc δ) (B.eNat χ) ∧ th22U D (tor0 D cc δ) (B.eNat χ)

def SevenFamilyProperties : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK → ∀ (C : ℝ) (χ : IdE D → ℂ), IsChi D χ → EigenvectorPacketProperties B C χ → B.LateralTheory C χ

def LinkStandardBase : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, B.StdOK ∧ ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def LinkStandardBase' : Prop :=
  LinkPer → ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, B.StdOK ∧ ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem lamOf_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  unfold lamOf
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨c, -, rfl⟩
  simp

theorem base_linkage_nonempty : LinkBaseNe := by
  intro D cc δ B h0
  subst h0
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, lamOf_zero, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)

theorem vector_link_holds : LinkVecE :=
  fun D cc hcc δ hδ B hS χ hχ => B.vec_mem_ne hcc hδ (base_linkage_nonempty D cc δ B) hS χ hχ

theorem theta_link_holds : LinkThE :=
  fun D cc hcc δ hδ B hS χ hχ =>
    ⟨B.th_indep hcc hδ (base_linkage_nonempty D cc δ B) hS χ hχ, B.th_U hcc hδ (base_linkage_nonempty D cc δ B) hS χ hχ⟩

theorem seven_family_properties : SevenFamilyProperties := by
  intro D cc hcc δ hδ B hS C χ hχ ⟨r1, r2, r3, r4, r5, r6, r7⟩
  have hT := theta_link_holds D cc hcc δ hδ B hS χ hχ
  exact ⟨(theta_vector_family_iff_parts D _ _).2 ⟨vector_link_holds D cc hcc δ hδ B hS χ hχ, r1⟩, ⟨hT.1, r2, r3, hT.2⟩, r4, r5, r6, r7⟩

theorem eigen_linkage_holds : LinkStandardBase := by
  intro D C hA hper h
  refine conclusion_of_hecke_commutation D C hper (character_linkage_holds D hA) ?_
  intro cc hcc δ hδ
  obtain ⟨B, hS, hB⟩ := h cc hcc δ hδ
  exact ⟨B, fun χ hχ => seven_family_properties D cc hcc δ hδ B hS C χ hχ (hB χ hχ)⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
