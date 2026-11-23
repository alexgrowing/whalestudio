import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem lev_of_mulChi (χ : HChar E) (φ : Sm E a) (h : HasLev (mulChi a χ φ)) : HasLev φ := by
  have hl : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := h
  change IsOpen {k | finRep E a k φ = φ}
  refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
  rintro k ⟨h1, h2⟩
  have h1' : rt E a (finGL E a k) (mulChi a χ φ) = mulChi a χ φ := h1
  have h2' : chiDet a χ (finGL E a k) = 1 := h2
  rw [rt_mulChi, h2'] at h1'
  change rt E a (finGL E a k) φ = φ
  apply (mulChi a χ).injective
  simpa using h1'

end

theorem UpperTheory.V.Cj.H.twSq :
    UpperTheory.V.Cj.H.TwSq := by
  intro E _ _ _ a ha μ _ _ r χ hχ φ hφ
  obtain ⟨⟨s, hs⟩, hχ⟩ := hχ
  have hG := gardFacts E a ha μ
  have hlie : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ X, mulChi a χ (lie E a X ψ) ∈ gard μ := fun ψ hψ X => by
    have h1 := (hG _ hψ).2.2.2.1 X
    rw [hχ, map_add, map_smul] at h1
    simpa using (gard μ).sub_mem h1 ((gard μ).smul_mem ((r * ell E a X : ℝ) : ℂ) hψ)
  have hleft : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ γ g,
      (mulChi a χ ψ).1 (ratGL E a γ * g) = (mulChi a χ ψ).1 g := fun ψ hψ γ g =>
    (hG _ hψ).2.1.1 _ (CuspidalL2GL.ratGL_mem_latticeGL γ) g
  have key : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → lie E a (oneL E a) ψ = -(r : ℂ) • ψ → IsSqIntMod ψ := fun ψ hψ hr => by
    have h0 : lie E a (oneL E a) (mulChi a χ ψ) = (0 : ℂ) • mulChi a χ ψ := by
      rw [hχ, hr, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, zero_smul, map_zero]
    have h1 : IsSqInt (mulChi a χ ψ).1 :=
      (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E a _ (hG _ hψ).1) (hleft ψ hψ) fun t g => by
        rw [aInv E a _ 0 h0 t g, zero_mul, Complex.exp_zero, one_mul]).1 (hG _ hψ).2.1
    refine ⟨s, χ, hs, ?_⟩
    have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * ψ.1 g) = (mulChi a χ ψ).1 := funext fun g => by
      rw [mulChi_apply, mul_comm]
    rw [e]
    exact h1
  refine ⟨hlie φ hφ, fun hr => ⟨fun γ g => ?_, lev_of_mulChi χ φ (hG _ hφ).1, hr, fun l => ?_⟩⟩
  · have h := hleft φ hφ γ g
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul] at h
    exact mul_right_cancel₀ (Units.ne_zero _) h
  · have h : mulChi a χ ((l.map (lie E a)).prod φ) ∈ gard μ ∧
        lie E a (oneL E a) ((l.map (lie E a)).prod φ) = -(r : ℂ) • (l.map (lie E a)).prod φ := by
      induction l with
      | nil => exact ⟨hφ, hr⟩
      | cons X l ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
        exact ⟨hlie _ ih.1 X, by rw [lie_one_comm, ih.2, map_smul]⟩
    exact key _ h.1 h.2
