import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EigFinite

theorem eigSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  intro hP D μ j X l Q B hB hBv
  classical
  have hex := GlobalTheory.SplitConjPlace.splitEx_all D
  let ι := {p : PlE D.host × ℕ // GenAt D l Q p.1 p.2}
  have hch : ∀ i : ι, ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host i.1.1 s.w ∧ IsUnif D.host.E s.v ϖ := fun i => hex i.1.1 i.2.1
  choose s ϖ hs hϖ using hch
  have hfact := fun i : ι => hP D.host.E D.R.nV X.wt X.J X.χ B X.J_open hB (s i) (ϖ i) i.1.2
    (hBv _ _ _ i.2 (hs i)) (hϖ i) i.2.2.2.2.2.1 i.2.2.2.2.2.2
  have hTS : ∀ y, X.real y ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun y => X.real_range ▸ LinearMap.mem_range_self X.real y
  have hmem : ∀ (i : ι) (y : D.what₂.Mt μ j), ∃ y', X.real y' = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => by
    have h := (hfact i).1 _ (hTS y)
    rw [← X.real_range] at h
    exact h
  choose g hg using hmem
  have h0 : ∀ i : ι, NG.tN X.J (s i) (ϖ i) i.1.2 0 = 0 := fun i => by
    have h := (hfact i).2.1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at h
    simpa using h
  let op : ι → Module.End ℂ (D.what₂.Mt μ j) := fun i =>
    { toFun := g i
      map_add' := fun y y' => X.real_inj (by
        rw [hg, map_add, map_add, hg, hg]
        have h := (hfact i).2.1 _ (hTS y) _ (hTS y') 1
        simpa using h)
      map_smul' := fun c y => X.real_inj (by
        rw [hg, map_smul, map_smul, hg]
        have h := (hfact i).2.1 _ (hTS y) 0 (Submodule.zero_mem _) c
        simpa [h0] using h) }
  have hop : ∀ i y, X.real (op i y) = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => hg i y
  have hcomm : ∀ i i' : ι, Commute (op i) (op i') := fun i i' => by
    ext y
    apply X.real_inj
    show X.real (op i (op i' y)) = X.real (op i' (op i y))
    rw [hop, hop, hop, hop]
    exact (hfact i).2.2.1 (s i') (ϖ i') i'.1.2 (hBv _ _ _ i'.2 (hs i')) (hϖ i') i'.2.2.2.2.2.1 i'.2.2.2.2.2.2 _ (hTS y)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo op
    (fun i i' φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm i' i) φ)
  have hfin : {χ : ι → ℂ | ⨅ i, (op i).maxGenEigenspace (χ i) ≠ ⊥}.Finite :=
    Set.finite_coe_iff.mp (@Finite.of_fintype _ hind.fintypeNeBotOfFiniteDimensional)
  let Φ : (PlE D.host → ℕ → ℂ) → (ι → ℂ) := fun c i => c i.1.1 i.1.2
  apply Set.Finite.of_finite_image (f := Φ)
  · apply hfin.subset
    rintro _ ⟨c, ⟨-, y, hy0, hy⟩, rfl⟩
    show ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) ≠ ⊥
    intro hbot
    apply hy0
    have hyin : y ∈ ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) := by
      rw [Submodule.mem_iInf]
      intro i
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      apply X.real_inj
      rw [hop, map_smul]
      exact hy i.1.1 i.1.2 (s i) (ϖ i) i.2 (hs i) (hϖ i)
    rw [hbot] at hyin
    exact (Submodule.mem_bot ℂ).1 hyin
  · rintro c ⟨hc, -⟩ c' ⟨hc', -⟩ hcc
    funext v k
    by_cases h : GenAt D l Q v k
    · exact congrFun hcc ⟨(v, k), h⟩
    · rw [hc v k h, hc' v k h]

end GlobalTheory.EigFinite
