import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.BlockConj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem algSat_sum {ι : Type} [Fintype ι] (n q : ℕ) (B : ι → Multiset ℂˣ) :
    algSat n q (∑ i, B i) = ∑ i, algSat n q (B i) := by
  have e : ∀ C : Multiset ℂˣ, algSat n q C =
      C.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun C => by simp [algSat]
  simp only [e]
  exact map_sum (Multiset.mapAddMonoidHom _) B Finset.univ

theorem UpperTheory.V.Cj.noEis :
    UpperTheory.V.Cj.NoEis := by
  intro hJ E _ _ _ a ha ih π σ τ τ' hτ hc m hm ι _ n P μ k1 k2 k3 k4 k5 hw
  have hle : ∀ i t, μ i t ≤ m t := fun i t => by
    rw [← k5 t]
    exact Finset.single_le_sum (f := fun i => μ i t) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  choose Q hQ using fun i => blockConj E a (n i) (ih _ (k2 i) (k3 i)) (P i) (μ i) m (k4 i) (hle i) hm σ.symm
  have s1 : Sep σ.symm τ'.ρ π.finPart := hc.sep.2.trans hτ.sep.2
  have s2 : Sep σ.symm.symm π.finPart τ'.ρ := hτ.sep.1.trans hc.sep.1
  obtain ⟨s, -⟩ := hJ E Unit ι (fun _ => a) n (fun _ => CG.mk π) Q (fun _ => ha) k2 (hw.mono fun w ⟨B, h1, h2⟩ => by
    choose B' b1 b2 using fun i => hQ i w (B i) (h1 i)
    refine ⟨fun _ => ∑ i, B' i, B', fun _ => (CG.hasSat_mk ..).2 ?_, b1, by simp⟩
    refine (s1.comp _).hasSatGL (s2.comp _) h2 ?_
    rw [algSat_sum, algSat_sum, Finset.sum_congr rfl fun i _ => b2 i]
    exact (map_sum (Multiset.mapAddMonoidHom _) _ Finset.univ).symm)
  have := Fintype.card_congr s
  rw [Fintype.card_unit] at this
  omega
