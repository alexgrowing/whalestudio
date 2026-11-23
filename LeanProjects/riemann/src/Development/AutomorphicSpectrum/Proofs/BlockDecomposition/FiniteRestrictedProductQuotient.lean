import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem finite_cosets_of_components_mem
    {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i)
    (V : ∀ i, Subgroup (Hl i)) (Q : ∀ i, Set (Hl i))
    (hQ : ∀ i, ∀ x ∈ Q i, ∀ u ∈ V i, x * u ∈ Q i)
    (hQf : ∀ i, {q : Hl i ⧸ V i | q.out ∈ Q i}.Finite)
    (hQV : ∀ᶠ i in cofinite, Q i ⊆ V i) :
    {q : Γ ⧸ (⨅ i, (V i).comap (p i)) | ∀ i, p i q.out ∈ Q i}.Finite := by
  have hT : {i | ¬ Q i ⊆ V i}.Finite := Filter.eventually_cofinite.mp hQV
  haveI : Finite {i | ¬ Q i ⊆ V i} := hT.to_subtype
  let f : Γ ⧸ (⨅ i, (V i).comap (p i)) → ∀ i : {i | ¬ Q i ⊆ V i}, Hl i.1 ⧸ V i.1 :=
    fun q i => ((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)
  have hfin : (Set.univ.pi fun i : {i | ¬ Q i ⊆ V i} =>
      {c : Hl i.1 ⧸ V i.1 | c.out ∈ Q i.1}).Finite :=
    Set.Finite.pi fun i => hQf i.1
  refine Set.Finite.of_injOn (f := f) ?_ ?_ hfin
  · intro q hq i _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V i.1) (p i.1 q.out)
    show (((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)).out ∈ Q i.1
    rw [hh]
    exact hQ i.1 _ (hq i.1) _ h.2
  · intro q hq q' hq' hfq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    refine Subgroup.mem_iInf.mpr fun i => ?_
    rw [Subgroup.mem_comap, map_mul, map_inv]
    by_cases hi : Q i ⊆ V i
    · exact (V i).mul_mem ((V i).inv_mem (hi (hq i))) (hi (hq' i))
    · exact QuotientGroup.eq.mp (congrFun hfq ⟨i, hi⟩)

end GlobalTheory.CompanionTheory.FinActS
