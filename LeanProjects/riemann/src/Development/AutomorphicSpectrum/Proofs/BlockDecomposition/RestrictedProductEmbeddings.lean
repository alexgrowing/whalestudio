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

theorem map_list_prod_embed_of_nodup {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (f : ∀ i, Hl i) (j : ι) (l : List ι) (hl : l.Nodup) :
    p j (l.map fun i => e i (f i)).prod = if j ∈ l then f j else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2
    rw [List.map_cons, List.prod_cons, map_mul, ih']
    by_cases hja : a = j
    · subst hja
      simp [hnd.1, hpe]
    · have hne : ¬ j = a := fun h => hja h.symm
      rw [hpe' a j _ hja, one_mul]
      simp [hne]

theorem exists_local_levels_le_open : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  intro ι Γ _ Hl _ _ _ _ _ p e K KH hpc hec hpe hpe' hsep hK hKc hKo U hU
  classical
  have hcomp : IsCompact ((K : Set Γ) \ (U : Set Γ)) := hKc.diff hU
  have hopen : ∀ i, IsOpen {x : Γ | p i x ≠ 1} := fun i =>
    (isOpen_ne (x := (1 : Hl i))).preimage (hpc i)
  have hcover : (K : Set Γ) \ (U : Set Γ) ⊆ ⋃ i, {x : Γ | p i x ≠ 1} := by
    intro x hx
    by_contra hcon
    have hall : ∀ i, p i x = p i 1 := by
      intro i
      by_contra hi
      exact hcon (Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩)
    have hx1 : x = 1 := hsep x 1 hall
    exact hx.2 (hx1 ▸ U.one_mem)
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover _ hopen hcover
  have hTU : ∀ x, x ∈ K → (∀ i ∈ T, p i x = 1) → x ∈ U := by
    intro x hxK hx
    by_contra hxU
    have hmem := hT ⟨hxK, hxU⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨i, hi, hne⟩ := hmem
    exact hne (hx i hi)
  refine ⟨fun i => if i ∈ T then KH i ⊓ U.comap (e i) else KH i, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hKo i).inter (hU.preimage (hec i))
    · simp only [hi, if_false]
      exact hKo i
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact inf_le_left
    · simp only [hi, if_false]
      exact le_rfl
  · have hfin : ∀ᶠ i in cofinite, i ∉ T := T.finite_toSet.compl_mem_cofinite
    filter_upwards [hfin] with i hi
    simp only [hi, if_false]
  · intro u hu
    have hle : ∀ i, p i u ∈ KH i := by
      intro i
      have := hu i
      by_cases hi : i ∈ T
      · simp only [hi, if_true] at this
        exact this.1
      · simpa only [hi, if_false] using this
    have huK : u ∈ K := (hK u).mpr hle
    set v : Γ := (T.toList.map fun i => e i (p i u)).prod with hv
    have hpv : ∀ j, p j v = if j ∈ T then p j u else 1 := by
      intro j
      have := map_list_prod_embed_of_nodup p e hpe hpe' (fun i => p i u) j T.toList T.nodup_toList
      simpa [hv] using this
    have hvU : v ∈ U := by
      refine U.list_prod_mem ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hiT : i ∈ T := Finset.mem_toList.mp hi
      have := hu i
      simp only [hiT, if_true] at this
      exact this.2
    have hwK : v⁻¹ * u ∈ K := by
      refine (hK _).mpr fun j => ?_
      rw [map_mul, map_inv, hpv j]
      by_cases hj : j ∈ T
      · simp [hj, (KH j).one_mem]
      · simpa [hj] using hle j
    have hwU : v⁻¹ * u ∈ U := by
      refine hTU _ hwK fun i hi => ?_
      rw [map_mul, map_inv, hpv i]
      simp [hi]
    have := U.mul_mem hvU hwU
    simpa using this

end GlobalTheory.CompanionTheory.FinActS
