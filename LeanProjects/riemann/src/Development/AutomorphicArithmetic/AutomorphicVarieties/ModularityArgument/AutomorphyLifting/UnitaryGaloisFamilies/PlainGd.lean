import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Af.Gu
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private UpperTheory.V.Z.Win.MonodromyFreeReciprocity.isL_chars UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_sum_list UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_of_character UpperTheory.V.Z.Win.MonodromyFreeReciprocity.tor_sum from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec

namespace UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant

private theorem equiv_prinSeries {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i)) (hs : HasSupport ρ (GlobalTheory.RoadU.chars ξ hξ))
    (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) : Nonempty (ρ.Equiv (prinSeries ξ)) := by
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V ρ ξ hξ).1 hs
  let y : Fin n → IrrGL k := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hP : (prodIrr y hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j)))
      (fun i => (single_spec (hy i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (y i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ξ i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (y i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i)))).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI := GlobalTheory.TypeTwo.PowIrrProof.nontrivial_of_isSubquotient (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ξ)
  obtain ⟨e⟩ := GlobalTheory.TypeTwo.PowIrrProof.equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
  obtain ⟨f⟩ := hq.nonempty_equiv hi (GlobalTheory.Parabolic.isIrreducible_of_equiv e hM)
  exact ⟨f.symm⟩

end UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant

open UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant in
theorem UpperTheory.V.Z.Win.Gu.plainGd :
    PlainGd := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨e⟩ := equiv_prinSeries σ.ρ ξ hξ hs' hu
  have hL := (UpperTheory.V.Z.Win.MonodromyFreeReciprocity.isL_chars σ.ρ σ.irred ξ hξ hu e).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, L.one]
  have hA : rc (algNorm σ) = (sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i)))).lpTw
      ((1 - (n : ℝ)) / 2) := by
    rw [algNorm, L.nu, hr]
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.tor_sum _ _ _ (by rw [← hA, L.dim]; rfl)
  · rw [hA, WD.monomial_twist_iff]
    exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_sum_list _ fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_of_character _ _
