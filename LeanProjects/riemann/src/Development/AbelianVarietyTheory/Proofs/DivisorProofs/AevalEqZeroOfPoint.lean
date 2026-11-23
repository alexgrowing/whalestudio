import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMultiplicityDvdFixFirstBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.HSElim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_eq_zero_of_point {F K : Type} [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
    {N e δ : ℕ} {P : Ideal (MvPolynomial (Fin N) F)} {f : MvPolynomial (Fin (e + 1) × Fin N) F}
    (hf : IsChowFormInt P e δ f) (s : Fin (e + 1) → Fin N → K) (y : Fin N → K) (hy : y ≠ 0)
    (hyP : ∀ a ∈ P, aeval y a = 0) (hs : ∀ i, ∑ j, s i j * y j = 0) :
    aeval (fun p : Fin (e + 1) × Fin N => s p.1 p.2) f = 0 := by
  let φ : K ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F K (AlgebraicClosure F)
  have hmap : ∀ {σ : Type} (x : σ → K) (a : MvPolynomial σ F),
      aeval (fun i => φ (x i)) a = φ (aeval x a) := fun x a =>
    (AlgHom.congr_fun (MvPolynomial.comp_aeval (f := x) (φ : K →ₐ[F] AlgebraicClosure F)) a).symm
  have key : aeval (fun p : Fin (e + 1) × Fin N => φ (s p.1 p.2)) f = 0 := by
    refine (hf.zero_iff _).2 ⟨fun j => φ (y j), ?_, fun a ha => ?_, fun i => ?_⟩
    · intro h
      apply hy
      funext j
      have := congrFun h j
      simpa using this
    · rw [hmap, hyP a ha, map_zero]
    · have := congrArg φ (hs i)
      simpa [map_sum, map_mul] using this
  rw [hmap (fun p : Fin (e + 1) × Fin N => s p.1 p.2)] at key
  simpa using key

theorem exists_elim_form : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ)
    (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime →
    (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) →
    ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I →
    ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ D * d * hilbertDegree I ∧
      ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin D → Fin N → K)
        (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 →
        (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hp hcomp hdim hg hgI
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have hIh := GlobalTheory.ChowExists.isHomogeneous_of_component hcomp
  obtain ⟨f0, hf0⟩ := GlobalTheory.ChowExists.exists_isChowFormInt hp hIh hdim
  obtain ⟨i0, hi0⟩ := GlobalTheory.ChowExists.exists_X_notMem hf0
  have hJh := isHomogeneous_sup_span_singleton hIh hg
  have hex : ∀ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset,
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) F, IsChowFormInt P e (hilbertDegree P) f := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    have hPp := hP.1.1.1
    obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup hIh hdim hg hgI hP
    obtain rfl : e = e' := by omega
    exact GlobalTheory.ChowExists.exists_isChowFormInt hPp (isHomogeneous_of_mem_projComponents hJh hP) h2
  choose! f hf using hex
  refine ⟨∏ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, f P, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun P hP => (hf P hP).ne_zero
  · refine (totalDegree_finsetProd _ _).trans ?_
    have h1 : ∑ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, (f P).totalDegree =
        (e + 1) * projSetDegree (I ⊔ Ideal.span {g}) := by
      rw [projSetDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P hP => GlobalTheory.ChowSection.totalDegree_of_isChowFormInt (hf P hP)
    rw [h1, mul_assoc]
    exact Nat.mul_le_mul_left _ (projSetDegree_sup_le_of_isPrime hIh hi0 hg hgI)
  · intro K _ _ _ s y hy hyI hyg hs
    rw [map_prod]
    let Jy : Ideal (MvPolynomial (Fin N) F) := RingHom.ker (aeval y : MvPolynomial (Fin N) F →ₐ[F] K)
    have hJy : I ⊔ Ideal.span {g} ≤ Jy := sup_le (fun a ha => (RingHom.mem_ker).2 (hyI a ha))
      ((Ideal.span_singleton_le_iff_mem _).2 ((RingHom.mem_ker).2 hyg))
    have : Jy.IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hPc : P ∈ projComponents (I ⊔ Ideal.span {g}) :=
      ⟨hPmin, i, fun h => hi (by simpa using (RingHom.mem_ker).1 (hPle h))⟩
    have hPf : P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset :=
      (Set.Finite.mem_toFinset _).2 hPc
    exact Finset.prod_eq_zero hPf (aeval_eq_zero_of_point (hf P hPf) s y hy
      (fun a ha => (RingHom.mem_ker).1 (hPle ha)) hs)

end GlobalTheory.HSElim
