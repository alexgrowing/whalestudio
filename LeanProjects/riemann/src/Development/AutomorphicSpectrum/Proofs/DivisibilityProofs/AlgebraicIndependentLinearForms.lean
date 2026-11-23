import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem algebraicIndependent_linearForms {F E : Type} [Field F] [Field E] [Algebra F E]
    {D κ : Type} [Fintype D] [Fintype κ] (u : D → E) (hu : AlgebraicIndependent F u)
    (v : κ → D → F) (hv : LinearIndependent F v) :
    AlgebraicIndependent F fun i => ∑ c, algebraMap F E (v i c) * u c := by
  classical
  obtain ⟨T, hT⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F v)
    (LinearMap.ker_eq_bot.2 hv.fintypeLinearCombination_injective)
  have hTv : ∀ i, T (v i) = Pi.single i 1 := by
    intro i
    have := LinearMap.congr_fun hT (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hdual : ∀ i j, ∑ c, v i c * T (Pi.single c 1) j = (Pi.single i 1 : κ → F) j := by
    intro i j
    have hvi : v i = ∑ c, v i c • (Pi.single c 1 : D → F) := by
      ext d
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← hTv i]
    conv_rhs => rw [hvi]
    simp [map_sum, Finset.sum_apply]
  let A : MvPolynomial κ F →ₐ[F] MvPolynomial D F :=
    aeval fun i => ∑ c, MvPolynomial.C (v i c) * MvPolynomial.X c
  let B : MvPolynomial D F →ₐ[F] MvPolynomial κ F :=
    aeval fun c => ∑ j, MvPolynomial.C (T (Pi.single c 1) j) * MvPolynomial.X j
  have hBA : B.comp A = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [A, B, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply,
      algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, hdual]
    simp [Pi.single_apply, ite_mul]
  have hA : Function.Injective A := by
    intro f g h
    have := congrArg B h
    have e : ∀ f, B (A f) = f := fun f => by
      simpa using DFunLike.congr_fun hBA f
    rwa [e, e] at this
  have hcomp : (aeval fun i => ∑ c, algebraMap F E (v i c) * u c : MvPolynomial κ F →ₐ[F] E) =
      (aeval u).comp A := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [A, map_sum, aeval_X, algHom_C]
  have : Function.Injective (aeval fun i => ∑ c, algebraMap F E (v i c) * u c :
      MvPolynomial κ F →ₐ[F] E) := by
    rw [hcomp]
    exact Function.Injective.comp (f := A) hu hA
  exact this

theorem ker_eq_span_homogeneous {F E : Type} [Field F] [Field E] [Algebra F E]
    {P D : Type} [Fintype P] [Fintype D] (u : D → E) (hu : AlgebraicIndependent F u)
    (l : P → D → F) :
    RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MvPolynomial P F →ₐ[F] E) =
      Ideal.span {f : MvPolynomial P F | f.IsHomogeneous 1 ∧
        aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) f = 0} := by
  classical
  set x : P → E := fun p => ∑ c, algebraMap F E (l p c) * u c with hx
  set S : Set (MvPolynomial P F) := {f | f.IsHomogeneous 1 ∧ aeval x f = 0} with hS
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F l
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hc : ∀ p, ∃ c : κ → F, ∑ i, c i • l (a i) = l p := by
    intro p
    have hp : l p ∈ Submodule.span F (Set.range (l ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, rfl⟩
    simpa using (Submodule.mem_span_range_iff_exists_fun F).1 hp
  choose c hc using hc
  let ρ' : MvPolynomial P F →ₐ[F] MvPolynomial κ F :=
    aeval fun p => ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X i
  let ρ : MvPolynomial P F →ₐ[F] MvPolynomial P F := (rename a).comp ρ'
  have hρX : ∀ p, ρ (MvPolynomial.X p) = ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X (a i) := by
    intro p
    simp [ρ, ρ', map_sum, aeval_X, rename_C, rename_X]
  have hxp : ∀ p, x p = ∑ i, algebraMap F E (c p i) * x (a i) := by
    intro p
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have : l p d = ∑ i, c p i * l (a i) d := by
      rw [← hc p]
      simp [Finset.sum_apply]
    rw [this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
  have hmem : ∀ p, MvPolynomial.X p - ρ (MvPolynomial.X p) ∈ S := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [hρX]
      exact (isHomogeneous_X F p).sub
        (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (c p i) (a i))
    · rw [hρX]
      simp only [map_sub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq]
      simpa [sub_eq_zero] using hxp p
  have hle : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial P F →ₐ[F] E) := by
    rw [Ideal.span_le]
    intro f hf
    exact hf.2
  have hq : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp ρ = Ideal.Quotient.mkₐ F (Ideal.span S) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.Quotient.eq.2 (Ideal.subset_span (hmem p))).symm
  have hdiff : ∀ f, f - ρ f ∈ Ideal.span S := by
    intro f
    have := DFunLike.congr_fun hq f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq.1 this.symm
  refine le_antisymm ?_ hle
  intro f hf
  have hf0 : aeval x f = 0 := hf
  have h1 : aeval x (ρ f) = 0 := by
    have := hle (hdiff f)
    have h2 : aeval x (f - ρ f) = 0 := this
    rw [map_sub, hf0, zero_sub, neg_eq_zero] at h2
    exact h2
  have hind : AlgebraicIndependent F (x ∘ a) :=
    algebraicIndependent_linearForms u hu (l ∘ a) hli
  have h2 : ρ' f = 0 := by
    apply hind
    rw [map_zero, ← h1]
    simp [ρ, aeval_rename]
  have h3 : ρ f = 0 := by simp [ρ, h2]
  simpa [h3] using hdiff f

theorem ker_linearForms_span : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K), (∀ a : K, a = k₀) → ∀ (C : Type) [Fintype C]
    (u : C → E) (l : (Σ k, ι k) → C → F), AlgebraicIndependent F u →
    ∃ S : Set (MRingOver F ι), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧
      RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MRingOver F ι →ₐ[F] E) =
        Ideal.span S := by
  intro F E _ _ _ K _ ι _ k₀ hk C _ u l hu
  refine ⟨_, ?_, ker_eq_span_homogeneous u hu l⟩
  rintro f ⟨hf, -⟩ m hm k
  have hd : ∑ p : (Σ k, ι k), m p = 1 := by
    have h : Finsupp.degree m = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hf (mem_support_iff.1 hm)
    rw [← h, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun p _ hp => by simpa using hp).symm
  rw [Fintype.sum_sigma] at hd
  have hk' : ∀ j : K, j = k := fun j => (hk j).trans (hk k).symm
  rw [Fintype.sum_eq_single k (fun j hj => absurd (hk' j) hj)] at hd
  exact hd

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer
