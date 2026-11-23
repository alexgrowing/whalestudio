import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.SemilocalBasis

def awayFrom {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    Submonoid R where
  carrier := {s | s ≠ 0 ∧ ∀ P ∈ SB, s ∉ P.asIdeal}
  one_mem' := ⟨one_ne_zero, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, fun P hP h =>
    (P.isPrime.mem_or_mem h).elim (ha.2 P hP) (hb.2 P hP)⟩

theorem awayFrom_le {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    awayFrom SB ≤ nonZeroDivisors R := fun _ h => mem_nonZeroDivisors_of_ne_zero h.1

theorem isPrincipalIdealRing_awayFrom {R : Type} [CommRing R] [IsDedekindDomain R]
    (SB : Finset (HeightOneSpectrum R)) (A : Type) [CommRing A] [IsDomain A] [Algebra R A]
    [IsLocalization (awayFrom SB) A] : IsPrincipalIdealRing A := by
  classical
  haveI : IsDedekindDomain A := IsLocalization.isDedekindDomain R (awayFrom_le SB) A
  apply IsPrincipalIdealRing.of_finite_primes
  let T : Finset (Ideal R) := insert ⊥ (SB.image (·.asIdeal))
  have hT : ∀ Q ∈ T, Q.IsPrime := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact Ideal.isPrime_bot
    · obtain ⟨P, _, rfl⟩ := Finset.mem_image.1 hQ
      exact P.isPrime
  have hinj : Function.Injective (fun I : Ideal A => I.comap (algebraMap R A)) := by
    intro I J h
    rw [← IsLocalization.map_comap (awayFrom SB) A I, ← IsLocalization.map_comap (awayFrom SB) A J]
    exact congrArg _ h
  refine ((T.finite_toSet).preimage hinj.injOn).subset ?_
  intro I hI
  have hI' : I.IsPrime := hI
  have hsub : ((I.comap (algebraMap R A) : Ideal R) : Set R) ⊆ ⋃ i ∈ (T : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro s hs
    by_contra hn
    simp only [Set.mem_iUnion, not_exists, id] at hn
    have hS : s ∈ awayFrom SB := by
      refine ⟨fun h0 => hn ⊥ (by simp [T]) (by simp [h0]), fun P hP h => hn P.asIdeal ?_ h⟩
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))
    exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (IsLocalization.map_units A ⟨s, hS⟩))
  obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ (fun i hi _ _ => hT i hi)).1 hsub
  show I.comap (algebraMap R A) ∈ (T : Set (Ideal R))
  by_cases h0 : I.comap (algebraMap R A) = ⊥
  · rw [h0]; simp [T]
  · have hmax : (I.comap (algebraMap R A)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime h0 (Ideal.comap_isPrime _ _)
    rw [hmax.eq_of_le (hT Q hQ).ne_top hle]
    exact hQ

theorem exists_basis {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (SB : Finset (HeightOneSpectrum R))
    (N : Submodule R (Fin n → K)) (hN : Submodule.IsLattice K N) :
    ∃ v : Module.Basis (Fin n) K (Fin n → K), (∀ i, v i ∈ N) ∧
      ∀ x ∈ N, ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R (Set.range v) := by
  classical
  let A : Subalgebra R K := Localization.subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsLocalization (awayFrom SB) A :=
    Localization.subalgebra.isLocalization_subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsPrincipalIdealRing A := isPrincipalIdealRing_awayFrom SB A
  haveI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (awayFrom SB) A K

  have clear : ∀ (X : Set (Fin n → K)) (x : Fin n → K), x ∈ Submodule.span A X →
      ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R X := by
    intro X x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, mul_mem hs ht, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hty
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hr⟩ := IsLocalization.surj (awayFrom SB) a
      refine ⟨s * t, mul_mem hs t.2, ?_⟩
      have : (t : R) • a • x = r • x := by
        rw [← algebraMap_smul A (t : R), ← mul_smul, mul_comm, hr, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hsx
  let M : Submodule A (Fin n → K) := Submodule.span A (N : Set (Fin n → K))
  haveI hM : Submodule.IsLattice K M := by
    refine ⟨?_, ?_⟩
    · obtain ⟨X, hX⟩ := hN.fg
      refine ⟨X, ?_⟩
      simp only [M, ← hX]
      exact (Submodule.span_span_of_tower R A _).symm
    · simp only [M]
      rw [Submodule.span_span_of_tower]
      exact hN.span_eq_top
  haveI : Module.Free A M := Submodule.IsLattice.free K M
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  have hrk : Module.finrank A M = n := by
    simpa using Submodule.IsLattice.finrank_of_pi K M
  let b : Module.Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hb : ∀ i, ∃ s ∈ awayFrom SB, s • (b i : Fin n → K) ∈ N := by
    intro i
    obtain ⟨s, hs, h⟩ := clear _ _ (b i).2
    exact ⟨s, hs, by simpa using h⟩
  choose s hs hsb using hb
  let b' : Module.Basis (Fin n) A M :=
    b.isUnitSMul (w := fun i => algebraMap R A (s i)) (fun i => IsLocalization.map_units A ⟨s i, hs i⟩)
  have hb' : ∀ i, (b' i : Fin n → K) = s i • (b i : Fin n → K) := by
    intro i
    simp only [b', Module.Basis.isUnitSMul_apply, Submodule.coe_smul, algebraMap_smul]
    try rfl
  refine ⟨b'.extendOfIsLattice K, fun i => ?_, fun x hx => ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply, hb']
    exact hsb i
  · apply clear
    have hxM : x ∈ M := Submodule.subset_span hx
    have h1 := b'.sum_repr ⟨x, hxM⟩
    have h2 : x = ∑ i, b'.repr ⟨x, hxM⟩ i • (b' i : Fin n → K) := by
      have := congrArg Subtype.val h1
      rw [AddSubmonoidClass.coe_finset_sum] at this
      exact this.symm
    rw [h2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    rw [Module.Basis.extendOfIsLattice_apply]

theorem mem_localization_iff {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem stdLat_eq_span (E : Type) [Field E] (n : ℕ) :
    Formalism.L2.Col.stdLat E n = Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
      Submodule.mem_one.1 (hx i (Set.mem_univ _))
    choose r hr using hx'
    have : x = ∑ i, r i • Pi.basisFun E (Fin n) i := by
      conv_lhs => rw [← (Pi.basisFun E (Fin n)).sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.basisFun_repr, ← hr, algebraMap_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ j _
    rw [Pi.basisFun_apply]
    by_cases h : j = i
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

theorem exists_equiv (E : Type) [Field E] [NumberField E] (n : ℕ)
    (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ γ : Sp E n ≃ₗ[E] Sp E n, (∀ x ∈ Formalism.L2.Col.stdLat E n, γ x ∈ N) ∧
      ∀ P ∈ SB, ∀ x, γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔
        x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E n) := by
  obtain ⟨v, hv, hgen⟩ := exists_basis E n SB N hN
  let γ : Sp E n ≃ₗ[E] Sp E n := (Pi.basisFun E (Fin n)).equiv v (Equiv.refl _)
  have key : ∀ x, x ∈ Formalism.L2.Col.stdLat E n ↔ γ x ∈ Submodule.span (𝓞 E) (Set.range v) := by
    intro x
    have hmap : (Formalism.L2.Col.stdLat E n).map ((γ.restrictScalars (𝓞 E)) : Sp E n →ₗ[𝓞 E] Sp E n)
        = Submodule.span (𝓞 E) (Set.range v) := by
      rw [stdLat_eq_span, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact (Pi.basisFun E (Fin n)).equiv_apply i v (Equiv.refl _)
    rw [← hmap]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, h⟩
      have : y = x := γ.injective h
      exact this ▸ hy
  have hle : Submodule.span (𝓞 E) (Set.range v) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hsm : ∀ (s : 𝓞 E) x, γ (s • x) = s • γ x := fun s x =>
    (γ.restrictScalars (𝓞 E)).map_smul s x
  refine ⟨γ, fun x hx => hle ((key x).1 hx), fun P hP x => ?_⟩
  rw [mem_localization_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht, h'⟩ := hgen _ h
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim (ht.2 P hP) hs, ?_⟩
    rw [key, hsm, mul_smul]
    exact h'
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hle ?_⟩
    rw [← hsm]
    exact (key _).1 h

end GlobalTheory.SemilocalBasis
