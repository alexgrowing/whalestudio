import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes

open IsLocalRing

private theorem height_map_mk_comap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (I : Ideal S) (hI : I = RingHom.ker φ) (J : Ideal T) :
    ((J.comap φ).map (Ideal.Quotient.mk I)).height = J.height := by
  subst hI
  have h : (J.comap φ).map (Ideal.Quotient.mk (RingHom.ker φ)) =
      J.comap (RingHom.quotientKerEquivOfSurjective hφ) := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (RingHom.ker φ)) Ideal.Quotient.mk_surjective
      (J.comap (RingHom.quotientKerEquivOfSurjective hφ))]
    congr 1
  rw [h, RingEquiv.height_comap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem height_ker_add {B C : Type} [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Algebra B C]
    [FaithfulSMul B C] (t N : ℕ) (ht : Algebra.trdeg B C = t) (g : MvPolynomial (Fin N) B →ₐ[B] C)
    (hg : Function.Surjective g) :
    ((RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).height : WithBot ℕ∞) + t = N := by
  let K := FractionRing B
  let L := FractionRing C
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B C L]
    exact (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective B C)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  letI : Algebra K L := FractionRing.liftAlgebra B L
  have : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  let g' : MvPolynomial (Fin N) K →ₐ[K] L :=
    MvPolynomial.aeval fun i => algebraMap C L (g (MvPolynomial.X i))
  have hgg : ∀ x, g' (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K) x) = algebraMap C L (g x) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, MvPolynomial.algHom_C, MvPolynomial.algHom_C,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul_X a i ha =>
      simp only [map_mul, ha]
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      simp [g']
  have hL : IsLocalization ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) K) :=
    MvPolynomial.isLocalization _ _
  have hp : (RingHom.ker g').IsPrime := RingHom.ker_isPrime g'
  have hc : (RingHom.ker g').comap (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K)) =
      RingHom.ker (g : MvPolynomial (Fin N) B →+* C) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hgg]
    exact map_eq_zero_iff _ (IsFractionRing.injective C L)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker g')
  have h2 : ringKrullDim (MvPolynomial (Fin N) K ⧸ RingHom.ker g') = ringKrullDim g'.range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange g').toRingEquiv
  have hft : Algebra.FiniteType K g'.range :=
    Algebra.FiniteType.of_surjective g'.rangeRestrict g'.rangeRestrict_surjective
  have h3 : Algebra.trdeg K g'.range = t := by
    have hmem : ∀ c : C, algebraMap C L c ∈ g'.range := fun c => by
      obtain ⟨x, rfl⟩ := hg c
      exact ⟨_, hgg x⟩
    let j : C →ₐ[B] g'.range.restrictScalars B :=
      (IsScalarTower.toAlgHom B C L).codRestrict (g'.range.restrictScalars B) hmem
    have hj : Function.Injective j := fun a b hab =>
      IsFractionRing.injective C L (congrArg Subtype.val hab)
    have a1 : Algebra.trdeg B C ≤ Algebra.trdeg B g'.range := trdeg_le_of_injective j hj
    have a2 : Algebra.trdeg B g'.range ≤ Algebra.trdeg B L :=
      trdeg_le_of_injective (g'.range.val.restrictScalars B) Subtype.val_injective
    have : Algebra.IsAlgebraic C L := IsLocalization.isAlgebraic L (nonZeroDivisors C)
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
    have a3 : Algebra.trdeg B L = Algebra.trdeg B C := by
      rw [← trdeg_add_eq B C (A := L), trdeg_eq_zero (R := C) (A := L), add_zero]
    have a4 : Algebra.trdeg B g'.range = Algebra.trdeg K g'.range := by
      have : FaithfulSMul K g'.range :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K g'.range).injective
      rw [← trdeg_add_eq B K (A := g'.range), trdeg_eq_zero (R := B) (A := K), zero_add]
    rw [← a4, ← ht]
    exact le_antisymm (a2.trans a3.le) a1
  rw [h2, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t h3,
    ← IsLocalization.height_comap ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (RingHom.ker g'), Ideal.under_def, hc] at h1
  exact h1

theorem UpperTheory.V.CA.g_dimform :
    ∀ (B C : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing C] [IsDomain C] [Algebra B C] [FaithfulSMul B C]
      [Algebra.FiniteType B C] (t : ℕ), ReciprocityTheory.CA.IsCMQuot B → Algebra.trdeg B C = t →
        ∀ (𝔪 : Ideal C) [𝔪.IsMaximal], 𝔪.comap (algebraMap B C) = maximalIdeal B →
          (𝔪.height : WithBot ℕ∞) = ringKrullDim B + t := by
  intro B C _ _ _ _ _ _ _ hft t hB ht 𝔪 _ h𝔪
  obtain ⟨P, _, _, f, hP, hf⟩ := hB
  have := hP.1
  obtain ⟨N, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let F : MvPolynomial (Fin N) P →+* MvPolynomial (Fin N) B := MvPolynomial.map f
  have hF : Function.Surjective F := MvPolynomial.map_surjective f hf
  let G : MvPolynomial (Fin N) P →+* C := (g : MvPolynomial (Fin N) B →+* C).comp F
  have hG : Function.Surjective G := hg.comp hF
  have hGC : ∀ a : P, G (MvPolynomial.C a) = algebraMap B C (f a) := fun a => by
    simp [G, F]
  have : (𝔪.comap G).IsMaximal := Ideal.comap_isMaximal_of_surjective G hG
  have hc : (𝔪.comap G).comap MvPolynomial.C = maximalIdeal P := by
    have : (𝔪.comap G).comap MvPolynomial.C = (maximalIdeal B).comap f := by
      ext a
      rw [← h𝔪]
      simp only [Ideal.mem_comap, hGC]
    rw [this]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)
  obtain ⟨hCM, e1⟩ := ReciprocityTheory.CA.isCM_localization_mvPolynomial hP N (𝔪.comap G) hc
  have : (RingHom.ker G).IsPrime := RingHom.ker_isPrime G
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have e2 := ReciprocityTheory.CA.height_eq_add_of_isCM_localization (𝔪.comap G) (RingHom.ker G) hCM
    (Ideal.ker_le_comap G)
  rw [height_map_mk_comap G hG _ rfl] at e2
  have : (RingHom.ker G).LiesOver (RingHom.ker f) := ⟨by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, MvPolynomial.algebraMap_eq, hGC]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B C)).symm⟩
  have e3 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (RingHom.ker f) (RingHom.ker G)
  have hk : RingHom.ker G = (RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).comap F := rfl
  have e4 := height_map_mk_comap F hF ((RingHom.ker f).map (algebraMap P (MvPolynomial (Fin N) P)))
    (by rw [MvPolynomial.algebraMap_eq]; exact (MvPolynomial.ker_map f).symm)
    (RingHom.ker (g : MvPolynomial (Fin N) B →+* C))
  rw [← hk] at e4
  rw [e4] at e3
  have e5 := height_ker_add t N ht g hg
  have e6 := hP.height_add_ringKrullDim_quotient (RingHom.ker f)
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)] at e6
  have f1 : (RingHom.ker G).height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have key : (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + 𝔪.height =
      (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + (ringKrullDim B + t) := by
    rw [← WithBot.coe_add, ← e2, e1, ← e6, ← e5, e3, WithBot.coe_add]
    abel
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp f1
  rw [← hn] at key
  exact (ENat.WithBot.natCast_add_cancel).mp key
