import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocCpl
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KTypesBoundedFinite

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem td_fin {B A D : Type} [CommRing B] [CommRing A] [CommRing D] [Algebra B A] [Algebra A D]
    [Algebra B D] [IsScalarTower B A D] [Algebra.IsIntegral A D] (p : Ideal D) [p.IsPrime] (η : Ideal A)
    (hη : p.comap (algebraMap A D) = η) :
    p.comap (algebraMap B D) = η.comap (algebraMap B A) ∧
    Algebra.trdeg (B ⧸ p.comap (algebraMap B D)) (D ⧸ p) = Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  subst hη
  rename_i iBD iT iI hp
  have hI : iBD = ((algebraMap A D).comp (algebraMap B A)).toAlgebra := by
    apply Algebra.algebra_ext
    intro r
    exact IsScalarTower.algebraMap_apply B A D r
  subst hI
  refine ⟨(Ideal.comap_comap _ _).symm, ?_⟩
  letI iBD' : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  letI : Algebra (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (D ⧸ p) :=
    (Ideal.quotientAlgebra : Algebra (B ⧸ Ideal.comap (algebraMap B D) p) (D ⧸ p))
  haveI : IsScalarTower (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  haveI : FaithfulSMul (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : FaithfulSMul (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : Algebra.IsAlgebraic (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    Algebra.IsIntegral.isAlgebraic
  have key := trdeg_add_eq (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
    (A ⧸ Ideal.comap (algebraMap A D) p) (A := D ⧸ p)
  have h0 : Algebra.trdeg (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at key
  exact key.symm

private theorem dim_gen (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {B A D R : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing A]
    [CommRing D] [Algebra B A] [Algebra A D] [Algebra.FiniteType B A] [Module.Finite A D] [Module.Flat A D]
    [CommRing R] [IsLocalRing R] [Algebra D R] (hB : UpperTheory.V.CA.IsCL O B) (x : Ideal A) (hx : x.IsMaximal)
    (hxB : x.comap (algebraMap B A) = maximalIdeal B) (y : Ideal D) (hy : y.comap (algebraMap A D) = x)
    (hR : UpperTheory.V.CA.IsCplAt y R) :
    (∀ P : Ideal R, P.IsPrime → ∀ η : Ideal A, (P.comap (algebraMap D R)).comap (algebraMap A D) = η → ∀ t : ℕ,
      Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) ≤ t →
        ringKrullDim (R ⧸ P) ≤ ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t) ∧
    ∀ η : Ideal A, η.IsPrime → η ≤ x → ∀ t : ℕ, Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) = t →
      ∃ P : Ideal R, P.IsPrime ∧ (P.comap (algebraMap D R)).comap (algebraMap A D) = η ∧
        ringKrullDim (R ⧸ P) = ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t := by
  haveI : IsNoetherianRing B := hB.noeth
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  haveI : IsNoetherianRing R := hR.noeth
  letI : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  haveI : IsScalarTower B A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType B D := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI := hx
  have hyc : Ideal.comap (algebraMap D R) (maximalIdeal R) = y := by
    simpa using hR.comap_pow 1
  haveI hyP : y.IsPrime := by
    rw [← hyc]
    infer_instance
  haveI hyM : y.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) y (by rw [hy]; exact hx)
  have hyB : Ideal.comap (algebraMap B D) y = maximalIdeal B := by
    rw [IsScalarTower.algebraMap_eq B A D, ← Ideal.comap_comap, hy, hxB]
  constructor
  · intro P hP η hη t ht
    haveI := hP
    haveI hpDP : (P.comap (algebraMap D R)).IsPrime := Ideal.comap_isPrime _ _
    have hpDy : P.comap (algebraMap D R) ≤ y := by
      rw [← hyc]
      exact Ideal.comap_mono (le_maximalIdeal hP.ne_top)
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB (P.comap (algebraMap D R)) hpDy
    have htd := td_fin (B := B) (P.comap (algebraMap D R)) η hη
    have h1 := (UpperTheory.V.CA.c3c y hR).2 (P.comap (algebraMap D R)) P le_rfl
    rw [ht'dim, htd.1] at h1
    rw [htd.2] at ht'tr
    have hc : (t' : Cardinal) ≤ t := ht'tr ▸ ht
    have htt : t' ≤ t := by exact_mod_cast hc
    have hcast : ((t' : ℕ∞) : WithBot ℕ∞) ≤ ((t : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast htt
    exact h1.trans (add_le_add le_rfl hcast)
  · intro η hη hηx t ht
    haveI := hη
    haveI : y.LiesOver x := ⟨hy.symm⟩
    obtain ⟨pD, hpDy, hpD, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := η) (q := x) y hηx
    have hηD : pD.comap (algebraMap A D) = η := (Ideal.over_def pD η).symm
    have hmap : Ideal.map (algebraMap D R) pD ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap, hyc]
      exact hpDy
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hmap
    obtain ⟨hqdim, hqc⟩ := UpperTheory.V.CA.c3d O y hB hyB hR pD hpDy q hq
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB pD hpDy
    have htd := td_fin (B := B) pD η hηD
    refine ⟨q, hq.1.1, by rw [hqc, hηD], ?_⟩
    rw [hqdim, ht'dim, htd.1]
    rw [htd.2, ht] at ht'tr
    have htt : t' = t := by exact_mod_cast ht'tr.symm
    rw [htt]

theorem UpperTheory.V.Fr.loc_dim :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∀ P : Ideal L.R, P.IsPrime → ∀ t : ℕ, S.td (L.im P) ≤ t → ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + t) ∧ ∀ η : Ideal S.A, η.IsPrime → η ≤ x → ∀ t : ℕ, S.td η = t → ∃ P : Ideal L.R, P.IsPrime ∧ L.im P = η ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ S.π η) + t := by
  intro l _ O _ _ _ _ F C₀ n hOk hn S x L
  obtain ⟨hco, hmB⟩ := co_B hOk hn S
  haveI := hco
  haveI : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  have hB : UpperTheory.V.CA.IsCL O S.B := UpperTheory.V.CA.IsCL.of_isCO O S.B
  obtain ⟨-, -, -, -, hFT, -, -⟩ := gr_A hOk hn S
  haveI := hFT
  obtain ⟨-, hxM, hmx⟩ := loc_flat hOk hn S x L
  have hxB : x.comap (algebraMap S.B S.A) = maximalIdeal S.B := by
    refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ hxM.ne_top)) ?_
    rw [hmB]
    exact hmx
  have hinj : Function.Injective (algebraMap O L.O') := by
    by_cases hK : RingHom.ker (algebraMap O L.O') = ⊥
    · exact (RingHom.injective_iff_ker_eq_bot _).mpr hK
    · exfalso
      have hKm : (RingHom.ker (algebraMap O L.O')).IsMaximal :=
        Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hK
      have hKeq := IsLocalRing.eq_maximalIdeal hKm
      have hmap : Ideal.map (algebraMap O L.O') (maximalIdeal O) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr hKeq.ge
      rw [L.unr] at hmap
      exact IsDiscreteValuationRing.not_a_field L.O' hmap
  have htor : Submodule.torsion O L.O' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨r, hr⟩, hrz⟩ := (Submodule.mem_torsion_iff z).mp hz
    rw [Submodule.mem_bot]
    have hr0 : algebraMap O L.O' r ≠ 0 := by
      intro h
      apply nonZeroDivisors.ne_zero hr
      exact hinj (by rw [h, map_zero])
    change r • z = 0 at hrz
    rw [Algebra.smul_def] at hrz
    exact (mul_eq_zero.mp hrz).resolve_left hr0
  haveI : Module.Flat O L.O' := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htor
  letI : Algebra S.A (TensorProduct O L.O' S.A) := Algebra.TensorProduct.rightAlgebra
  let e : (TensorProduct O S.A L.O') ≃ₐ[S.A] (TensorProduct O L.O' S.A) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv) (fun a => by
      simp [Algebra.TensorProduct.algebraMap_apply]
      rfl)
  haveI : Module.Finite S.A (TensorProduct O L.O' S.A) := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Flat S.A (TensorProduct O L.O' S.A) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
    Algebra.TensorProduct.lift (Algebra.ofId L.O' L.R) L.ι (fun _ _ => Commute.all _ _)
  have hι' : ∀ a : S.A, ι' (TensorProduct.tmul O (1 : L.O') a) = L.ι a := by
    intro a
    simp [ι']
  have hR := loc_cpl hOk hn S x L ι' hι'
  letI : Algebra (TensorProduct O L.O' S.A) L.R := ι'.toRingHom.toAlgebra
  have hcm : ∀ Q : Ideal L.R, (Q.comap (algebraMap (TensorProduct O L.O' S.A) L.R)).comap
      (algebraMap S.A (TensorProduct O L.O' S.A)) = L.im Q := by
    intro Q
    ext a
    change ι' (TensorProduct.tmul O (1 : L.O') a) ∈ Q ↔ L.ι a ∈ Q
    rw [hι']
  have hy : (Ideal.comap ι'.toRingHom (maximalIdeal L.R)).comap (algebraMap S.A (TensorProduct O L.O' S.A)) = x := by
    exact (hcm (maximalIdeal L.R)).trans L.lies
  have key := dim_gen O hB x hxM hxB _ hy hR
  constructor
  · intro P hP t ht
    exact key.1 P hP (L.im P) (hcm P) t ht
  · intro η hη hηx t ht
    obtain ⟨P, hP, hPη, hdim⟩ := key.2 η hη hηx t ht
    refine ⟨P, hP, ?_, hdim⟩
    rw [← hcm P]
    exact hPη
