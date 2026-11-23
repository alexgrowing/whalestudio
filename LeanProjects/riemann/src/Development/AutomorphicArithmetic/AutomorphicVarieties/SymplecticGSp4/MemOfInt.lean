import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FlagL
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.IneSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.ResidualIrreducibilityUnramified

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))
  exact hz ▸ z.2

private theorem det_lt {Ω ι : Type} [Field Ω] [Fintype ι] [DecidableEq ι] (A : ValuationSubring Ω) (M : Matrix ι ι Ω)
    (hM : ∀ i j, M i j ∈ A) {a b : ι} (hab : a ≠ b) (h : ∀ i, A.valuation (M i a - M i b) < 1) :
    A.valuation M.det < 1 := by
  let M' : Matrix ι ι A := fun i j => ⟨M i j, hM i j⟩
  have e : M = A.subtype.mapMatrix M' := rfl
  have h0 : ((IsLocalRing.residue A).mapMatrix M').det = 0 := by
    refine Matrix.det_zero_of_column_eq hab fun i => ?_
    change IsLocalRing.residue A (M' i a) = IsLocalRing.residue A (M' i b)
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    exact h i
  rw [← RingHom.map_det, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h0
  rw [e, ← RingHom.map_det]
  exact h0

private theorem ine_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} (hl : l.Prime) (hd : ¬ l ∣ (discr K).natAbs) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  intro σ hσ
  let φ : K →ₐ[ℚ] Ω := (algebraMap K Ω).toRatAlgHom
  let φ' : K →ₐ[ℚ] Ω := (σ : Ω →ₐ[ℚ] Ω).comp φ
  by_contra hne
  have hφ : φ' ≠ φ := fun h => hne fun x => DFunLike.congr_fun h x
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →ₐ[ℚ] Ω) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis K)])
  have hint : ∀ (f : K →ₐ[ℚ] Ω) i, f (integralBasis K i) ∈ A := fun f i => by
    rw [integralBasis_apply]
    exact mem_of_int A ((RingOfIntegers.isIntegral_coe _).map f.toRingHom.toIntAlgHom)
  have hM : ∀ i j, Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis K) e i j = e j (integralBasis K i) :=
    fun i j => rfl
  have h1 := det_lt A (Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis K) e) (fun i j => hint _ _)
    (e.symm.injective.ne hφ) fun i => by
      rw [hM, hM, e.apply_symm_apply, e.apply_symm_apply]
      exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hint φ i))
  have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis K) e
  rw [← coe_discr, map_intCast] at h2
  have h3 : A.valuation ((discr K : ℤ) : Ω) < 1 := by
    rw [h2, map_pow]
    exact pow_lt_one₀ zero_le' h1 two_ne_zero
  have hc : IsCoprime (l : ℤ) (discr K) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hd
  obtain ⟨u, v, huv⟩ := hc
  have h4 : (1 : Ω) = (u : Ω) * l + (v : Ω) * (discr K : ℤ) := by exact_mod_cast huv.symm
  have h5 : A.valuation (1 : Ω) < 1 := by
    rw [h4]
    refine A.valuation.map_add_lt ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) hA
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) h3
  simp at h5

private theorem one_prime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ} (h : p.Coprime l)
    (hv' : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := fun hv => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have h1 : (a : Ω) * p + (b : Ω) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h2 : ∀ (z : ℤ) (y : Ω), A.valuation y < 1 → A.valuation (z * y) < 1 := fun z y hy => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem _ z))) hy
  have h3 := A.valuation.map_add_lt (h2 a _ hv') (h2 b _ hv)
  rw [h1, map_one] at h3
  exact lt_irrefl _ h3

private theorem det_tri {k : Type} [Field k] {n : ℕ} (u X : GL (Fin n) k) (d : Fin n → k)
    (h : (∀ i j, j < i → (u * X * u⁻¹ : GL (Fin n) k) i j = 0) ∧ ∀ i, (u * X * u⁻¹ : GL (Fin n) k) i i = d i) (a : k) :
    (a • (X : Matrix (Fin n) (Fin n) k) - 1).det = ∏ i, (a * d i - 1) := by
  rw [← Matrix.det_units_conj u]
  have e : (u : Matrix (Fin n) (Fin n) k) * (a • (X : Matrix (Fin n) (Fin n) k) - 1) * (u⁻¹ : GL (Fin n) k) =
      a • ((u * X * u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1 := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, Units.val_mul, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.det_of_upperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.sub_apply, Matrix.smul_apply, h.2 i, Matrix.one_apply_eq, smul_eq_mul]
  · intro i j hij
    have hij' : j < i := hij
    rw [Matrix.sub_apply, Matrix.smul_apply, h.1 i j hij', Matrix.one_apply_ne hij'.ne', smul_zero, sub_zero]

private theorem det_tw {k : Type} [Field k] {n : ℕ} (M : GL (Fin n) k) (X : Matrix (Fin n) (Fin n) k) (a : k)
    (h : (M : Matrix (Fin n) (Fin n) k) * (a • X) = X * M) : (a • X - 1).det = ((1 : k) • X - 1).det := by
  have e : (M : Matrix (Fin n) (Fin n) k) * (a • X - 1) = ((1 : k) • X - 1) * M := by
    rw [mul_sub, sub_mul, h, one_smul, mul_one, one_mul]
  have h1 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h1
  exact mul_right_cancel₀ ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero h1

private theorem tw_iff {k : Type} [Field k] {n : ℕ} [NeZero n] (M X : GL (Fin n) k) (a : kˣ)
    (h1 : (M : Matrix (Fin n) (Fin n) k) * ((a : k) • (X : Matrix (Fin n) (Fin n) k)) = X * M) :
    a = 1 ↔ (M : Matrix (Fin n) (Fin n) k) * X = X * M := by
  refine ⟨fun h => by simpa [h] using h1, fun h => ?_⟩
  rw [← h, Matrix.mul_smul] at h1
  have hu : IsUnit ((M : Matrix (Fin n) (Fin n) k) * X) := (M * X).isUnit
  exact Units.ext (smul_left_injective k hu.ne_zero (h1.trans (one_smul _ _).symm))

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem unr_l (D : Raw Ω c) (hD : D.Good) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (φ : G ℚ Ω →* (PadicAlgCl l)ˣ) (h4 : φ ^ 4 = 1) (M : GL (Fin 4) (PadicAlgCl l))
    (hM : ∀ g, (M : M4 (PadicAlgCl l)) * ((φ g : PadicAlgCl l) • r g) = r g * M) : D.Ip l ≤ φ.ker := by
  obtain ⟨-, -, -, f4, -⟩ := facts D hD
  obtain ⟨κ, ⟨u, hu⟩, k2, -⟩ := flagL D hD r hr
  have h3 : ∀ s, D.ps 3 s = 1 := fun _ => rfl
  have key : ∀ s ∈ D.Ip l, ∃ i, (φ s : PadicAlgCl l) * ((D.ps i s : c.O) : PadicAlgCl l) = 1 := by
    intro s hs
    have t := det_tri u _ _ (hu ⟨s, Ine_le_Dec _ hs⟩)
    have h1 := det_tw M (r s) _ (hM s)
    have t1 := (t (φ s)).symm.trans (h1.trans (t 1))
    rw [Finset.prod_eq_zero (Finset.mem_univ 3) (f := fun i => 1 * (κ i ⟨s, Ine_le_Dec _ hs⟩ : PadicAlgCl l) - 1)
      (by rw [k2 3 _ hs, h3]; simp)] at t1
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 t1
    rw [k2 i _ hs] at hi
    exact ⟨i, sub_eq_zero.1 hi⟩
  intro s hs
  have hs0 : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  choose f hf using fun n : ℕ => key (s * ((D.s0 : G ℚ Ω) ^ n) ^ 4) (mul_mem hs (pow_mem (pow_mem hs0 _) _))
  have hφ : ∀ n : ℕ, φ (s * ((D.s0 : G ℚ Ω) ^ n) ^ 4) = φ s := fun n => by
    have := DFunLike.congr_fun h4 ((D.s0 : G ℚ Ω) ^ n)
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    rw [map_mul, map_pow, this, mul_one]
  obtain ⟨n, n', hne, hnn⟩ := Finite.exists_ne_map_eq_of_infinite f
  have a1 := hf n
  have a2 := hf n'
  rw [hφ] at a1 a2
  rw [← hnn] at a2
  by_cases hw : D.wts4 (f n) = 0
  · have : f n = 3 := by
      have := hD.two_le
      generalize f n = i at hw
      fin_cases i <;> simp [Raw.wts4] at hw ⊢
      omega
    rw [this, h3] at a1
    exact Units.ext (by simpa using a1)
  · exfalso
    have a3 := mul_left_cancel₀ (φ s).ne_zero (a1.trans a2.symm)
    have a4 := Units.ext (Subtype.val_injective a3)
    rw [map_mul, map_mul, mul_right_inj, ← pow_mul, ← pow_mul, map_pow, map_pow, f4 _ _ hD.decompSigma_mem, ← pow_mul, ← pow_mul] at a4
    have hinj : Function.Injective (algebraMap ℤ_[l] c.O) := by
      refine Function.Injective.of_comp (f := algebraMap c.O (PadicAlgCl l)) ?_
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l]]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp Subtype.val_injective
    have a5 : cycZ ℚ Ω l D.s0 ^ (D.wts4 (f n) * (n * 4)) = cycZ ℚ Ω l D.s0 ^ (D.wts4 (f n) * (n' * 4)) := by
      apply Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hinj
      rw [map_pow, map_pow]
      exact a4
    have a6 := injective_pow_iff_not_isOfFinOrder.2 hD.decompSigma_ord a5
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hw) a6
    omega

private theorem matIrr (D : Raw Ω c) (hD : D.Good) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r) (hi : Irr r)
    (U : Subgroup (G ℚ Ω)) (h2 : U.index = 2) (hU : ∀ p ∈ D.S, D.Ip p ≤ U) :
    U3.MatIrr (U ⊓ (cycZ ℚ Ω l).ker) fun g => r g := by
  by_contra hred
  haveI : IsGalois ℚ Ω := {}
  haveI : U.Normal := Subgroup.normal_of_index_eq_two h2
  have hirr := ((irrIff (PadicAlgCl l)).1 r).1 hi
  obtain ⟨φ, hφ1, hH, h4, M, hM⟩ := U3.exists_selfTwist r.toHomUnits (U ⊓ (cycZ ℚ Ω l).ker)
    (fun a b => ⟨by
      show a * b * a⁻¹ * b⁻¹ ∈ U
      simp only [Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff]
      tauto, by simp [MonoidHom.mem_ker, mul_right_comm]⟩)
    (fun W hW => hirr.2.2 W le_top fun g => hW g trivial) hred
  have hM' : ∀ g, (M : M4 (PadicAlgCl l)) * ((φ g : PadicAlgCl l) • r g) = r g * M := fun g => hM g trivial
  have hiff : ∀ g, φ g = 1 ↔ (M : M4 (PadicAlgCl l)) * r g = r g * M := fun g =>
    tw_iff M (r.toHomUnits g) (φ g) (hM' g)
  obtain ⟨hc, -⟩ := eptInt D hD r hr
  obtain ⟨-, p2, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, f14⟩ := facts D hD
  have hcl : IsClosed (φ.ker : Set (G ℚ Ω)) := by
    have : (φ.ker : Set (G ℚ Ω)) = {g | (M : M4 (PadicAlgCl l)) * r g = r g * M} := Set.ext hiff
    rw [this]
    exact isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)
  haveI : φ.ker.FiniteIndex := by
    haveI : Finite φ.range := Finite.of_injective
      (fun x => (⟨x.1, by
        obtain ⟨_, g, rfl⟩ := x
        exact DFunLike.congr_fun h4 g⟩ : rootsOfUnity 4 (PadicAlgCl l)))
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
    exact Subgroup.finiteIndex_ker φ
  have hTS : D.T ⊆ D.S := Finset.insert_subset hD.l_mem (Finset.filter_subset _ _)
  have key := B1.ineSpan Ω φ.ker D.S D.pl (Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl)
    (Abelianization.commutator_subset_ker _) (fun p hp => ⟨hD.S_prime p hp, hD.pl_over p (hD.S_prime p hp)⟩)
    (fun A hA g hg => by
      have h0 : D.r0 g = 1 := by
        have : ∀ i, D.ps i g = 1 := fun i => f14 i A hA hg
        show Matrix.diagonal (fun i => (D.ps i g : c.O)) = 1
        simp [this]
      have h1 : D.rbar g = 1 := by
        show (residue c.O).mapMatrix (D.r0 g) = 1
        rw [h0, map_one]
      have h3 : r g = 1 := p2 A (fun p hp => hA p (hTS hp)) g hg h1
      exact (hiff g).2 (by rw [h3, mul_one, one_mul]))
  have hle : (⨆ p ∈ D.S, Ine (F := ℚ) (D.pl p)) ≤ φ.ker := by
    refine iSup₂_le fun p hp => ?_
    by_cases hl : p = l
    · rw [hl]
      exact unr_l D hD r hr φ h4 M hM'
    · refine le_trans (le_inf (hU p hp) ((places ℚ Ω l _).2.2.2 ?_)) hH
      exact one_prime _ ((Nat.coprime_primes (hD.S_prime p hp) Fact.out).2 hl) (hD.pl_over p (hD.S_prime p hp))
  rw [sup_eq_left.2 hle] at key
  exact hφ1 (MonoidHom.ker_eq_top_iff.1 key)

end UpperTheory.V.GradeZeroInterpolatingElement.ResidualIrreducibilityUnramified

open UpperTheory.V.GradeZeroInterpolatingElement.ResidualIrreducibilityUnramified in
theorem UpperTheory.V.GradeZeroInterpolatingElement.irrK :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → Irr r → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (_ : IsAlgClosure K Ω), Module.finrank ℚ K = 2 ∧ Af.IsIrr ((r.toHomUnits.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).comp (GlobalTheory.GalOfCusp.cycBar K Ω l).ker.subtype) := by
  intro Ω _ _ _ l _ c D hD r hr hi
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, hqS, hq, hq4⟩ := Nat.forall_exists_prime_gt_and_modEq (D.S.sup id) (q := 4) (a := 3) (by norm_num) (by norm_num)
  obtain ⟨hd, htc, h2, -⟩ := HV.kstar q hq hq4
  letI : Algebra (Kstar q) Ω := (IsAlgClosed.lift (R := ℚ) (S := Kstar q) (M := Ω)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (Kstar q) Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosure (Kstar q) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ (Kstar q) := ⟨h2⟩
  refine ⟨Kstar q, inferInstance, inferInstance, IsCMField.ofCMExtension ℚ _, inferInstance, inferInstance, inferInstance,
    h2, ?_⟩
  have key := matIrr D hD r hr hi (galOf ℚ (Kstar q) Ω) ((galEmbTop ℚ _ Ω).2.2.trans h2) fun p hp => by
    have hp' := hD.S_prime p hp
    refine ine_le Ω _ hp' (fun h => ?_) _ (hD.pl_over p hp')
    rw [hd, Int.natAbs_neg, Int.natAbs_natCast, Nat.prime_dvd_prime_iff_eq hp' hq] at h
    have : p ≤ D.S.sup id := Finset.le_sup (f := id) hp
    omega
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => key W ?_⟩
  rintro g ⟨hg1, hg2⟩
  rw [← range_galEmb] at hg1
  obtain ⟨σ, rfl⟩ := hg1
  refine hW ⟨σ, ?_⟩
  have h1 : cycZ (Kstar q) Ω l σ = 1 := hg2
  rw [MonoidHom.mem_ker, GlobalTheory.GalOfCusp.cycBar, MonoidHom.comp_apply, h1, map_one]
