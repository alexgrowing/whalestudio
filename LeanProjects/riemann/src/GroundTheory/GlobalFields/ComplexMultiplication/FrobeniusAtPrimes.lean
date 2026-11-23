import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesIsogeny
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal
import GroundTheory.GlobalFields.ComplexMultiplication.BadPrimesFinite
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Residue

variable {L : Type*} [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L))

instance finite_residueField_localizationAt : Finite (ResidueField (localizationAt L 𝔓)) :=
  Finite.of_equiv _
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔓.asIdeal (localizationAt L 𝔓)).toEquiv

theorem algebraMap_mem_maximalIdeal_localizationAt_iff (a : 𝓞 L) :
    algebraMap (𝓞 L) (localizationAt L 𝔓) a ∈ maximalIdeal (localizationAt L 𝔓) ↔ a ∈ 𝔓.asIdeal :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a

theorem charP_residueField_localizationAt {p : ℕ} (hp : p.Prime) (hmem : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    CharP (ResidueField (localizationAt L 𝔓)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 p).2 hmem
  rw [map_natCast] at h
  rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
  exact h

variable {K : Type*} [Field K] [Algebra K L]

theorem residue_smul_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    (a : 𝓞 L) :
    IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ (σ • a)) =
      IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ a) ^
        Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff, ← map_pow, ← map_sub,
    algebraMap_mem_maximalIdeal_localizationAt_iff]
  exact hσ a

omit [NumberField L] in

theorem smul_notMem_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {s : 𝓞 L} (hs : s ∉ 𝔓.asIdeal) : σ • s ∉ 𝔓.asIdeal := by
  intro h
  apply hs
  have h' : s ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) ∈ 𝔓.asIdeal := by
    have := 𝔓.asIdeal.sub_mem h (hσ s)
    simpa using this
  exact 𝔓.isPrime.mem_of_pow_mem _ h'

theorem residue_apply_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {x : L} (hx : x ∈ localizationAt L 𝔓) :
    ∃ h : σ x ∈ localizationAt L 𝔓, IsLocalRing.residue (localizationAt L 𝔓) ⟨σ x, h⟩ =
      IsLocalRing.residue (localizationAt L 𝔓) ⟨x, hx⟩ ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  set q := Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K))
  obtain ⟨a, s, hs, hxs⟩ := mem_localizationAt_iff.1 hx
  have hs0 : (algebraMap (𝓞 L) L s) ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσs := smul_notMem_of_isArithFrobAt 𝔓 hσ hs
  have hσs0 : (algebraMap (𝓞 L) L (σ • s)) ≠ 0 := by
    intro h0
    apply hσs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσx : σ x = algebraMap (𝓞 L) L (σ • a) * (algebraMap (𝓞 L) L (σ • s))⁻¹ := by
    rw [hxs, map_mul, map_inv₀]
    rfl
  have hmem : σ x ∈ localizationAt L 𝔓 := mem_localizationAt_iff.2 ⟨σ • a, σ • s, hσs, hσx⟩
  refine ⟨hmem, ?_⟩
  set R := localizationAt L 𝔓
  set A := algebraMap (𝓞 L) R
  have e1 : (⟨x, hx⟩ : R) * A s = A a := by
    apply Subtype.ext
    change x * algebraMap (𝓞 L) L s = algebraMap (𝓞 L) L a
    rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have e2 : (⟨σ x, hmem⟩ : R) * A (σ • s) = A (σ • a) := by
    apply Subtype.ext
    change σ x * algebraMap (𝓞 L) L (σ • s) = algebraMap (𝓞 L) L (σ • a)
    rw [hσx, mul_assoc, inv_mul_cancel₀ hσs0, mul_one]
  have hres : IsLocalRing.residue R (A (σ • s)) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, algebraMap_mem_maximalIdeal_localizationAt_iff]
    exact hσs
  have r1 := congrArg (IsLocalRing.residue R) e1
  have r2 := congrArg (IsLocalRing.residue R) e2
  rw [map_mul] at r1 r2
  rw [residue_smul_of_isArithFrobAt 𝔓 hσ, residue_smul_of_isArithFrobAt 𝔓 hσ, ← r1, mul_pow] at r2
  exact mul_right_cancel₀ (by rwa [residue_smul_of_isArithFrobAt 𝔓 hσ] at hres) r2

end Residue

section DegreeOne

theorem intCast_surjective_ringOfIntegers_rat :
    Function.Surjective (Int.castRingHom (𝓞 ℚ)) := by
  intro z
  refine ⟨Rat.ringOfIntegersEquiv z, Rat.ringOfIntegersEquiv.injective ?_⟩
  simp

theorem absNorm_prime_of_ringOfIntegers_rat (𝔮 : Ideal (𝓞 ℚ)) (h0 : 𝔮 ≠ ⊥) [𝔮.IsMaximal] :
    (Ideal.absNorm 𝔮).Prime := by
  let _ : Field (𝓞 ℚ ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hfin : Finite (𝓞 ℚ ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h0
  set p := ringChar (𝓞 ℚ ⧸ 𝔮)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 ℚ ⧸ 𝔮) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 ℚ ⧸ 𝔮) p)
  have : Fact p.Prime := ⟨hp⟩
  let f : ZMod p →+* 𝓞 ℚ ⧸ 𝔮 := ZMod.castHom (dvd_refl p) _
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := intCast_surjective_ringOfIntegers_rat z
    exact ⟨n, by simp [f]⟩
  have hbij : Function.Bijective f := ⟨f.injective, hsurj⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_congr (Equiv.ofBijective f hbij),
    Nat.card_zmod]
  exact hp

theorem absNorm_prime_of_mem_degreeOnePrimes {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ degreeOnePrimes ℚ K) :
    (Ideal.absNorm v.asIdeal).Prime := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under (𝓞 ℚ)) v.asIdeal
  have hv' : v.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := hv
  rw [hv', pow_one] at h
  rw [← h]
  have hne : v.asIdeal.under (𝓞 ℚ) ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
  have : (v.asIdeal.under (𝓞 ℚ)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  exact absNorm_prime_of_ringOfIntegers_rat _ hne

end DegreeOne

section LatticeForm

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem exists_unit_of_homConstSet_eq (L L' : PeriodPair) (hL : latticeEnd L = cmRing σ₀)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hL' : L'.lattice = idealLattice σ₀ ↑𝔞⁻¹ * L.lattice)
    (φ : Isogeny (weierstrassCurve L) (weierstrassCurve L'))
    (hφ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    ∃ u : (𝓞 K)ˣ, invConst φ = σ₀ (algebraMap (𝓞 K) K u) ∧
      ∀ z : ℂ, homPt φ.toHom (toPoint L z) = toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z) := by
  classical
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hM : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← hφ, homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL']
  have hM' := eq_image_mul_inv hc hM
  have hP : (idealPeriodPair σ₀ hK 𝔞⁻¹).lattice = idealLattice σ₀ ↑𝔞⁻¹ :=
    lattice_idealPeriodPair σ₀ hK _
  have hPend : latticeEnd (idealPeriodPair σ₀ hK 𝔞⁻¹) = cmRing σ₀ := latticeEnd_idealPeriodPair σ₀ hK _
  have mult : ∀ d : ℂ, (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (d * ·) '' idealLattice σ₀ ↑𝔞⁻¹ →
      d ∈ cmRing σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    have h' : d * l ∈ (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) := by
      rw [hd]
      exact ⟨l, hl, rfl⟩
    exact h'
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c hM)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ hM')
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc])
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm, fun z ↦ ?_⟩
  rw [← latticeToHom_homConst φ.toHom, homPt_latticeToHom]
  congr 1
  change homConst _ _ φ.toHom * z = _
  rw [homConst_toHom, ← hcdef, ← ha]

end LatticeForm

section Main

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem algebraMap_mem_of_liesOver {𝔭 : HeightOneSpectrum (𝓞 K)} {𝔓 : HeightOneSpectrum (𝓞 L)}
    [h : 𝔓.asIdeal.LiesOver 𝔭.asIdeal] {a : 𝓞 K} (ha : a ∈ 𝔭.asIdeal) :
    algebraMap (𝓞 K) (𝓞 L) a ∈ 𝔓.asIdeal := by
  rw [h.over] at ha
  exact ha

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem isogBaseChange_eq_map {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (φ : Isogeny A A') : isogBaseChange (F' := ℂ) φ = φ.map (algebraMap L ℂ) :=
  Isogeny.ext_xy
    (by rw [isogBaseChange_alt, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_x _ φ).symm)
    (by rw [isogBaseChange_y, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_y _ φ).symm)

omit [NumberField L] in
include hK in

theorem exists_isogBaseChange_eq_of_isogeny {A A' : WeierstrassCurve L} [A.IsElliptic]
    [A'.IsElliptic] (hA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)) (φ : Isogeny A A')
    (ψ : Isogeny (A.baseChange ℂ) (A'.baseChange ℂ)) :
    ∃ φ' : Isogeny A A', isogBaseChange φ' = ψ := by
  classical
  suffices h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ by
    obtain ⟨φ', hφ'⟩ := ψ.exists_map_eq_of_forall_conj_eq h
    exact ⟨φ', (isogBaseChange_eq_map φ').trans hφ'⟩
  intro g
  set D := dualOver (isogBaseChange (F' := ℂ) φ)
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (A.baseChange ℂ)
  have hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ) := latticeEnd_eq_cmRing_of_ringEquiv
    (algebraMap K ℂ) hK Λ ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hA.some))
  have hmem : endConst (A.baseChange ℂ) (D.comp ψ).toHom ∈ cmRing (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  rw [endConst_apply, homConst_toHom, invConst_comp] at ha
  have hD := invConst_dualOver_mul (isogBaseChange (F' := ℂ) φ)
  rw [invConst_isogBaseChange, degree_isogBaseChange] at hD
  change invConst D * _ = _ at hD
  have hD0 : invConst D ≠ 0 := invConst_ne_zero D
  have hc0 : algebraMap L ℂ (invConst φ) ≠ 0 := by
    rw [← invConst_isogBaseChange]
    exact invConst_ne_zero _
  have hψ : invConst ψ = algebraMap L ℂ (algebraMap K L (algebraMap (𝓞 K) K a) * invConst φ /
      φ.degree) := by
    have hdeg0 : (φ.degree : ℂ) ≠ 0 := Nat.cast_ne_zero.2 φ.degree_pos.ne'
    rw [map_div₀, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply, ha, ← hD]
    field_simp
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj, hψ]
    exact g.commutes _
  have hQ : (ψ.conj g).toHom - ψ.toHom = 0 := by
    by_contra hne
    have h0 := invConst_ne_zero (isogOfHom _ hne)
    rw [← homConst_toHom, isogOfHom_toHom, map_sub, homConst_toHom, homConst_toHom, hc,
      sub_self] at h0
    exact h0 rfl
  have hQ' : (ψ.conj g).toHom = ψ.toHom := sub_eq_zero.1 hQ
  have h2 := congrArg Subtype.val hQ'
  exact Isogeny.ext' h2

include hK in

theorem exists_mem_maximalIdeal_invConst (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    ∃ c ∈ maximalIdeal (localizationAt L 𝔓), algebraMap (localizationAt L 𝔓) L c = invConst φ := by
  classical
  set c := invConst φ with hcdef
  have hc0 : algebraMap L ℂ c ≠ 0 := by
    rw [hcdef, ← invConst_isogBaseChange]
    exact invConst_ne_zero _

  have step1 : ∀ β ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      c * algebraMap K L β ∈ localizationAt L 𝔓 := by
    intro β hβ
    by_cases hβ0 : β = 0
    · rw [hβ0, map_zero, mul_zero]
      exact zero_mem _
    have hmem : algebraMap L ℂ c * algebraMap K ℂ β ∈
        homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) := by
      have h' : algebraMap L ℂ c * algebraMap K ℂ β ∈ (homConstSet ((W.baseChange L).baseChange ℂ)
          ((W'.baseChange L).baseChange ℂ) : Set ℂ) := by
        rw [hφ]
        exact ⟨_, map_mem_idealLattice _ hβ, rfl⟩
      exact h'
    obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hQ
      exact mul_ne_zero hc0 ((map_ne_zero _).2 hβ0) hQ.symm
    obtain ⟨ν, hν⟩ := exists_isogBaseChange_eq_of_isogeny hK hEW φ (isogOfHom Q hQ0)
    have e : algebraMap L ℂ (invConst ν) = algebraMap L ℂ (c * algebraMap K L β) := by
      rw [← invConst_isogBaseChange, hν, ← homConst_toHom, isogOfHom_toHom, hQ, map_mul,
        ← IsScalarTower.algebraMap_apply]
    have e' := (algebraMap L ℂ).injective e
    obtain ⟨d, hd, -⟩ := exists_invConst_reduceIsogeny L W W' ν
    rw [← e', ← hd]
    exact d.2

  have h1 : (1 : K) ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 𝔭.ne_bot)]
    exact FractionalIdeal.one_mem_one _
  have key := FractionalIdeal.mul_induction_on
    (C := fun z : K ↦ ∃ m ∈ maximalIdeal (localizationAt L 𝔓),
      algebraMap (localizationAt L 𝔓) L m = c * algebraMap K L z) h1
    (fun i hi j hj ↦ by
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
      refine ⟨⟨c * algebraMap K L i, step1 i hi⟩ * algebraMap (𝓞 L) (localizationAt L 𝔓)
        (algebraMap (𝓞 K) (𝓞 L) a), Ideal.mul_mem_left _ _
          ((algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2
            (algebraMap_mem_of_liesOver ha)), ?_⟩
      change c * algebraMap K L i * algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L, map_mul,
        mul_assoc])
    (fun x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩ ↦
      ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add, e₁, e₂, map_add, mul_add]⟩)
  obtain ⟨m, hm, e⟩ := key
  exact ⟨m, hm, by rw [e, map_one, mul_one]⟩

include hK in

theorem reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (hEW' : Nonempty (isogEnd ((W'.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' φ = ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  obtain ⟨c, hc, hcφ⟩ := exists_mem_maximalIdeal_invConst hK 𝔭 𝔓 hEW φ hφ
  have hdeg : φ.degree = Ideal.absNorm 𝔭.asIdeal := by
    have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, hEW⟩) (E' := ⟨_, hEW'⟩) 𝔭 hv
      (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ)
    rwa [degree_isogBaseChange] at h
  have hp : p = Ideal.absNorm 𝔭.asIdeal := by
    have hmem : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 L) ∈ 𝔓.asIdeal := by
      have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
      rwa [map_natCast] at this
    have h0 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ResidueField (localizationAt L 𝔓)) = 0 := by
      have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2 hmem
      rw [map_natCast] at h
      rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
      exact h
    have hdvd := (CharP.cast_eq_zero_iff (ResidueField (localizationAt L 𝔓)) p _).1 h0
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) hv).1 hdvd
  have hdeg' : φ.degree = p := hdeg.trans hp.symm
  obtain ⟨ψ, h1, h2, -, h4, h5⟩ := reduceIsogeny_eq_comp_frobeniusIsogeny L p φ hdeg' hc hcφ
  exact ⟨hp, hdeg', ⟨ψ, h1, h2, h4, h5⟩, residue_j_eq_pow L p φ hdeg' hc hcφ⟩

include hK in

theorem reduceIsogeny_congr_eq_comp_frobeniusIsogeny (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd (A'.baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A A')
    (hφ : (homConstSet (A.baseChange ℂ) (A'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A)
    (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) = A')
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
          ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  subst hW hW'
  erw [Isogeny.congr_rfl]
  exact reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet hK 𝔭 hv 𝔓 hEA hEA' φ hφ p

end Main

section Global

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

abbrev primeClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem ELL.j_eq_algebraMap_j {A : WeierstrassCurve L} [A.IsElliptic] {x : ELL K}
    {h : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)}
    (hx : (⟨A.baseChange ℂ, h⟩ : CMCurve K).toEll = x) : ELL.j x = algebraMap L ℂ A.j := by
  rw [← hx, ELL.j_toEll]
  exact WeierstrassCurve.map_j _ _

omit [NumberField L] in
include hK in

theorem exists_isogeny_primeClass_smul
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : ELL K) :
    ∃ φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧
      ((Ideal.absNorm 𝔭.asIdeal).Prime → φ.degree = Ideal.absNorm 𝔭.asIdeal) := by
  classical
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x
  obtain ⟨h₀, hx⟩ := hE x
  obtain ⟨h₁, hy⟩ := hE y
  obtain ⟨ψ, hψ⟩ := exists_isogeny_homConstSet_eq (algebraMap K ℂ) hK
    (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 (by rw [hx, hy])
  obtain ⟨φ, hφ⟩ := exists_isogBaseChange_eq_of_isogeny hK h₀ (hiso x y).some ψ
  have hφ' : (homConstSet ((E x).baseChange ℂ) ((E y).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← invConst_isogBaseChange, hφ]
    exact hψ
  refine ⟨φ, hφ', fun hv ↦ ?_⟩
  have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 hv
    (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ')
  rwa [degree_isogBaseChange] at h

include hK in

theorem frobenius_at_primes_of_degree_one (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ 𝔭 ∉ S, 𝔭 ∈ degreeOnePrimes ℚ K →
      ∀ (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal],
        (∃ (W : ELL K → WeierstrassCurve (localizationAt L 𝔓)) (_ : ∀ x, (W x).IsElliptic),
          (∀ x, (W x).map (algebraMap (localizationAt L 𝔓) L) = E x) ∧
          Pairwise fun x y ↦ IsLocalRing.residue _ (W x).j ≠ IsLocalRing.residue _ (W y).j) ∧
        (∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal →
          galClassOf hK L hL σ = primeClass 𝔭 ∧
          ∀ x : ELL K, σ ⟨ELL.j x, hL x⟩ =
            ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x), hL _⟩) ∧
        ∀ (x : ELL K)
          (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
          (homConstSet ((E x).baseChange ℂ)
              ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) :
                Set ℂ) =
            (algebraMap L ℂ (invConst φ) * ·) ''
              idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
          ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
            (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
            (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
              E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
            (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
            p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
              (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
                  (W'.map (IsLocalRing.residue _)),
                reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
                  ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
                ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
                ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
              IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  have : Finite (ELL K) := finite_ell hK
  have hj : ∀ x, ELL.j x = algebraMap L ℂ (E x).j := fun x ↦ by
    obtain ⟨h, hx⟩ := hE x
    exact ELL.j_eq_algebraMap_j hx
  have hEj : Pairwise fun x y ↦ (E x).j ≠ (E y).j := fun x y hxy e ↦
    hxy (ELL.j_injective (by rw [hj, hj, e]))
  obtain ⟨T, hT, hTgood⟩ :=
    exists_finite_forall_liesOver (K := K) (eventually_goodReduction E hEj)
  refine ⟨T, hT, fun 𝔭 h𝔭T h𝔭1 𝔓 _ ↦ ?_⟩
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  obtain ⟨W, hWell, hWmap, hWj, hWres⟩ := hTgood 𝔭 h𝔭T 𝔓 inferInstance
  have partB : ∀ (x : ELL K)
      (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
      ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
        (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
        (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
          E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
        (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
        p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
          (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
              (W'.map (IsLocalRing.residue _)),
            reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
              ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
            ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
            ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
          IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
    intro x φ hφ W W' _ _ hW hW' q _ _
    obtain ⟨h₁, -⟩ := hE x
    obtain ⟨h₂, -⟩ := hE ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)
    exact reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv 𝔓 h₁ h₂ φ hφ hW hW' q
  refine ⟨⟨W, hWell, hWmap, hWres⟩, fun σ hσ ↦ ?_, partB⟩

  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast] at this
  set x₀ : ELL K := classToEll (algebraMap K ℂ) hK 1
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀
  set z := (ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK L hL σ) x₀
  obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK E hE hiso 𝔭 x₀
  obtain ⟨-, -, -, hjy⟩ := partB x₀ φ hφ (W x₀) (W y) (hWmap x₀) (hWmap y) p
  have hjmem : (E x₀).j ∈ localizationAt L 𝔓 := by
    rw [← hWj x₀]
    exact (W x₀).j.2
  obtain ⟨hσmem, hσres⟩ := residue_apply_of_isArithFrobAt 𝔓 hσ hjmem
  have hq : Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) = p := by
    rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), hpdef, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  have hσj : σ (E x₀).j = (E z).j := by
    have h := galClassOf_apply_j hK L hL σ x₀
    have e1 : (⟨ELL.j x₀, hL x₀⟩ : L) = (E x₀).j := Subtype.ext (hj x₀)
    rw [e1] at h
    apply Subtype.ext
    rw [h, hj z]
    rfl
  have key : IsLocalRing.residue _ (W z).j = IsLocalRing.residue _ (W y).j := by
    have ez : (W z).j = ⟨σ (E x₀).j, hσmem⟩ := Subtype.ext (by
      show ((W z).j : L) = σ (E x₀).j
      rw [hσj, ← hWj z]
      rfl)
    have ex : (W x₀).j = ⟨(E x₀).j, hjmem⟩ := Subtype.ext (by
      show ((W x₀).j : L) = (E x₀).j
      rw [← hWj x₀]
      rfl)
    rw [ez, hσres, hq, hjy, ex]
  have hzy : z = y := by
    by_contra hne
    exact hWres hne key
  have hcls : galClassOf hK L hL σ = primeClass 𝔭 := by
    obtain ⟨a, -, huniq⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK x₀ y
    exact (huniq _ hzy).trans (huniq _ rfl).symm
  refine ⟨hcls, fun x ↦ Subtype.ext ?_⟩
  rw [galClassOf_apply_j, hcls]

end Global

end

end Elliptic
end GroundTheory.Global
