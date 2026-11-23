import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapToZModEq

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open IsLocalRing

theorem valuation_le_one_iff_of_lt_iff {K F : Type} [Field K] [NumberField K] [NormedField F]
    (v : HeightOneSpectrum (𝓞 K)) (a : K →+* F)
    (h : ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1) (x : K) :
    v.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 := h x⁻¹
  have hv : 0 < v.valuation K x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)
  have hn : 0 < ‖a x‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hx)
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ hv, inv_lt_one₀ hn] at h1
  rw [← not_lt, ← not_lt, h1]

theorem exists_embedding_inducing_place (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 K)) (hl : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ a : K →+* PadicAlgCl l, ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1 := by
  classical
  let a₀ : K →+* PadicAlgCl l := (IsAlgClosed.lift (R := ℚ) (S := K) (M := PadicAlgCl l)).toRingHom
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a₀
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    have hfin : ‖a₀ ((l : ℕ) : K)‖ < 1 := by
      rw [map_natCast]
      have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by simp
      rw [h1, PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    convert hfin using 3
    first | exact map_natCast _ _ | simp
  have := v.isPrime
  have := w₀.isPrime
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem v.asIdeal hl
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem w₀.asIdeal hlw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) v.asIdeal
    w₀.asIdeal (K ≃ₐ[ℚ] K)
  let a : K →+* PadicAlgCl l := a₀.comp (σ : K →+* K)
  obtain ⟨v', hv'⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a
  have hvv : v' = v := by
    apply HeightOneSpectrum.ext
    ext y
    have h2 : (σ • y) ∈ w₀.asIdeal ↔ y ∈ v.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul_iff
    rw [← h2, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hv',
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    rfl
  subst hvv
  exact ⟨a, hv'⟩

theorem algebraMap_toZMod_eq {l : ℕ} [Fact l.Prime] {R : Type} [Field R] [Algebra (ZMod l) R]
    (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | (apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq ..)

theorem isAlgebraic_residueField {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [IsLocalRing B]
    [Algebra (ZMod l) (ResidueField B)] (c : ℤ_[l] →+* B)
    (hcl : c (l : ℤ_[l]) ∈ maximalIdeal B)
    (halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0) :
    Algebra.IsAlgebraic (ZMod l) (ResidueField B) := by
  have hl : (residue B).comp c (l : ℤ_[l]) = 0 := (residue_eq_zero_iff _).mpr hcl
  have hcomp : (algebraMap (ZMod l) (ResidueField B)).comp PadicInt.toZMod = (residue B).comp c :=
    RingHom.ext fun x => algebraMap_toZMod_eq _ hl x
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp, hb⟩ := halg b
  refine ⟨p.map PadicInt.toZMod, fun h => ?_, ?_⟩
  · have hdvd : Polynomial.C (l : ℤ_[l]) ∣ p := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h1 : PadicInt.toZMod (p.coeff i) = 0 := by
        have := congrArg (fun q => q.coeff i) h
        simpa using this
      have h2 : p.coeff i ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h2
      exact Ideal.mem_span_singleton.mp h2
    have hu := hp _ hdvd
    exact PadicInt.prime_p.not_unit hu
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hb, map_zero]

theorem exists_isPrimitive_eval₂_eq_zero {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) :
    ∃ p : ℤ_[l][X], p.IsPrimitive ∧
      p.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) x = 0 := by
  classical
  have hmap : algebraMap ℤ_[l] (PadicAlgCl l) =
      (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom :=
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [hmap]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => Subtype.ext h)
  letI : NormalizedGCDMonoid ℤ_[l] := Classical.arbitrary _
  have hx : IsAlgebraic ℤ_[l] x :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  rw [← hmap]
  exact Polynomial.aeval_primPart_eq_zero hp0 hp

def unitBall {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) : ValuationSubring ℂ :=
  (PadicAlgCl.valued l).v.valuationSubring.comap (ι.symm : ℂ →+* PadicAlgCl l)

theorem mem_unitBall_iff {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) :
    z ∈ unitBall ι ↔ ‖ι.symm z‖ ≤ 1 := by
  rw [unitBall, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    ← NNReal.coe_le_coe]
  rfl

theorem nonempty_residueField_unitBall_equiv {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) :
    Nonempty (ResidueField (unitBall ι) ≃+* Formalism.CyclotomicNorms.Fbar l) := by
  classical
  set B := unitBall ι with hB
  let inc : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hinc : ∀ x : ℤ_[l], ‖inc x‖ = ‖x‖ := fun x => by
    change ‖((x : ℚ_[l]) : PadicAlgCl l)‖ = ‖x‖
    rw [PadicAlgCl.norm_extends]; rfl
  let c : ℤ_[l] →+* B := (ι.toRingHom.comp inc).codRestrict B.toSubring fun x => by
    change ι (inc x) ∈ B
    rw [hB, mem_unitBall_iff, RingEquiv.symm_apply_apply, hinc]
    exact PadicInt.norm_le_one x
  have hcl : c (l : ℤ_[l]) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨⟨y, hy⟩, hxy⟩ := hu.exists_right_inv
    have h1 : ι (inc (l : ℤ_[l])) * y = 1 := congrArg Subtype.val hxy
    have h2 : inc (l : ℤ_[l]) * ι.symm y = 1 := by
      apply ι.injective
      rw [map_mul, RingEquiv.apply_symm_apply, h1, map_one]
    have h3 := congrArg norm h2
    have h4 : ‖ι.symm y‖ ≤ 1 := (mem_unitBall_iff ι y).mp hy
    rw [norm_mul, hinc, norm_one] at h3
    have h5 : ‖(l : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    nlinarith [norm_nonneg (ι.symm y), norm_nonneg (l : ℤ_[l])]
  have halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0 := by
    intro b
    obtain ⟨p, hp, h0⟩ := exists_isPrimitive_eval₂_eq_zero (ι.symm (b : ℂ))
    refine ⟨p, hp, Subtype.ext ?_⟩
    have h1 := Polynomial.hom_eval₂ p c B.subtype b
    have h2 := Polynomial.hom_eval₂ p inc ι.toRingHom (ι.symm (b : ℂ))
    have h3 : B.subtype.comp c = ι.toRingHom.comp inc := RingHom.ext fun _ => rfl
    have h4 : ι.toRingHom (ι.symm (b : ℂ)) = B.subtype b := ι.apply_symm_apply _
    rw [h3, ← h4, ← h2] at h1
    have h5 : p.eval₂ inc (ι.symm (b : ℂ)) = 0 := h0
    rw [h5, map_zero] at h1
    exact h1
  have hlR : ((l : ℕ) : ResidueField B) = 0 := by
    have := (residue_eq_zero_iff _).mpr hcl
    simpa using this
  haveI : CharP (ResidueField B) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlR
  letI : Algebra (ZMod l) (ResidueField B) := ZMod.algebra _ l
  haveI : Algebra.IsAlgebraic (ZMod l) (ResidueField B) := isAlgebraic_residueField c hcl halg
  haveI : IsAlgClosed (ResidueField B) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed B ℂ
  haveI : IsAlgClosure (ZMod l) (ResidueField B) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod l) (ResidueField B) (AlgebraicClosure (ZMod l))).toRingEquiv⟩

theorem val_nonneg_iff (D : D7) (lam : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val lam x ↔ (D.plEq lam).valuation D.what₂.LL x ≤ 1 := by
  haveI := D.nfLL
  by_cases hx : x = 0
  · simp [hx]
  rw [D.val_eq lam x hx]
  have h0 : (D.plEq lam).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have h1 := WithZero.log_le_log (x := (D.plEq lam).valuation D.what₂.LL x) (y := 1) h0 one_ne_zero
  rw [WithZero.log_one] at h1
  rw [← h1]
  unfold vAdd
  norm_cast
  omega

theorem nonempty_plSide : ∀ D : D7, Nonempty (PlSide D) := by
  intro D
  haveI := D.nfLL
  haveI := D.galLL
  have key : ∀ lam : D.what₂.places.Pl, ∃ ι : Qbar (D.what₂.places.resChar lam) ≃+* ℂ,
      ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1 := by
    intro lam
    obtain ⟨a, ha⟩ := exists_embedding_inducing_place D.what₂.LL (D.what₂.places.resChar lam)
      (D.plEq lam) (Formalism.BasicNotions.Examples₂.PlOver.resChar_mem D lam)
    obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq
      (D.what₂.places.resChar lam) D.what₂.LL a D.what₂.embLL
    refine ⟨ι, fun x => ?_⟩
    have h1 : ι.symm (D.what₂.embLL x) = a x := by
      rw [← hι]; exact ι.symm_apply_apply _
    rw [h1, val_nonneg_iff, valuation_le_one_iff_of_lt_iff _ a ha]
  choose ι hι using key
  exact ⟨⟨ι, hι, fun lam => unitBall (ι lam), fun lam z => mem_unitBall_iff (ι lam) z,
    fun lam => Classical.choice (nonempty_residueField_unitBall_equiv (ι lam))⟩⟩

end GlobalTheory.HeightCounting

end
