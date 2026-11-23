import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremLattice
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFrobenius
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremIdeles
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformizationClassification
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Points

variable {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']

omit [DecidableEq F] [DecidableEq F'] in
theorem point_some_eq_some {W : WeierstrassCurve F'} {x y x' y' : F'} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

theorem pointMapRing_vcPoint (f : F →+* F') {W₁ W₂ : WeierstrassCurve F} (C : VariableChange F)
    (h : C • W₁ = W₂) (P : W₁.toAffine.Point) :
    pointMapRing f W₂ (vcPoint C h P) =
      vcPoint (C.map f) (by rw [map_variableChange, h]) (pointMapRing f W₁ P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · exact point_some_eq_some _ _ (map_vcX C f x) (map_vcY C f x y)

theorem toPointHom_apply' (L : PeriodPair) (z : ℂ) : toPointHom L z = toPoint L z := rfl

theorem IsAnalyticUniformization.pointCongr {Λ : Submodule ℤ ℂ} {E E' : WeierstrassCurve ℂ}
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization Λ f) (e : E = E') :
    IsAnalyticUniformization Λ ((pointCongr e).toAddMonoidHom.comp f) := by
  subst e
  exact hf

end Points

section BaseChange

variable {L : Type} [Field L] [Algebra L ℂ] [DecidableEq L]

theorem exists_constMap_eq (A : WeierstrassCurve L) (P : (A.baseChange ℂ).toAffine.Point)
    (hP : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y), P = .some x y h →
      x ∈ (algebraMap L ℂ).range ∧ y ∈ (algebraMap L ℂ).range) :
    ∃ t : A.toAffine.Point, constMap A ℂ t = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hP _ _ h rfl
    have h' : A.toAffine.Nonsingular a b :=
      (A.toAffine.baseChange_nonsingular (f := Algebra.ofId L ℂ) (algebraMap L ℂ).injective a b).1 h
    exact ⟨.some a b h', rfl⟩

omit [DecidableEq L] in

theorem baseChange_map_eq (A : WeierstrassCurve L) (τ : L →+* L) (σ : ℂ →+* ℂ)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a)) :
    (A.baseChange ℂ).map σ = (A.map τ).baseChange ℂ := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map]
  congr 1
  ext a
  exact hτσ a

omit [Algebra L ℂ] in

theorem constMap_eq_pointMapRing {M : Type} [Field M] [Algebra L M] [DecidableEq M]
    (A : WeierstrassCurve L) (t : A.toAffine.Point) :
    constMap A M t = pointMapRing (algebraMap L M) A t := by
  rcases t with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem pointMapRing_constMap (A : WeierstrassCurve L) (τ : L →+* L) (σ : ℂ →+* ℂ)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a)) (t : A.toAffine.Point) :
    pointMapRing σ (A.baseChange ℂ) (constMap A ℂ t) =
      pointCongr (baseChange_map_eq A τ σ hτσ).symm (constMap (A.map τ) ℂ (pointMapRing τ A t)) := by
  have e : σ.comp (algebraMap L ℂ) = (algebraMap L ℂ).comp τ := RingHom.ext hτσ
  rw [constMap_eq_pointMapRing, constMap_eq_pointMapRing]
  have h1 := pointMapRing_pointMapRing (algebraMap L ℂ) σ A t
  have h2 := pointMapRing_pointMapRing τ (algebraMap L ℂ) A t
  rw [pointMapRing_congr e] at h1
  refine h1.trans ?_
  rw [← h2]
  rfl

end BaseChange

section Ideals

variable {K : Type} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem mem_idealLattice_unit_mul_iff (J : FractionalIdeal (𝓞 K)⁰ K) (v : (𝓞 K)ˣ) (w : ℂ) :
    σ₀ (algebraMap (𝓞 K) K v) * w ∈ idealLattice σ₀ J ↔ w ∈ idealLattice σ₀ J := by
  have key : ∀ (v : (𝓞 K)ˣ) (w : ℂ), w ∈ idealLattice σ₀ J →
      σ₀ (algebraMap (𝓞 K) K v) * w ∈ idealLattice σ₀ J := by
    intro v w hw
    obtain ⟨k, hk, rfl⟩ := (mem_idealLattice σ₀).1 hw
    refine (mem_idealLattice σ₀).2 ⟨algebraMap (𝓞 K) K v * k, ?_, by rw [map_mul]⟩
    rw [← Algebra.smul_def]
    exact (J : Submodule (𝓞 K) K).smul_mem (v : 𝓞 K) hk
  refine ⟨fun h ↦ ?_, key v w⟩
  have := key v⁻¹ _ h
  rwa [← mul_assoc, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
    map_one, one_mul] at this

theorem mem_idealLattice_diagonal_smul_iff (x : Kˣ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : ℂ) :
    z ∈ idealLattice σ₀ ↑(IdeleGroup.diagonal K x⁻¹ • J) ↔ σ₀ x * z ∈ idealLattice σ₀ J := by
  rw [mem_idealLattice, mem_idealLattice]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_diagonal_smul_iff, Units.val_inv_eq_inv_val, inv_inv] at hk
    exact ⟨x * k, hk, by rw [map_mul]⟩
  · rintro ⟨k, hk, hkz⟩
    refine ⟨(x⁻¹ : K) * k, ?_, ?_⟩
    · rw [mem_diagonal_smul_iff, Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
        mul_inv_cancel₀ x.ne_zero, one_mul]
      exact hk
    · rw [map_mul, hkz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ x.ne_zero, map_one, one_mul]

end Ideals

section Level

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem exists_uniformization_of_data (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    {m : ℕ} {L : IntermediateField K ℂ} [NumberField L] (τ : L ≃ₐ[K] L)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a))
    {A : WeierstrassCurve L} [A.IsElliptic] (V₀ : VariableChange ℂ) (hV₀ : V₀ • E = A.baseChange ℂ)
    (htors : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y),
      m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0 →
        x ∈ (algebraMap L ℂ).range ∧ y ∈ (algebraMap L ℂ).range)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : Kˣ)
    (hs𝔞 : s⁻¹ • 𝔞 = IdeleGroup.diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞))
    (hsq : ∀ t : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
      IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) =
        Submodule.Quotient.mk ((x⁻¹ : K) * t))
    (φ : Isogeny A (A.map (τ : L →+* L)))
    (hφ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (D : VariableChange L) (hD : D • A.map (τ : L →+* L) = A.map (τ : L →+* L))
    (hDφ : ∀ t : A.toAffine.Point, m • t = 0 →
      pointHomOver ℂ φ t = vcPoint D hD (pointMapRing (τ : L →+* L) A t))
    (V' : VariableChange ℂ)
    (hV' : V' • weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)) =
      (A.map (τ : L →+* L)).baseChange ℂ) :
    ∃ f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical

  have hL₁ := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hL₂ := lattice_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  generalize idealPeriodPair (algebraMap K ℂ) hK 𝔞 = L₁ at hL₁
  generalize idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞) = L₂ at hL₂ hV'

  have hfA := hf.vcPoint V₀ hV₀
  rw [← hL₁] at hfA
  obtain ⟨V, hV, hfV⟩ := exists_vcPoint_of_isAnalyticUniformization hfA

  have hφℂ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (invConst (isogBaseChange (F' := ℂ) φ) * ·) ''
        idealLattice (algebraMap K ℂ) ↑((primeIdealUnit 𝔭)⁻¹) := by
    rw [invConst_isogBaseChange, hφ, Units.val_inv_eq_inv_val, coe_primeIdealUnit]
  obtain ⟨u, hu⟩ := exists_unit_pointMap_vcPoint (algebraMap K ℂ) hK 𝔞 (primeIdealUnit 𝔭)⁻¹ L₁ L₂
    hL₁ hL₂ V hV V' hV' (isogBaseChange (F' := ℂ) φ) hφℂ

  have hDℂ := Elliptic.baseChange_smul_eq D ℂ hD
  have hg₁ := (isAnalyticUniformization_toPointHom L₂).vcPoint V' hV'
  have hg₂ := hg₁.vcPoint (D.baseChange ℂ) hDℂ
  obtain ⟨c, hc0, hcl, hcg⟩ := exists_mul_eq_of_isAnalyticUniformization hg₁ hg₂
  rw [hL₂] at hcl
  obtain ⟨ε, hε⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl

  have hεinv : algebraMap K ℂ (algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) * c = 1 := by
    rw [hε, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hcinv : c⁻¹ * algebraMap K ℂ (algebraMap (𝓞 K) K u) =
      algebraMap K ℂ (algebraMap (𝓞 K) K ((ε⁻¹ * u : (𝓞 K)ˣ) : 𝓞 K)) := by
    rw [Units.val_mul, map_mul, map_mul, inv_eq_of_mul_eq_one_left hεinv]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = c⁻¹ * algebraMap K ℂ (algebraMap (𝓞 K) K u) * algebraMap K ℂ x :=
    ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ, hcinv]
    refine mul_ne_zero ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2
      (Units.ne_zero _))) ((map_ne_zero _).2 x.ne_zero)
  have hΛ : ∀ z, z ∈ idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞) ↔ κ * z ∈ L₂.lattice := by
    intro z
    rw [hs𝔞, mem_idealLattice_diagonal_smul_iff, hL₂, hκ, hcinv, mul_assoc,
      mem_idealLattice_unit_mul_iff]

  have h₄ : (V₀.map (σ : ℂ →+* ℂ)) • E.map (σ : ℂ →+* ℂ) = (A.baseChange ℂ).map (σ : ℂ →+* ℂ) := by
    rw [map_variableChange, hV₀]
  have h₃ := inv_smul_eq_of_smul_eq _ h₄
  have e₂ : (A.map (τ : L →+* L)).baseChange ℂ = (A.baseChange ℂ).map (σ : ℂ →+* ℂ) :=
    (baseChange_map_eq A (τ : L →+* L) σ hτσ).symm
  have hf' := ((hg₁.comp_mul hκ0 hΛ).pointCongr e₂).vcPoint _ h₃
  refine ⟨_, hf', fun t y hmt hq ↦ ?_⟩

  have hdiff : algebraMap K ℂ y - algebraMap K ℂ ((x⁻¹ : K) * t) ∈
      idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞) := by
    rw [hsq t hmt] at hq
    have h1 := (Submodule.Quotient.eq _).1 hq
    rw [← map_sub]
    refine map_mem_idealLattice _ ?_
    rw [← neg_sub]
    exact Submodule.neg_mem _ h1
  rw [← sub_add_cancel (algebraMap K ℂ y) (algebraMap K ℂ ((x⁻¹ : K) * t)), map_add,
    (hf'.map_eq_zero_iff _).2 hdiff, zero_add]

  set z := algebraMap K ℂ t with hz
  have hmz : (m : ℂ) * z ∈ L₁.lattice := by
    rw [hL₁, hz, ← map_natCast (algebraMap K ℂ), ← map_mul]
    exact map_mem_idealLattice _ hmt
  have hPA : vcPoint V₀ hV₀ (f z) = vcPoint V hV (toPoint L₁ z) := hfV z
  have hPAm : m • vcPoint V₀ hV₀ (f z) = 0 := by
    rw [hPA, ← toPointHom_apply', ← vcPointEquiv_apply, ← map_nsmul, ← map_nsmul, nsmul_eq_mul,
      toPointHom_apply', toPoint_of_mem hmz, map_zero]
  obtain ⟨tL, htL⟩ := exists_constMap_eq A (vcPoint V₀ hV₀ (f z)) (fun a b h hP ↦
    htors a b h (by rw [← hP]; exact hPAm))
  have htLm : m • tL = 0 := by
    apply constMap_injective A ℂ
    rw [map_nsmul, htL, hPAm, map_zero]

  have key := congrArg (constMap (A.map (τ : L →+* L)) ℂ) (hDφ tL htLm)
  rw [constMap_pointHomOver, htL, hPA, hu z, constMap_eq_pointMapRing, pointMapRing_vcPoint,
    ← constMap_eq_pointMapRing] at key

  have hw : c * (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z)) =
      algebraMap K ℂ (algebraMap (𝓞 K) K u) * z := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hcg' := hcg (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z))
  rw [hw] at hcg'
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
    toPointHom_apply'] at hcg'
  have h5 : vcPoint (D.baseChange ℂ) hDℂ
      (constMap (A.map (τ : L →+* L)) ℂ (pointMapRing (τ : L →+* L) A tL)) =
      vcPoint (D.baseChange ℂ) hDℂ
        (vcPoint V' hV' (toPoint L₂ (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z)))) :=
    key.symm.trans hcg'.symm
  have h6 := vcPoint_injective _ _ h5

  have h7 := pointMapRing_constMap A (τ : L →+* L) σ hτσ tL
  rw [htL, pointMapRing_vcPoint] at h7
  change vcPoint _ h₃ (pointCongr e₂ (vcPoint V' hV'
    (toPoint L₂ (κ * algebraMap K ℂ ((x⁻¹ : K) * t))))) = pointMapRing (σ : ℂ →+* ℂ) E (f z)
  have e3 : κ * algebraMap K ℂ ((x⁻¹ : K) * t) =
      c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z) := by
    rw [hκ, hz, map_mul, map_inv₀]
    field_simp
  rw [e3, ← h6]
  have h8 : pointCongr e₂ (constMap (A.map (τ : L →+* L)) ℂ (pointMapRing (τ : L →+* L) A tL)) =
      vcPoint (V₀.map (σ : ℂ →+* ℂ)) h₄ (pointMapRing (σ : ℂ →+* ℂ) E (f z)) := h7.symm
  rw [h8]
  exact vcPoint_vcPoint_of_eq_inv _ _ rfl _ _ _

end Level

end

end Elliptic
end GroundTheory.Global
