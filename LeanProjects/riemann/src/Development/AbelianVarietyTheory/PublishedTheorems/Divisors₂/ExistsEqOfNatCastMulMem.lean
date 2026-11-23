import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice

open NumberField Neutral.B1 GlobalTheory.Idele GlobalTheory.ConjPoint Filter
open scoped nonZeroDivisors IntermediateField Topology

noncomputable section

namespace GlobalTheory.EllipticCM

def IsAnalyticIso {X : WeierstrassCurve ℂ} {Λ : AddSubgroup ℂ}
    (ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point) : Prop :=
  ∀ z ∉ Λ, ∃ f g : ℂ → ℂ, AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧
    ∀ᶠ w in 𝓝 z, ∃ h, ξ (w : ℂ) = .some (f w) (g w) h

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

def idealSub (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : AddSubgroup ℂ :=
  (𝔞 : Submodule (𝓞 K) K).toAddSubgroup.map (algebraMap K ℂ).toAddMonoidHom

def torsionIncl (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :
    (K ⧸ (𝔞 : Submodule (𝓞 K) K)) →+ (ℂ ⧸ idealSub 𝔞) :=
  QuotientAddGroup.map _ _ (algebraMap K ℂ).toAddMonoidHom fun x hx => ⟨x, hx, rfl⟩

def Transports (σ : ℂ ≃ₐ[K] ℂ) (t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ)
    {X : WeierstrassCurve ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point) : Prop :=
  ∃! ξ' : (ℂ ⧸ idealSub (t⁻¹ • 𝔞)) ≃+ (X.map (σ : ℂ →+* ℂ)).toAffine.Point,
    IsAnalyticIso ξ' ∧ ∀ x : K ⧸ (𝔞 : Submodule (𝓞 K) K),
      mapPoint X (σ : ℂ →+* ℂ) (ξ (torsionIncl 𝔞 x)) =
        ξ' (torsionIncl (t⁻¹ • 𝔞) (mulEquiv t⁻¹ h𝔞 rfl x))

def RestrictsTo (σ : ℂ ≃ₐ[K] ℂ) (a : Field.absoluteGaloisGroupAbelianization K) : Prop :=
  ∃ (ι : AlgebraicClosure K →ₐ[K] ℂ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
    (∀ x, σ (ι x) = ι (g x)) ∧ toAb K g = a

def finitePart (s : Ideles K) : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) s

end Defs

end GlobalTheory.EllipticCM

namespace GlobalTheory.Published

open GlobalTheory.EllipticCM

def EllipticMainTheoremCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K,
      IsGlobalArtinMap K Art →
    ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Ideles K), RestrictsTo σ (Art (QuotientGroup.mk s)) →
    ∀ (X : WeierstrassCurve ℂ) [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
      (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point), IsAnalyticIso ξ →
      Transports σ (finitePart s) h𝔞 ξ

def HilbertClassFieldJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ L₀ : PeriodPair, IsIdealLattice (K := K) 1 L₀ →
      IsHilbertClassField K⟮(latticeCurve L₀).j⟯ ∧
      Module.finrank K K⟮(latticeCurve L₀).j⟯ = classNumber K ∧
      (∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
        IsIdealLattice 𝔞 L → IsIdealLattice 𝔟 L' →
        ((latticeCurve L).j = (latticeCurve L').j ↔ ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟)) ∧
      (idealInvariants K).ncard = classNumber K ∧
      Set.range (fun g : K⟮(latticeCurve L₀).j⟯ ≃ₐ[K] K⟮(latticeCurve L₀).j⟯ =>
        (g (IntermediateField.AdjoinSimple.gen K (latticeCurve L₀).j) : ℂ)) = idealInvariants K

theorem ComplexMultiplicationJSt.hilbertClassFieldJ (h : ComplexMultiplicationJSt) :
    HilbertClassFieldJ := by
  intro K _ _ _ _ h2 L₀ hL₀
  obtain ⟨H, art, hH, hart, hgen, hj⟩ := id h K h2
  have hm : ∀ {𝔞 L}, IsIdealLattice (K := K) 𝔞 L → (latticeCurve L).j ∈ H := fun {𝔞 L} hL =>
    hgen 𝔞 L hL ▸ IntermediateField.mem_adjoin_simple_self K _
  have hiff : ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
      IsIdealLattice 𝔞 L → IsIdealLattice 𝔟 L' →
      ((latticeCurve L).j = (latticeCurve L').j ↔ ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) := by
    intro 𝔞 𝔟 L L' hL hL'
    have hL'' : IsIdealLattice ((𝔞 * 𝔟⁻¹)⁻¹ * 𝔞) L' := by
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have e := hj 𝔞 _ L L' hL hL'' ⟨_, hm hL⟩ rfl
    rw [← mul_inv_eq_one (a := ClassGroup.mk K 𝔞), ← map_inv, ← map_mul]
    constructor
    · intro hjj
      rw [← hjj] at e
      rw [← map_eq_one_iff art art.injective]
      generalize art (ClassGroup.mk K (𝔞 * 𝔟⁻¹)) = g at e
      have hH' := hgen 𝔞 L hL
      subst hH'
      apply AlgEquiv.coe_toAlgHom_injective
      refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
      rintro x rfl
      exact Subtype.ext e
    · intro hc
      rw [hc, map_one] at e
      exact e
  obtain rfl := hgen 1 L₀ hL₀
  have hrange : Set.range (fun g : K⟮(latticeCurve L₀).j⟯ ≃ₐ[K] K⟮(latticeCurve L₀).j⟯ =>
      (g (IntermediateField.AdjoinSimple.gen K (latticeCurve L₀).j) : ℂ)) = idealInvariants K := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨c, rfl⟩ := art.surjective g
      obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
      obtain ⟨L', hL'⟩ := exists_isIdealLattice h2 ((FractionalIdeal.mk0 K I)⁻¹ * 1)
      refine ⟨_, L', hL', ?_⟩
      rw [← hj 1 _ L₀ L' hL₀ hL' (IntermediateField.AdjoinSimple.gen K _) rfl, ClassGroup.mk_mk0]
    · rintro ⟨𝔠, L', hL', rfl⟩
      exact ⟨art (ClassGroup.mk K 𝔠⁻¹), hj 1 𝔠⁻¹ L₀ L' hL₀ (by simpa using hL') _ rfl⟩
  refine ⟨hH, h.finrank_eq h2 hH, hiff, ?_, hrange⟩
  rw [← hrange, ← Set.image_univ, Set.ncard_image_of_injective, Set.ncard_univ,
    ← Nat.card_congr art.toEquiv, classNumber, Nat.card_eq_fintype_card]
  intro g g' e
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
  rintro x rfl
  exact Subtype.ext e

theorem exists_restrictsTo {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (σ : ℂ ≃ₐ[K] ℂ) :
    ∃ a, RestrictsTo σ a := by
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower K (AlgebraicClosure K) ℂ :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact ⟨_, ι, σ.restrictNormal (AlgebraicClosure K),
    fun x => (σ.restrictNormal_commutes (AlgebraicClosure K) x).symm, rfl⟩

theorem EllipticMainTheoremCM.exists_idele (h : EllipticMainTheoremCM) {K : Type} [Field K]
    [NumberField K] [IsTotallyComplex K] [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2)
    (hA : GlobalReciprocity K) (σ : ℂ ≃ₐ[K] ℂ) :
    ∃ t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ,
      ∀ (X : WeierstrassCurve ℂ) [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
        (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point), IsAnalyticIso ξ → Transports σ t h𝔞 ξ := by
  obtain ⟨Art, hArt⟩ := hA
  obtain ⟨a, ha⟩ := exists_restrictsTo σ
  obtain ⟨c, rfl⟩ := hArt.2.1 a
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨finitePart s, fun X _ 𝔞 h𝔞 ξ hξ => h K h2 Art hArt σ s ha X 𝔞 h𝔞 ξ hξ⟩

end GlobalTheory.Published

namespace GlobalTheory.EllipticCM

open WeierstrassCurve

section Analytic

variable {X : WeierstrassCurve ℂ} {Λ : AddSubgroup ℂ} {L : PeriodPair} {C : VariableChange ℂ}

theorem IsAnalyticIso.exists_mul {ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point} (hξ : IsAnalyticIso ξ)
    (h : C • X = latticeCurve L) :
    ∃ α : ℂ, α ≠ 0 ∧ (∀ z, z ∈ Λ ↔ α * z ∈ L.lattice) ∧
      ∀ z : ℂ, ξ z = variableChangePoint C h (latticePoint L (α * z)) := by
  have hinj := (variableChangePoint_bijective C h).1
  obtain ⟨q, hq⟩ := ξ.surjective (variableChangePoint C h (latticePoint L (L.ω₁ / 2)))
  obtain ⟨z₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hz₀ : z₀ ∉ Λ := fun hz => by
    rw [(QuotientAddGroup.eq_zero_iff _).2 hz, map_zero, eq_comm, map_eq_zero_iff _ hinj,
      latticePoint_eq_zero_iff] at hq
    exact L.ω₁_div_two_notMem_lattice hq
  obtain ⟨f, g, hf, -, hev⟩ := hξ z₀ hz₀
  let ψ : ℂ →+ (latticeCurve L).toAffine.Point :=
    (variableChangePointEquiv C h).symm.toAddMonoidHom.comp
      (ξ.toAddMonoidHom.comp (QuotientAddGroup.mk' Λ))
  have hψ : ∀ z : ℂ, variableChangePoint C h (ψ z) = ξ z := fun z =>
    (variableChangePointEquiv C h).apply_symm_apply _
  obtain ⟨α, hα⟩ := exists_eq_latticePoint_mul ψ (z₀ := z₀)
    (F := fun w => (f w - C.r) / (C.u : ℂ) ^ 2) (by fun_prop) (by
      filter_upwards [hev] with w ⟨hw, e⟩
      rw [← hψ] at e
      rcases hP : ψ w with _ | ⟨x, y, hxy⟩
      · rw [hP] at e
        exact (Affine.Point.some_ne_zero _ (e.symm.trans (map_zero _))).elim
      · rw [hP, variableChangePoint_some, Affine.Point.some.injEq] at e
        obtain rfl : x = (f w - C.r) / (C.u : ℂ) ^ 2 := by
          rw [← e.1]; field_simp; ring
        exact ⟨y, hxy, rfl⟩)
  have hΛ : ∀ z, z ∈ Λ ↔ α * z ∈ L.lattice := fun z => by
    rw [← latticePoint_eq_zero_iff, ← hα, ← map_eq_zero_iff _ hinj, hψ, ξ.map_eq_zero_iff,
      QuotientAddGroup.eq_zero_iff]
  refine ⟨α, ?_, hΛ, fun z => by rw [← hα, hψ]⟩
  rintro rfl
  exact hz₀ ((hΛ _).2 (by simp))

theorem exists_isAnalyticIso (h : C • X = latticeCurve L) {α : ℂ} (hα : α ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ α * z ∈ L.lattice) :
    ∃ ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point, IsAnalyticIso ξ ∧
      ∀ z : ℂ, ξ z = variableChangePoint C h (latticePoint L (α * z)) := by
  let φ : ℂ →+ X.toAffine.Point :=
    (variableChangePoint C h).comp ((latticePointHom L).comp (AddMonoidHom.mulLeft α))
  have hφ : ∀ z, φ z = variableChangePoint C h (latticePoint L (α * z)) := fun _ => rfl
  have hker : Λ = φ.ker := by
    ext z
    rw [AddMonoidHom.mem_ker, hφ, map_eq_zero_iff _ (variableChangePoint_bijective C h).1,
      latticePoint_eq_zero_iff, hΛ]
  have hs : Function.Surjective φ :=
    (variableChangePoint_bijective C h).2.comp
      ((latticePoint_surjective L).comp (mul_left_surjective₀ hα))
  refine ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hs), fun z hz => ?_, fun z => rfl⟩
  have hz' : α * z ∉ L.lattice := (hΛ z).not.1 hz
  have hP : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z :=
    (L.analyticOnNhd_weierstrassP _ hz').comp_of_eq (f := fun w => α * w) (by fun_prop) rfl
  have hP' : AnalyticAt ℂ (fun w => L.derivWeierstrassP (α * w)) z :=
    (L.analyticOnNhd_derivWeierstrassP _ hz').comp_of_eq (f := fun w => α * w) (by fun_prop) rfl
  refine ⟨fun w => (C.u : ℂ) ^ 2 * L.weierstrassP (α * w) + C.r,
    fun w => (C.u : ℂ) ^ 3 * (L.derivWeierstrassP (α * w) / 2) +
      (C.u : ℂ) ^ 2 * C.s * L.weierstrassP (α * w) + C.t, by fun_prop, by fun_prop, ?_⟩
  filter_upwards [(continuous_const_mul α).continuousAt.eventually
    (eventually_notMem_periodLattice L hz')] with w hw
  change ∃ h, φ w = _
  rw [hφ, latticePoint_of_notMem L hw, variableChangePoint_some]
  exact ⟨_, rfl⟩

theorem eq_zero_of_forall_div_mem {c : ℂ} (h : ∀ n : ℕ, c / n ∈ L.lattice) : c = 0 := by
  obtain ⟨n, hn, hn0⟩ := (((tendsto_const_div_atTop_nhds_zero_nat c).eventually
    (L.compl_lattice_sdiff_singleton_mem_nhds 0)).and (eventually_gt_atTop 0)).exists
  by_contra hc
  exact hn ⟨h n, div_ne_zero hc (by exact_mod_cast hn0.ne')⟩

theorem IsAnalyticIso.ext [X.IsElliptic] {ξ ξ' : (ℂ ⧸ Λ) ≃+ X.toAffine.Point}
    (hξ : IsAnalyticIso ξ) (hξ' : IsAnalyticIso ξ')
    (e : ∀ n : ℕ, ξ ((n : ℂ)⁻¹ : ℂ) = ξ' ((n : ℂ)⁻¹ : ℂ)) : ξ = ξ' := by
  obtain ⟨L, C, h⟩ := exists_variableChange_eq_latticeCurve X
  obtain ⟨α, -, -, hα⟩ := hξ.exists_mul h
  obtain ⟨β, -, -, hβ⟩ := hξ'.exists_mul h
  obtain rfl : α = β := sub_eq_zero.1 <| eq_zero_of_forall_div_mem (L := L) fun n => by
    have := e n
    rw [hα, hβ, (variableChangePoint_bijective C h).1.eq_iff, latticePoint_eq_iff] at this
    rwa [div_eq_mul_inv, sub_mul]
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [hα, hβ]

theorem mapPoint_variableChangePoint {Y Y' : WeierstrassCurve ℂ} (σ : ℂ →+* ℂ) (h : C • X = Y)
    (h' : C.map σ • X.map σ = Y') {s : Y.toAffine.Point ≃+ Y'.toAffine.Point}
    (hs : ∀ x y h, ∃ h', s (.some x y h) = .some (σ x) (σ y) h') (P : Y.toAffine.Point) :
    mapPoint X σ (variableChangePoint C h P) = variableChangePoint (C.map σ) h' (s P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · change mapPoint X σ (variableChangePoint C h 0) = variableChangePoint (C.map σ) h' (s 0)
    simp
  · obtain ⟨h'', e⟩ := hs x y hP
    rw [e, variableChangePoint_some, variableChangePoint_some]
    change Affine.Point.some _ _ _ = _
    rw [Affine.Point.some.injEq]
    simp [VariableChange.map]

end Analytic

section Ideals

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

omit [NumberField K] in
theorem mem_idealSub {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {z : ℂ} :
    z ∈ idealSub 𝔞 ↔ ∃ x ∈ 𝔞, algebraMap K ℂ x = z := Iff.rfl

omit [NumberField K] in
theorem algebraMap_mem_idealSub {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {x : K} :
    algebraMap K ℂ x ∈ idealSub 𝔞 ↔ x ∈ 𝔞 :=
  ⟨fun ⟨_, hy, e⟩ => (algebraMap K ℂ).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [NumberField K] in
@[simp] theorem torsionIncl_mk (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (x : K) :
    torsionIncl 𝔞 (Submodule.Quotient.mk x) = (algebraMap K ℂ x : ℂ) := rfl

omit [Algebra K ℂ] in

theorem exists_natCast_mul_mem {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0) (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) * x ∈ 𝔞 := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h𝔞
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b * c}))
  refine ⟨Ideal.absNorm (Ideal.span {b * c}), by simp [hb0, hc0], ?_⟩
  have := (𝔞 : Submodule (𝓞 K) K).smul_mem (e * r) hc
  rw [← map_natCast (algebraMap (𝓞 K) K), ← he]
  rw [← FractionalIdeal.mem_coe]
  convert this using 1
  simp only [Algebra.smul_def, map_mul]
  field_simp

omit [NumberField K] in

theorem exists_eq_of_natCast_mul_mem {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∈ idealSub 𝔞) : ∃ x : K, algebraMap K ℂ x = z := by
  obtain ⟨x, -, e⟩ := mem_idealSub.1 hz
  refine ⟨x / n, ?_⟩
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [map_div₀, e, map_natCast]
  field_simp

theorem exists_uniformised [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2)
    {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0) :
    ∃ (L : PeriodPair) (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ (latticeCurve L).toAffine.Point),
      (∀ z, z ∈ idealSub 𝔞 ↔ z ∈ L.lattice) ∧ IsAnalyticIso ξ ∧
        ∀ z : ℂ, ξ z = latticePoint L z := by
  obtain ⟨L, hL⟩ := Published.exists_isIdealLattice h2 (Units.mk0 𝔞 h𝔞)
  have hΛ : ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ L.lattice := fun z => by
    change _ ↔ z ∈ (L.lattice : Set ℂ)
    rw [hL]
    rfl
  obtain ⟨ξ, h1, h2⟩ := exists_isAnalyticIso (X := latticeCurve L) (C := 1) (one_smul _ _)
    one_ne_zero (fun z => by rw [one_mul, hΛ])
  refine ⟨L, ξ, hΛ, h1, fun z => ?_⟩
  rw [h2, one_mul]
  rcases latticePoint L z with _ | ⟨x, y, h⟩
  · rfl
  · rw [variableChangePoint_some, Affine.Point.some.injEq]
    simp [VariableChange.one_def]

theorem transports_of_exists {σ : ℂ ≃ₐ[K] ℂ} {t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ}
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 𝔟 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    (h𝔟 : 𝔟 = t⁻¹ • 𝔞) {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point}
    {ξ' : (ℂ ⧸ idealSub 𝔟) ≃+ (X.map (σ : ℂ →+* ℂ)).toAffine.Point} (h' : IsAnalyticIso ξ')
    (h : ∀ x, mapPoint X (σ : ℂ →+* ℂ) (ξ (torsionIncl 𝔞 x)) =
      ξ' (torsionIncl 𝔟 (mulEquiv t⁻¹ h𝔞 h𝔟 x))) : Transports σ t h𝔞 ξ := by
  subst h𝔟
  refine ⟨ξ', ⟨h', h⟩, fun η hη => hη.1.ext h' fun n => ?_⟩
  obtain ⟨x, hx⟩ := (mulEquiv t⁻¹ h𝔞 rfl).surjective (Submodule.Quotient.mk (n : K)⁻¹)
  have := (hη.2 x).symm.trans (h x)
  rwa [hx, torsionIncl_mk, map_inv₀, map_natCast] at this

omit [Algebra K ℂ] in
theorem exists_ne_intCast (h2 : Module.finrank ℚ K = 2) : ∃ s : 𝓞 K, ∀ a : ℤ, s ≠ a := by
  by_contra! h
  have h1 : Module.finrank ℤ (𝓞 K) ≤ Module.finrank ℤ ℤ :=
    LinearMap.finrank_le_finrank_of_surjective (f := Algebra.linearMap ℤ (𝓞 K))
      fun s => (h s).imp fun a e => by simpa using e.symm
  rw [RingOfIntegers.rank, h2, Module.finrank_self] at h1
  omega

theorem exists_transports (h2 : Module.finrank ℚ K = 2) (σ : ℂ ≃ₐ[K] ℂ)
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point} (hξ : IsAnalyticIso ξ) :
    ∃ t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ, Transports σ t h𝔞 ξ := by
  obtain ⟨L, C, h⟩ := exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα0, hα, hξα⟩ := hξ.exists_mul h
  obtain ⟨L', g2, g3⟩ := CMRam.exists_conj_lattice σ.toRingEquiv L
  obtain ⟨s, hs, hc⟩ := exists_conjEquiv g2 g3
  let f : 𝓞 K →+* ℂ := (algebraMap K ℂ).comp (algebraMap (𝓞 K) K)
  have hst : ∀ r : 𝓞 K, ∀ l ∈ L.lattice, f r * l ∈ L.lattice := fun r l hl => by
    obtain ⟨x, hx, e⟩ := mem_idealSub.1 ((hα (l / α)).2 (by rwa [mul_div_cancel₀ _ hα0]))
    have := (hα _).1 (algebraMap_mem_idealSub.2 ((𝔞 : Submodule (𝓞 K) K).smul_mem r hx))
    rw [Algebra.smul_def, map_mul, e] at this
    convert this using 1
    simp only [f, RingHom.comp_apply]
    field_simp
  have hmul : ∀ (r : 𝓞 K) {u u' : ℂ}, IsConj L L' σ.toRingEquiv u u' →
      IsConj L L' σ.toRingEquiv (f r * u) (f r * u') := fun r u u' huu => by
    have := huu.mul g2 g3 (hst r)
    rwa [show σ.toRingEquiv (f r) = f r from σ.commutes _] at this
  have hmem : ∀ {u u' : ℂ}, IsConj L L' σ.toRingEquiv u u' → (u ∈ L.lattice ↔ u' ∈ L'.lattice) :=
    fun huu => by simpa using huu.nsmul_mem_iff g2 g3 1
  obtain ⟨r₀, hr₀⟩ := exists_ne_intCast h2
  obtain ⟨I, δ, hI, hδ, hIδ⟩ := ConjCurve.exists_ideal f L'.lattice.toAddSubgroup L'.ω₁ L'.ω₂
    (by simpa using L'.indep.ne_zero 0) (fun z => PeriodPair.mem_lattice)
    (fun r z hz => (hmem (hmul r (.inl ⟨zero_mem _, hz⟩))).1 (by simp)) r₀
    (fun a e => hr₀ a (IsFractionRing.injective (𝓞 K) K ((algebraMap K ℂ).injective
      (e.trans (map_intCast f a).symm))))
  let 𝔟 : FractionalIdeal (𝓞 K)⁰ K := I
  have h𝔟 : 𝔟 ≠ 0 := by simpa [𝔟] using hI
  have hδ' : ∀ z, z ∈ idealSub 𝔟 ↔ δ * z ∈ L'.lattice := fun z => by
    rw [← Submodule.mem_toAddSubgroup, hIδ, mem_idealSub]
    constructor
    · rintro ⟨_, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩, (mul_left_cancel₀ hδ e).symm⟩
  let R : K → K → Prop := fun x y =>
    IsConj L L' σ.toRingEquiv (α * algebraMap K ℂ x) (δ * algebraMap K ℂ y)
  have Rtot : ∀ x, ∃ y, R x y := fun x => by
    obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L (α * algebraMap K ℂ x)))
    have hw' := (hc _ _).2 hw.symm
    obtain ⟨n, hn, hx⟩ := exists_natCast_mul_mem h𝔞 x
    have h1 := (hα _).1 (algebraMap_mem_idealSub.2 hx)
    rw [map_mul, map_natCast, mul_left_comm, hw'.nsmul_mem_iff g2 g3] at h1
    obtain ⟨y, hy⟩ := exists_eq_of_natCast_mul_mem (𝔞 := 𝔟) hn (z := w / δ)
      ((hδ' _).2 (by convert h1 using 1; field_simp))
    exact ⟨y, by simp only [R]; rwa [hy, mul_div_cancel₀ _ hδ]⟩
  have Rsurj : ∀ y, ∃ x, R x y := fun y => by
    obtain ⟨w, hw⟩ := latticePoint_surjective L (s.symm (latticePoint L' (δ * algebraMap K ℂ y)))
    have hw' := (hc w _).2 (by rw [hw, s.apply_symm_apply])
    obtain ⟨n, hn, hy⟩ := exists_natCast_mul_mem h𝔟 y
    have h1 := (hδ' _).1 (algebraMap_mem_idealSub.2 hy)
    rw [map_mul, map_natCast, mul_left_comm, ← hw'.nsmul_mem_iff g2 g3] at h1
    obtain ⟨x, hx⟩ := exists_eq_of_natCast_mul_mem (𝔞 := 𝔞) hn (z := w / α)
      ((hα _).2 (by convert h1 using 1; field_simp))
    exact ⟨x, by simp only [R]; rwa [hx, mul_div_cancel₀ _ hα0]⟩
  have Radd : ∀ {x y x' y'}, R x y → R x' y' → R (x + x') (y + y') := fun a b => by
    simpa only [R, map_add, mul_add] using a.add g2 g3 b
  have Rsmul : ∀ (r : 𝓞 K) {x y}, R x y → R (r • x) (r • y) := fun r x y a => by
    have := hmul r a
    rw [mul_left_comm, mul_left_comm (f r)] at this
    simp only [R, Algebra.smul_def, map_mul]
    exact this
  have Rmem : ∀ {x y}, R x y → (x ∈ 𝔞 ↔ y ∈ 𝔟) := fun a => by
    rw [← algebraMap_mem_idealSub, ← algebraMap_mem_idealSub, hα, hδ', hmem a]
  have Runiq : ∀ {x y y'}, R x y → R x y' → (Submodule.Quotient.mk y :
      K ⧸ (𝔟 : Submodule (𝓞 K) K)) = Submodule.Quotient.mk y' := fun a b => by
    have := Rmem (Radd a (Rsmul (-1) b))
    rw [neg_one_smul, neg_one_smul, add_neg_cancel, ← sub_eq_add_neg] at this
    exact (Submodule.Quotient.eq _).2 (this.1 (FractionalIdeal.zero_mem _))
  choose F hF using Rtot
  let Φ : K →ₗ[𝓞 K] K ⧸ (𝔟 : Submodule (𝓞 K) K) :=
    { toFun := fun x => Submodule.Quotient.mk (F x)
      map_add' := fun x y => Runiq (hF _) (Radd (hF x) (hF y))
      map_smul' := fun r x => Runiq (hF _) (Rsmul r (hF x)) }
  have hker : (𝔞 : Submodule (𝓞 K) K) = LinearMap.ker Φ := by
    ext x
    exact (Rmem (hF x)).trans (Submodule.Quotient.mk_eq_zero _).symm
  have hΦ : Function.Surjective Φ := fun q => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := Rsurj y
    exact ⟨x, Runiq (hF x) hx⟩
  obtain ⟨u, ⟨hu, hφ⟩, -⟩ := existsUnique_mulEquiv h𝔞
    ((Submodule.quotEquivOfEq _ _ hker).trans (Φ.quotKerEquivOfSurjective hΦ))
  have h' : C.map (σ : ℂ →+* ℂ) • X.map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [map_variableChange, h]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨ξ', hξ', e'⟩ := exists_isAnalyticIso h' hδ hδ'
  obtain ⟨t, rfl⟩ : ∃ t, u = t⁻¹ := ⟨u⁻¹, (inv_inv u).symm⟩
  refine ⟨t, transports_of_exists h𝔞 hu hξ' fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← hφ]
  change _ = ξ' (torsionIncl 𝔟 (Submodule.Quotient.mk (F x)))
  rw [torsionIncl_mk, torsionIncl_mk, hξα, e', mapPoint_variableChangePoint _ h h' hs,
    (hc _ _).1 (hF x)]

theorem Transports.unique {σ : ℂ ≃ₐ[K] ℂ} {t t' : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ}
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {h𝔞 : 𝔞 ≠ 0}
    {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point} (h : Transports σ t h𝔞 ξ)
    (h' : Transports σ t' h𝔞 ξ) :
    ∃ c : Kˣ, t = IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 K) K c * t' := by
  obtain ⟨η, ⟨hη, e⟩, -⟩ := h
  obtain ⟨η', ⟨hη', e'⟩, -⟩ := h'
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve (X.map (σ : ℂ →+* ℂ))
  obtain ⟨α, hα0, hα, a⟩ := hη.exists_mul hC
  obtain ⟨β, hβ0, hβ, b⟩ := hη'.exists_mul hC
  have h0 := Idele.smul_ne_zero t⁻¹ h𝔞
  obtain ⟨x₀, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h0
  have hx1 : algebraMap K ℂ (algebraMap (𝓞 K) K x₀) ≠ 0 := by simpa using hx0
  obtain ⟨y₀, -, hy⟩ := mem_idealSub.1 ((hβ (α * algebraMap K ℂ (algebraMap (𝓞 K) K x₀) / β)).2
    (by rw [mul_div_cancel₀ _ hβ0]; exact (hα _).1 (algebraMap_mem_idealSub.2 hx)))
  obtain ⟨c, hc⟩ : ∃ c : K, β * algebraMap K ℂ c = α :=
    ⟨y₀ / algebraMap (𝓞 K) K x₀, by rw [map_div₀, hy]; field_simp⟩
  have hc0 : c ≠ 0 := by rintro rfl; exact hα0 (by simpa using hc.symm)
  set u := IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 K) K (Units.mk0 c hc0) with hu
  have hJ : t'⁻¹ • 𝔞 = u • t⁻¹ • 𝔞 := by
    ext y
    rw [smul_def u, hu, idealOf_unitEmbedding, FractionalIdeal.mem_singleton_mul]
    obtain ⟨y, rfl⟩ := mul_left_surjective₀ hc0 y
    rw [← algebraMap_mem_idealSub, hβ, map_mul, ← mul_assoc, hc, ← hα, algebraMap_mem_idealSub]
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', h, e⟩ => mul_left_cancel₀ hc0 e ▸ h⟩
  have hJ' : t'⁻¹ • 𝔞 = (u * t⁻¹) • 𝔞 := by rw [mul_smul, hJ]
  have key : t'⁻¹ = u * t⁻¹ := by
    refine mulEquiv_injective h𝔞 rfl hJ' ?_
    rw [mulEquiv_mul u t⁻¹ h𝔞 h0 rfl hJ]
    ext q
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (mulEquiv t⁻¹ h𝔞 rfl q)
    obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ (mulEquiv t'⁻¹ h𝔞 rfl q)
    have := (e' q).symm.trans (e q)
    rw [← hy, ← hy', torsionIncl_mk, torsionIncl_mk, a, b,
      (variableChangePoint_bijective C hC).1.eq_iff, latticePoint_eq_iff, ← hc, mul_assoc,
      ← mul_sub, ← hβ, ← map_mul, ← map_sub, algebraMap_mem_idealSub] at this
    rw [LinearEquiv.trans_apply, ← hy, ← hy']
    exact ((Submodule.Quotient.eq _).2 this).trans
      (mulEquiv_unitEmbedding_mk (Units.mk0 c hc0) h0 hJ y).symm
  exact ⟨Units.mk0 c hc0, by
    rw [← hu, mul_comm, ← inv_mul_eq_iff_eq_mul, ← eq_mul_inv_iff_mul_eq]; exact key⟩

theorem IsAnalyticIso.j_eq {X : WeierstrassCurve ℂ} [X.IsElliptic] {Λ : AddSubgroup ℂ}
    {ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point} (hξ : IsAnalyticIso ξ) {M : PeriodPair}
    (hM : ∀ z, z ∈ Λ ↔ z ∈ M.lattice) : X.j = (latticeCurve M).j := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα0, hα, -⟩ := hξ.exists_mul hC
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau M
  have hj : X.j = (latticeCurve L).j := by
    rw [← X.variableChange_j C]
    congr 1
  rw [hj, latticeCurve_j ha h, latticeCurve_j (mul_ne_zero hα0 ha) (τ := τ) fun x => ?_]
  obtain ⟨x, rfl⟩ := mul_left_surjective₀ hα0 x
  simp only [← hα, hM, h, mul_assoc, mul_right_inj' hα0]

theorem Transports.map_j {σ : ℂ ≃ₐ[K] ℂ} {t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ}
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {h𝔞 : 𝔞 ≠ 0}
    {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point} (h : Transports σ t h𝔞 ξ) {M : PeriodPair}
    (hM : ∀ z, z ∈ idealSub (t⁻¹ • 𝔞) ↔ z ∈ M.lattice) : σ X.j = (latticeCurve M).j := by
  obtain ⟨η, ⟨hη, -⟩, -⟩ := h
  exact (X.map_j (σ : ℂ →+* ℂ)).symm.trans (hη.j_eq hM)

omit [Algebra K ℂ] in

theorem finitePart_inr (t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
    finitePart (K := K) (Units.map (MonoidHom.inr (InfiniteAdeleRing K) _) t) = t :=
  Units.ext rfl

end Ideals

end GlobalTheory.EllipticCM
