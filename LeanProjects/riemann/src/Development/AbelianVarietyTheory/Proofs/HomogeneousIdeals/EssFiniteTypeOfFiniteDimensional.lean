import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIntegralRatioRingIffMemAdjoin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG valR lbPow LBIso IsProjOver isProper_str)
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TupleCone GlobalTheory.TuplePoint

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TupleNorm

variable {L : Type} [Field L]

open Polynomial in

theorem pow_mem_forms (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*}
    (t : σ → L) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Fintype σ] {e : ℕ}
    (he : 0 < e) (hv : ∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) {a : L}
    (ha : a ∈ piece o t e) :
    ∃ n, ∃ c : σ → L, (∀ i, c i ∈ piece o t e ^ n) ∧ a ^ (n + 1) = ∑ i, t i ^ e * c i := by
  obtain ⟨d, hd, h⟩ := exists_piece_succ_eq o t
  let A := integralClosure (cone o t) L[X]
  let τ : σ → A := fun i =>
    ⟨C (t i) * X, isIntegral_algebraMap (x := (⟨_, C_mul_X_mem_cone i⟩ : cone o t))⟩
  let I : Ideal A := Ideal.span (Set.range fun i => τ i ^ e)
  have h1 : ∀ m, ∀ b ∈ Submodule.span o (Set.range t) * piece o t m,
      ∃ q : A, q ∈ I.radical ∧ (q : L[X]) = C b * X ^ (m + 1) := by
    intro m b hb
    induction hb using Submodule.mul_induction_on' with
    | add x _ y _ hx hy =>
      obtain ⟨q, hq, hx⟩ := hx
      obtain ⟨q', hq', hy⟩ := hy
      exact ⟨q + q', add_mem hq hq', by rw [AddMemClass.coe_add, hx, hy, map_add, add_mul]⟩
    | mem_mul_mem x hx y hy =>
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have : τ i ∈ I.radical := ⟨e, Ideal.subset_span ⟨i, rfl⟩⟩
        refine ⟨τ i * ⟨_, mem_piece.mp hy⟩, I.radical.mul_mem_right _ this, ?_⟩
        change (C (t i) * X) * (C y * X ^ m) = _
        rw [map_mul]; ring
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add x x' _ _ hx hx' =>
        obtain ⟨q, hq, hx⟩ := hx
        obtain ⟨q', hq', hy⟩ := hx'
        exact ⟨q + q', add_mem hq hq',
          by rw [AddMemClass.coe_add, hx, hy, add_mul, map_add, add_mul]⟩
      | smul c x _ hx =>
        obtain ⟨q, hq, hx⟩ := hx
        refine ⟨algebraMap (cone o t) A (algebraMap o _ c) * q, I.radical.mul_mem_left _ hq, ?_⟩
        rw [MulMemClass.coe_mul, hx]
        change algebraMap o L[X] c * _ = _
        rw [Algebra.smul_def, Polynomial.algebraMap_apply]; simp only [map_mul]; ring
  obtain ⟨m, hm⟩ : ∃ m, (d + 1) * e = m + 1 := Nat.exists_eq_add_one.mpr (by positivity)
  have hdm : d ≤ m := by nlinarith
  have h3 : a ^ (d + 1) ∈ piece o t (m + 1) := by
    rw [← hm, hv _ d.succ_pos]; exact Submodule.pow_mem_pow _ ha _
  rw [h m hdm] at h3
  obtain ⟨q, ⟨N, hN⟩, hq⟩ := h1 m _ h3
  obtain ⟨p, hp⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (I.pow_mem_of_pow_mem hN (Nat.le_add_right N 2))
  obtain ⟨n, hn⟩ : ∃ n, (d + 1) * (N + 2) = n + 1 := Nat.exists_eq_add_one.mpr (by positivity)
  have hn0 : 0 < n := by nlinarith
  refine ⟨n, fun i => (p i : L[X]).coeff (n * e),
    fun i => hv n hn0 ▸ isIntegral_cone_iff.mp (p i).2 _, ?_⟩
  have h4 := congrArg (fun q : A => (q : L[X]).coeff (n * e + e)) hp
  simp only [τ, hq, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
    finsetSum_coeff, mul_pow, ← C_pow, ← pow_mul, ← mul_assoc, coeff_mul_X_pow, coeff_mul_C] at h4
  rw [hn, ← hm, show (d + 1) * e * (N + 2) = n * e + e by rw [mul_right_comm, hn]; ring,
    coeff_C_mul_X_pow, if_pos rfl] at h4
  rw [← h4]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem isIntegralElem_iff_of_range_eq {o A : Type*} [CommRing o] [Algebra o L] [CommRing A]
    (φ : A →+* L) (S : Subalgebra o L) (h : Set.range φ = S) (a : L) :
    φ.IsIntegralElem a ↔ IsIntegral S a := by
  let ψ : A →+* S := φ.codRestrict S fun x => show φ x ∈ (S : Set L) from h ▸ ⟨x, rfl⟩
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨x, hx⟩ : s.1 ∈ Set.range φ := h ▸ s.2
    exact ⟨x, Subtype.ext hx⟩
  have e : φ = (algebraMap S L).comp ψ := rfl
  constructor
  · rintro ⟨p, hp, hpa⟩
    exact ⟨p.map ψ, hp.map _, by rwa [Polynomial.eval₂_map]⟩
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨q, hq, -, hq'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p).mpr (Polynomial.map_surjective ψ hψ p)) hp
    exact ⟨q, hq', by rwa [← hq, Polynomial.eval₂_map] at hpa⟩

theorem mem_range_valMap_toNormalization {Y : Scheme.{0}} (f : Sp L ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⊤ ≤ f ⁻¹ᵁ V)
    (h' : ⊤ ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V)) (a : L) :
    a ∈ Set.range (valMap f.toNormalization _ h').hom ↔ (valMap f V h).hom.IsIntegralElem a := by
  let := (f.app V).hom.toAlgebra
  have h₀ : ⊤ ≤ 𝟙 (Sp L) ⁻¹ᵁ (f ⁻¹ᵁ V) := h
  let v := (valMap (𝟙 (Sp L)) (f ⁻¹ᵁ V) h₀).hom
  have hv₁ : Function.Injective v := valMap_injective _ h₀
  have hv₂ : Function.Surjective v := fun x =>
    ⟨_, valMap_baseRingHom (o := L) (f := 𝟙 _) ((Category.id_comp _).trans (Spec.map_id _).symm)
      h₀ x⟩
  have e₁ : (valMap f V h).hom = v.comp (f.app V).hom := RingHom.ext fun s => by
    have := valR_comp (𝟙 (Sp L)) f V s
    rwa [Category.id_comp, valR_eq _ _ h, valR_eq _ _ h₀] at this
  have e₂ (s) : (valMap f.toNormalization _ h').hom s =
      v ((f.normalizationObjIso hV).hom.hom s).1 := by
    have := valR_appLE (𝟙 (Sp L)) f.toNormalization (U := f.fromNormalization ⁻¹ᵁ V)
      (V := f ⁻¹ᵁ V) (le_top.trans h') h₀ s
    rw [Category.id_comp, valR_eq _ _ h', valR_eq _ _ h₀, ← f.normalizationObjIso_hom_val hV]
      at this
    exact this.symm
  rw [e₁]
  constructor
  · rintro ⟨s, rfl⟩
    rw [e₂]
    exact RingHom.IsIntegralElem.map ((f.normalizationObjIso hV).hom.hom s).2 v
  · intro ha
    obtain ⟨b, rfl⟩ := hv₂ a
    obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hV).hom).2
      ⟨b, RingHom.IsIntegralElem.of_map hv₁ ha⟩
    exact ⟨s, (e₂ s).trans (congrArg (fun x => v x.1) hs)⟩

variable (o : Type) [CommRing o] [Algebra o L] {r m : ℕ} (t : Fin (r + 1) → L) (ht : t ≠ 0)

abbrev Cl : Scheme.{0} := (point o t ht).image

abbrev clι : Cl o t ht ⟶ PSpace o r := (point o t ht).imageι

abbrev clPoint : Sp L ⟶ Cl o t ht := (point o t ht).toImage

abbrev Nm : Scheme.{0} := (clPoint o t ht).normalization

abbrev nmPoint : Sp L ⟶ Nm o t ht := (clPoint o t ht).toNormalization

abbrev toCl : Nm o t ht ⟶ Cl o t ht := (clPoint o t ht).fromNormalization

abbrev toProj : Nm o t ht ⟶ PSpace o r := toCl o t ht ≫ clι o t ht

abbrev str : Nm o t ht ⟶ Sp o := toProj o t ht ≫ PSpace.str o r

abbrev twist : LB (Nm o t ht) := (O1 o r).pull (toProj o t ht)

theorem nmPoint_toProj : nmPoint o t ht ≫ toProj o t ht = point o t ht := by simp

theorem nmPoint_str : nmPoint o t ht ≫ str o t ht = spMap (algebraMap o L) := by
  rw [← Category.assoc, nmPoint_toProj, point_str]

theorem isIntegral_Nm : IsIntegral (Nm o t ht) := inferInstance

theorem isNormalScheme_Nm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Nm o t ht) :=
  IsNormalScheme.pred _

theorem isAffineOpen_preimage_chart (i : Fin (r + 1)) :
    IsAffineOpen (toProj o t ht ⁻¹ᵁ chart o r i) :=
  (isAffineOpen_chart o r i).preimage _

theorem iSup_preimage_chart :
    ⨆ i : {i // t i ≠ 0}, toProj o t ht ⁻¹ᵁ chart o r i.1 = ⊤ := by
  refine top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := exists_mem_chart o r (toProj o t ht x)
  exact ⟨⟨i, ne_zero_of_le (nmPoint_toProj o t ht)
    (le_preimage_of_mem (W := toProj o t ht ⁻¹ᵁ chart o r i) _ hi) le_rfl⟩, hi⟩

variable {o t ht} in

theorem mem_range_valMap_iff {i : Fin (r + 1)} {W : (Nm o t ht).Opens}
    (hW : W = toProj o t ht ⁻¹ᵁ chart o r i) (h : ⊤ ≤ nmPoint o t ht ⁻¹ᵁ W) (a : L) :
    a ∈ Set.range (valMap (nmPoint o t ht) W h).hom ↔ IsIntegral (ratioRing o t i) a := by
  subst hW
  have h₁ : ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i :=
    (le_point_preimage_iff i).2 (ne_zero_of_le (nmPoint_toProj o t ht) h le_rfl)
  have h₂ : ⊤ ≤ clPoint o t ht ⁻¹ᵁ (clι o t ht ⁻¹ᵁ chart o r i) := by
    rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι]
  refine (mem_range_valMap_toNormalization (clPoint o t ht)
    ((isAffineOpen_chart o r i).preimage (clι o t ht)) h₂ h a).trans
    (isIntegralElem_iff_of_range_eq _ _ ?_ a)
  rw [ratioRing, ← range_valMap_point h₁,
    ← ((clι o t ht).app_surjective _ (isAffineOpen_chart o r i)).range_comp]
  congr 1
  funext s
  have := valR_comp (clPoint o t ht) (clι o t ht) (chart o r i) s
  rw [Scheme.Hom.toImage_imageι, valR_eq _ _ h₁, valR_eq _ _ h₂] at this
  exact this.symm

theorem exists_hom_of_isIntegral {z : Fin (m + 1) → L} (hz : z ≠ 0)
    (c : {i // t i ≠ 0} → Fin (m + 1)) (hc : ∀ i, z (c i) ≠ 0)
    (h : ∀ i k, IsIntegral (ratioRing o t i.1) (z k / z (c i))) :
    ∃ φ : Nm o t ht ⟶ PSpace o m, nmPoint o t ht ≫ φ = point o z hz ∧
      φ ≫ PSpace.str o m = str o t ht ∧
      ∀ i, toProj o t ht ⁻¹ᵁ chart o r i.1 ≤ φ ⁻¹ᵁ chart o m (c i) := by
  have hη (i : {i // t i ≠ 0}) := le_preimage_chart (nmPoint_toProj o t ht) i.2
  choose u hu using fun i k => (mem_range_valMap_iff rfl (hη i) _).2 (h i k)
  exact exists_hom_of_coords _ _ (nmPoint_str o t ht) _ (iSup_preimage_chart o t ht) hη hz c hc u
    fun i k => (valR_eq _ _ (hη i) _).trans (hu i k)

theorem exists_hom_Cl_of_factor {z : Fin (m + 1) → L} (hz : z ≠ 0) {τ : Type*} (z' : τ → L)
    (p : Fin (r + 1) ≃ Fin (m + 1) × τ) (hp : ∀ i, t i = z (p i).1 * z' (p i).2) :
    ∃ φ : Nm o t ht ⟶ Cl o z hz, nmPoint o t ht ≫ φ = clPoint o z hz ∧
      φ ≫ clι o z hz ≫ PSpace.str o m = str o t ht := by
  obtain ⟨φ, h₁, h₂, -⟩ := exists_hom_of_isIntegral o t ht hz (fun i => (p i.1).1)
    (fun i => left_ne_zero_of_mul (hp i.1 ▸ i.2)) fun i k => by
      have : z k / z (p i.1).1 = t (p.symm (k, (p i.1).2)) / t i.1 := by
        rw [hp, hp i.1, Equiv.apply_symm_apply,
          mul_div_mul_right _ _ (right_ne_zero_of_mul (hp i.1 ▸ i.2))]
      rw [this]
      exact isIntegral_algebraMap
        (x := (⟨_, Algebra.subset_adjoin ⟨_, rfl⟩⟩ : ratioRing o t i.1))
  have := IsSchemeTheoreticallyDominant.of_isDominant (nmPoint o t ht)
  refine ⟨closureLift _ φ (nmPoint o t ht) (𝟙 _) (by simpa using h₁), by simp, ?_⟩
  rw [closureLift_imageι_assoc, h₂]

def ratioField : Subfield L :=
  Subfield.closure (Set.range (algebraMap o L) ∪
    Set.range fun p : Fin (r + 1) × Fin (r + 1) => t p.1 / t p.2)

variable {t} in

theorem ratioField_eq {i : Fin (r + 1)} (hi : t i ≠ 0) :
    ratioField o t = Subfield.closure (ratioRing o t i : Set L) := by
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_le.mpr fun x hx => ?_)
  · have h (k) : t k / t i ∈ Subfield.closure (ratioRing o t i : Set L) :=
      Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨p, rfl⟩)
    · exact Subfield.subset_closure ((ratioRing o t i).algebraMap_mem a)
    · have := div_mem (h p.1) (h p.2)
      rwa [div_div_div_cancel_right₀ hi] at this
  · induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Subfield.subset_closure (Or.inr ⟨(k, i), rfl⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

variable {t} in

theorem isAlgebraic_and_essFiniteType [FiniteDimensional (ratioField o t) L] {i : Fin (r + 1)}
    (hi : t i ≠ 0) :
    Algebra.IsAlgebraic (ratioRing o t i) L ∧ Algebra.EssFiniteType (ratioRing o t i) L := by
  have hK := ratioField_eq o hi
  let : Algebra (ratioRing o t i) (ratioField o t) :=
    ((algebraMap (ratioRing o t i) L).codRestrict (ratioField o t) fun x =>
      hK ▸ Subfield.subset_closure x.2).toAlgebra
  have : IsScalarTower (ratioRing o t i) (ratioField o t) L := .of_algebraMap_eq' rfl
  have : FaithfulSMul (ratioRing o t i) (ratioField o t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h =>
      Subtype.ext (congrArg (fun a : ratioField o t => (a : L)) h)
  have : IsFractionRing (ratioRing o t i) (ratioField o t) := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, ha, b, hb, h⟩ := Subfield.mem_closure_iff.mp (hK.le x.2)
    have e := Subring.closure_eq (ratioRing o t i).toSubring
    exact ⟨⟨a, e.le ha⟩, ⟨b, e.le hb⟩, Subtype.ext h.symm⟩
  have : Algebra.EssFiniteType (ratioRing o t i) (ratioField o t) :=
    .of_isLocalization _ (nonZeroDivisors _)
  exact ⟨(IsFractionRing.comap_isAlgebraic_iff (K := ratioField o t)).mpr inferInstance,
    .comp _ (ratioField o t) _⟩

include ht in

theorem essFiniteType_of_finiteDimensional [FiniteDimensional (ratioField o t) L] :
    Algebra.EssFiniteType o L := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  have := (isAlgebraic_and_essFiniteType o hi).2
  have : Algebra.FiniteType o (ratioRing o t i) := .adjoin_of_finite (Set.finite_range _)
  exact .comp o (ratioRing o t i) L

theorem isIso_stalkMap_nmPoint [FiniteDimensional (ratioField o t) L] (x : Sp L) :
    IsIso ((nmPoint o t ht).stalkMap x) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  have := (isAlgebraic_and_essFiniteType o hi).1
  have h := le_preimage_chart (nmPoint_toProj o t ht) hi
  let := (valMap (nmPoint o t ht) _ h).hom.toAlgebra
  have : FaithfulSMul Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (valMap_injective _ h)
  have : IsFractionRing Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i) L := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨y, hy, hyx⟩ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ratioRing o t i) x).exists_integral_multiple
    obtain ⟨a, ha⟩ := (mem_range_valMap_iff rfl h _).2 hyx
    obtain ⟨b, hb⟩ := (mem_range_valMap_iff rfl h _).2 (isIntegral_algebraMap (x := y))
    refine ⟨a, b, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ha, hb, Algebra.smul_def]
    exact (mul_div_cancel_left₀ _ fun h0 => hy (Subtype.ext h0)).symm
  have h1 : IsPreimmersion (Spec.map (valMap (nmPoint o t ht) _ h)) :=
    IsPreimmersion.of_isLocalization (R := Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i)) (S := L)
      (nonZeroDivisors _)
  have h2 : IsPreimmersion (nmPoint o t ht) := by
    rw [← specMap_valMap_fromSpec (isAffineOpen_preimage_chart o t ht i) _ h]
    infer_instance
  have hη : nmPoint o t ht x = genericPoint _ := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec _)
    rw [isGenericPoint_def, ← (nmPoint o t ht).denseRange.closure_range]
    congr 1
    ext y
    exact ⟨fun hy => ⟨x, hy.symm⟩, fun ⟨x', hy⟩ => by rw [← hy, Subsingleton.elim x' x]; rfl⟩
  have hf : IsField ((Nm o t ht).presheaf.stalk (nmPoint o t ht x)) := by
    rw [hη]
    exact Field.toIsField (Nm o t ht).functionField
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, (nmPoint o t ht).stalkMap_surjective _⟩
  let := hf.toField
  exact RingHom.injective ((nmPoint o t ht).stalkMap x).hom

theorem exists_isClosedImmersion [IsFinite (toCl o t ht)] {e : ℕ} (he : 0 < e)
    (hv : ∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) {z : Fin (m + 1) → L} (hz : z ≠ 0)
    (hs : Submodule.span o (Set.range z) = piece o t e) (c : Fin (r + 1) → Fin (m + 1))
    (hc : ∀ j, z (c j) = t j ^ e) :
    ∃ φ : Nm o t ht ⟶ PSpace o m, IsClosedImmersion φ ∧ nmPoint o t ht ≫ φ = point o z hz ∧
      φ ≫ PSpace.str o m = str o t ht ∧
      ∀ j, φ ⁻¹ᵁ chart o m (c j) = toProj o t ht ⁻¹ᵁ chart o r j := by
  have hπ := nmPoint_toProj o t ht
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_hom_of_isIntegral o t ht hz (fun i => c i.1)
    (fun i => hc i.1 ▸ pow_ne_zero e i.2) fun i k =>
      hc i.1 ▸ isIntegral_div_of_mem_piece i.1 (hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  have h₄ (j) : φ ⁻¹ᵁ chart o m (c j) = toProj o t ht ⁻¹ᵁ chart o r j := by
    refine le_antisymm (fun x hx => ?_) fun x hx =>
      h₃ ⟨j, ne_zero_of_le hπ (le_preimage_of_mem _ hx) le_rfl⟩ hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((iSup_preimage_chart o t ht).ge (Set.mem_univ x))
    have e₁ : pullRatio φ _ (c i.1) (h₃ i) (c j) = pullRatio (toProj o t ht) _ i.1 le_rfl j ^ e :=
      ext_of_dense (nmPoint o t ht) fun h => by
        rw [valR_pow _ _ h, valR_pullRatio h₁ h, valR_pullRatio hπ h, hc, hc, div_pow]
    have e₂ := basicOpen_pullRatio (hi := h₃ i) (j := c j)
    rw [e₁, Scheme.basicOpen_pow _ _ he, basicOpen_pullRatio] at e₂
    exact (e₂.ge ⟨hi, hx⟩).2
  refine ⟨φ, ?_, h₁, h₂, h₄⟩
  have := isProper_str o r
  have := isProper_str o m
  have : IsProper (φ ≫ PSpace.str o m) := by rw [h₂]; infer_instance
  have : IsProper φ := .of_comp φ (PSpace.str o m)
  refine isClosedImmersion_of_cover φ φ.isClosedMap.isClosed_range
    (fun i : {i // t i ≠ 0} => chart o m (c i.1)) (fun i => isAffineOpen_chart o m _)
    (fun i => h₄ i.1 ▸ isAffineOpen_preimage_chart o t ht i.1) (fun i => ?_)
    (by simpa only [h₄] using iSup_preimage_chart o t ht)
  rw [Scheme.Hom.app_eq_appLE, surjective_appLE_chart_iff]
  intro s
  have h : ⊤ ≤ nmPoint o t ht ⁻¹ᵁ (φ ⁻¹ᵁ chart o m (c i.1)) := h₄ i.1 ▸ le_preimage_chart hπ i.2
  have h₅ := (isIntegral_ratioRing_iff_mem_adjoin he hs hv i.2).1
    ((mem_range_valMap_iff (h₄ i.1) h _).1 ⟨s, rfl⟩)
  rw [Algebra.adjoin_range_eq_range_aeval] at h₅
  obtain ⟨p, hp⟩ := h₅
  refine ⟨p, valMap_injective _ h ?_⟩
  rw [valMap_eval₂Hom (by rw [h₂, nmPoint_str]) h]
  simp only [valR_pullRatio h₁ h, hc]
  exact hp

section Dedekind

variable [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L]

theorem isFinite_toCl : IsFinite (toCl o t ht) := by
  have := isProper_str o r
  refine isFinite_fromNormalization_of_genericPoints (o := .of o) _ (clι o t ht ≫ PSpace.str o r)
    (fun x _ => charZero_of_injective_ringHom
      ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation x).hom.injective) fun x _ => ?_
  have h : ((clPoint o t ht ≫ clι o t ht ≫ PSpace.str o r).stalkMap x).hom.EssFiniteType := by
    rw [Scheme.Hom.toImage_imageι_assoc, point_str]
    exact essFiniteType_stalkMap_SpecMap _ (RingHom.essFiniteType_algebraMap.mpr ‹_›) x
  rw [Scheme.Hom.stalkMap_comp] at h
  exact RingHom.EssFiniteType.residueFieldMap (.of_comp _ h)

theorem exists_iso_Cl : ∃ (e : ℕ) (_ : 0 < e) (M : ℕ) (z : Fin (M + 1) → L) (hz : z ≠ 0),
    (∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) ∧
    Submodule.span o (Set.range z) = piece o t e ∧ (∀ j, t j ^ e ∈ Set.range z) ∧
    ∃ ν : Nm o t ht ≅ Cl o z hz, nmPoint o t ht ≫ ν.hom = clPoint o z hz ∧
      (ν.hom ≫ clι o z hz) ≫ PSpace.str o M = str o t ht ∧
      (∀ j k, z k = t j ^ e →
        (ν.hom ≫ clι o z hz) ⁻¹ᵁ chart o M k = toProj o t ht ⁻¹ᵁ chart o r j) ∧
      ∃ w : LB.Iso (lbPow (twist o t ht) e) ((O1 o M).pull (ν.hom ≫ clι o z hz)), w.IsGen ∧
        ∀ (k : PUnit → Fin (M + 1)) (j : PUnit → PUnit → Fin (r + 1)),
          ⊤ ≤ nmPoint o t ht ⁻¹ᵁ (((O1 o M).pull (ν.hom ≫ clι o z hz)).U k ⊓
            (lbPow (twist o t ht) e).U j) →
          valR (nmPoint o t ht) _ (w.s (k, j)).val =
            t (j PUnit.unit PUnit.unit) ^ e / z (k PUnit.unit) := by
  classical
  have := isFinite_toCl o t ht
  obtain ⟨e, he, hv⟩ := exists_piece_mul_eq_pow o t
  obtain ⟨M, z, c, hs, hc⟩ := exists_spanning_tuple o t e
  have hz : z ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    exact Function.ne_iff.mpr ⟨c i, hc i ▸ pow_ne_zero e hi⟩
  obtain ⟨φ, _, h₁, h₂, h₃⟩ := exists_isClosedImmersion o t ht he hv hz hs c hc
  have := IsSchemeTheoreticallyDominant.of_isDominant (nmPoint o t ht)
  let ν := (asIso (closureToClosed (point o z hz) (nmPoint o t ht) φ h₁)).symm
  have hν : ν.hom ≫ clι o z hz = φ := by simp [ν, IsIso.inv_comp_eq]
  refine ⟨e, he, M, z, hz, hv, hs, fun j => ⟨c j, hc j⟩, ν, by simp [ν, IsIso.comp_inv_eq], ?_⟩
  rw [hν]
  refine ⟨h₂, fun j k hk => ?_,
    exists_iso_lbPow (nmPoint_toProj o t ht) h₁ c hc fun j => (h₃ j).ge⟩
  obtain ⟨φ', -, h₁', -, h₃'⟩ := exists_isClosedImmersion o t ht he hv hz hs (Function.update c j k)
    fun j' => by
      by_cases h : j' = j
      · rw [h, Function.update_self, hk]
      · rw [Function.update_of_ne h, hc]
  rw [ext_of_isDominant (nmPoint o t ht) (h₁.trans h₁'.symm), ← h₃' j, Function.update_self]

theorem isProjOver_str : IsProjOver (str o t ht) := by
  obtain ⟨e, -, M, z, hz, -, -, -, ν, -, h, -⟩ := exists_iso_Cl o t ht
  exact ⟨M, ν.hom ≫ clι o z hz, inferInstance, h⟩

theorem exists_pow_twist_veryAmple : ∃ (e : ℕ) (_ : 0 < e) (M : ℕ) (φ : Nm o t ht ⟶ PSpace o M),
    IsClosedImmersion φ ∧ φ ≫ PSpace.str o M = str o t ht ∧
      LBIso (lbPow (twist o t ht) e) ((O1 o M).pull φ) := by
  obtain ⟨e, he, M, z, hz, -, -, -, ν, -, h, -, w, hw, -⟩ := exists_iso_Cl o t ht
  exact ⟨e, he, M, ν.hom ≫ clι o z hz, inferInstance, h, w, hw⟩

end Dedekind

theorem normalization_closure_projective [IsDedekindDomain o] [CharZero o] [FaithfulSMul o L]
    [FiniteDimensional (ratioField o t) L] :
    (∀ p : Polynomial L, IsIntegral (cone o t) p ↔ ∀ n, p.coeff n ∈ piece o t n) ∧
    Module.Finite (cone o t) (integralClosure (cone o t) (Polynomial L)) ∧
    piece o t 0 = (integralClosure o L).toSubmodule ∧ (∀ n, (piece o t n).FG) ∧
    IsIntegral (Nm o t ht) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Nm o t ht) ∧
    (∀ x, IsIso ((nmPoint o t ht).stalkMap x)) ∧ IsFinite (toCl o t ht) ∧
    (∀ i, t i ≠ 0 → ∃ h : ⊤ ≤ nmPoint o t ht ⁻¹ᵁ (toProj o t ht ⁻¹ᵁ chart o r i),
      Function.Injective (valMap (nmPoint o t ht) _ h).hom ∧
      Set.range (valMap (nmPoint o t ht) _ h).hom = integralClosure (ratioRing o t i) L) ∧
    IsProjOver (str o t ht) ∧
    ∃ (e : ℕ) (_ : 0 < e) (M : ℕ) (z : Fin (M + 1) → L) (hz : z ≠ 0),
      (∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) ∧
      Submodule.span o (Set.range z) = piece o t e ∧ (∀ j, t j ^ e ∈ Set.range z) ∧
      (∀ i, t i ≠ 0 → ∀ f, f ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔
        IsIntegral (ratioRing o t i) f) ∧
      (∀ k, ∃ (n : ℕ) (c : Fin (r + 1) → L), (∀ i, c i ∈ Submodule.span o (Set.range z) ^ n) ∧
        z k ^ (n + 1) = ∑ i, t i ^ e * c i) ∧
      (⨆ k : {k // ∃ j, t j ≠ 0 ∧ z k = t j ^ e}, clι o z hz ⁻¹ᵁ chart o M k.1 = ⊤) ∧
      ∃ ν : Nm o t ht ≅ Cl o z hz, nmPoint o t ht ≫ ν.hom = clPoint o z hz ∧
        (ν.hom ≫ clι o z hz) ≫ PSpace.str o M = str o t ht ∧
        (∀ j k, z k = t j ^ e →
          (ν.hom ≫ clι o z hz) ⁻¹ᵁ chart o M k = toProj o t ht ⁻¹ᵁ chart o r j) ∧
        LBIso (lbPow (twist o t ht) e) ((O1 o M).pull (ν.hom ≫ clι o z hz)) := by
  have : CharZero L := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective o L)
  have := essFiniteType_of_finiteDimensional o t ht
  obtain ⟨e, he, M, z, hz, h₁, h₂, h₃, ν, h₄, h₅, h₆, w, hw, -⟩ := exists_iso_Cl o t ht
  have h₇ : ⨆ k : {k // ∃ j, t j ≠ 0 ∧ z k = t j ^ e}, clι o z hz ⁻¹ᵁ chart o M k.1 = ⊤ := by
    refine top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ?_
    obtain ⟨x, rfl⟩ := ν.hom.surjective y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((iSup_preimage_chart o t ht).ge (Set.mem_univ x))
    obtain ⟨k, hk⟩ := h₃ i.1
    exact ⟨⟨k, i.1, i.2, hk⟩, (h₆ i.1 k hk).ge hi⟩
  exact ⟨fun _ => isIntegral_cone_iff, finite_integralClosure_cone o t, piece_zero, piece_fg o t,
    isIntegral_Nm o t ht, isNormalScheme_Nm o t ht, isIso_stalkMap_nmPoint o t ht,
    isFinite_toCl o t ht, fun i hi => ⟨le_preimage_chart (nmPoint_toProj o t ht) hi,
      valMap_injective _ _, Set.ext fun a => mem_range_valMap_iff rfl _ a⟩,
    isProjOver_str o t ht, e, he, M, z, hz, h₁, h₂, h₃,
    fun i hi f => (isIntegral_ratioRing_iff_mem_adjoin he h₂ h₁ hi).symm,
    fun k => h₂ ▸ pow_mem_forms o t he h₁ (h₂ ▸ Submodule.subset_span ⟨k, rfl⟩), h₇,
    ν, h₄, h₅, h₆, w, hw⟩

example (K : Type) [Field K] [NumberField K] (t : Fin (r + 1) → K) (ht : t ≠ 0) :
    IsProjOver (str ℤ t ht) :=
  have : FiniteDimensional (ratioField ℤ t) K := Module.Finite.of_restrictScalars_finite ℚ _ _
  (normalization_closure_projective ℤ t ht).2.2.2.2.2.2.2.2.2.1

example : let K := FractionRing (Polynomial ℤ)
    let x : K := algebraMap (Polynomial ℤ) K Polynomial.X
    ∃ ht : ![1, x ^ 2, x ^ 3] ≠ 0, IsProjOver (str ℤ ![1, x ^ 2, x ^ 3] ht) := by
  intro K x
  have : Algebra.EssFiniteType ℤ K := .comp ℤ (Polynomial ℤ) K
  exact ⟨Function.ne_iff.mpr ⟨0, one_ne_zero⟩, isProjOver_str _ _ _⟩

end GlobalTheory.TupleNorm
