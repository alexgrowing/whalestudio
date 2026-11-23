import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace IntNumPoint

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def chartMonomial (i : ∀ k, ι k) (e : K → ℕ) : MRing ι F :=
  ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ e k

theorem isMultiHomog_chartMonomial (i : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) i e) e := by
  have h : IsWeightedHomogeneous (blockWeight ι) (chartMonomial (F := F) i e)
      (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ =>
      (isWeightedHomogeneous_X (R := F) (blockWeight ι) ⟨k, i k⟩).pow (e k)
  have he : (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h

def chartUnitIdeal (i : ∀ k, ι k) : Ideal (MRing ι F) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι F) - 1)

theorem mk_X_chart (i : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨k, rfl⟩

theorem mk_chartMonomial (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (chartMonomial i e) = 1 := by
  simp [chartMonomial, map_prod, map_pow, mk_X_chart]

theorem exists_homog_congr (i : ∀ k, ι k) (p : MRing ι F) :
    ∃ N : K → ℕ, ∀ N', N ≤ N' → ∃ h : MRing ι F, IsMultiHomog h N' ∧
      Ideal.Quotient.mk (chartUnitIdeal i) p = Ideal.Quotient.mk (chartUnitIdeal i) h := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun N' _ => ⟨C a * chartMonomial i N', ?_, ?_⟩⟩
    · exact IsWeightedHomogeneous.C_mul (isMultiHomog_chartMonomial i N') a
    · rw [map_mul, mk_chartMonomial, mul_one]
  | add p q hp hq =>
    obtain ⟨Np, hp⟩ := hp
    obtain ⟨Nq, hq⟩ := hq
    refine ⟨Np ⊔ Nq, fun N' hN => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hp N' (le_sup_left.trans hN)
    obtain ⟨b, hb, hb'⟩ := hq N' (le_sup_right.trans hN)
    exact ⟨a + b, IsWeightedHomogeneous.add ha hb, by rw [map_add, map_add, ha', hb']⟩
  | mul_X p s hp =>
    obtain ⟨Np, hp⟩ := hp
    refine ⟨Np + blockWeight ι s, fun N' hN => ?_⟩
    have h1 : Np ≤ N' - blockWeight ι s := fun k => Nat.le_sub_of_add_le (hN k)
    have h2 : N' - blockWeight ι s + blockWeight ι s = N' := by
      funext k
      exact Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) (hN k))
    obtain ⟨a, ha, ha'⟩ := hp _ h1
    refine ⟨a * X s, ?_, by rw [map_mul, map_mul, ha']⟩
    have := IsWeightedHomogeneous.mul ha (isWeightedHomogeneous_X (R := F) (blockWeight ι) s)
    rwa [h2] at this

section Dehom

variable (V : Ideal (MRing ι F)) [V.IsPrime]

def xc (p : Σ k, ι k) : FractionRing (MRing ι F ⧸ V) :=
  algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V (X p))

def cls : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  (IsScalarTower.toAlgHom F (MRing ι F ⧸ V) _).comp (Ideal.Quotient.mkₐ F V)

def dehom (i : ∀ k, ι k) : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  aeval fun p => xc V p / xc V ⟨p.1, i p.1⟩

theorem cls_apply (f : MRing ι F) :
    cls V f = algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V f) := rfl

theorem cls_eq_zero_iff (f : MRing ι F) : cls V f = 0 ↔ f ∈ V := by
  rw [cls_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

theorem xc_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι F) ∉ V) : xc V p ≠ 0 :=
  fun h => hp ((cls_eq_zero_iff V _).1 h)

variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi

theorem chartProd_ne_zero (a : K → ℕ) : ∏ k, xc V ⟨k, i k⟩ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (xc_ne_zero (hi k))

theorem dehom_monomial_mul (m : (Σ k, ι k) →₀ ℕ) :
    dehom V i (monomial m 1) * ∏ k, xc V ⟨k, i k⟩ ^ (Finsupp.weight (blockWeight ι) m k) =
      cls V (monomial m 1) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    have hy : xc V ⟨p.1, i p.1⟩ ≠ 0 := xc_ne_zero (hi p.1)
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [blockWeight, hk])]
    simp only [dehom, aeval_X, blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hy)]
    rfl

theorem dehom_mul_of_isMultiHomog {h : MRing ι F} {a : K → ℕ} (hh : IsMultiHomog h a) :
    dehom V i h * ∏ k, xc V ⟨k, i k⟩ ^ a k = cls V h := by
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (blockWeight ι) m = a := hh (mem_support_iff.mp hm)
  have hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : F) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw, dehom_monomial_mul i hi]

theorem dehom_chartUnitIdeal {f : MRing ι F} (hf : f ∈ chartUnitIdeal i) : dehom V i f = 0 := by
  have : chartUnitIdeal (F := F) i ≤ RingHom.ker (dehom V i) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehom, aeval_X]
    rw [div_self (xc_ne_zero (hi k)), sub_self]
  exact this hf

theorem dehom_eq_zero_of_mem (hV : IsMultiHomogIdeal V) {f : MRing ι F} (hf : f ∈ V) :
    dehom V i f = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  have h1 := dehom_mul_of_isMultiHomog i hi
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) (n := b) (φ := f))
  rw [(cls_eq_zero_iff V _).2 (hV f hf b)] at h1
  exact (mul_eq_zero.mp h1).resolve_right (chartProd_ne_zero i hi b)

theorem dehom_eq_zero_of_mem_chartIdeal (hV : IsMultiHomogIdeal V) {f : MRing ι F}
    (hf : f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) : dehom V i f = 0 := by
  have : ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i ≤ RingHom.ker (dehom V i) :=
    sup_le (fun g hg => dehom_eq_zero_of_mem i hi hV hg) (fun g hg => dehom_chartUnitIdeal i hi hg)
  exact this hf

theorem mem_chartIdeal_of_dehom_eq_zero {f : MRing ι F} (hf : dehom V i f = 0) :
    f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i := by
  obtain ⟨N, hN⟩ := exists_homog_congr i f
  obtain ⟨h, hh, hc⟩ := hN N le_rfl
  have hfh : f - h ∈ chartUnitIdeal i := Ideal.Quotient.eq.mp hc
  have h0 : dehom V i h = 0 := by
    have := dehom_chartUnitIdeal i hi hfh
    rwa [map_sub, hf, zero_sub, neg_eq_zero] at this
  have hV : h ∈ V := by
    rw [← cls_eq_zero_iff, ← dehom_mul_of_isMultiHomog i hi hh, h0, zero_mul]
  have : f = (f - h) + h := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hV)

end Dehom

theorem finrank_chart_eq (V : Ideal (MRing ι F)) (hV : IsMultiProjPrime V) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
    (hfin : haveI := hV.isPrime; FiniteDimensional F (FieldNumbers.homFracDegZero V)) :
    haveI := hV.isPrime
    Module.finrank F (MRing ι F ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) =
      Module.finrank F (FieldNumbers.homFracDegZero V) := by
  haveI := hV.isPrime
  set H := FieldNumbers.homFracDegZero V
  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) (dehom V i)
    (fun a ha => dehom_eq_zero_of_mem_chartIdeal i hi hV.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = dehom V i f := fun f => rfl
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_chartIdeal_of_dehom_eq_zero i hi ha)
  have hmemρ : ∀ f, dehom V i f ∈ ρ.range := fun f => ⟨Ideal.Quotient.mk _ f, hρ f⟩
  have hdH : ∀ f, dehom V i f ∈ H := by
    intro f
    have : (dehom V i).range ≤ H.toSubalgebra := by
      rw [dehom, aeval_range]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin F _
        ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
          isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
    exact this ⟨f, rfl⟩
  have hle : ρ.range ≤ H.toSubalgebra := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hdH f
  let E : IntermediateField F (FractionRing (MRing ι F ⧸ V)) :=
    ρ.range.toIntermediateField fun x hx =>
      ρ.range.inv_mem_of_algebraic (x := ⟨x, hx⟩)
        ((IntermediateField.isAlgebraic_iff (x := (⟨x, hle hx⟩ : H))).1 (IsAlgebraic.of_finite F _))
  have hHE : H ≤ E := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgV, rfl⟩
    have h1 := dehom_mul_of_isMultiHomog i hi hf
    have h2 := dehom_mul_of_isMultiHomog i hi hg
    rw [← cls_apply, ← cls_apply, ← h1, ← h2, mul_div_mul_right _ _ (chartProd_ne_zero i hi b),
      div_eq_mul_inv]
    exact E.mul_mem (hmemρ f) (E.inv_mem (hmemρ g))
  have heq : ρ.range = H.toSubalgebra := le_antisymm hle fun x hx => hHE hx
  rw [(AlgEquiv.ofInjective ρ hinj).toLinearEquiv.finrank_eq, heq,
    IntermediateField.finrank_eq_finrank_subalgebra]

theorem proof (hBase : FieldNumbers.IntNumBase.Statement.{u}) : IntNumPoint.Statement.{u} := by
  intro F _ K _ _ ι _ V i hV hdim hi
  haveI := hV.isPrime
  have hrel : FieldNumbers.relDim V = 0 := by
    rw [FieldNumbers.relDim, hdim]
    have : (((0 + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = 0 := by simp
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  obtain ⟨hfin, hnum⟩ := hBase F K ι V hV hrel
  rw [hnum, ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg, finrank_chart_eq V hV i hi hfin]

end IntNumPoint

end

end GroundTheory.Heights₂.Heights.NumbersDVR
