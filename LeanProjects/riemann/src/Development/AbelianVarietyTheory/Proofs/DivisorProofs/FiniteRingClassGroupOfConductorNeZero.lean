import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.PicFin

variable {E : Type} [Field E] [NumberField E]

theorem mul_mem_hatO {c : Ideal (OF E)} {n : OF E} (hn : n ∈ c) {y : Af E}
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c := by
  refine GlobalTheory.IntDense.mem_of_isClosed E (C := {y | algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun b => ?_) y hy
  show _ * _ ∈ hatO c
  rw [← map_mul]
  refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), ?_⟩)
  rw [map_zero, zero_add, map_mul]
  rfl

def intR (E : Type) [Field E] [NumberField E] : Subring (Af E) where
  carrier := {y | ∀ v, y v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem finite_quot {N : ℕ} (hN : N ≠ 0) : Finite (intR E ⧸ Ideal.span {(N : intR E)}) := by
  have hi : ∀ a : 𝓞 E, algebraMap (𝓞 E) (Af E) a ∈ intR E := fun a v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one a))
  let f : 𝓞 E →+* intR E := (algebraMap (𝓞 E) (Af E)).codRestrict _ hi
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)}) (Ideal.span {(N : intR E)}) f
    ((Ideal.span_singleton_le_iff_mem _).2 (by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _))) fun x => ?_
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N (Nat.pos_of_ne_zero hN)).2 α.1 α.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨β, hβ⟩, Subtype.ext ?_⟩
  show α.1 - algebraMap (𝓞 E) (Af E) a = (N : Af E) * β
  rw [e, ← nsmul_eq_mul]
  exact add_sub_cancel_left _ _

theorem mem_intR {u : (Af E)ˣ} (h : GlobalTheory.Idele.idealOf u = 1) : (u : Af E) ∈ intR E := fun v => by
  have h1 := (GlobalTheory.Idele.smul_eq_self_iff u (I := 1) one_ne_zero).1 (by rw [GlobalTheory.Idele.smul_one_eq, h]) v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1.le

theorem mem_sup {a : (Af E)ˣ} {x : E} (hx : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 E)⁰ x) :
    a ∈ ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx.trans (FractionalIdeal.spanSingleton_zero))
  obtain ⟨b, hb⟩ : ∃ b : (Af E)ˣ, b = FiniteAdeleRing.unitEmbedding (𝓞 E) E (Units.mk0 x hx0) := ⟨_, rfl⟩
  have h2 : GlobalTheory.Idele.idealOf (a * b⁻¹) = 1 := by
    rw [GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hb, GlobalTheory.Idele.idealOf_unitEmbedding, hx]
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have h3 : GlobalTheory.Idele.idealOf (a * b⁻¹)⁻¹ = 1 := by rw [GlobalTheory.Idele.idealOf_inv, h2, inv_one]
  have h4 : a * b⁻¹ ∈ (intR E).toSubmonoid.units := (Submonoid.mem_units_iff _ _).2 ⟨mem_intR h2, mem_intR h3⟩
  have h5 : b ∈ princ := MonoidHom.mem_range.2 ⟨Units.mk0 x hx0, by rw [hb]; exact Units.ext (by simp)⟩
  have h6 := Subgroup.mul_mem_sup h4 h5
  rwa [inv_mul_cancel_right] at h6

theorem finiteIndex_top : ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ).FiniteIndex := by
  classical
  let g : (Af E)ˣ →* ClassGroup (𝓞 E) := (ClassGroup.mk E).comp (GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits
  have : g.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := g.ker) fun a ha => ?_
  have h1 : ClassGroup.mk E ((GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  exact mem_sup hx

theorem finiteIndex_units {c : Ideal (OF E)} (hc : c ≠ ⊥) :
    ((hatOUnits c).subgroupOf (intR E).toSubmonoid.units).FiniteIndex := by
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have := finite_quot (E := E) hN
  let r : (intR E).toSubmonoid.units →* intR E ⧸ Ideal.span {((Ideal.absNorm c : ℕ) : intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), u.2.1⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have key : ∀ u ∈ r.toHomUnits.ker, ((u.1 : (Af E)ˣ) : Af E) ∈ hatO c := fun u hu => by
    have h2 : Ideal.Quotient.mk (Ideal.span {((Ideal.absNorm c : ℕ) : intR E)}) ⟨(u.1 : Af E), u.2.1⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = ((Ideal.absNorm c : ℕ) : Af E) * β.1 := congrArg Subtype.val hβ
    have h4 := mul_mem_hatO (Ideal.absNorm_mem c) β.2
    rw [map_natCast, map_natCast, ← h3] at h4
    simpa using add_mem h4 (one_mem _)
  exact Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu => ⟨key u hu, key u⁻¹ (inv_mem hu)⟩

theorem finite_picO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  intro E _ _ _ c hc
  let U : Subgroup (Af E)ˣ := (intR E).toSubmonoid.units
  let K : Subgroup (Af E)ˣ := princ ⊔ hatOUnits c
  have h1 := finiteIndex_units hc
  have h2 : (K.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := (hatOUnits c).subgroupOf U) (Subgroup.comap_mono le_sup_right)
  have := finiteIndex_top (E := E)
  have h3 : (U ⊔ K).FiniteIndex := Subgroup.finiteIndex_of_le (H := U ⊔ princ) (sup_le_sup_left le_sup_left _)
  have : K.FiniteIndex := ⟨by
    rw [← Subgroup.relIndex_mul_index (le_sup_right : K ≤ U ⊔ K), Subgroup.relIndex_sup_right]
    exact mul_ne_zero h2.1 h3.1⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end GlobalTheory.CMVal.PicFin
