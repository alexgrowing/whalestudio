import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.UnipotentAdelicQuotients.GlobalNormIndexTwo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Topology

namespace GlobalTheory.IdeleNormChar

open GlobalTheory.QuadSymbol

variable {K : Type} [Field K] [NumberField K]

def finEval (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEval (w : InfinitePlace K) : AdeleRing (𝓞 K) K →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def finComp : (AdeleRing (𝓞 K) K)ˣ →* FinFam K :=
  MonoidHom.pi fun v => Units.map (finEval v)

def infComp : (AdeleRing (𝓞 K) K)ˣ →* InfFam K :=
  MonoidHom.pi fun w => Units.map (infEval w)

theorem finComp_toUnits (t : Kˣ) : finComp (toUnits K (AdeleRing (𝓞 K) K) t) = finDiag K t :=
  funext fun _ => Units.ext rfl

theorem infComp_toUnits (t : Kˣ) : infComp (toUnits K (AdeleRing (𝓞 K) K) t) = infDiag K t :=
  funext fun _ => Units.ext rfl

theorem eventually_valued_eq_one (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  filter_upwards [(a : AdeleRing (𝓞 K) K).2.2, ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2]
    with v h3 h4
  have hmul : (a : AdeleRing (𝓞 K) K).2 v *
      ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  change Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1
  refine le_antisymm h3 ?_
  rw [← hm]
  exact mul_le_of_le_one_right' h4

theorem eventually_integral_form (δ : K) (hδ : δ ≠ 0) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
  filter_upwards [eventually_valued_eq_one a,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).compl_mem_cofinite,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ)).compl_mem_cofinite] with v ha h2 hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, Units.val_mk0] at h2 hd
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  exact GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v (algebraMap K _ δ) _
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2)
    (by rw [key, hd]) ha

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

omit [NumberField L] in

theorem almostNorm_finComp (a : (AdeleRing (𝓞 K) K)ˣ) : AlmostNorm K L (finComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine Filter.eventually_cofinite.1 ((eventually_integral_form δ hδ0 a).mono ?_)
  rintro v ⟨x, -, y, -, h⟩
  exact (mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩

omit [NumberField L] in

theorem mem_normGroup_iff_everywhereNorm (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ normGroup K L (AdeleRing (𝓞 K) K) ↔ EverywhereNorm K L (finComp a) (infComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨fun v => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.2 v, y.2 v, congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) h⟩,
      fun w => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.1 w, y.1 w, congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) h⟩⟩
  · rintro ⟨hf, hi⟩
    have hc := eventually_integral_form δ hδ0 a
    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        ((∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2) →
          x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K) ∧
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
      intro v
      by_cases hv : ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2
      · obtain ⟨x, hx, y, hy, h⟩ := hv
        exact ⟨x, y, fun _ => ⟨hx, hy⟩, h⟩
      · obtain ⟨x, y, h⟩ := (mem_normGroup_iff_form b h0 h1).1 (hf v)
        exact ⟨x, y, fun h' => absurd h' hv, h⟩
    choose x y hxy h using hloc
    choose r s hr using fun w => (mem_normGroup_iff_form b h0 h1).1 (hi w)
    let X : FiniteAdeleRing (𝓞 K) K := ⟨x, hc.mono fun v hv => (hxy v hv).1⟩
    let Y : FiniteAdeleRing (𝓞 K) K := ⟨y, hc.mono fun v hv => (hxy v hv).2⟩
    refine ⟨((r : InfiniteAdeleRing K), X), ((s : InfiniteAdeleRing K), Y), Prod.ext ?_ ?_⟩
    · funext w
      exact hr w
    · exact FiniteAdeleRing.ext K fun v => h v

def normSign : (AdeleRing (𝓞 K) K)ˣ →* ℤˣ :=
  MonoidHom.mk' (fun a => etaProd K L (finComp a) (infComp a)) fun a b => by
    obtain ⟨h1, h2⟩ := localCharacters K L
    unfold etaProd
    simp only [map_mul, Pi.mul_apply, h1, h2]
    rw [finprod_mul_distrib (almostNorm_finComp L a).finite_mulSupport
      (almostNorm_finComp L b).finite_mulSupport, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem normSign_eq_one_iff (a : (AdeleRing (𝓞 K) K)ˣ) :
    normSign L a = 1 ↔ ∃ t : Kˣ, a / toUnits K (AdeleRing (𝓞 K) K) t ∈ normGroup K L (AdeleRing (𝓞 K) K) := by
  refine ((exactSequence K L).2.2.1 _ _ (almostNorm_finComp L a)).symm.trans (exists_congr fun t => ?_)
  rw [mem_normGroup_iff_everywhereNorm, map_div, map_div, finComp_toUnits, infComp_toUnits]

theorem normSign_of_mem {a : (AdeleRing (𝓞 K) K)ˣ} (h : a ∈ normGroup K L (AdeleRing (𝓞 K) K)) :
    normSign L a = 1 :=
  (normSign_eq_one_iff L a).2 ⟨1, by rwa [map_one, div_one]⟩

theorem normSign_toUnits (t : Kˣ) : normSign L (toUnits K (AdeleRing (𝓞 K) K) t) = 1 :=
  (normSign_eq_one_iff L _).2 ⟨t, by rw [div_self']; exact one_mem _⟩

theorem exists_normSign_ne_one : ∃ a : (AdeleRing (𝓞 K) K)ˣ, normSign L a ≠ 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  obtain ⟨a, ha⟩ := GlobalTheory.QNorm.exists_idele_not_mul_norm K δ hδ
  refine ⟨a, fun h => ?_⟩
  obtain ⟨t, ht⟩ := (normSign_eq_one_iff L a).1 h
  obtain ⟨x, y, e⟩ := (mem_normGroup_iff_form b h0 h1).1 ht
  refine ha t x y ?_
  rw [← e]
  exact (congrArg Units.val (mul_div_cancel (toUnits K (AdeleRing (𝓞 K) K) t) a)).symm

theorem eventually_normSign : ∀ᶠ a in 𝓝 (1 : (AdeleRing (𝓞 K) K)ˣ), normSign L a = 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  filter_upwards [GlobalTheory.QNorm.norm_form_mem_nhds_one K δ hδ0] with a ha
  exact normSign_of_mem L ((mem_normGroup_iff_form b h0 h1).2 ha)

def signToCircle : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' u u' := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;> simp

theorem circle_neg_one_ne_one : (-1 : Circle) ≠ 1 := fun h => by
  have := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at this

theorem eq_signToCircle_comp {G : Type} [Group G] (ε : G →* ℤˣ) (η : G →* Circle)
    (h : ∀ a, ε a = 1 → η a = 1) (hη : η ≠ 1) : η = signToCircle.comp ε := by
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hη (MonoidHom.ext hh)
  have hεb : ε b = -1 := (Int.units_eq_one_or _).resolve_left fun e => hb (h b e)
  refine MonoidHom.ext fun a => ?_
  rcases Int.units_eq_one_or (ε a) with e | e
  · rw [MonoidHom.comp_apply, e, map_one, h a e]
  · have h1 : η a * η b = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e, hεb]; simp)
    have h2 : η a * η a = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e]; simp)
    have h3 : (η a : ℂ) * η a = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h2
    rw [MonoidHom.comp_apply, e]
    change η a = if (-1 : ℤˣ) = 1 then 1 else -1
    rw [if_neg (by decide)]
    rcases mul_self_eq_one_iff.1 h3 with h4 | h4
    · have h5 : η a = 1 := Circle.ext h4
      rw [h5, one_mul] at h1
      exact absurd h1 hb
    · exact Circle.ext h4

theorem globalNormIndexTwo : Formalism.D.Classical.GlobalNormIndexTwo := by
  intro F E _ _ _ _ _ h2
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  refine ⟨signToCircle.comp (normSign E), ⟨?_, fun a => ?_, fun x => ?_, fun e => ?_⟩, ?_⟩
  · refine continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : Circle))).congr ?_)
    filter_upwards [eventually_normSign (K := F) E] with a ha
    rw [MonoidHom.comp_apply, ha, map_one]
  · exact (congrArg signToCircle (normSign_toUnits E a)).trans (map_one _)
  · exact (congrArg signToCircle (normSign_of_mem E ⟨x, rfl⟩)).trans (map_one _)
  · obtain ⟨a, ha⟩ := exists_normSign_ne_one (K := F) E
    have h : signToCircle (normSign E a) = 1 := DFunLike.congr_fun e a
    exact circle_neg_one_ne_one ((if_neg ha).symm.trans h)
  · rintro η ⟨-, h1, h3, h4⟩
    refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
    obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
    rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
    exact h1 t

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta in

theorem existsUnique_isEta : ∀ D : D7, ∃! η : (AF D.host.F)ˣ →* Circle, IsEta D η := fun D =>
  globalNormIndexTwo D.host.F D.host.E D.sp.cm.deg2

end GlobalTheory.IdeleNormChar

end
