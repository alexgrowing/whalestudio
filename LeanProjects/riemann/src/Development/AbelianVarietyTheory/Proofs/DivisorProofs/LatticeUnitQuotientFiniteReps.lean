import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLineComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def intAd : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ w : Pl F, evFin F w a ∈ w.adicCompletionIntegers F}
  add_mem' {a b} ha hb := by
    refine ⟨?_, fun w => ?_⟩
    · have e : evI F (a + b) = evI F a + evI F b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
      rw [e, ha.1, hb.1, add_zero]
    · rw [map_add]; exact add_mem (ha.2 w) (hb.2 w)
  zero_mem' := by
    refine ⟨?_, fun w => ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    · rw [map_zero]; exact zero_mem _
  neg_mem' {a} ha := by
    refine ⟨?_, fun w => ?_⟩
    · have e : evI F (-a) = -evI F a := map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
      rw [e, ha.1, neg_zero]
    · rw [map_neg]; exact neg_mem (ha.2 w)

def atPl (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem evI_atPl (v : Pl F) (β : Fv F v) : evI F (atPl v β) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
  exact map_zero _

theorem evFin_atPl (v w : Pl F) (β : Fv F v) :
    evFin F w (atPl v β) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v β) := rfl

theorem atPl_mem_intAd (v : Pl F) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F) : atPl v β ∈ intAd F := by
  refine ⟨evI_atPl v β, fun w => ?_⟩
  rw [evFin_atPl]
  by_cases hw : w = v
  · subst hw; rw [evalV_singleFin_self]; exact hβ
  · rw [evalV_singleFin_ne hw]; exact zero_mem _

theorem eq_atPl (v : Pl F) (x : AF F) (hx : evI F x = 0) (hxw : ∀ w : Pl F, w ≠ v → evFin F w x = 0) :
    x = atPl v (evFin F v x) := by
  have h1 : x.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hx)
  refine Prod.ext h1 ?_
  refine RestrictedProduct.ext _ _ fun w => ?_
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w x.2 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v (evFin F v x))
  by_cases hw : w = v
  · subst hw; rw [evalV_singleFin_self]; rfl
  · rw [evalV_singleFin_ne hw]; exact hxw w hw

theorem incV_sum {d r : ℕ} (c : Fin r → ℤ) (g : Fin r → Fin d → E) :
    incV F (∑ j, c j • g j) = ∑ j, c j • incV F (g j) := by
  funext i
  simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]

theorem exists_int_gens {d : ℕ} (L : Submodule (𝓞 E) (Fin d → E)) (hL : L.IsLattice E) :
    ∃ (r : ℕ) (g : Fin r → Fin d → E), (∀ j, g j ∈ L) ∧ ∀ x ∈ L, ∃ c : Fin r → ℤ, ∑ j, c j • g j = x := by
  have hfg : (L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  refine ⟨r, g, fun j => ?_, fun x hx => ?_⟩
  · have : g j ∈ L.restrictScalars ℤ := hg ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  · have : x ∈ Submodule.span ℤ (Set.range g) := hg ▸ hx
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this

theorem latHat_decomp {d r : ℕ} (W : Spc F E d) (g : Fin r → Fin d → E)
    (hg : ∀ x ∈ W.L, ∃ c : Fin r → ℤ, ∑ j, c j • g j = x) {z : Fin d → AE F E} (hz : z ∈ latHat W) :
    ∃ a : Fin r → AF F, (∀ j, a j ∈ intAd F) ∧ z = ∑ j, a j • incV F (g j) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hbv, x, hx, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := hg x hx
    refine ⟨fun j => c j • b, fun j => zsmul_mem (show b ∈ intAd F from ⟨hb, hbv⟩) _, ?_⟩
    rw [incV_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_assoc]
    exact smul_comm _ _ _
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a', ha', rfl⟩ := hy
    exact ⟨a + a', fun j => add_mem (ha j) (ha' j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, fun j => neg_mem (ha j), by simp [neg_smul, Finset.sum_neg_distrib]⟩

theorem fin_reps (v : Pl F) (m : ℕ) (hm : m ≠ 0) :
    ∃ R : Finset (Fv F v), (∀ ρ ∈ R, ρ ∈ v.adicCompletionIntegers F) ∧
      ∀ β ∈ v.adicCompletionIntegers F, ∃ ρ ∈ R, ∃ γ ∈ v.adicCompletionIntegers F, β = ρ + m * γ := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hm' : (m : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  let H : AddSubgroup (v.adicCompletionIntegers F) := (AddMonoidHom.mulLeft (m : v.adicCompletionIntegers F)).range
  have hopen : IsOpen (H : Set (v.adicCompletionIntegers F)) := by
    refine AddSubgroup.isOpen_of_mem_nhds H (g := 0) ?_
    have hS : IsOpen {x : v.adicCompletionIntegers F | (m : Fv F v)⁻¹ * (x : Fv F v) ∈ v.adicCompletionIntegers F} :=
      hO.preimage (continuous_const.mul continuous_subtype_val)
    refine Filter.mem_of_superset (hS.mem_nhds (by simp)) fun x hx => ?_
    refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel_left₀ hm']
  haveI : Finite (v.adicCompletionIntegers F ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hopen
  haveI := Fintype.ofFinite (v.adicCompletionIntegers F ⧸ H)
  refine ⟨Finset.univ.image fun q : v.adicCompletionIntegers F ⧸ H => ((Quotient.out q : v.adicCompletionIntegers F) : Fv F v), ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hρ
    exact (Quotient.out q).2
  · intro β hβ
    let q : v.adicCompletionIntegers F ⧸ H := QuotientAddGroup.mk ⟨β, hβ⟩
    have hq : (QuotientAddGroup.mk (Quotient.out q) : v.adicCompletionIntegers F ⧸ H) = QuotientAddGroup.mk ⟨β, hβ⟩ :=
      QuotientAddGroup.out_eq' q
    obtain ⟨γ, hγ⟩ := QuotientAddGroup.eq.1 hq
    refine ⟨_, Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, γ, γ.2, ?_⟩
    have h2 := congrArg Subtype.val hγ
    simp only [AddMonoidHom.coe_mulLeft] at h2
    have h3 : (((m : v.adicCompletionIntegers F)) : Fv F v) = m := by simp
    have h4 : ((-Quotient.out q + ⟨β, hβ⟩ : v.adicCompletionIntegers F) : Fv F v) =
        -((Quotient.out q : v.adicCompletionIntegers F) : Fv F v) + β := rfl
    rw [Subring.coe_mul, h3, h4] at h2
    linear_combination -h2

theorem smul_latHat_finite_mod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d) (v : Pl F)
    (u : AF F), W.L.IsLattice E → evI F u = 0 → (∀ w : Pl F, w ≠ v → evFin F w u = 0) →
    evFin F v u ∈ v.adicCompletionIntegers F → ∀ m : ℕ, m ≠ 0 →
    ∃ S : Finset (Fin d → AE F E), (∀ s ∈ S, s ∈ latHat W) ∧
      ∀ z ∈ latHat W, ∃ s ∈ S, ∃ y ∈ latHat W, u • z - s = m • y := by
  intro F E _ _ _ _ _ d W v u hL hu hw hv m hm
  classical
  obtain ⟨r, g, hgL, hg⟩ := exists_int_gens W.L hL
  obtain ⟨R, hRO, hR⟩ := fin_reps v m hm
  have gen : ∀ β ∈ v.adicCompletionIntegers F, ∀ j, atPl v β • incV F (g j) ∈ latHat W := fun β hβ j =>
    AddSubgroup.subset_closure ⟨atPl v β, (atPl_mem_intAd v hβ).1, (atPl_mem_intAd v hβ).2, g j, hgL j, rfl⟩
  refine ⟨(Fintype.piFinset fun _ : Fin r => R).image (fun ρ => ∑ j, atPl v (ρ j) • incV F (g j)), ?_, ?_⟩
  · intro s hs
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hs
    exact AddSubgroup.sum_mem _ fun j _ => gen _ (hRO _ (Fintype.mem_piFinset.1 hρ j)) j
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := latHat_decomp W g hg hz
    have hβ : ∀ j, evFin F v (u * a j) ∈ v.adicCompletionIntegers F := fun j => by
      rw [map_mul]; exact mul_mem hv ((ha j).2 v)
    have hua : ∀ j, u * a j = atPl v (evFin F v (u * a j)) := fun j => by
      refine eq_atPl v _ ?_ fun w hw' => ?_
      · have e : evI F (u * a j) = evI F u * evI F (a j) :=
          map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 (a j).1
        rw [e, hu, zero_mul]
      · rw [map_mul, hw w hw', zero_mul]
    choose ρ hρR γ hγ hsplit using fun j => hR _ (hβ j)
    refine ⟨∑ j, atPl v (ρ j) • incV F (g j), Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρR, rfl⟩,
      ∑ j, atPl v (γ j) • incV F (g j), AddSubgroup.sum_mem _ fun j _ => gen _ (hγ j) j, ?_⟩
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hua j, hsplit j, map_add, add_smul, add_sub_cancel_left, ← nsmul_eq_mul, map_nsmul, smul_assoc]

end GlobalTheory.SphLineComm

end
