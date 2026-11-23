import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open scoped Pointwise Topology
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.AddSA

variable {F : Type} [Field F] [NumberField F]

theorem exists_approx_finite (w : InfinitePlace F) (x : InfiniteAdeleRing F)
    (y : FiniteAdeleRing (𝓞 F) F) (O : ∀ v : InfinitePlace F, Set v.Completion)
    (hO : ∀ v, O v ∈ 𝓝 (x v)) {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 y) :
    ∃ t : F, (∀ v, v ≠ w → algebraMap F v.Completion t ∈ O v) ∧
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t ∈ U := by
  classical
  have hW : (fun z => y + z) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  have hdF : (d : F) ≠ 0 := by simpa using hd0
  set e : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (d : F)⁻¹ with he
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ¬ (e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F)}.Finite := by
    have h1 := e.2
    have h2 := (e * y).2
    have := h1.and h2
    exact this
  let T₂ : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
  have hOF : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} ∧
        y v ∈ {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} := by
    intro v
    refine ⟨(Valued.isOpen_valuationSubring _).preimage
      (continuous_const.mul (continuous_id.sub continuous_const)), ?_⟩
    show e v * (y v - y v) ∈ v.adicCompletionIntegers F
    simp
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := GlobalTheory.CompanionTheory.PlaneSA.Additive.exists_approx_core (F := F) (Sum.inl w)
    (Finset.univ.erase w) T₂ (fun v hv h => (Finset.mem_erase.1 hv).1 (Sum.inl_injective h))
    (fun v _ h => by cases h) x O (fun v _ => hO v) (fun v => y v)
    (fun v => {z | e v * (z - y v) ∈ v.adicCompletionIntegers F}) (fun v _ => hOF v)
  refine ⟨t, fun v hv => ht₁ v (Finset.mem_erase.2 ⟨hv, Finset.mem_univ v⟩), ?_⟩
  have hmem : e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
    refine GroundTheory.Global.mem_integralFiniteAdeles.2 fun v => ?_
    by_cases hv : v ∈ T₂
    · exact ht₂ v hv
    · have hv' : e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F := by
        simpa [T₂] using hv
      have h3 := ht₃ v hv (by simp)
      have : (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) v =
          e v * algebraMap F (v.adicCompletion F) t - (e * y) v := by
        show e v * (algebraMap F (v.adicCompletion F) t - y v) = e v * _ - e v * y v
        ring
      rw [this]
      exact sub_mem (mul_mem hv'.1 h3) hv'.2
  have h := hd _ hmem
  have hde : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * e = 1 := by
    rw [he, ← map_mul, mul_inv_cancel₀ hdF, map_one]
  have h4 : y + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) *
      (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t := by
    rw [← mul_assoc, hde]; ring
  simpa only [Set.mem_preimage, h4] using h

theorem dense_add_place : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  intro F _ _ w
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
    (show U ∈ 𝓝 ((a.1, a.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from hU.mem_nhds ha)
  have hU₁' : U₁ ∈ Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := by
    have h : 𝓝 a.1 = Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := nhds_pi
    rwa [← h]
  obtain ⟨I, -, O, hO, hIO⟩ := Filter.mem_pi.1 hU₁'
  obtain ⟨t, ht₁, ht₂⟩ := exists_approx_finite w a.1 a.2 O hO hU₂
  let b : NumberField.AdeleRing (𝓞 F) F :=
    ((Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  refine ⟨algebraMap F _ t + b, ?_, Set.add_mem_add ⟨t, rfl⟩ ⟨rfl, fun v hv => ?_⟩⟩
  · apply hsub
    refine ⟨hIO fun v _ => ?_, ?_⟩
    · by_cases hv : v = w
      · subst hv
        have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = a.1 v := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) v
            (a.1 v - algebraMap F v.Completion t) v = a.1 v
          simp
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact mem_of_mem_nhds (hO v)
      · have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = algebraMap F v.Completion t := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
            (a.1 w - algebraMap F w.Completion t) v = _
          simp [Function.update_of_ne hv]
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact ht₁ v hv
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) t + 0 ∈ U₂
      simpa using ht₂
  · show Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) v = 0
    simp [Function.update_of_ne hv]

end GlobalTheory.CompanionTheory.AddSA
