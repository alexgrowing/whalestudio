import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem UpperTheory.locally_constant_fourier {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (m : Measure A) [m.IsAddRightInvariant] (χ : A → ℂ)
    (hl : IsLocallyConstant χ) (h0 : χ 0 = 1) (hadd : ∀ a b, χ (a + b) = χ a * χ b)
    (hann : ∀ U ∈ nhds (0 : A), IsCompact {l : A | ∀ t ∈ U, χ (t * l) = 1})
    (T : A → ℂ) (hTl : IsLocallyConstant T) (hTc : HasCompactSupport T) :
    IsLocallyConstant (fun t => ∫ s, T s * χ (t * s) ∂m) ∧ HasCompactSupport (fun t => ∫ s, T s * χ (t * s) ∂m) := by
  have key : ∀ y ∈ tsupport T, ∀ᶠ z : A × A in nhds ((0 : A), y),
      χ (z.1 * z.2) = 1 ∧ T (z.2 + z.1) = T z.2 ∧ T (z.2 - z.1) = T z.2 := by
    intro y _
    have e1 := (hl.comp_continuous (continuous_fst.mul continuous_snd : Continuous fun z : A × A => z.1 * z.2)).eventually_eq
      (x := ((0 : A), y))
    have e2 := (hTl.comp_continuous (continuous_snd.add continuous_fst : Continuous fun z : A × A => z.2 + z.1)).eventually_eq
      (x := ((0 : A), y))
    have e3 := (hTl.comp_continuous (continuous_snd.sub continuous_fst : Continuous fun z : A × A => z.2 - z.1)).eventually_eq
      (x := ((0 : A), y))
    have e4 := (hTl.comp_continuous (continuous_snd : Continuous fun z : A × A => z.2)).eventually_eq
      (x := ((0 : A), y))
    filter_upwards [e1, e2, e3, e4] with z h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, zero_mul, add_zero, sub_zero, h0] at h1 h2 h3 h4
    exact ⟨h1, h2.trans h4.symm, h3.trans h4.symm⟩
  have h := hTc.eventually_forall_of_forall_eventually (x₀ := (0 : A))
    (P := fun (w y : A) => χ (w * y) = 1 ∧ T (y + w) = T y ∧ T (y - w) = T y) key
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hc : Tendsto (fun t : A => t - x) (nhds x) (nhds 0) := by
      have : Continuous fun t : A => t - x := continuous_id.sub continuous_const
      simpa using this.tendsto x
    filter_upwards [hc.eventually h] with t ht
    congr 1
    funext s
    by_cases hs : s ∈ tsupport T
    · have e : t * s = x * s + (t - x) * s := by ring
      rw [e, hadd, (ht s hs).1, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul, zero_mul]
  · refine HasCompactSupport.intro (hann _ h) fun l hl' => ?_
    by_contra hne
    refine hl' fun u hu => ?_
    have hT : ∀ s, T (s + u) = T s := by
      intro s
      by_cases hs : s ∈ tsupport T
      · exact (hu s hs).2.1
      by_cases hs' : s + u ∈ tsupport T
      · have := (hu _ hs').2.2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hs, image_eq_zero_of_notMem_tsupport hs']
    have e := integral_add_right_eq_self (μ := m) (fun s => T s * χ (l * s)) u
    have e2 : ∀ s, T (s + u) * χ (l * (s + u)) = χ (u * l) * (T s * χ (l * s)) := by
      intro s
      rw [hT, mul_add, hadd, mul_comm l u]
      ring
    simp only [e2, integral_const_mul] at e
    exact mul_right_cancel₀ hne (e.trans (one_mul _).symm)

theorem UpperTheory.fourier_schwartz_bruhat_preserved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
        ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure], ∀ T ∈ SB (Fv F v ⊗[F] E), four v ψ m T ∈ SB (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ v ψ hc hψ _ _ m _ T hT
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v
  have hψl : IsLocallyConstant ψ := GlobalTheory.SchrSB.isLocallyConstant_addChar ψ hc
  obtain ⟨hTl, hTc⟩ := hT
  exact UpperTheory.locally_constant_fourier m (fun a => ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a))
    (hψl.comp_continuous (IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))))
    (by simp) (fun a b => by simp only [map_add, AddChar.map_add_eq_mul])
    (GlobalTheory.TraceAnnCompact.isCompact_trace_ann v ψ hc hψ) T hTl hTc
