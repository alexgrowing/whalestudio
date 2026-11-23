import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.EvAdm.CosetSum

variable {F : Type} [Field F] [NumberField F]

theorem finAdele_algebraMap_apply (x : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v = algebraMap F (v.adicCompletion F) x := rfl

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ v.valuation F x ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact iff_of_eq (congrArg (· ≤ 1) (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x))

theorem int_mem (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
  rw [algebraMap_mem_iff]
  exact v.valuation_le_one x

variable {κ : Type}

theorem mul_int_mem {b : F} (hb : b ≠ 0) (x : κ → 𝓞 F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (b * (x i : F))) ∈ scaledInt F κ b := by
  rw [mem_scaledInt]
  intro i v
  rw [finAdele_algebraMap_apply, map_mul, ← mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 hb), one_mul]
  exact int_mem v (x i)

theorem scaledInt_mul_le {a : F} (ha : a ≠ 0) {m : 𝓞 F} (hm : m ≠ 0) :
    scaledInt F κ (a * m) ≤ scaledInt F κ a := by
  intro z hz
  rw [mem_scaledInt] at hz ⊢
  intro i v
  have hm' : algebraMap F (v.adicCompletion F) (m : F) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hm)
  have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v =
      algebraMap F (v.adicCompletion F) (m : F) *
        ((algebraMap F (v.adicCompletion F) (a * m))⁻¹ * (z i) v) := by
    set A := algebraMap F (v.adicCompletion F) a
    set M := algebraMap F (v.adicCompletion F) (m : F)
    rw [map_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_comm M A⁻¹, mul_assoc A⁻¹ M M⁻¹,
      mul_inv_cancel₀ hm', mul_one]
  rw [e]
  exact mul_mem (int_mem v m) (hz i v)

theorem rat_mem {b : F} (hb : b ≠ 0) (ξ : κ → F)
    (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ scaledInt F κ b) (i : κ) :
    ∃ x : 𝓞 F, (x : F) = ξ i / b := by
  rw [mem_scaledInt] at h
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ i / b) ≤ 1 := fun v => by
    rw [← algebraMap_mem_iff, div_eq_inv_mul, map_mul, map_inv₀]
    exact h i v
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ i / b) hv
  exact ⟨x, hx⟩

theorem indicator_scaledInt_eq_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ a ha m hm
  set I : Ideal (𝓞 F) := Ideal.span {m} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hm
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Fintype (κ → 𝓞 F ⧸ I) := Fintype.ofFinite _
  let out : 𝓞 F ⧸ I → 𝓞 F := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hout : ∀ q, Ideal.Quotient.mk I (out q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
  let rep : (κ → 𝓞 F ⧸ I) → (κ → F) := fun c i => a * ((out (c i) : 𝓞 F) : F)
  let ι : (κ → F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun ξ i => algebraMap F _ (ξ i)
  have hrep_inj : Function.Injective rep := by
    intro c c' h
    funext i
    have h1 := congrFun h i
    simp only [rep, mul_right_inj' ha] at h1
    have h2 : out (c i) = out (c' i) := by exact_mod_cast h1
    rw [← hout (c i), ← hout (c' i), h2]
  have hrepS : ∀ c, ι (rep c) ∈ scaledInt F κ a := fun c => mul_int_mem ha (fun i => out (c i))
  have hsub := scaledInt_mul_le (κ := κ) ha hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast hm
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha hm0
  have huniq : ∀ c c' (y : κ → FiniteAdeleRing (𝓞 F) F), y - ι (rep c) ∈ scaledInt F κ (a * m) →
      y - ι (rep c') ∈ scaledInt F κ (a * m) → c = c' := by
    intro c c' y h h'
    have hd : ι (fun i => rep c' i - rep c i) ∈ scaledInt F κ (a * m) := by
      have := sub_mem h h'
      convert this using 1
      funext i
      simp only [ι, map_sub, Pi.sub_apply]
      abel
    funext i
    obtain ⟨z, hz⟩ := rat_mem ham _ hd i
    have h3 : ((out (c' i) - out (c i) : 𝓞 F) : F) = ((z * m : 𝓞 F) : F) := by
      have hz' : (z : F) * (a * m) = rep c' i - rep c i := by rw [hz, div_mul_cancel₀ _ ham]
      simp only [rep] at hz'
      push_cast
      apply mul_left_cancel₀ ha
      linear_combination (-1 : F) * hz'
    have h4 : out (c' i) - out (c i) ∈ I := by
      rw [hIdef, Ideal.mem_span_singleton']
      exact ⟨z, by exact_mod_cast h3.symm⟩
    have h5 := (Ideal.Quotient.eq).2 h4
    rw [hout, hout] at h5
    exact h5.symm
  have hexist : ∀ y ∈ scaledInt F κ a, ∃ c, y - ι (rep c) ∈ scaledInt F κ (a * m) := by
    intro y hy
    have hd : DenseRange ι :=
      DenseRange.piMap (fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F)
    have hopen : IsOpen {z | y - z ∈ (scaledInt F κ (a * m) : Set (κ → FiniteAdeleRing (𝓞 F) F))} :=
      (isOpen_scaledInt (a * m)).preimage (continuous_const.sub continuous_id)
    obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hopen ⟨y, by simp [zero_mem]⟩
    have hξ' : y - ι ξ ∈ scaledInt F κ (a * m) := hξ
    have hξa : ι ξ ∈ scaledInt F κ a := by
      have := sub_mem hy (hsub hξ')
      simpa using this
    choose x hx using fun i => rat_mem ha ξ hξa i
    have ht : ∀ i, ∃ t : 𝓞 F, t * m = out (Ideal.Quotient.mk I (x i)) - x i := fun i => by
      have := (Ideal.Quotient.eq).1 (hout (Ideal.Quotient.mk I (x i)))
      exact Ideal.mem_span_singleton'.1 this
    choose t htm using ht
    refine ⟨fun i => Ideal.Quotient.mk I (x i), ?_⟩
    have hF : ∀ i, rep (fun i => Ideal.Quotient.mk I (x i)) i = ξ i + a * m * (t i : F) := fun i => by
      have e1 : ((t i * m : 𝓞 F) : F) = ((out (Ideal.Quotient.mk I (x i)) - x i : 𝓞 F) : F) := by rw [htm i]
      push_cast at e1
      have e2 : ξ i = a * (x i : F) := by rw [hx i]; field_simp
      simp only [rep]
      rw [e2]
      linear_combination (-a) * e1
    have hw : ι (fun i => a * m * (t i : F)) ∈ scaledInt F κ (a * m) := mul_int_mem ham t
    have e : y - ι (rep (fun i => Ideal.Quotient.mk I (x i))) = (y - ι ξ) - ι (fun i => a * m * (t i : F)) := by
      funext i
      simp only [ι, Pi.sub_apply]
      rw [hF i, map_add]
      abel
    rw [e]
    exact sub_mem hξ' hw
  refine ⟨Finset.univ.image rep, ?_⟩
  rw [Finset.sum_image (fun c _ c' _ h => hrep_inj h)]
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ scaledInt F κ a
  · obtain ⟨c0, hc0⟩ := hexist y hy
    rw [Set.indicator_of_mem (by exact hy), Finset.sum_eq_single c0]
    · rw [Set.indicator_of_mem (by exact hc0)]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      intro h
      exact hc (huniq c c0 y h hc0)
    · intro h
      exact absurd (Finset.mem_univ c0) h
  · rw [Set.indicator_of_notMem (by exact hy)]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [Set.indicator_of_notMem]
    intro h
    apply hy
    rw [show y = (y - ι (rep c)) + ι (rep c) from (sub_add_cancel _ _).symm]
    exact add_mem (hsub h) (hrepS c)

end GlobalTheory.EvAdm.CosetSum
