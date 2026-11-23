import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Topology Filter

theorem adic_ringEquiv_eq_self {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (ψ : w.adicCompletion F ≃+* w.adicCompletion F)
    (hF : ∀ a : F, ψ (algebraMap F _ a) = algebraMap F _ a)
    (hO : ∀ y, y ∈ w.adicCompletionIntegers F ↔ ψ y ∈ w.adicCompletionIntegers F) (y : w.adicCompletion F) :
    ψ y = y := by
  have hval : ∀ b : F, Valued.v (algebraMap F (w.adicCompletion F) b) = w.valuation F b := by
    intro b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

  have hcmp : ∀ (b : F) (u : w.adicCompletion F), b ≠ 0 →
      (Valued.v u ≤ Valued.v (algebraMap F (w.adicCompletion F) b) ↔
        Valued.v (ψ u) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)) := by
    intro b u hb
    have hb' : (algebraMap F (w.adicCompletion F) b) ≠ 0 := by simpa using hb
    have hpos : 0 < Valued.v (algebraMap F (w.adicCompletion F) b) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb')
    have h1 := hO (u / algebraMap F _ b)
    rw [map_div₀, hF, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_div₀, div_le_one₀ hpos,
      div_le_one₀ hpos] at h1
    exact h1

  have hball : ∀ (b : F) (z : w.adicCompletion F), b ≠ 0 →
      {x : w.adicCompletion F | Valued.v (x - z) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)} ∈ 𝓝 z := by
    intro b z hb
    set t := algebraMap F (w.adicCompletion F) b
    have ht : t ≠ 0 := by simpa [t] using hb
    have hpos : 0 < Valued.v t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)
    have hc : Continuous fun x : w.adicCompletion F => (x - z) / t := by fun_prop
    have ho := (Valued.isOpen_valuationSubring (w.adicCompletion F)).preimage hc
    refine mem_of_superset (ho.mem_nhds ?_) ?_
    · show (z - z) / t ∈ Valued.v.valuationSubring
      rw [sub_self, zero_div]; exact zero_mem _
    · intro x hx
      have hx' : Valued.v ((x - z) / t) ≤ 1 := hx
      rw [map_div₀, div_le_one₀ hpos] at hx'
      exact hx'
  by_contra hne
  have hz0 : ψ y - y ≠ 0 := sub_ne_zero.mpr hne
  have hvz : Valued.v (ψ y - y) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuation_surjective F w (Valued.v (ψ y - y) * WithZero.exp (-1 : ℤ))
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hb
    exact (mul_ne_zero hvz WithZero.exp_ne_zero) hb.symm
  have hbv : Valued.v (algebraMap F (w.adicCompletion F) b) < Valued.v (ψ y - y) := by
    rw [hval, hb]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hvz) (by have h : (WithZero.exp (1:ℤ))⁻¹ < 1 := compareOfLessAndEq_eq_lt.mp rfl; simpa using h)
  obtain ⟨_, hx, a, rfl⟩ := mem_closure_iff_nhds.1
    ((HeightOneSpectrum.denseRange_algebraMap F w) y) _ (hball b y hb0)
  have h1 : Valued.v (y - algebraMap F _ a) ≤ Valued.v (algebraMap F (w.adicCompletion F) b) := by
    rw [← Valuation.map_neg, neg_sub]; exact hx
  have h2 := (hcmp b _ hb0).1 h1
  rw [map_sub, hF] at h2
  have h3 : ψ y - y = (ψ y - algebraMap F _ a) - (y - algebraMap F _ a) := by ring
  have h4 := Valuation.map_sub Valued.v (ψ y - algebraMap F _ a) (y - algebraMap F _ a)
  rw [← h3] at h4
  exact absurd (h4.trans (max_le h2 h1)) (not_le.2 hbv)

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

theorem firstFactor_agree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W Q : Type) [CommRing W] [Field Q] [Algebra W Q] (w w' : HeightOneSpectrum (𝓞 F)) (e : Q ≃+* w.adicCompletion F) (e' : Q ≃+* w'.adicCompletion F) (φ : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F) (φ' : E ⊗[F] w'.adicCompletion F →+* w'.adicCompletion F), (∀ c, φ ((1 : E) ⊗ₜ[F] c) = c) → (∀ c, φ' ((1 : E) ⊗ₜ[F] c) = c) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e' x ∈ w'.adicCompletionIntegers F) → (∀ a : E, e.symm (φ (a ⊗ₜ[F] 1)) = e'.symm (φ' (a ⊗ₜ[F] 1))) → w = w' ∧ ∀ x : AfE F E, e.symm (φ (prV (E := E) w x)) = e'.symm (φ' (prV (E := E) w' x)) := by
  intro F E _ _ _ _ _ W Q _ _ _ w w' e e' φ φ' hφ hφ' hW hW' hE
  have hF : ∀ a : F, e.symm (algebraMap F _ a) = e'.symm (algebraMap F _ a) := by
    intro a
    have h := hE (algebraMap F E a)
    have h1 : (algebraMap F E a) ⊗ₜ[F] (1 : w.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    have h2 : (algebraMap F E a) ⊗ₜ[F] (1 : w'.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    rwa [h1, h2, hφ, hφ'] at h
  have hO : ∀ x : Q, e x ∈ w.adicCompletionIntegers F ↔ e' x ∈ w'.adicCompletionIntegers F :=
    fun x => (hW x).symm.trans (hW' x)
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (b : F),
      Valued.v (algebraMap F (v.adicCompletion F) b) = v.valuation F b := by
    intro v b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hww : w = w' := by
    by_contra hne
    have hle : ¬ w.asIdeal ≤ w'.asIdeal := fun h =>
      hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h))
    obtain ⟨b, hbw, hbw'⟩ := Set.not_subset.1 hle
    have key := hO (e.symm (algebraMap F _ (algebraMap (𝓞 F) F b)⁻¹))
    rw [RingEquiv.apply_symm_apply, hF, RingEquiv.apply_symm_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      hval, hval, map_inv₀, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hbw', inv_one] at key
    have h1 : w.intValuation b < 1 := (HeightOneSpectrum.intValuation_lt_one_iff_mem w b).2 hbw
    have h0 : w.intValuation b ≠ 0 :=
      HeightOneSpectrum.intValuation_ne_zero w b (fun h => hbw' (h ▸ w'.asIdeal.zero_mem))
    have := key.2 le_rfl
    exact absurd this (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 h1))
  subst hww
  refine ⟨rfl, ?_⟩
  have hψ := adic_ringEquiv_eq_self w (e.symm.trans e') (fun a => by simp [hF a])
    (fun y => by simpa using hO (e.symm y))
  have hc : ∀ c, e.symm c = e'.symm c := fun c => by
    have h := hψ c
    simp only [RingEquiv.trans_apply] at h
    rw [← e'.symm_apply_apply (e.symm c), h]
  intro x
  generalize prV (E := E) w x = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
      have : a ⊗ₜ[F] c = (a ⊗ₜ[F] (1 : w.adicCompletion F)) * ((1 : E) ⊗ₜ[F] c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, map_mul, map_mul, map_mul, map_mul, hφ, hφ', hE a, hc]
  | add x y hx hy => simp [map_add, hx, hy]

end GlobalTheory.TwV.Xc

end
