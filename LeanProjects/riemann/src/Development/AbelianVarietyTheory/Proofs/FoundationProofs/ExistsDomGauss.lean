import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_dom_gauss : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ V : ValuationSubring Ω, ∃ W : ValuationSubring X.K, Dom X V W ∧ Gauss X.jK V W := by
  intro Ω _ _ _ ε X V
  classical
  open GaussDom in
  haveI : (RingHom.ker (redA V X.exp)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hA, hinv, hlt⟩ :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (GaussDom.intA V X.exp) (RingHom.ker (GaussDom.redA V X.exp))
  have hker : ∀ x : GaussDom.intA V X.exp, x ∈ RingHom.ker (GaussDom.redA V X.exp) ↔
      ∀ r, (X.exp x).coeff r ∈ V.nonunits :=
    fun x => (RingHom.mem_ker).trans (GaussDom.redA_eq_zero V X.exp x)
  have hone : ∀ x : GaussDom.intA V X.exp, x ∉ RingHom.ker (GaussDom.redA V X.exp) → W.valuation (x : X.K) = 1 := by
    intro x hx
    have hx0 : (x : X.K) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this]
      exact Ideal.zero_mem _
    have h1 := (W.valuation_le_one_iff _).2 (hA x)
    have h2 := (W.valuation_le_one_iff _).2 (hinv x hx)
    rw [map_inv₀] at h2
    have hv0 : W.valuation (x : X.K) ≠ 0 := by simpa using hx0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)
  have hj3 : ∀ r, (X.exp X.jK).coeff r ∈ V := fun r => by
    obtain ⟨n, hn⟩ := X.j_exp.2.2 r
    rw [hn]
    exact intCast_mem V n
  have hj1 : (X.exp X.jK).coeff (-1) = 1 := X.j_exp.1
  have hj2 : ∀ r : ℚ, r < -1 → (X.exp X.jK).coeff r = 0 := X.j_exp.2.1
  refine ⟨W, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    exact hA ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
  · intro f hf
    have hfi : f ∈ GaussDom.intA V X.exp :=
      (GaussDom.mem_intA V X.exp f).2 (fun r => V.valuation_le_one_iff _ |>.1 (le_of_lt
        ((ValuationSubring.mem_nonunits_iff _).1 (hf r))))
    exact hlt ⟨f, hfi⟩ ((hker _).2 hf)
  · rintro f ⟨hf, r, hr⟩
    apply hone ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
    intro hk
    have := (hker _).1 hk r
    rw [ValuationSubring.mem_nonunits_iff] at this
    exact absurd hr (ne_of_lt this)
  · intro a
    constructor
    · intro ha
      by_contra hnot
      have ha0 : a ≠ 0 := fun h => hnot (h ▸ V.zero_mem)
      have hinvV : a⁻¹ ∈ V := (V.mem_or_inv_mem a).resolve_left hnot
      have hnu : a⁻¹ ∈ V.nonunits := by
        rw [ValuationSubring.mem_nonunits_iff]
        refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_
        intro h1
        apply hnot
        rw [map_inv₀, inv_eq_one] at h1
        exact (V.valuation_le_one_iff a).1 (le_of_eq h1)
      have hm : algebraMap Ω X.K a⁻¹ ∈ GaussDom.intA V X.exp := GaussDom.const_mem V X.exp _ hinvV
      have hk : (⟨_, hm⟩ : GaussDom.intA V X.exp) ∈ RingHom.ker (GaussDom.redA V X.exp) := by
        rw [hker]
        intro r
        show (X.exp (algebraMap Ω X.K a⁻¹)).coeff r ∈ V.nonunits
        rw [GaussDom.coeff_const]
        split_ifs
        · exact hnu
        · exact GaussDom.zero_mem_nonunits V
      have h3 : W.valuation (algebraMap Ω X.K a⁻¹) < 1 := hlt _ hk
      have h4 := (W.valuation_le_one_iff _).2 ha
      have h5 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have h6 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) ≤
          1 * W.valuation (algebraMap Ω X.K a⁻¹) := by gcongr
      rw [h5, one_mul] at h6
      exact absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)
    · intro ha
      exact hA ⟨_, GaussDom.const_mem V X.exp a ha⟩
  · rintro P hP ⟨i0, hne, hi0, hi0'⟩
    have hjA : X.jK ∈ GaussDom.intA V X.exp := (GaussDom.mem_intA V X.exp X.jK).2 hj3
    obtain ⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P :=
      (Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)
    let ι : V →+* GaussDom.intA V X.exp :=
      ((algebraMap Ω X.K).comp V.subtype).codRestrict (GaussDom.intA V X.exp)
        (fun v => GaussDom.const_mem V X.exp v v.2)
    have hx : Polynomial.aeval X.jK P = (GaussDom.intA V X.exp).subtype (P'.eval₂ ι ⟨X.jK, hjA⟩) := by
      rw [Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hx]
    apply hone
    intro hk
    rw [RingHom.mem_ker, Polynomial.hom_eval₂] at hk
    have hc : (GaussDom.redA V X.exp).comp ι =
        (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp
          (IsLocalRing.residue V) := by
      apply RingHom.ext
      intro v
      exact GaussDom.redA_const V X.exp v
    rw [hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hk
    set J := GaussDom.redA V X.exp ⟨X.jK, hjA⟩ with hJdef
    have hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ) := by
      apply HahnSeries.orderTop_eq_of_le
      · rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff]
        have h1 : (⟨(X.exp X.jK).coeff (-1), (GaussDom.mem_intA V X.exp X.jK).1 hjA (-1)⟩ : V) = 1 :=
          Subtype.ext hj1
        rw [h1, map_one]
        exact one_ne_zero
      · intro g hg
        rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff] at hg
        by_contra hlt'
        apply hg
        have h0 : (⟨(X.exp X.jK).coeff g, (GaussDom.mem_intA V X.exp X.jK).1 hjA g⟩ : V) = 0 :=
          Subtype.ext (hj2 g (lt_of_not_ge hlt'))
        rw [h0, map_zero]
    have hQ : P'.map (IsLocalRing.residue V) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun Q => Q.coeff i0) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0
      have hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0 := by
        rw [← hP', Polynomial.coeff_map]
        rfl
      have hu : IsUnit (P'.coeff i0) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩
        show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1
        rw [hPi, mul_inv_cancel₀ hne]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at hc0
      exact hc0 hu
    have hot := GaussDom.orderTop_aeval J hJ _ _ hQ rfl
    rw [hk, HahnSeries.orderTop_zero] at hot
    exact WithTop.top_ne_coe hot

end GlobalTheory.KZ.ES
