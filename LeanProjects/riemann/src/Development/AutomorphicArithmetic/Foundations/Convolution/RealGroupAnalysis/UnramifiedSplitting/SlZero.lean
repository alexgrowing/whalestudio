import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.H

local notation "Γv" => WithZero (Multiplicative ℤ)

private def eV : Γv := ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : Γv)

private lemma val_le_one_of (m : Γv) (h : eV * m ^ 2 ≤ 1) : m ≤ 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact zero_le'
  obtain ⟨k, rfl⟩ := WithZero.ne_zero_iff_exists.mp hm
  have h' : (Multiplicative.ofAdd (-1 : ℤ) * k ^ 2 : Multiplicative ℤ) ≤ 1 := by
    unfold eV at h
    exact_mod_cast h
  have h'' : (-1 : ℤ) + 2 * Multiplicative.toAdd k ≤ 0 := by
    have := Multiplicative.toAdd_le.mpr h'
    simpa [toAdd_mul, toAdd_pow] using this
  have : (k : Multiplicative ℤ) ≤ 1 := by
    apply Multiplicative.toAdd_le.mp
    simp only [toAdd_one]
    omega
  exact_mod_cast this

private lemma val_le_e_of (m : Γv) (h : eV⁻¹ * m ^ 2 ≤ 1) : m ≤ eV := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact zero_le'
  obtain ⟨k, rfl⟩ := WithZero.ne_zero_iff_exists.mp hm
  have h' : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ * k ^ 2 : Multiplicative ℤ) ≤ 1 := by
    unfold eV at h
    exact_mod_cast h
  have h'' : (1 : ℤ) + 2 * Multiplicative.toAdd k ≤ 0 := by
    have := Multiplicative.toAdd_le.mpr h'
    simpa [toAdd_mul, toAdd_pow] using this
  have : (k : Multiplicative ℤ) ≤ Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd_le.mp
    simp only [toAdd_ofAdd]
    omega
  unfold eV
  exact_mod_cast this

private lemma one_lt_eV : (1 : Γv) < eV⁻¹ := by
  have h : (1 : Multiplicative ℤ) < (Multiplicative.ofAdd (-1 : ℤ))⁻¹ := by
    apply Multiplicative.toAdd_lt.mp
    simp
  unfold eV
  exact_mod_cast h

private lemma psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, (adelicChar F).map_add_eq_mul]

private lemma cp_rt {K : Type} [Field K] [NumberField K] (v : P K) (x : K) :
    cp v (rt x) = algebraMap K (Kv v) x := rfl

private lemma key {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (hG : Gd D.δ v)
    (a : Kv v) (φ : S4 F) (hfix : ∀ c, IsInt c → W.Om (nU (sg v (a * c))) φ = φ) (u t : A F)
    (h : hat φ.1 ![0, 0, u, t] ≠ 0) :
    IsInt (a * (cp v u ^ 2 - algebraMap F (Kv v) D.δ * cp v t ^ 2)) := by
  have hH := hatSt F E D W
  obtain ⟨-, hmul, -⟩ := sgLaws F v
  apply hG.psi.2.2
  intro c hc
  have h1 := hH.n (sg v (a * c)) φ ![0, 0, u, t]
  rw [hfix c hc] at h1
  have hu : Function.update (![0, 0, u, t] : Fin 4 → A F) 1
      ((![0, 0, u, t] : Fin 4 → A F) 1 + sg v (a * c) * (![0, 0, u, t] : Fin 4 → A F) 0) = ![0, 0, u, t] := by
    ext1 i
    fin_cases i <;> simp [Function.update]
  rw [hu] at h1
  have h2 : ψ (sg v (a * c) * ((![0, 0, u, t] : Fin 4 → A F) 2 ^ 2 - rt D.δ * (![0, 0, u, t] : Fin 4 → A F) 3 ^ 2)) = 1 :=
    mul_right_cancel₀ h (by rw [one_mul]; exact h1.symm)
  have h3 : sg v (a * c) * ((![0, 0, u, t] : Fin 4 → A F) 2 ^ 2 - rt D.δ * (![0, 0, u, t] : Fin 4 → A F) 3 ^ 2) =
      sg v (c * (a * (cp v u ^ 2 - algebraMap F (Kv v) D.δ * cp v t ^ 2))) := by
    rw [mul_comm, hmul]
    congr 1
    simp only [Matrix.cons_val, map_sub, map_mul, map_pow, cp_rt]
    ring
  rw [h3] at h2
  exact h2

private lemma supp_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (v : P F) (hA : Aniso D.δ v) (a x y : Kv v)
    (h : IsInt (a * (x ^ 2 - algebraMap F (Kv v) D.δ * y ^ 2))) :
    Valued.v a * (max (Valued.v x) (Valued.v y)) ^ 2 ≤ 1 := by
  have h' : Valued.v (a * (x ^ 2 - algebraMap F (Kv v) D.δ * y ^ 2)) ≤ 1 := h
  rwa [map_mul, hA x y] at h'

end UpperTheory.ConvolutionTheory.R2.H

theorem UpperTheory.ConvolutionTheory.R2.H.slZero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → Aniso D.δ v → ∀ φ : S4 F,
      (∀ b, IsInt b → W.Om (nU (sg v ((ϖ : Kv v) * b))) φ = φ) →
      (∀ c, IsInt c → W.Om (wW F * nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) * (wW F)⁻¹) φ = φ) → Sl0 φ.1 := by
  intro F E _ _ _ _ _ _ _ D W v ϖ hU hG hA φ h1 h2 u t
  by_contra hne
  have hH := hatSt F E D W
  obtain ⟨hsgadd, hmul, hcp, -⟩ := sgLaws F v
  have hval : Valued.v (ϖ : Kv v) = eV := hU
  have hvali : Valued.v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) = eV⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval]
  obtain ⟨φ', hφ, h2'⟩ : ∃ φ' : S4 F, W.Om (wW F) φ' = φ ∧
      ∀ c, IsInt c → W.Om (nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c))) φ' = φ' := by
    refine ⟨W.Om (wW F)⁻¹ φ, ?_, ?_⟩
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro c hc
      have h3 := h2 c hc
      have e : (wW F)⁻¹ * (wW F * nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) * (wW F)⁻¹) =
          nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) * (wW F)⁻¹ := by group
      have h5 : W.Om (wW F)⁻¹ (W.Om (wW F * nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) * (wW F)⁻¹) φ) =
          W.Om (nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c))) (W.Om (wW F)⁻¹ φ) := by
        show (W.Om _ * W.Om _) φ = (W.Om _ * W.Om _) φ
        rw [← map_mul, ← map_mul, e]
      rw [← h5, h3]
  subst hφ

  have hs' : ∀ z₀ z₁ : A F, hat φ'.1 ![0, 0, z₀, z₁] ≠ 0 → Valued.v (cp v z₀) ≤ eV := by
    intro z₀ z₁ hz
    have h3 := supp_le D v hA _ _ _ (key D W v hG _ φ' h2' z₀ z₁ hz)
    rw [hvali] at h3
    exact (le_max_left _ _).trans (val_le_e_of _ h3)

  have hshift : ∀ u' : A F, hat (W.Om (wW F) φ').1 ![0, 0, u' + sg v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v), t] =
      hat (W.Om (wW F) φ').1 ![0, 0, u', t] := by
    intro u'
    rw [hH.w, hH.w]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have e1 : ∀ r : A F, (![-((![0, 0, r, t] : Fin 4 → A F) 1), (![0, 0, r, t] : Fin 4 → A F) 0, z 0, z 1] : Fin 4 → A F) = ![0, 0, z 0, z 1] := by
      intro r
      simp
    show hat φ'.1 _ * ψ _ = hat φ'.1 _ * ψ _
    rw [e1, e1]
    by_cases hz : hat φ'.1 ![0, 0, z 0, z 1] = 0
    · rw [hz, zero_mul, zero_mul]
    congr 1
    have hz0 := hs' _ _ hz
    have e2 : (2 : A F) * (z 0 * (![0, 0, u' + sg v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v), t] : Fin 4 → A F) 2 - rt D.δ * (z 1 * (![0, 0, u' + sg v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v), t] : Fin 4 → A F) 3)) =
        2 * (z 0 * (![0, 0, u', t] : Fin 4 → A F) 2 - rt D.δ * (z 1 * (![0, 0, u', t] : Fin 4 → A F) 3)) +
          sg v (cp v (2 * z 0) * ((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) := by
      rw [← hmul]
      simp only [Matrix.cons_val]
      ring
    rw [e2, psi_add]
    have e3 : ψ (sg v (cp v (2 * z 0) * ((ϖ⁻¹ : (Kv v)ˣ) : Kv v))) = 1 := by
      apply hG.psi.2.1
      show Valued.v _ ≤ 1
      have e4 : cp v (2 * z 0) = 2 * cp v (z 0) := by
        rw [map_mul, map_ofNat]
      rw [e4, map_mul, map_mul, hG.two, one_mul, hvali]
      calc Valued.v (cp v (z 0)) * eV⁻¹ ≤ eV * eV⁻¹ := mul_le_mul_left hz0 _
        _ = 1 := mul_inv_cancel₀ (by simp [eV])
    rw [e3, mul_one]

  have hint : ∀ u' : A F, hat (W.Om (wW F) φ').1 ![0, 0, u', t] ≠ 0 → Valued.v (cp v u') ≤ 1 := by
    intro u' hz
    have h3 := supp_le D v hA _ _ _ (key D W v hG _ _ h1 u' t hz)
    rw [hval] at h3
    exact (le_max_left _ _).trans (val_le_one_of _ h3)
  have hb1 := hint u hne
  have hb2 := hint (u + sg v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) (by rw [hshift]; exact hne)
  rw [map_add, hcp] at hb2
  have hb3 : Valued.v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) ≤ 1 := by
    have e5 : ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) = (cp v u + ((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) - cp v u := by ring
    rw [e5]
    exact (Valuation.map_sub _ _ _).trans (max_le hb2 hb1)
  rw [hvali] at hb3
  exact absurd hb3 (not_le.mpr one_lt_eV)
