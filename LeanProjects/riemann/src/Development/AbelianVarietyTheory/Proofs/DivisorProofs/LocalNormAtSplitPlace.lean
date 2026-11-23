import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalNormSplit

theorem exists_sq_of_split (E : Type) [Field E] [NumberField E] [IsCMField E]
    (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧
      w'.under (𝓞 (maximalRealSubfield E)) = v)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) :
    ∃ s : v.adicCompletion (maximalRealSubfield E),
      s * s = algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) d := by
  classical
  by_contra hns
  push_neg at hns
  obtain ⟨w, w', hne, hw, hw'⟩ := hv
  obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp (maximalRealSubfield E) E
  have hθF : ∀ a : maximalRealSubfield E, (a : E) ≠ θ := by
    intro a ha
    have h1 : IsCMField.complexConj E (a : E) = a := (IsCMField.complexConj_eq_self_iff E _).2 a.2
    rw [ha, hθ] at h1
    exact hθ0 (by linear_combination -h1 / 2)
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      simpa using hpq
    · exfalso
      refine hθF (-p / q) ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hpq
      have hq' : (q : E) ≠ 0 := by simpa using hq
      change ((-p / q : maximalRealSubfield E) : E) = θ
      push_cast
      field_simp
      rw [show algebraMap _ E p = p from rfl, show algebraMap _ E q = q from rfl] at hpq
      linear_combination -hpq
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  set K := v.adicCompletion (maximalRealSubfield E)
  let bA := Algebra.TensorProduct.basis K b
  let t : K ⊗[maximalRealSubfield E] E := 1 ⊗ₜ θ
  have hb0 : bA 0 = 1 := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hb1 : bA 1 = t := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, t]
  have li : ∀ p q : K, algebraMap K _ p + algebraMap K _ q * t = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have := Fintype.linearIndependent_iff.1 bA.linearIndependent ![p, q] (by
      rw [Fin.sum_univ_two, hb0, hb1]
      simpa [Algebra.smul_def] using h)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have sp : ∀ y, y = algebraMap K _ (bA.repr y 0) + algebraMap K _ (bA.repr y 1) * t := by
    intro y
    conv_lhs => rw [← bA.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  have htt : t * t = algebraMap K _ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ θ * (1 : K) ⊗ₜ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd]
    exact (Algebra.TensorProduct.includeRight.commutes d)
  let W := {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 (maximalRealSubfield E)) = v}
  let w₀ : W := ⟨w, hw⟩
  let w₁ : W := ⟨w', hw'⟩
  have h01 : w₀ ≠ w₁ := fun h => hne (congrArg Subtype.val h)
  let e₀ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₀ 1
  let e₁ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₁ 1
  obtain ⟨u₀, hu₀⟩ := (hb v).2 e₀
  obtain ⟨u₁, hu₁⟩ := (hb v).2 e₁
  have hprod : u₀ * u₁ = 0 := by
    apply (hb v).1
    funext u
    simp only [map_mul, map_zero]
    rw [show ψ v u u₀ = e₀ u from congrFun hu₀ u, show ψ v u u₁ = e₁ u from congrFun hu₁ u]
    by_cases h : u = w₀
    · subst h
      simp [e₁, Pi.single_apply, h01]
    · simp [e₀, Pi.single_apply, h]
  have hn₀ : u₀ ≠ 0 := by
    rintro rfl
    have := congrFun hu₀ w₀
    simp [e₀] at this
  have hn₁ : u₁ ≠ 0 := by
    rintro rfl
    have := congrFun hu₁ w₁
    simp [e₁] at this
  obtain ⟨a, b', hu0⟩ : ∃ a b' : K, u₀ = algebraMap K _ a + algebraMap K _ b' * t := ⟨_, _, sp u₀⟩
  obtain ⟨c, e, hu1⟩ : ∃ c e : K, u₁ = algebraMap K _ c + algebraMap K _ e * t := ⟨_, _, sp u₁⟩
  set d' := algebraMap (maximalRealSubfield E) K d
  have ha : ¬ (a = 0 ∧ b' = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₀
    rw [hu0, h1, h2]
    simp
  have hc : ¬ (c = 0 ∧ e = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₁
    rw [hu1, h1, h2]
    simp
  have heq := li (a * c + d' * b' * e) (a * e + b' * c) (by
    rw [← hprod, hu0, hu1]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap K _ b' * algebraMap K _ e)) * htt)
  have hz : c * c - d' * e * e = 0 := by
    by_contra hz
    apply ha
    constructor
    · refine (mul_eq_zero.1 (?_ : a * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination c * heq.1 - d' * e * heq.2
    · refine (mul_eq_zero.1 (?_ : b' * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination -(e * heq.1) + c * heq.2
  by_cases he : e = 0
  · apply hc
    refine ⟨?_, he⟩
    rw [he] at hz
    simpa using hz
  · apply hns (c / e)
    field_simp
    linear_combination hz

theorem exists_norm_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v) → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x := by
  intro E _ _ _ r Q x hx v hv
  obtain ⟨θ, hθ0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  have hθ' : IsCMField.complexConj E θ = -θ := hθ
  have hdmem : θ * θ ∈ maximalRealSubfield E :=
    (IsCMField.complexConj_eq_self_iff E _).1 (by rw [map_mul, hθ']; ring)
  let K := v.adicCompletion (maximalRealSubfield E)
  obtain ⟨d, hd⟩ : ∃ d : maximalRealSubfield E, (d : E) = θ * θ := ⟨⟨_, hdmem⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_sq_of_split E θ hθ0 hθ' v hv d hd
  let B := K ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm] at hs
    have h1 := (_root_.map_eq_zero (algebraMap (maximalRealSubfield E) K)).1 hs
    rw [h1] at hd
    exact hθ0 (mul_self_eq_zero.1 (by simpa using hd.symm))
  let uT : B := 1 ⊗ₜ algebraMap E _ θ
  have hTT : uT * uT = algebraMap K B (s * s) := by
    rw [hs, ← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ algebraMap E _ θ * (1 : K) ⊗ₜ algebraMap E _ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, ← hd,
      show (d : E) = algebraMap (maximalRealSubfield E) E d from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes _)
  let uc : B := algebraMap K B s⁻¹ * uT
  have hc : uc * uc = 1 := by
    have : uc * uc = algebraMap K B (s⁻¹ * s⁻¹ * (s * s)) := by
      rw [map_mul, map_mul, ← hTT]; ring
    rw [this, show s⁻¹ * s⁻¹ * (s * s) = 1 by rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hs0 hs0)], map_one]
  have hiT : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uT = -uT := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ algebraMap E _ θ) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap, hθ',
      map_neg, TensorProduct.tmul_neg]
  have hic : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uc = -uc := by
    change GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (algebraMap K B s⁻¹ * uT) = -(algebraMap K B s⁻¹ * uT)
    rw [map_mul, AlgHom.commutes, hiT, mul_neg]
  have hiX : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (1 ⊗ₜ x) = 1 ⊗ₜ x := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hx]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap (maximalRealSubfield E) K) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  let hf : B := algebraMap K B 2⁻¹
  have hh : hf * 2 = 1 := by
    rw [← map_ofNat (algebraMap K B) 2, ← map_mul, inv_mul_cancel₀ h2K, map_one]
  have hih : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K hf = hf := AlgHom.commutes _ _
  refine ⟨hf * (1 + uc) * (1 ⊗ₜ x) + hf * (1 - uc), ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, map_add, map_sub, map_one, hic, hiX, hih]
  linear_combination (hf ^ 2 * (2 * (1 ⊗ₜ x : B) - (1 ⊗ₜ x : B) ^ 2 - 1)) * hc + ((2 * hf + 1) * (1 ⊗ₜ x : B)) * hh

end GlobalTheory.LocalNormSplit
