import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi.OpenInv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def invSub (F : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, F (g * finGL E a k) = F g}
  one_mem' g := by simp
  mul_mem' {k l} hk hl g := by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' {k} hk g := by
    have := hk (g * finGL E a k⁻¹)
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    exact this.symm

variable (E a) in

def openInv : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsOpen (invSub F : Set (GL (Fin a) (Af E)))}
  zero_mem' := by
    have : invSub (0 : GA E a → ℂ) = ⊤ := by
      ext k; simp [invSub]
    show IsOpen ((invSub (0 : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E))) : Set (GL (Fin a) (Af E)))
    rw [this]; exact isOpen_univ
  add_mem' {F G} hF hG := by
    have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
    have hG' : IsOpen (invSub G : Set (GL (Fin a) (Af E))) := hG
    refine Subgroup.isOpen_mono (H₁ := invSub F ⊓ invSub G) ?_ (hF'.inter hG')
    intro k hk g
    simp only [Pi.add_apply]
    rw [hk.1 g, hk.2 g]
  smul_mem' c F hF := by
    refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ hF
    intro k hk g
    simp only [Pi.smul_apply]
    rw [hk g]

theorem rt_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) (h : GA E a) :
    (fun g => F (g * h)) ∈ openInv E a := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have hh : infGL E a y * finGL E a k = h := infGL_mul_finGL h
  have hc : Continuous fun u : GL (Fin a) (Af E) => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  let U : Subgroup (GL (Fin a) (Af E)) := (invSub F).comap (MulAut.conj k⁻¹).toMonoidHom
  have hU : (U : Set _) = (fun u : GL (Fin a) (Af E) => k⁻¹ * u * k) ⁻¹' (invSub F : Set _) := by
    ext u; simp [U, MulAut.conj_apply]
  have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
  refine Subgroup.isOpen_mono (H₁ := U) ?_ (by rw [hU]; exact hF'.preimage hc)
  intro u hu g
  have hu' : ∀ g, F (g * finGL E a (k⁻¹ * u * k)) = F g := by
    have hm : k⁻¹ * u * k ∈ invSub F := by
      have := Subgroup.mem_comap.1 hu; simpa [MulAut.conj_apply] using this
    exact hm
  change F (g * finGL E a u * h) = F (g * h)
  rw [← hu' (g * h), ← hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E a u) (infGL E a y), ← infGL_comm, mul_assoc, mul_inv_cancel_left]

theorem kerInf_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) {X : Type} [MeasurableSpace X]
    (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : kerInf ν k γ F ∈ openInv E a := by
  refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ (show IsOpen (invSub F : Set (GL (Fin a) (Af E))) from hF)
  intro u hu g
  change ∫ x, k x * F (g * finGL E a u * infGL E a (γ x)) ∂ν = ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
  congr 1; funext x
  rw [mul_assoc, ← infGL_comm, ← mul_assoc, hu]

theorem mem_openInv_of_mem {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ openInv E a := by
  have h := π.isSmooth_finPart ⟨φ, hφ⟩
  show IsOpen (invSub φ.1 : Set (GL (Fin a) (Af E)))
  have e : (invSub φ.1 : Set (GL (Fin a) (Af E))) = {k | π.finPart k ⟨φ, hφ⟩ = ⟨φ, hφ⟩} := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    exact ⟨fun hk => Subtype.ext (Subtype.ext (funext hk)), fun hk g => congrArg (fun ψ : π.V => ψ.1.1 g) hk⟩
  rw [e]; exact h

end GlobalTheory.JSW.MirSemi.OpenInv

open GlobalTheory.JSW.MirSemi.OpenInv in

theorem GlobalTheory.JSW.MirSemi.locSpan_openInv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V →
    ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)),
      IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  intro E _ _ _ a S π φ hφ F hF
  have h := GlobalTheory.JSW.MirSemi.locSpan_le (V := openInv E a) (S := S) (mem_openInv_of_mem hφ)
    (fun F hF h _ => rt_mem_openInv hF h) (fun F hF X _ ν _ k γ _ => kerInf_mem_openInv hF ν k γ) hF
  exact ⟨invSub F, h, fun u hu g => hu g⟩
