import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SURepsExist

open Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem isUA_mul {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hg' : IsUA c G g') :
    IsUA c G (g * g') := by
  refine ⟨by rw [det_mul]; exact hg.1.mul hg'.1, fun x y => ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hg'.2]

theorem isUA_of_inv {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (h1 : g * g' = 1) :
    IsUA c G g' := by
  refine ⟨IsUnit.of_mul_eq_one g.det (by rw [mul_comm, ← det_mul, h1, det_one]), fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, h1, one_mulVec, one_mulVec]

variable {L : Set (Fin n → E)}

theorem stabilizer_maps_lattice_completion {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  rw [one_nsmul, sub_eq_iff_eq_add] at e
  rw [e]; exact (hat F L).add_mem hy hx

theorem stabilizer_of_maps_onto {k : Matrix (Fin n) (Fin n) (RA F E)} (hU : IsUA c G k)
    (hm : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L) (hs : ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x) :
    IsKM c G L 1 k :=
  ⟨hU, fun x hx => ⟨k *ᵥ x - x, (hat F L).sub_mem (hm x hx) hx, by rw [one_nsmul]⟩, hs⟩

theorem stabilizer_mul {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (hk' : IsKM c G L 1 k') :
    IsKM c G L 1 (k * k') := by
  refine stabilizer_of_maps_onto c G (isUA_mul c G hk.1 hk'.1) (fun x hx => ?_) (fun x hx => ?_)
  · rw [← mulVec_mulVec]; exact stabilizer_maps_lattice_completion c G hk (stabilizer_maps_lattice_completion c G hk' hx)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, rfl⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [mulVec_mulVec]⟩

theorem stabilizer_inv {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (h1 : k * k' = 1)
    (h2 : k' * k = 1) : IsKM c G L 1 k' := by
  refine stabilizer_of_maps_onto c G (isUA_of_inv c G hk.1 h1) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    rwa [mulVec_mulVec, h2, one_mulVec]
  · exact ⟨k *ᵥ x, stabilizer_maps_lattice_completion c G hk hx, by rw [mulVec_mulVec, h2, one_mulVec]⟩

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))

theorem isSA_mul {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (hg' : IsSA G g') : IsSA G (g * g') :=
  ⟨isUA_mul _ G hg.1 hg'.1, by rw [det_mul, hg.2, hg'.2, one_mul]⟩

theorem isSA_of_inv {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (h1 : g * g' = 1) : IsSA G g' :=
  ⟨isUA_of_inv _ G hg.1 h1, by
    have := congrArg Matrix.det h1
    rwa [det_mul, hg.2, one_mul, det_one] at this⟩

theorem ratM_inv (γ : Matrix (Fin r) (Fin r) E) (hγ : IsSA G (ratM (maximalRealSubfield E) γ)) :
    ratM (maximalRealSubfield E) γ * ratM (maximalRealSubfield E) γ⁻¹ = 1 ∧
    ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
  by_cases h : γ.det = 0
  · have e : (ratM (maximalRealSubfield E) γ).det = 0 := by
      have := (Algebra.TensorProduct.includeRight :
        E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).map_det γ
      rw [h, map_zero] at this
      exact this.symm
    rw [hγ.2] at e
    haveI : Subsingleton (RA (maximalRealSubfield E) E) := subsingleton_of_zero_eq_one e.symm
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · have hu : IsUnit γ.det := isUnit_iff_ne_zero.mpr h
    rw [← ratM_mul, ← ratM_mul, mul_nonsing_inv γ hu, nonsing_inv_mul γ hu, ratM_one]
    exact ⟨rfl, rfl⟩

def sSetoid : Setoid {g // IsSA G g} where
  r a b := SEquiv G L 1 a.1 b.1
  iseqv := by
    refine ⟨fun a => ⟨1, by rw [ratM_one]; exact ⟨⟨by simp, fun x y => by simp⟩, by simp⟩,
      1, isKM_one _ G L 1, by simp, by rw [ratM_one]; simp⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, k, hk, hdk, e⟩
      have hr := ratM_inv G γ hγ
      have hku : IsUnit k.det := by rw [hdk]; exact isUnit_one
      refine ⟨γ⁻¹, isSA_of_inv G hγ hr.1, k⁻¹, stabilizer_inv _ G hk (mul_nonsing_inv k hku)
        (nonsing_inv_mul k hku), ?_, ?_⟩
      · rw [det_nonsing_inv, hdk, Ring.inverse_one]
      · rw [e]
        calc a.1 = (ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ) * a.1 * (k * k⁻¹) := by
                rw [hr.2, mul_nonsing_inv k hku]; simp
          _ = _ := by simp only [Matrix.mul_assoc]
    · rintro a b d ⟨γ, hγ, k, hk, hdk, e⟩ ⟨γ', hγ', k', hk', hdk', e'⟩
      refine ⟨γ' * γ, by rw [ratM_mul]; exact isSA_mul G hγ' hγ, k * k', stabilizer_mul _ G hk hk',
        by rw [det_mul, hdk, hdk', one_mul], ?_⟩
      rw [e', e, ratM_mul]; simp only [Matrix.mul_assoc]

theorem exists_sReps : ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    IsSReps G L 1 s := by
  letI := sSetoid G L
  refine ⟨Quotient (sSetoid G L), fun q => q.out.1, fun q => q.out.2, fun i j h => ?_, fun g hg => ?_⟩
  · rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound h
  · exact ⟨⟦⟨g, hg⟩⟧, Quotient.mk_out (s := sSetoid G L) ⟨g, hg⟩⟩

end CM

end GlobalTheory.SURepsExist

theorem GlobalTheory.SURepsExist.main : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s := by
  intro D Tu Cl t0 _ i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  exact GlobalTheory.SURepsExist.exists_sReps _ _
