import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def IsU (z : Fv F v ⊗[F] E) : Prop := ∃ w ∈ OEv (E := E) v, z * w = 1

theorem sigR_algebraMap (a : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_mem {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) : sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    rw [sigR_inclR]
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    exact gen_mem v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * sigR (Fv F v) σ x =
        r • sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    rw [h1, map_mul, sigR_algebraMap, h2]
    exact Submodule.smul_mem _ r hx

theorem hR_add_left' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + y) z = hR (Fv F v) σ J x z + hR (Fv F v) σ J y z := by
  simp only [hR, hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hR_add_right' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_sub_left' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x - y) z = hR (Fv F v) σ J x z - hR (Fv F v) σ J y z := by
  simp only [hR, hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hR_sum_left' {ι : Type} (s : Finset ι) (f : ι → Fin n → Fv F v ⊗[F] E) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k ∈ s, f k) z = ∑ k ∈ s, hR (Fv F v) σ J (f k) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_left _
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hR_add_left', ih]

theorem splitG (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ) (hU : UniG σ J v X) (x : Fin n → Fv F v ⊗[F] E)
    (hx : x ∈ latLoc (E := E) v Λ) :
    ∃ c : ι → Fv F v ⊗[F] E, (∀ i, c i ∈ OEv (E := E) v) ∧ x - ∑ i, c i • X i ∈ PerpG σ J v Λ X := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let X' : TupV (E := E) v n (Fintype.card ι) := fun k => X (e.symm k)
  have hX' : X' ∈ LamT v Λ (Fintype.card ι) := fun k => hX _
  obtain ⟨w, hw0, hw⟩ := hU
  have hdet : (gramR (Fv F v) σ J X').det = (gramG σ J v X).det := by
    have : gramR (Fv F v) σ J X' = (gramG σ J v X).submatrix e.symm e.symm := by
      ext i j; rfl
    rw [this, det_submatrix_equiv_self]
  obtain ⟨c', hc'0, hc'⟩ := split σ J v Λ (oSub v) (fun c hc y hy => oSmul v Λ hL c hc y hy) hsd X' hX' w hw0
    (by rw [hdet]; exact hw) x hx
  refine ⟨fun i => c' (e i), fun i => hc'0 _, ?_⟩
  have hs : ∑ i, c' (e i) • X i = ∑ k, c' k • X' k := by
    rw [← e.symm.sum_comp]
    simp [X']
  rw [hs]
  refine ⟨hc'.1, fun i => ?_⟩
  have := hc'.2 (e i)
  simpa [X'] using this

end PI.OmLocU.UnN
