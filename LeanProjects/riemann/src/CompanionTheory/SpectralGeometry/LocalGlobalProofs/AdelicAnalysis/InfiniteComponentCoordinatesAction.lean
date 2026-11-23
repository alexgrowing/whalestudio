import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem repr_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]

theorem cv_ratTup (R : Type) [CommRing R] [Algebra F R] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) :
    cv R b (ratTup R (ofF b x) 0) = fun j => algebraMap F R (x j) := by
  funext p
  have h : b.repr (∑ k, x (p.1, k) • b k) p.2 = x p := by
    rw [Module.Basis.repr_sum_self]
  simp only [cv, ratTup, ofF, inclR]
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (∑ k, x (p.1, k) • b k)) p.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, h, one_smul]

theorem cv_act (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J)
    (x : Fin M × Fin d → F) :
    cv R b (actW R σ J h (ratTup R (ofF b x)) 0) =
      gmat R σ J b h *ᵥ fun j => algebraMap F R (x j) := by
  rw [← cv_ratTup R b x]
  refine TraceCoord.coord_mulVec (Algebra.TensorProduct.basis R b)
    (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (gmat R σ J b h) (fun p q => ?_) _
  rw [Algebra.TensorProduct.basis_apply]
  rfl

end Alg

theorem coords_ratTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (ω : HA (AF F) σ J) (x : Fin M × Fin d → F), (∀ w, xw e b (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)))) w = ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ∧ cv (Af F) b (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x))) 0) = gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j) := by
  intro F E _ _ _ _ _ σ _ M J _ d b ρ e he ω x
  have hY := cv_act (AF F) σ J b ω⁻¹ x
  set Y := actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)) with hYdef
  have hc : ∀ p, (Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2 =
      (gmat (AF F) σ J b ω⁻¹ *ᵥ fun j => algebraMap F (AF F) (x j)) p := fun p =>
    congrFun hY p
  refine ⟨fun w => ?_, ?_⟩
  · funext p
    let φ : AF F →+* ℝ :=
      (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F))
    have h1 : xw e b (projInf Y) w p = φ ((Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2) := by
      change e ((Algebra.TensorProduct.basis (Ainf F) b).repr
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (Y 0 p.1)) p.2) w = _
      rw [repr_map]
      rfl
    rw [h1, hc, RingHom.map_mulVec]
    have h2 : (φ ∘ fun j => algebraMap F (AF F) (x j)) = fun j => ρ w (x j) := by
      funext j
      change e (fstA F (algebraMap F (AF F) (x j))) w = _
      rw [(fstA F).commutes, he]
    rw [h2]
    rfl
  · funext p
    have h1 : cv (Af F) b (projFin Y 0) p =
        (sndA F : AF F →+* Af F) ((Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2) := by
      change (Algebra.TensorProduct.basis (Af F) b).repr
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (Y 0 p.1)) p.2 = _
      rw [repr_map]
      rfl
    rw [h1, hc, RingHom.map_mulVec]
    have h2 : ((sndA F : AF F →+* Af F) ∘ fun j => algebraMap F (AF F) (x j)) =
        fun j => algebraMap F (Af F) (x j) := by
      funext j
      exact (sndA F).commutes (x j)
    rw [h2]
    rfl

end GlobalTheory.CompanionTheory.SW.BB.RatCoord
