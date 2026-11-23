import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

noncomputable def evVec {n : Type} (v : HeightOneSpectrum (𝓞 F)) (x : n → Af F ⊗[F] E) : n → Fv F v ⊗[F] E :=
  fun i => evF E v (x i)

theorem evVec_mul {n : Type} (v : HeightOneSpectrum (𝓞 F)) (ε : Af F ⊗[F] E) (x : n → Af F ⊗[F] E) :
    evVec v (fun a => ε * x a) = evF E v ε • evVec v x := by
  funext a
  exact map_mul _ _ _

theorem evVec_mulVec {m n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F))
    (A : Matrix m n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    evVec v (A.mulVec z) = (A.map (evF E v)).mulVec (evVec v z) := by
  funext a
  exact RingHom.map_mulVec _ _ _ _

theorem evVec_sgT {n : Type} (v : HeightOneSpectrum (𝓞 F)) (y : n → Fv F v ⊗[F] E) :
    evVec v (fun i => sgT E v (y i)) = y := by
  funext a
  exact evF_sgT_self _ _

theorem mul_eq_iff {n : Type} {v : HeightOneSpectrum (𝓞 F)} {ε : Af F ⊗[F] E}
    (hε : ∀ w, w ≠ v → evF E w ε = 0) (x x' : n → Af F ⊗[F] E) :
    ((fun a => ε * x a) = fun a => ε * x' a) ↔ evF E v ε • evVec v x = evF E v ε • evVec v x' := by
  rw [← evVec_mul, ← evVec_mul]
  refine ⟨fun h => by rw [h], fun h => funext fun a => evF_ext fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact congrFun h a
  · rw [map_mul, map_mul, hε w hw, zero_mul, zero_mul]

theorem evVec_newBasis {m n : ℕ} (hr : m = n) (v : HeightOneSpectrum (𝓞 F))
    (φ : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (B : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (z : Fin m → Af F ⊗[F] E) :
    evVec v (((φ.map (sgT E v) * B).submatrix id (Fin.cast hr)).mulVec z) =
      φ.mulVec (evVec v (B.mulVec fun i => z (Fin.cast hr.symm i))) := by
  subst hr
  have h : (φ.map (sgT E v)).map (evF E v) = φ := by
    ext i j : 1
    exact evF_sgT_self _ _
  show evVec v ((φ.map (sgT E v) * B).mulVec z) = φ.mulVec (evVec v (B.mulVec z))
  rw [← Matrix.mulVec_mulVec, evVec_mulVec, h]

theorem mul_mem_lamHat_iff [NumberField E] [StarRing E] (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}
    {ε : Af F ⊗[F] E} (hε : ∀ w, w ≠ v → evF E w ε = 0) (x : Fin V.rank → Af F ⊗[F] E) :
    (fun a => ε * x a) ∈ lamHat F V ↔ evF E v ε • evVec v x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  rw [mem_lamHat_iff, ← evVec_mul]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · simp only [map_mul, hε w hw, zero_mul]; exact zero_mem _

theorem divG_of_local_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → ∀ (hr : V'.rank = V.rank) (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram) (g' : HA (AF F) hc.sig V'.gram), f * e = e → (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ → DivG hc V e ϖ d g → DivG hc V' e ϖ (fun i => d (Fin.cast hr i)) g' := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf hφψ hψφ hL hr e ϖ d g g' hfe hg ⟨B, h1, h2, h3, h4⟩
  have hε : ∀ w, w ≠ v → evF E w (finP F E e) = 0 := ((GlobalTheory.SuppLocal.idem_mul_iff hf e).1 hfe).2
  have hback : ∀ y, φ.mulVec (ψ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  have hback' : ∀ y, ψ.mulVec (φ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hψφ, Matrix.one_mulVec]
  have hψ : ∀ y ∈ lamHat F V', (fun i => sgT E v (ψ.mulVec (evVec v y) i)) ∈ lamHat F V := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hL _).2 (by rw [hback]; exact (mem_lamHat_iff V' y).1 hy v))
  have hφ : ∀ y ∈ lamHat F V, (fun i => sgT E v (φ.mulVec (evVec v y) i)) ∈ lamHat F V' := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V' v ((hL _).1 ((mem_lamHat_iff V y).1 hy v))
  have hg' : ∀ y, evVec v ((finMat hc.sig V'.gram g').mulVec y) =
      φ.mulVec (((finMat hc.sig V.gram g).map (evF E v)).mulVec (ψ.mulVec (evVec v y))) := fun y => by
    rw [evVec_mulVec, ← locMat_val, hg, locMat_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨(φ.map (sgT E v) * B).submatrix id (Fin.cast hr), fun z hz => ?_, fun y hy => ?_, fun y hy => ?_,
    fun z hz => ?_⟩
  · rw [mul_mem_lamHat_iff V' hε, evVec_newBasis, ← Matrix.mulVec_smul, ← hL, ← mul_mem_lamHat_iff V hε]
    exact h1 _ fun i => hz _
  · obtain ⟨z, hz, e2⟩ := h2 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, ← Matrix.mulVec_smul]
    refine Eq.trans ?_ (congrArg φ.mulVec e2)
    rw [Matrix.mulVec_smul, hback]
  · obtain ⟨z, hz, e2⟩ := h3 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2
  · obtain ⟨y, hy, e2⟩ := h4 (fun i => z (Fin.cast hr.symm i)) fun i => hz _
    refine ⟨_, hφ y hy, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', evVec_sgT, hback', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2

end GlobalTheory.DivTransport
