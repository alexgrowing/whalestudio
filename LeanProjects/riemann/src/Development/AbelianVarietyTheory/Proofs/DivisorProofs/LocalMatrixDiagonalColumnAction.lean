import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.LeviBlockRealization.LocEmb

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
  [Algebra F R']

abbrev tm (E : Type) [Field E] [Algebra F E] (φ : R →ₐ[F] R') : R ⊗[F] E →+* R' ⊗[F] E :=
  (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom

theorem tm_inclR (φ : R →ₐ[F] R') (a : E) : tm E φ (inclR (F := F) R a) = inclR (F := F) R' a := by
  change Algebra.TensorProduct.map φ (AlgHom.id F E) (1 ⊗ₜ a) = 1 ⊗ₜ a
  simp

theorem tm_sigR (φ : R →ₐ[F] R') (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    tm E φ (sigR R σ z) = sigR R' σ (tm E φ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl

theorem tm_mat {n r : ℕ} (φ : R →ₐ[F] R') (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Matrix (Fin n) (Fin r) E)
    (i : Fin r) (a : R ⊗[F] E)
    (h : A.map (tm E φ) * X.map (inclR (F := F) R') =
      X.map (inclR (F := F) R') * diagonal (Function.update 1 i (tm E φ a))) (k : Fin n) (l : Fin r) :
    tm E φ ((A * X.map (inclR (F := F) R)) k l) =
      tm E φ ((X.map (inclR (F := F) R) * diagonal (Function.update 1 i a)) k l) := by
  have e1 : (X.map (inclR (F := F) R)).map (tm E φ) = X.map (inclR (F := F) R') := by
    ext k l
    exact tm_inclR φ _
  have e2 : (diagonal (Function.update (1 : Fin r → R ⊗[F] E) i a)).map (tm E φ) =
      diagonal (Function.update 1 i (tm E φ a)) := by
    rw [diagonal_map (map_zero _)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have := congrFun (congrFun h k) l
  rw [← e1, ← e2, ← Matrix.map_mul, ← Matrix.map_mul] at this
  exact this

theorem tm_vec {n : ℕ} (φ : R →ₐ[F] R') (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (z : Fin n → E)
    (h : A.map (tm E φ) *ᵥ (fun k => inclR (F := F) R' (z k)) = fun k => inclR (F := F) R' (z k)) (k : Fin n) :
    tm E φ ((A *ᵥ (fun k => inclR (F := F) R (z k))) k) = tm E φ (inclR (F := F) R (z k)) := by
  rw [RingHom.map_mulVec, tm_inclR]
  have e : (tm E φ) ∘ (fun k => inclR (F := F) R (z k)) = fun k => inclR (F := F) R' (z k) :=
    funext fun k => tm_inclR φ _
  rw [e, h]

end

theorem isPositionCentre_emb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (e : (Fv F v ⊗[F] E)ˣ) (i : Fin r),
    (matHom _ σ J x).1 * X.map (inclR (F := F) (Fv F v)) =
        X.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (e : Fv F v ⊗[F] E)) →
    (matHom _ σ J x).1 * Y.map (inclR (F := F) (Fv F v)) =
        Y.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (sigR (Fv F v) σ ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))) →
    (∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J x).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (z a)) = fun a => inclR (F := F) (Fv F v) (z a)) →
    GlobalTheory.LeviBlockRealization.IsBlockCentre σ J X Y i (GlobalTheory.Doubling.ideleAt F E v e) (emb σ J v x) := by
  intro F E _ _ _ _ _ σ n J r X Y v x e i h1 h2 h3
  have mv : (matHom _ σ J (emb σ J v x)).1.map (tm E (evFin F v)) = (matHom _ σ J x).1 :=
    congrArg (fun g => (matHom _ σ J g).1) (proj_emb_self σ J v x)
  have mu : ∀ u, u ≠ v → (matHom _ σ J (emb σ J v x)).1.map (tm E (evFin F u)) = 1 := fun u hu =>
    congrArg (fun g => (matHom _ σ J g).1) (proj_emb_ne σ J hu x)
  have mw : ∀ w, (matHom _ σ J (emb σ J v x)).1.map (tm E (evInf F w)) = 1 := fun w =>
    congrArg (fun g => (matHom _ σ J g).1) (projArch_emb σ J w v x)
  have ev : ∀ e : (Fv F v ⊗[F] E)ˣ, tm E (evFin F v) (GlobalTheory.Doubling.ideleAt F E v e).1 = e.1 := fun e =>
    congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_self v e)
  have eu : ∀ u, u ≠ v → ∀ e : (Fv F v ⊗[F] E)ˣ, tm E (evFin F u) (GlobalTheory.Doubling.ideleAt F E v e).1 = 1 :=
    fun u hu e => congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_ne hu e)
  have ew : ∀ w, ∀ e : (Fv F v ⊗[F] E)ˣ, tm E (evInf F w) (GlobalTheory.Doubling.ideleAt F E v e).1 = 1 :=
    fun w e => congrArg Units.val (GlobalTheory.Doubling.unitInf_ideleAt w v e)
  refine ⟨?_, ?_, fun z hz1 hz2 => ?_⟩
  · ext k l
    refine GlobalTheory.Doubling.adele_ext (fun w => tm_mat (evInf F w) _ X i _ ?_ k l)
      fun u => tm_mat (evFin F u) _ X i _ ?_ k l
    · rw [mw, ew]; simp
    · by_cases hu : u = v
      · subst hu; rw [mv, ev]; exact h1
      · rw [mu u hu, eu u hu]; simp
  · ext k l
    refine GlobalTheory.Doubling.adele_ext (fun w => tm_mat (evInf F w) _ Y i _ ?_ k l)
      fun u => tm_mat (evFin F u) _ Y i _ ?_ k l
    · rw [mw, tm_sigR, ← map_inv, ew]; simp
    · by_cases hu : u = v
      · subst hu; rw [mv, tm_sigR, ← map_inv, ev]; exact h2
      · rw [mu u hu, tm_sigR, ← map_inv, eu u hu]; simp
  · funext k
    refine GlobalTheory.Doubling.adele_ext (fun w => tm_vec (evInf F w) _ z ?_ k) fun u => tm_vec (evFin F u) _ z ?_ k
    · rw [mw]; simp
    · by_cases hu : u = v
      · subst hu; rw [mv]; exact h3 z hz1 hz2
      · rw [mu u hu]; simp

end GlobalTheory.LeviBlockRealization.LocEmb

end
