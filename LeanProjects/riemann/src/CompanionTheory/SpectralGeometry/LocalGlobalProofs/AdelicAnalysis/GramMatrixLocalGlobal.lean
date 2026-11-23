import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramLocal

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

abbrev bcE (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

theorem bcE_inclR (f : R →ₐ[F] S) (e : E) : bcE E f (inclR R e) = inclR S e := by
  simp [inclR, bcE]

theorem bcE_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    bcE E f (sigR R σ z) = sigR S σ (bcE E f z) := by
  induction z with
  | zero => simp
  | tmul r e => simp [sigR, bcE]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bcE_hR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → R ⊗[F] E) :
    bcE E f (hR R σ J x y) = hR S σ J (fun i => bcE E f (x i)) (fun i => bcE E f (y i)) := by
  simp only [hR, hform, map_sum, map_mul, bcE_sigR, JR, Matrix.map_apply, bcE_inclR]

theorem bcE_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR S σ J (fun a i => bcE E f (X a i)) = fun a b => bcE E f (gramR R σ J X a b) := by
  funext a b
  simp only [gramR, bcE_hR]

theorem repr_bcE {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (f : R →ₐ[F] S)
    (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (bcE E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z with
  | zero => simp
  | tmul r e => simp [bcE, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

end Ring

section Adelic

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem adele_ext (x y : AF F) (h1 : fstA F x = fstA F y)
    (h2 : ∀ v, evalV F v (sndA F x) = evalV F v (sndA F y)) : x = y := by
  refine Prod.ext h1 ?_
  exact Subtype.ext (funext h2)

theorem tensor_ext [Module.Finite F E] (z w : AF F ⊗[F] E)
    (h1 : bcE E (fstA F) z = bcE E (fstA F) w)
    (h2 : ∀ v, bcE E (evalV F v) (bcE E (sndA F) z) = bcE E (evalV F v) (bcE E (sndA F) w)) :
    z = w := by
  classical
  let b := Module.finBasis F E
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  apply adele_ext
  · rw [← repr_bcE, ← repr_bcE, h1]
  · intro v
    rw [← repr_bcE, ← repr_bcE, ← repr_bcE, ← repr_bcE, h2 v]

end Adelic

theorem gram_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  intro F E _ _ _ _ _ σ hCM M J _ n X T
  have hfin : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hInf : gramR (Ainf F) σ J (projInf X) =
      fun a b => bcE E (fstA F) (gramR (AF F) σ J X a b) := bcE_gramR (fstA F) σ J X
  have hFin : gramR (Af F) σ J (projFin X) =
      fun a b => bcE E (sndA F) (gramR (AF F) σ J X a b) := bcE_gramR (sndA F) σ J X
  have hV : ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) =
      fun a b => bcE E (evalV F v) (bcE E (sndA F) (gramR (AF F) σ J X a b)) := by
    intro v
    have := bcE_gramR (evalV F v) σ J (projFin X : Fin n → Fin M → Af F ⊗[F] E)
    rw [hFin] at this
    exact this
  refine ⟨⟨fun h => ⟨?_, fun v => ?_⟩, fun h => ?_⟩, fun Y => gramR_ratTup σ J Y⟩
  · rw [hInf, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · rw [hV v, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · funext a b
    apply tensor_ext
    · have := congrFun (congrFun (hInf.symm.trans h.1) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this
    · intro v
      have := congrFun (congrFun ((hV v).symm.trans (h.2 v)) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this

end GlobalTheory.CompanionTheory.SW.GramLocal
