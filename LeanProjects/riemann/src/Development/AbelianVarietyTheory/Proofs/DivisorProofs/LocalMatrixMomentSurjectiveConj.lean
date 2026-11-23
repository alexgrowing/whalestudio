import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right atPlace_mul_right evFin_atPlace)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace [FiniteDimensional F E] (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    rw [e, trace_tmul', trace_tmul', map_mul, AlgHom.commutes]

theorem trace_split {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = splitProj t y + splitProj (t.comp σ) y := by
  rw [← Algebra.trace_eq_of_algEquiv (splitAlgEquiv h t) y, Algebra.trace_prod_apply, splitAlgEquiv_apply]
  simp [Algebra.trace_self_apply]

theorem piW_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : AE F E) :
    piW (t.comp σ) (cA σ y) = piW t y := by
  have e : compFin F E v (cA σ y) = sigR (Fv F v) σ (compFin F E v y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  change splitProj (t.comp σ) (compFin F E v (cA σ y)) = splitProj t (compFin F E v y)
  rw [e]
  exact splitProj_comp_sigR h t _

theorem piW_inclR {v : Pl F} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (AF F) x) = t x := by
  change splitProj t (evFin F v 1 ⊗ₜ[F] x) = t x
  rw [map_one]
  exact splitProj_inclR t x

theorem piW_tensAt {v : Pl F} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  change splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

theorem at_tensAt {v : Pl F} (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro a ha
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change evFin F v a ⊗ₜ[F] (1 : E) = 0
    rw [ha, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem eq_liftV_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  have h1 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h2 := ha _ h1
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
  calc a = atPlace v 1 * a := h2
    _ = atPlace v (1 * evFin F v a) := atPlace_mul_right v 1 a
    _ = GlobalTheory.LatVac.liftV v (evFin F v a) := by rw [one_mul]; rfl

end GlobalTheory.OppLinChar

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (tensAt)

theorem char_eq_psi_symp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Z
  have h := hB.cm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  refine ⟨Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0)), ?_, ?_, ?_⟩
  · intro a ha
    ext k l
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact at_tensAt _ a ha
  · ext k l
    simp [piW_tensAt]
  · intro x hxv hx
    set u : Matrix (Fin n) (Fin d) (AE F E) := Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0))
      with hu_def
    have hx' : ∀ i j, piW t (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
    have hJX : ∀ i k, piW (t.comp σ) (incM F X.J i k) = t (X.J k i) := fun i k => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hX.herm]
    have hJW : ∀ j l, piW (t.comp σ) (incM F W.J j l) = -t (W.J l j) := fun j l => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hW.skew, map_neg]
    have hu : ∀ k l, piW (t.comp σ) (cA σ (u k l)) = -Z k l := fun k l => by
      rw [piW_cA h, hu_def, Matrix.of_apply, piW_tensAt, splitProj_symm]
    set S := symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u with hS_def
    have hat : At (evFin F v) S := by
      intro a ha
      rw [smul_eq_mul, ← one_mul S, ← mul_assoc, hS_def, ← GlobalTheory.LatVac.symp_smul_smul]
      have h0 : a • x = 0 := hxv a ha
      rw [h0]
      simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
    have hev : evFin F v S = ∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) *
        (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j := by
      rw [hS_def, GlobalTheory.WeilM.symp, evFin_trace, trace_split h t]
      change piW t _ + piW (t.comp σ) _ = _
      simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, hx', hJX, hJW, hu]
      have key : ∀ (f : Fin n → Fin d → Fin n → Fin d → Fv F v),
          ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
        intro f
        calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, Units.val_one, Matrix.transpose_one,
        Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib]
      refine (key _).trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    change B.ψ S = B.ψ (GlobalTheory.LatVac.liftV v _)
    rw [← hev, ← eq_liftV_of_at hat]

end GlobalTheory.OppLinChar
