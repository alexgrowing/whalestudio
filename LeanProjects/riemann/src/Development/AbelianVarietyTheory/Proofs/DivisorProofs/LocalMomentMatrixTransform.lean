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

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl F} (t : E →ₐ[F] Fv F v) (z : AE F E) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add, hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

open GlobalTheory.Div.CoordOpp in
theorem GlobalTheory.Div.CoordOpp.coord_opp_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  intro F E _ _ _ _ _ σ n d X W v t g h x
  have hg := unit_map σ g t
  have hh := unit_map σ h t
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul,
    Matrix.transpose_map, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  set gt := (mat g).map (piW t)
  set gb := (mat g).map (piW (t.comp σ))
  set ht := (mat h).map (piW t)
  set hb := (mat h).map (piW (t.comp σ))
  set xb := x.map (piW (t.comp σ))
  have hh' : hbᵀ * (W.J.map t)ᵀ * ht = (W.J.map t)ᵀ := by
    have := congrArg Matrix.transpose hh
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc gtᵀ * (X.J.map t * (gb * xb * ((mat h)ᵀ).map (piW (t.comp σ))) * (W.J.map t)ᵀ) * ht
      = (gtᵀ * X.J.map t * gb) * xb * (hbᵀ * (W.J.map t)ᵀ * ht) := by
        simp only [hb, Matrix.transpose_map, Matrix.mul_assoc]
    _ = X.J.map t * xb * (W.J.map t)ᵀ := by rw [hg, hh']
