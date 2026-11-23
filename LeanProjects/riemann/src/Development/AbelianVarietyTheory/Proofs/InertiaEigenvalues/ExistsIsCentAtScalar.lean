import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.CentScal

variable {D : D7}

def scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) : GA D V :=
  ⟨⟨Matrix.diagonal (fun _ => a), Matrix.diagonal (fun _ => cA D a),
      by rw [Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, mul_comm, h, Matrix.diagonal_one]⟩, by
    show Formalism.UG.cT _ (Matrix.diagonal (fun _ => a)) * _ * Matrix.diagonal (fun _ => a) = _
    ext k l
    simp only [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    have e : ∀ t : AE D, cA D a * t * a = t := fun t => by rw [mul_right_comm, mul_comm (cA D a) a, h, one_mul]
    exact e _⟩

theorem mt_scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a h) = Matrix.diagonal (fun _ => a) := rfl

theorem scalU_mem_center (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    scalU V a h ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  show (matHom V g).1 * Matrix.diagonal (fun _ => a) =
    Matrix.diagonal (fun _ => a) * (matHom V g).1
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalU_mem_GfC (V : HSp D) (a : AE D) (h : a * cA D a = 1) (h1 : infPart D a = 1) :
    scalU V a h ∈ GfC V := by
  show infHom V (scalU V a h) = 1
  apply Units.ext
  show (Matrix.diagonal (fun _ => a)).map (infPart D) = 1
  rw [Matrix.diagonal_map (map_zero _), h1, Matrix.diagonal_one]

theorem scal_norm_one {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ t, c (c t) = t) (e x w : R) (he2 : e * e = e)
    (hef : e * c e = 0) (hxw : x * w = 1) :
    (e * x + c e * c w + (1 - e - c e)) * c (e * x + c e * c w + (1 - e - c e)) = 1 := by
  have hf2 : c e * c e = c e := by rw [← map_mul, he2]
  have hyX : c w * c x = 1 := by rw [← map_mul, mul_comm, hxw, map_one]
  simp only [map_add, map_mul, map_sub, map_one, hc]
  linear_combination (x * c x + c w * w - x - c w - c x - w + 2) * hef +
    (x * w - x - w + 1) * he2 + (c w * c x - c w - c x + 1) * hf2 + e * hxw + c e * hyX

theorem hom_scal {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e f x y : R) (h0 : φ e = 0) (h1 : φ f = 0) :
    φ (e * x + f * y + (1 - e - f)) = 1 := by
  rw [map_add, map_add, map_mul, map_mul, map_sub, map_sub, map_one, h0, h1]
  simp

theorem scal_supp {R : Type} [CommRing R] (e f x y : R) (he2 : e * e = e) (hf2 : f * f = f) (hef : e * f = 0) :
    (e + f) * (e * x + f * y + (1 - e - f) - 1) = e * x + f * y + (1 - e - f) - 1 := by
  linear_combination (x - 1) * he2 + (y - 1) * hf2 + (y + x - 2) * hef

theorem exists_isCentAt_scalar : ∀ (D : D7) (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ ϖ : D.host.E, ϖ ≠ 0 → ∃ z : GA D (Vc D i), IsCentAt i Q z ∧ mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) := by
  intro D i Q eQ hQ ϖ hϖ
  have he2 : eQ * eQ = eQ := GlobalTheory.PlaceVec.idemSum_mul_self hQ
  have hf2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he2]
  have hef : eQ * cA D eQ = 0 := hQ.2
  have hxw : incA D ϖ⁻¹ * incA D ϖ = 1 := by rw [← map_mul, inv_mul_cancel₀ hϖ, map_one]
  have hunit := scal_norm_one (cA D) cA_cA eQ (incA D ϖ⁻¹) (incA D ϖ) he2 hef hxw
  have hinf : infPart D (eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) = 1 := by
    have h0 : infPart D eQ = 0 := GlobalTheory.PlaceVec.idemSum_infPart hQ
    have h0' : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA h0
    exact hom_scal (infPart D) _ _ _ _ h0 h0'
  refine ⟨scalU (Vc D i) _ hunit, ⟨scalU_mem_center _ _ hunit, scalU_mem_GfC _ _ hunit hinf, eQ, hQ, ?_⟩,
    mt_scalU _ _ hunit⟩
  intro k l
  rw [mt_scalU]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact scal_supp _ _ _ _ he2 hf2 hef
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hkl, Matrix.one_apply_ne hkl, sub_zero, mul_zero]

end GlobalTheory.CentScal
