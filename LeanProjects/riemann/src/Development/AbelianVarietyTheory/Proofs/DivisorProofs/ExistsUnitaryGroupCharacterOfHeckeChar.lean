import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetCharacter

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.mul R R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) := by
  linear_combination ε * hd + (d - 1) * (a1 + a2)

theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 := by
  have e4 : ε * (d - 1) = f * (d - 1) := by
    linear_combination ε * hd + (d - 1) * (a1 + a2)
  linear_combination (1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3

variable {D : D7}

theorem det_mul_conj (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det = 1 := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  have hu := (GlobalTheory.LatVac.gram_det_isUnit V).map (incA D)
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply (cA D), ← RingHom.map_det] at h2
  refine hu.mul_left_cancel ?_
  linear_combination h2

theorem algebraMap_norm (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * cA D z := by
  have hx : ∃ x, D.sp.cm.sig x ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
    have h2 := D.sp.cm.deg2
    omega
  obtain ⟨δ, -, h⟩ := GlobalTheory.QuadNormBase.norm_form D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) hx
  obtain ⟨x, y, e1, e2⟩ := (h (AF D.host.F)).1 z
  rw [e1, e2]

theorem char_norm {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (x x' : (AE D)ˣ)
    (hx : (x' : AE D) = cA D x) : χ x * χ x' = 1 := by
  obtain ⟨⟨η, hη⟩, h1⟩ := h
  have e : x * x' = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) := by
    refine Units.ext ?_
    rw [Units.val_mul, hx]
    exact (algebraMap_norm (x : AE D)).symm
  rw [← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]

theorem char_eq_of_mul_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (y x : (AE D)ˣ)
    (hy : (y : AE D) * cA D x = 1) : χ y = χ x := by
  obtain ⟨x', hx'⟩ : IsUnit (cA D x) := x.isUnit.map (cA D)
  have hc := char_norm h x x' hx'
  have h1 : y * x' = 1 := Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])
  have h2 := congrArg χ h1
  rw [map_mul, map_one, ← hc] at h2
  exact mul_right_cancel h2

def cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : GA D V →* (AE D)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin V.rank) (R := AE D)).comp (matHom V))

theorem cutDet_val (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V) :
    (cutDet ε h V g : AE D) = (1 - ε) + ε * (Formalism.L2.Theta.mt V g).det := rfl

theorem cutDet_eq_one (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V)
    (hg : ∀ i j, ε * (Formalism.L2.Theta.mt V g - 1) i j = 0) : cutDet ε h V g = 1 := by
  refine Units.ext ?_
  rw [cutDet_val, Units.val_one]
  linear_combination mul_det_sub_one ε _ hg

theorem continuous_cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : Continuous (cutDet ε h V) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h0 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have h1 : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp h0
  have h2 : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := by
    have e : (fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹) = fun g => ((matHom V g)⁻¹).1 := by
      funext g
      unfold Formalism.L2.Theta.mt
      rw [map_inv]
    rw [e]
    exact Units.continuous_coe_inv.comp h0
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul h1.matrix_det)
  · simp only [← map_inv, cutDet_val]
    exact continuous_const.add (continuous_const.mul h2.matrix_det)

theorem cutDet_real (ε : AE D) (h1 : ε * ε = ε) (h3 : infPart D ε = 0) (V : HSp D) (g : GA D V) (hg : g ∈ GinfC V) :
    cutDet ε h1 V g = 1 := by
  refine cutDet_eq_one ε h1 V g fun i j => ?_
  have hm : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val (show finHom V g = 1 from hg)
  have hf : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    have e1 : finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
      congrFun (congrFun hm i) j
    rw [Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]
    by_cases e : i = j
    · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
  exact GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h3, zero_mul, RingHom.map_zero])
    (by rw [RingHom.map_mul, hf, mul_zero, RingHom.map_zero])

theorem det_supp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) * ((Formalism.L2.Theta.mt V g).det - 1) = 0 :=
  mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]

set_option maxHeartbeats 1000000 in
theorem cutDet_same (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (a1 : ε * e = e) (a2 : ε * cA D e = 0) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) : cutDet ε h1 V g = x := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  refine Units.ext ?_
  rw [cutDet_val, hx']
  exact cut_eq a1 a2 (det_supp hg)

set_option maxHeartbeats 1000000 in
theorem cutDet_conj (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (he : e * e = e) (a1 : ε * e = 0) (a2 : ε * cA D e = cA D e)
    {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) :
    (cutDet ε h1 V g : AE D) * cA D x = 1 := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  have e2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have e5 : cA D x = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
    rw [hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rw [cutDet_val, e5]
  exact cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj V g)

set_option maxHeartbeats 1000000 in

theorem exists_character : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  rintro D ε ⟨h1, -, h3, h4, h5⟩ V χ n hχ hres
  refine ⟨χ.comp (cutDet ε h1 V), hχ.1.comp (continuous_cutDet ε h1 V), fun g hg => ?_, fun v η hv g hg => ?_,
    fun e he g x hg hx => ?_⟩
  · rw [MonoidHom.comp_apply, cutDet_real ε h1 h3 V g hg, map_one]
  · rw [MonoidHom.comp_apply, cutDet_eq_one ε h1 V g fun i j => ?_, map_one]
    rw [← hg i j, ← mul_assoc, mul_comm ε, h5 v η hv, zero_mul]
  · rw [MonoidHom.comp_apply]
    rcases h4 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [cutDet_same ε h1 a1 a2 hg hx]
    · exact char_eq_of_mul_conj hres _ x (cutDet_conj ε h1 he.1 a1 a2 hg hx)

end GlobalTheory.SplitDetCharacter
