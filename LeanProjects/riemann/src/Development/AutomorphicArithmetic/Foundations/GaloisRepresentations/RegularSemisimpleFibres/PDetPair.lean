import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isCl {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ) :
    IsCl (detc θ t c) := by
  intro x y
  simp only [detc, Units.val_mul, Matrix.det_mul]
  congr 2
  rw [mul_comm _ (x : Matrix (Fin t) (Fin t) F).det, mul_assoc, ← Matrix.det_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]

private theorem detc_ne_zero {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (x : GL (Fin t) F) : detc θ t c x ≠ 0 := by
  unfold detc
  apply pow_ne_zero
  have hx : (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  have ha : algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    (_root_.map_ne_zero _).mpr hx
  intro h
  have h1 : θ (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det *
      (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det)⁻¹) = 1 := by
    rw [mul_inv_cancel₀ ha, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem detc_parab {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (hd : ∑ _i : Fin t, 1 = t) (p : parab F (stdBlocks (fun _ : Fin t => 1) hd)) :
    detc θ t c (p : GL (Fin t) F) =
      ∏ i, detc θ 1 c (leviProj F (stdBlocks (fun _ : Fin t => 1) hd) p i) := by
  have h := congrArg Units.val (det_parab F (stdBlocks (fun _ : Fin t => 1) hd) p)
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod] at h
  simp only [detc, h, map_prod, Finset.prod_pow]

theorem UpperTheory.Gal.InertialTypesAlt.detPair :
    FrobL → JDEq → DetPair := by
  intro hF hJ F _ _ θ t c
  obtain ⟨hJD, hcusp, _⟩ := hJ F θ
  have hd : ∑ _i : Fin t, 1 = t := by simp
  obtain ⟨c', hc', hfr⟩ := hF F t (fun _ => 1) t hd
  have hJt : J θ (List.replicate t (1, c)) t =
      hcL (List.ofFn fun _ : Fin t => (⟨1, detc θ 1 c⟩ : (m : ℕ) × (GL (Fin m) F → ℂ))) t := by
    rw [← JD_nil, hJD]
    congr 1
    simp [hcusp, List.map_replicate, List.ofFn_const]
  unfold Pairs
  rw [hJt, hfr _ _ (detc_isCl θ t c), mul_ne_zero_iff]
  refine ⟨hc', ?_⟩
  simp_rw [← detc_parab θ t c hd]
  haveI : Fintype (parab F (stdBlocks (fun _ : Fin t => 1) hd)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hpos : ∀ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      0 < (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re := by
    intro p
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr (detc_ne_zero θ t c _)
  have : 0 < ∑ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re :=
    Finset.sum_pos (fun p _ => hpos p) ⟨1, Finset.mem_univ _⟩
  linarith
