import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacSplit

open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem tensNU_map (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (z : R' ⊗[F] E) : tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = tensNU (E := E) j hj 1 * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.one_def, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem mat_extH_mapH (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (g : HA R' σ J) : ∃ c : R' ⊗[F] E, (HA.mat R' σ J (extH σ J j hj (mapH σ J φ g))).1 =
      (1 - c) • (1 : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) + c • (HA.mat R' σ J g).1 := by
  refine ⟨tensNU (E := E) j hj 1, ?_⟩
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH, GlobalTheory.AutFunCompare.mat_mapH, tensNU_map φ j hj h]
  rfl

omit [Algebra F R] in
theorem conj_mix {k n m : ℕ} (c : R) (P : Matrix (Fin k) (Fin n) R) (G : Matrix (Fin n) (Fin n) R)
    (Q : Matrix (Fin n) (Fin m) R) :
    P * (((1 - c) • (1 : Matrix (Fin n) (Fin n) R) + c • G) * Q) = (1 - c) • (P * Q) + c • (P * (G * Q)) := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [Algebra F R] in
theorem mix_zero {k m : ℕ} (c : R) {A B : Matrix (Fin k) (Fin m) R} (hA : A = 0) (hB : B = 0) :
    (1 - c) • A + c • B = 0 := by rw [hA, hB, smul_zero, smul_zero, add_zero]

omit [Algebra F R] in
theorem mix_uni {k : ℕ} (c : R) {A B : Matrix (Fin k) (Fin k) R} (hA : A = 1)
    (hB : ∀ i j : Fin k, (j < i → B i j = 0) ∧ B i i = 1) (i j : Fin k) :
    (j < i → ((1 - c) • A + c • B) i j = 0) ∧ ((1 - c) • A + c • B) i i = 1 := by
  subst hA
  refine ⟨fun hji => ?_, ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i j).1 hji, Matrix.one_apply_ne hji.ne',
      mul_zero, add_zero]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i i).2, Matrix.one_apply_eq, mul_one,
      sub_add_cancel]

end Gen

variable {D : D7}

theorem mt_ofInf_projInf (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (fstA D.host.F) _ _
    (fun a => Prod.ext (one_mul a.1).symm (zero_mul a.2).symm) g

theorem mt_ofFin_projFin (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (sndA D.host.F) _ _
    (fun a => Prod.ext (zero_mul a.1).symm (one_mul a.2).symm) g

theorem mem_jacGrp_of_mat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) {g h : GA D S} (hg : g ∈ jacGrp d)
    (hh : mt S h = (1 - c) • (1 : Mx D S.rank S.rank) + c • mt S g) : h ∈ jacGrp d := by
  obtain ⟨h0, hY, hX⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d g).1 hg
  have e : ∀ {k : ℕ} (P : Mx D k S.rank),
      P ⬝ (mt S h ⬝ d.jX) = (1 - c) • (P ⬝ d.jX) + c • (P ⬝ (mt S g ⬝ d.jX)) := fun P =>
    (congrArg (fun N : Mx D S.rank S.rank => P ⬝ (N ⬝ d.jX)) hh).trans (conj_mix c P (mt S g) d.jX)
  refine (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d h).2
    ⟨(e _).trans (mix_zero c d.p0_jX h0), (e _).trans (mix_zero c d.pY_jX hY), ?_⟩
  rw [e]
  exact mix_uni c d.pX_jX hX

end GlobalTheory.JacSplit

namespace GlobalTheory

open GlobalTheory.AdelicU

theorem jacGrp_split_inf_fin : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∀ a ∈ GinfC V, ∀ b ∈ GfC V,
    a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d := by
  intro D V V₀ ρ d a ha b hb hab
  rw [GinfC_eq, mem_infPts] at ha
  rw [GfC_eq, mem_finPts] at hb
  have hA : ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram (a * b)) = a := by
    rw [map_mul, hb, mul_one]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a]
    rw [ha, map_one, mul_one]
  have hB : ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram (a * b)) = b := by
    rw [map_mul, ha, one_mul]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b]
    rw [hb, map_one, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.JacSplit.mt_ofInf_projInf V (a * b)
  obtain ⟨c', hc'⟩ := GlobalTheory.JacSplit.mt_ofFin_projFin V (a * b)
  rw [hA] at hc
  rw [hB] at hc'
  exact ⟨GlobalTheory.JacSplit.mem_jacGrp_of_mat d c hab hc, GlobalTheory.JacSplit.mem_jacGrp_of_mat d c' hab hc'⟩

end GlobalTheory
