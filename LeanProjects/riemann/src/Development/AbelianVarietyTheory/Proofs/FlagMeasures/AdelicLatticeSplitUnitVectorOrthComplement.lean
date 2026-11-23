import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem hform_eq_star_dotProduct (I : AutInst) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = star x ⬝ᵥ (I.J *ᵥ y) := by
  change (∑ i, ∑ j, star (x i) * I.J i j * y j) = _
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem IsPerp.exists_split {I : AutInst} {D : Sib I} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin D.n) I.E} {xf : I.Gf} (h : IsPerp D s x A xf) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I (1, xf)) : ∃ a : 𝓞 I.E, ∃ w ∈ D.L, y = a • x + A *ᵥ w := by
  obtain ⟨hn, hβ, hxA, hAJ, hx, hL⟩ := h
  have hJ : I.Jᴴ = I.J := by
    rw [← (show Formalism.UG.cT (starRingEnd I.E) I.J = I.Jᴴ by ext i j; rfl)]
    exact I.J_herm
  have hsq : sgn I.E s * sgn I.E s = 1 := by cases s <;> simp [sgn]
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    intro h0
    rw [hβ] at h0
    rw [h0, zero_mul] at hsq
    exact zero_ne_one hsq
  obtain ⟨u, A', -, -, -, -, hres, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ

  have hdec : y = (u ⬝ᵥ y) • x + A *ᵥ (A' *ᵥ y) := by
    have h1 : (vecMulVec x u + A * A') *ᵥ y = y := by rw [hres, one_mulVec]
    rw [add_mulVec, ← mulVec_mulVec] at h1
    refine h1.symm.trans ?_
    congr 1
    funext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hpair : ∀ (c : I.E) (w : Fin D.n → I.E), y = c • x + A *ᵥ w →
      star x ⬝ᵥ (I.J *ᵥ y) = c * sgn I.E s := by
    intro c w e
    rw [e, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hβ, mulVec_mulVec,
      dotProduct_mulVec, hxA, zero_dotProduct, add_zero]
  have hcoef : u ⬝ᵥ y = sgn I.E s * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
    rw [hform_eq_star_dotProduct, hpair _ _ hdec]
    linear_combination (-(u ⬝ᵥ y)) * hsq
  have hint : Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range :=
    (((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.2.1 y).mp hy) x hx
  have hsgn : sgn I.E s ∈ (algebraMap (𝓞 I.E) I.E).range := by
    cases s
    · exact ⟨-1, by simp [sgn]⟩
    · exact ⟨1, by simp [sgn]⟩
  obtain ⟨a, ha⟩ := Subring.mul_mem _ hsgn hint
  have hca : (u ⬝ᵥ y) • x = a • x := by rw [hcoef, ← ha, algebraMap_smul]
  refine ⟨a, A' *ᵥ y, (hL _).mpr ?_, ?_⟩
  · have e : A *ᵥ (A' *ᵥ y) = y - a • x := by
      rw [← hca]
      exact eq_sub_of_add_eq' hdec.symm
    rw [e]
    exact Submodule.sub_mem _ hy (Submodule.smul_mem _ a hx)
  · rw [← hca]
    exact hdec

theorem afVec_mulVec_eq_afMat_mulVec (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) (w : Fin k → I.E) :
    afVec I (A *ᵥ w) = afMat I A *ᵥ afVec I w := by
  funext i
  simp [afVec, afMat, mulVec, dotProduct, map_sum]

private theorem mem_lf_iff_mem_latS (I : AutInst) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    v ∈ I.Lf ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
  show v ∈ lamAf (F := I.F) I.L ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L
  unfold lamAf Formalism.UG.latS
  constructor
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem adelicLattice_split : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, I.fmat xf⁻¹ *ᵥ z ∈ I.Lf ↔ ∃ a ∈ IntAf I.F I.E, ∃ w ∈ D.inst.Lf, z = a • afVec I x + afMat I A *ᵥ w := by
  intro I D s x A xf h z
  have hmem : ∀ y : Fin I.n → I.E, y ∈ lamX I (1, xf) → I.fmat xf⁻¹ *ᵥ afVec I y ∈ I.Lf :=
    fun y hy => ((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).1 y).mp hy
  obtain ⟨-, -, -, -, hx, hL⟩ := id h
  constructor
  · intro hz
    have hspan := Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds I.L
      (Module.Finite.iff_fg.mpr I.L_fg) I.L_span (xf : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) z
      ((mem_lf_iff_mem_latS I _).mp hz)
    clear hz
    induction hspan using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      have hy' : y ∈ lamX I (1, xf) := by
        rw [GlobalTheory.PointLattice.lamX_eq_globLat]
        exact hy
      obtain ⟨a0, w0, hw0, e⟩ := IsPerp.exists_split h hy'
      refine ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a0), Formalism.UG.CS.incl_int a0,
        afVec I w0, Submodule.subset_span ⟨⟨w0, hw0⟩, rfl⟩, ?_⟩
      rw [← afVec_mulVec_eq_afMat_mulVec]
      funext i
      simp [afVec, e, Algebra.smul_def, map_add, map_mul]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add v1 v2 _ _ h1 h2 =>
      obtain ⟨a1, ha1, w1, hw1, rfl⟩ := h1
      obtain ⟨a2, ha2, w2, hw2, rfl⟩ := h2
      refine ⟨a1 + a2, add_mem ha1 ha2, w1 + w2, add_mem hw1 hw2, ?_⟩
      rw [add_smul, mulVec_add]
      abel
    | smul c v _ h1 =>
      obtain ⟨a, ha, w, hw, rfl⟩ := h1
      refine ⟨(c : I.E ⊗[I.F] Af I.F) * a, mul_mem c.2 ha, (c : I.E ⊗[I.F] Af I.F) • w,
        Submodule.smul_mem _ c hw, ?_⟩
      show (c : I.E ⊗[I.F] Af I.F) • (a • afVec I x + afMat I A *ᵥ w) = _
      rw [smul_add, mul_smul, mulVec_smul]
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mulVec_add, mulVec_smul]
    refine add_mem (Submodule.smul_mem I.Lf ⟨a, ha⟩ (hmem x hx)) ?_
    have hw' : w ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun y : D.L => afVec I (y : Fin D.n → I.E)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hv
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ afVec I y) ∈ I.Lf
      rw [← afVec_mulVec_eq_afMat_mulVec]
      exact hmem _ ((hL y).mp hy)
    | zero => simp
    | add v1 v2 _ _ h1 h2 =>
      rw [mulVec_add, mulVec_add]
      exact add_mem h1 h2
    | smul c v _ h1 =>
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v)) ∈ I.Lf
      rw [mulVec_smul, mulVec_smul]
      exact Submodule.smul_mem I.Lf c h1

end GlobalTheory.StabUnfold
