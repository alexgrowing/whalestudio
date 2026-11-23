import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

variable {D : D7}

theorem mem_stab_onX_of_mul {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {p : GA D T} {b : GL (Fin r) (AE D)}
    (h : mt T p ⬝ d.jX = d.jX ⬝ b.1) : ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b :=
  ⟨⟨b, h⟩, Units.ext ((eq_of_mul_jX d (mul_jX d ⟨p, ⟨b, h⟩⟩)).trans (eq_of_mul_jX d h).symm)⟩

theorem parFlag_zero_eq_stab {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) :
    (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d := by
  ext p
  constructor
  · rintro ⟨⟨B, -, hB⟩, B', -, hB'⟩
    change mt T p ⬝ d.jX = d.jX ⬝ B at hB
    change mt T p⁻¹ ⬝ d.jX = d.jX ⬝ B' at hB'
    have e1 : B ⬝ B' = 1 := by
      rw [eq_of_mul_jX d hB]
      simp only [Matrix.mul_assoc]
      rw [← hB', ← Matrix.mul_assoc (mt T p), mt_mul_inv, Matrix.one_mul, d.pX_jX]
    have e2 : B' ⬝ B = 1 := by
      rw [eq_of_mul_jX d hB']
      simp only [Matrix.mul_assoc]
      rw [← hB, ← Matrix.mul_assoc (mt T p⁻¹), mt_inv_mul, Matrix.one_mul, d.pX_jX]
    exact ⟨⟨B, B', e1, e2⟩, hB⟩
  · intro hp
    obtain ⟨α, h⟩ := hp
    obtain ⟨β, h'⟩ := (stab d).inv_mem (show p ∈ stab d from ⟨α, h⟩)
    exact ⟨⟨α.1, fun i j hij => absurd hij (lt_irrefl _), h⟩, β.1, fun i j hij => absurd hij (lt_irrefl _), h'⟩

theorem det_onX_rat {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : stab d) (hq : (q : GA D T) ∈ GQ T) :
    ∃ u : D.host.Eˣ, Units.map (incA D : D.host.E →* AE D) u =
      Matrix.GeneralLinearGroup.det (onX d q) := by
  have hr : ∀ q : stab d, (q : GA D T) ∈ GQ T → (onX d q).1 ∈ ratMx D r r := fun q hq => by
    rw [eq_of_mul_jX d (mul_jX d q)]
    exact ratMx_mul ⟨_, rfl⟩ (ratMx_mul ((mem_GQ_iff T _).1 hq) ⟨_, rfl⟩)
  obtain ⟨A, hA⟩ := hr q hq
  obtain ⟨A', hA'⟩ := hr q⁻¹ ((GQ T).inv_mem hq)
  change rat A = _ at hA
  change rat A' = _ at hA'
  have hAA : A * A' = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.mul_inv]
  have hA'A : A' * A = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.inv_mul]
  refine ⟨⟨A.det, A'.det, by rw [← Matrix.det_mul, hAA, Matrix.det_one], by rw [← Matrix.det_mul, hA'A, Matrix.det_one]⟩,
    Units.ext ?_⟩
  change incA D A.det = (onX d q).1.det
  rw [← hA, RingHom.map_det]
  rfl

theorem indLaw_inv {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {μ : (AE D)ˣ →* Circle} {t : ℂ} {φ : GA D T → ℂ}
    (hφ : IndLaw (absDet d) (detChar d μ) t φ) (q : stab d) (h1 : detChar d μ q = 1) (h2 : absDet d q = 1) (g : GA D T) :
    φ (q * g) = φ g := by
  rw [hφ q g, h1, h2]
  simp [npow]

theorem leftInv_leftGrp_of_indLaw {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {μ : (AE D)ˣ →* Circle}
    (hμ : IsHeckeChar D μ) {t : ℂ} {φ : GA D T → ℂ} (hφ : IndLaw (absDet d) (detChar d μ) t φ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ := by
  let H : Subgroup (GA D T) :=
    { carrier := {γ | ∀ g, φ (γ * g) = φ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left] }
  have hH : (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) ≤ H := by
    refine sup_le ((Subgroup.closure_le _).2 fun u hu => ?_) fun γ hγ => ?_
    · obtain ⟨A, hA, e⟩ := lower_iff.1 hu.1
      rw [show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero, Matrix.sub_mul, Matrix.one_mul,
        sub_eq_zero] at e
      obtain ⟨hp, h1⟩ := mem_stab_onX_of_mul d (p := u) (b := 1) (e.trans (Matrix.mul_one _).symm)
      refine indLaw_inv hφ ⟨u, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
    · have hp : γ ∈ stab d := parFlag_zero_eq_stab d ▸ hγ.2
      obtain ⟨u, hu⟩ := det_onX_rat d ⟨γ, hp⟩ hγ.1
      refine indLaw_inv hφ ⟨γ, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact hμ.2 u
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact absE_inclR u
  exact fun γ hγ => hH hγ

theorem parFlag_stab_leftInv : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d ∧ ratPts D.sp.cm.sig T.gram = GQ T ∧ (∀ (p : GA D T) (b : GL (Fin r) (AE D)), (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram p).1 * adMat D.host.F d.e = adMat D.host.F d.e * b.1 → ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b) ∧ ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (t : ℂ) (φ : GA D T → ℂ), IndLaw (absDet d) (detChar d μ) t φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ :=
  fun _ _ _ _ d => ⟨parFlag_zero_eq_stab d, rfl, fun _ _ h => mem_stab_onX_of_mul d h,
    fun _ hμ _ _ hφ => leftInv_leftGrp_of_indLaw d hμ hφ⟩

end GlobalTheory.EisCont

end
