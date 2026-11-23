import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAddStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.OntoDer

theorem hasDerivAt_term {G : Type} [AddCommGroup G] (a : ℝ →+ G) (p : G →+ ℂ) (κ : ℂ) (hκ : ∀ t : ℝ, p (a t) = t * κ)
    (φ φ₁ : G → ℂ) (hφ : ∀ x, HasDerivAt (fun t : ℝ => φ (x + a t)) (φ₁ x) 0) (u : G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * p (a t) + t * p u + t * p u) * φ (u + a t))
      (Complex.exp (s * p (a s) + s * p u + s * p u) * ((p + p) (u + a s) * φ (u + a s) + φ₁ (u + a s))) s := by
  have h1 : HasDerivAt (fun t : ℝ => φ (u + a t)) (φ₁ (u + a s)) s := by
    have h := hφ (u + a s)
    rw [← sub_self s] at h
    have h' := HasDerivAt.comp_sub_const s s h
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show φ (u + a t) = φ (u + a s + a (t - s))
    rw [map_sub, add_assoc, add_sub_cancel]
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have h2 := (((h0.mul (h0.mul_const κ)).add (h0.mul_const (p u))).add (h0.mul_const (p u))).cexp
  have h3 := h2.mul h1
  simp only [hκ]
  refine h3.congr_deriv ?_
  simp only [AddMonoidHom.add_apply, map_add, hκ, Pi.add_apply, Pi.mul_apply]
  ring

variable {D : D7}

theorem two_halves (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem phase_identity {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y a b ξ : Mx D T.rank ρ) :
    symplOH S T (d.extX T x + d.extY T y) (d.extX T a + d.extY T b) +
        (-(symplOH S T (d.extX T (x + a)) (d.extY T (y + b)))) + symplO S T (d.extX T (x + a + ξ)) (d.extY T (y + b)) =
      -(symplOH S T (d.extX T x) (d.extY T y)) + symplO S T (d.extX T (x + ξ)) (d.extY T y) +
        (symplOH S T (d.extX T a) (d.extY T b) + symplOH S T (d.extX T (x + ξ)) (d.extY T b) +
          symplOH S T (d.extX T (x + ξ)) (d.extY T b)) := by
  simp only [two_halves, map_add, GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_right,
    HypDec.symplOH_extX_extX, HypDec.symplOH_extY_extY,
    GlobalTheory.WeilVacMove.symplOH_skew S T (d.extX T a) (d.extY T y)]
  ring

theorem eq_ext (A B : HSp D) (w : WO (dblSp A) B) :
    w = (dblDec A).extX B (HMul.hMul w (dblDec A).jX) + (dblDec A).extY B (HMul.hMul w (dblDec A).jY) := by
  have h0 : HMul.hMul (dblDec A).j0 (dblDec A).p0 = (0 : Mx D (dblSp A).rank (dblSp A).rank) := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h
  rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h, Matrix.mul_one]

def mulLine {m n k : ℕ} (M : ℝ →+ Mx D m n) (j : Mx D n k) : ℝ →+ Mx D m k where
  toFun t := HMul.hMul (M t) j
  map_zero' := by rw [map_zero, Matrix.zero_mul]
  map_add' s t := by rw [map_add, Matrix.add_mul]

theorem continuous_mulLine {m n k : ℕ} {M : ℝ →+ Mx D m n} (hM : Continuous M) (j : Mx D n k) :
    Continuous (mulLine M j) := hM.matrix_mul continuous_const

theorem map_mul_zero {m n k : ℕ} {R : Type} [CommRing R] (q : AE D →+* R) {u : Mx D m n} (hu : u.map q = 0)
    (j : Mx D n k) : (HMul.hMul u j : Mx D m k).map q = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {Q : Set (Mx D m n)} (hQ : IsCompact Q) :
    ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hφ
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hb.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb' x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

set_option maxHeartbeats 1600000 in

theorem hasDerivAt_heisO_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  intro D ψ hψ A B φ hφ f hf M hM hM0
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  let d := dblDec A
  let a : ℝ →+ Mx D B.rank A.rank := mulLine M d.jX
  let b : ℝ →+ Mx D B.rank A.rank := mulLine M d.jY
  let L : ℝ →+ WO (dblSp A) B := mulLine b d.pY
  have ha : Continuous a := continuous_mulLine hM _
  have hL : Continuous L := continuous_mulLine (continuous_mulLine hM _) _
  have ha0 : ∀ t, (a t).map (finPart D) = 0 := fun t => map_mul_zero _ (hM0 t) _
  have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => map_mul_zero _ (map_mul_zero _ (hM0 t) _) _
  let p : Mx D B.rank A.rank →+ ℂ := (GlobalTheory.WeilVacMove.phase lam (dblSp A) B (L 1)).comp (d.extX B)
  have hX : Continuous (d.extX B) := continuous_id.matrix_mul continuous_const
  have hp : Continuous p := hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH (dblSp A) B hX continuous_const)
  have hp0 : ∀ u : Mx D B.rank A.rank, u.map (infPart D) = 0 → p u = 0 := fun u hu => by
    show lam (symplOH (dblSp A) B (d.extX B u) (L 1)) = 0
    rw [(GlobalTheory.WeilVacMove.symplOH_fin_real (dblSp A) B (d.extX B u) (L 1) (map_mul_zero _ hu _) (hL0 1)).1, map_zero]
  have hψp : ∀ (u : Mx D B.rank A.rank) (t : ℝ),
      ψ (symplOH (dblSp A) B (d.extX B u) (d.extY B (b t))) = Complex.exp (t * p u) := fun u t =>
    GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 (d.extX B u) t
  have hκ : ∀ t : ℝ, p (a t) = t * p (a 1) := fun t =>
    GlobalTheory.WeilVacMove.additive_real (p.comp a) (hp.comp ha) t
  obtain ⟨hd, hm, hadd⟩ := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ φ hφ
  obtain ⟨φ₁, hφ₁, hder⟩ := hd a ha ha0
  have hℓ := hm (p + p) (hp.add hp) fun u hu => by rw [AddMonoidHom.add_apply, hp0 u hu, add_zero]
  have hφ' := (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ _ hℓ).2.2 φ₁ hφ₁
  refine ⟨_, hφ', fun f' hf' w => ?_⟩
  set φ' : Mx D B.rank A.rank → ℂ := (fun x => (p + p) x * φ x) + φ₁ with hφ'def
  let x : Mx D B.rank A.rank := HMul.hMul w d.jX
  let y : Mx D B.rank A.rank := HMul.hMul w d.jY
  let c : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℂ := fun ξ =>
    ψ (symplO (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B y))
  let e : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℝ → ℂ := fun ξ t =>
    Complex.exp (t * p (a t) + t * p (x + rat ξ) + t * p (x + rat ξ))
  have he : ∀ ξ t, e ξ t = ψ (symplOH (dblSp A) B (d.extX B (a t)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t))) := fun ξ t => by
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψp, hψp, ← Complex.exp_add, ← Complex.exp_add]
  have he0 : ∀ ξ, e ξ 0 = 1 := fun ξ => by simp [e]
  have hform : ∀ t, heisO ψ (dblSp A) B (M t) f w =
      ψ (-(symplOH (dblSp A) B (d.extX B x) (d.extY B y))) * ∑' ξ, c ξ * (e ξ t * φ (x + rat ξ + a t)) := by
    intro t
    have e1 : HMul.hMul (w + M t) (dblDec A).jX = x + a t := Matrix.add_mul _ _ _
    have e2 : HMul.hMul (w + M t) (dblDec A).jY = y + b t := Matrix.add_mul _ _ _
    have e3 : symplOH (dblSp A) B w (M t) =
        symplOH (dblSp A) B (d.extX B x + d.extY B y) (d.extX B (a t) + d.extY B (b t)) :=
      congrArg₂ (symplOH (dblSp A) B) (eq_ext A B w) (eq_ext A B (M t))
    rw [heisO, hf, e1, e2, e3, ← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [he, add_right_comm x (rat ξ) (a t), ← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, phase_identity]
  have hQ : IsCompact ((fun t : ℝ => x + a t) '' Set.Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.add ha)
  obtain ⟨u, hu, hu'⟩ := exists_summable_bound hθ hφ' hQ
  obtain ⟨v, hv, hv'⟩ := exists_summable_bound hθ hφ (isCompact_singleton (x := x))
  have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := (0 : ℝ)) (y := (0 : ℝ))
    (g := fun ξ t => c ξ * (e ξ t * φ (x + rat ξ + a t)))
    (g' := fun ξ t => c ξ * (e ξ t * φ' (x + rat ξ + a t))) hu isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_term a p _ hκ φ φ₁ hder (x + rat ξ) t).const_mul (c ξ))
    (fun ξ t ht => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, add_right_comm]
      exact hu' _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩ ξ)
    (by norm_num)
    (Summable.of_norm_bounded hv fun ξ => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, map_zero, add_zero]
      exact hv' x rfl ξ)
    (by norm_num)
  simp only [he0, map_zero, add_zero, one_mul] at key
  rw [hf', funext hform]
  exact key.const_mul _

end GlobalTheory.Core.Rk.OntoDer

end
