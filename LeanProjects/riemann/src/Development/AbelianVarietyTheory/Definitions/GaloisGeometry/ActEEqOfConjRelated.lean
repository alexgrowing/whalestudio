import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Model

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}

def actE {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ W) (g : Γ) : W ≃ₗ[ℂ] W :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)

theorem actE_eq_of_conj_related {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ W) (g h : Γ) {x y : W}
    (e : x = ρ (g⁻¹ * h * g) y) : actE ρ g x = ρ h (actE ρ g y) := by
  show ρ g x = ρ h (ρ g y)
  rw [e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem block_frame_conjugation_identity {H : Type} [Group H] (S : Subgroup H) (g h : S) (a : H) :
    ((g : H) * a)⁻¹ * h * (g * a) = a⁻¹ * ((g⁻¹ * h * g : S) : H) * a := by
  push_cast
  group

theorem inv_aux {H : Type} [Group H] (g a h : H) : a⁻¹ * (g⁻¹ * h) = (g * a)⁻¹ * h := by group

theorem real_apply_eq_actE_real_inv_mul {μ j} (m : MtReal D μ j) (x) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (h : Formalism.AUTREP.GAf D.host.E D.R.nV) :
    m.real x h = actE m.wt.ρ g (m.real x ((g : Formalism.AUTREP.GAf D.host.E D.R.nV)⁻¹ * h)) := by
  have hm : m.real x ∈ NG.TypeSp m.wt.ρ m.J m.χ := m.real_range ▸ LinearMap.mem_range_self _ x
  exact (congrArg (m.real x) (mul_inv_cancel_left _ h).symm).trans (hm.1.1 g _)

def shift (A : Agree X M rep) (g : Fin D.R.m → ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Agree X M rep where
  hF := A.hF
  PV := A.PV
  stdV := A.stdV
  stdW := A.stdW
  a j := (g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j
  rat j h := by
    have e : ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)⁻¹ * h * ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j) =
        (A.a j)⁻¹ * ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV)⁻¹ * h * g j) * A.a j := by group
    rw [e, ← A.rat j]
    constructor
    · intro hh
      exact mul_mem (mul_mem (inv_mem (g j).2) hh) (g j).2
    · intro hh
      have := mul_mem (mul_mem (g j).2 hh) (inv_mem (g j).2)
      simpa [mul_assoc] using this
  eW μ hμ j := (A.eW μ hμ j).trans
    (actE (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ (g j))
  wt μ hμ j h γ hγ eq v :=
    actE_eq_of_conj_related _ (g j) h (A.wt μ hμ j ((g j)⁻¹ * h * g j) γ hγ
      (eq.trans (congrArg (fun z => finHom (Vc D j) ((A.PV j).ψ z)) (block_frame_conjugation_identity _ (g j) h (A.a j)))) v)
  real μ hμ j x h :=
    (real_apply_eq_actE_real_inv_mul (M μ (j.1 + 1) (by omega) (by omega)) x (g j) h).trans
      (congrArg (actE (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ (g j)) ((A.real μ hμ j x _).trans
        (congrArg (fun z => A.eW μ hμ j (X.fn hμ j x ((A.PV j).ψ z))) (inv_aux _ _ _))))
  rep_iso := A.rep_iso

theorem shift_a (A : Agree X M rep) (g : Fin D.R.m → ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (j) :
    (shift A g).a j = g j * A.a j := rfl

theorem real_eq {M' : MtFam D} (A : Agree X M rep) (A' : Agree X M' rep) (hP : A.PV = A'.PV) (ha : A.a = A'.a)
    {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (x) (h) :
    (A'.eW μ hμ j).symm ((M' μ (j.1 + 1) (by omega) (by omega)).real x h) =
      (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x h) := by
  rw [A.real μ hμ, A'.real μ hμ, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hP, ha]

theorem eq_zero_of_fin (A : Agree X M rep) {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1))
    (hx : ∀ g ∈ GfC (Vc D j), X.fn hμ j x g = 0) : x = 0 := by
  apply (M μ (j.1 + 1) (by omega) (by omega)).real_inj
  funext h
  rw [A.real μ hμ, hx _ ((A.PV j).into _), map_zero, map_zero]
  rfl

theorem rep_inj (A : Agree X M rep) (σ σ' : D.what₂.FT) (h : rep σ = rep σ') : σ = σ' := by
  obtain ⟨T, hT⟩ := A.iso_rep σ
  obtain ⟨T', hT'⟩ := A.iso_rep σ'
  apply X.eFT.injective
  apply rowRepR_inj X.R.θ
  revert T hT
  rw [h]
  intro T hT
  refine ⟨T.symm.trans T', fun k f f' e => ?_⟩
  apply hT'
  have hm := (rep σ').stable k _ (T.symm f).2
  have h2 := hT k (T.symm f) ⟨_, hm⟩ rfl
  have h4 : T (T.symm f) = f := T.apply_symm_apply f
  have h3 : T ⟨_, hm⟩ = f' := Subtype.ext (h2.trans ((congrArg (fun z : (X.rep σ).S => NG.rt D.host.E D.R.r k z.1) h4).trans e.symm))
  exact congrArg Subtype.val (T.symm_apply_eq.2 h3.symm)

theorem canon_phi_inj (j : Fin D.R.m) (Y : GlobalTheory.NPin.RowMod D rep (j.1 + 1)) (h : IsCanon X j rfl Y) :
    Function.Injective Y.φ := by
  obtain ⟨e, c, -, -, -, -, -, h6⟩ := h
  intro y y' hy
  apply (X.IL.jMj j).injective
  apply Subtype.ext
  rw [← h6, ← h6]
  exact congrArg (fun z => PiTensorProduct.lift (e z)) hy

end GlobalTheory.NJoin.Model

end
