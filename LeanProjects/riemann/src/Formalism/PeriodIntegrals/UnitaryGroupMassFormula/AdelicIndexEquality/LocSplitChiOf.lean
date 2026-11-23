import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def GLChi : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (n : ℕ) (χ : GL (Fin n) k →* ℚ), (∀ g, 0 < χ g) →
    (∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1) →
    ∀ g, χ g = 1

theorem spl_sig_sig (I : AutInst) (a : I.E) : I.cm.sig (I.cm.sig a) = a := by
  change star (star a) = a
  exact star_star a

theorem spl_sig_fix (I : AutInst) (a : I.E) (h : I.cm.sig a = a) : a ∈ (algebraMap I.F I.E).range := (I.cm.fixed a).1 h

theorem spl_sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) :
    sigV I v (inclV I v x) = inclV I v (starRingEnd I.E x) := by
  simp only [sigV, inclV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

theorem spl_herm_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  have h := I.J_herm
  unfold Formalism.UG.IsHerm at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [spl_sigV_inclV, hij]

theorem spl_det_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : IsUnit (I.J.map (inclV I v)).det := by
  have h := RingHom.map_det (inclV I v) I.J
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (isUnit_iff_ne_zero.2 I.J_det).map _

theorem locSplitChi_of (hG : GLChi) : LocSplitChi := by
  intro I v hnf χ hpos hcent _ g
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F _).injective
  obtain ⟨π, hπ⟩ := SplitIso.exists_split (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (spl_sig_sig I) (spl_sig_fix I) I.cm.deg2 two_ne_zero hnf
  have hπ' : ∀ r, π (sigV I v r) = (π r).swap := hπ
  let f : Uv I v →* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    SplitGL.proj (sigV I v) π (I.J.map (inclV I v))
  have hbij : Function.Bijective f :=
    SplitGL.proj_bijective (sigV I v) π hπ' (I.J.map (inclV I v)) (spl_herm_v I v) (spl_det_v I v)
  let e : Uv I v ≃* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) := MulEquiv.ofBijective f hbij
  have key := hG (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.n (χ.comp e.symm.toMonoidHom) (fun g => hpos _) ?_ (e g)
  · have h2 : e.symm (e g) = g := e.symm_apply_apply g
    rw [← h2]; exact key
  · intro d
    show χ (e.symm _) = 1
    apply hcent
    intro t
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact Algebra.commutes _ _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
