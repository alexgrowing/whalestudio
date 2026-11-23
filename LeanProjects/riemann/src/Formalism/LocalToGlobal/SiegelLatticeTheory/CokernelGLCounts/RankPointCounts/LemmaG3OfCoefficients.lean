import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfInputs

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem lemmaG3_of_coefficients (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    nmlOf Y u u' t1 = nmlOf Y u u' t2 := by
  obtain ⟨iω, iς, i3⟩ := lemmaG3_of_inputs Y hT hT' t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hGF1 : Gflag (X.Fu u) t1.frame.fl ≠ 0 := G_ne_of_Gt Y h1
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  have hs'' := SRat_inv (lf D (X.Fu u')) hs'
  set ς := t1.lin * s'⁻¹ * t1.lin⁻¹ with hς
  have hςx : ∀ x, ς x = t1.lin (s'.symm (t1.lin.symm x)) := fun x => rfl
  have hςf : ∀ x ∈ t1.frame.fl.X, ς x - x ∈ t1.frame.fl.X := by
    intro x hx
    refine (mem_frameX Y t1 _).2 ?_
    have hx0 := (mem_frameX Y t1 x).1 hx
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply]
    exact Submodule.sub_mem _ (X_pres (lf D (X.Fu u')) hs''.2.1 _ hx0) hx0
  have hςz : ς t1.frame.fl.z - t1.frame.fl.z ∈ t1.frame.fl.X := by
    refine (mem_frameX Y t1 _).2 ?_
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
    exact hs''.2.2
  obtain ⟨τ, hτi, hτA, P1, P2⟩ := tau_exists (X.Fu u) t1.frame.fl hGF1 hTE (star_natCast _) hTE' (star_natCast _)
    σ ς hσ.1 (fun x hx => Submodule.sub_mem _ (X_pres (lf D (X.Fu u)) hσ.2.1 x hx) hx)
    (fun x hx => X_pres (lf D (X.Fu u)) hσ'.2.1 x hx) hσ.2.2 hςf hςz iω iς i3
  have hτX : ∀ x ∈ (X.Fu u).X, τ x = x := fun x hx => hτA x (X_le_Asp _ _ hx)
  have hτX1 : ∀ x ∈ t1.frame.fl.X, τ x = x := fun x hx => hτA x (by rw [← Asp_symm]; exact X_le_Asp _ _ hx)
  have hτs : ∀ x ∈ (X.Fu u).X, τ.symm x = x := fun x hx => by
    conv_lhs => rw [← hτX x hx]
    simp
  set n := σ * τ⁻¹ with hn
  set n' := t1.lin⁻¹ * τ * t1.lin * s' with hn'
  have hnN : n ∈ NRat (lf D (X.Fu u)) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hσ.1 ((Formalism.HermitianLatticesTheory.isom _).inv_mem hτi), fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u).X := Xflag_le_X (lf D (X.Fu u)) (j + 1) hx
      show σ (τ.symm x) - x ∈ _
      rw [hτs x hxX]
      exact hσ.2.1 j x hx
    · have hτi' : τ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).inv_mem hτi
      have hz : τ.symm y ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
        perp_pres (lf D (X.Fu u)) hτi' (fun x hx => by rw [LinearEquiv.symm_symm, hτX x hx]; exact hx) y hy
      have := P1 _ hz
      rw [LinearEquiv.apply_symm_apply] at this
      show σ (τ.symm y) - y ∈ _
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
  have hn'N : n' ∈ NRat (lf D (X.Fu u')) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem
      ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ1) hτi) hγ1) hs'.1, fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u').X := Xflag_le_X (lf D (X.Fu u')) (j + 1) hx
      have hsx : s' x ∈ (X.Fu u').X := X_pres (lf D (X.Fu u')) hs'.2.1 x hxX
      have h1x : t1.lin (s' x) ∈ t1.frame.fl.X := (mem_frameX Y t1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hsx)
      show t1.lin.symm (τ (t1.lin (s' x))) - x ∈ _
      rw [hτX1 _ h1x, LinearEquiv.symm_apply_apply]
      exact hs'.2.1 j x hx
    · have hsy : s' y ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
        perp_pres (lf D (X.Fu u')) hs'.1 (fun x hx => X_pres (lf D (X.Fu u')) hs''.2.1 x hx) y hy
      have hv : t1.lin (s' y) ∈ Lat.orth (VS D) t1.frame.fl.X := by
        refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
        rw [show x = t1.lin (t1.lin.symm x) by simp, hγ1]
        exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hsy _ ((mem_frameX Y t1 x).1 hx)
      have h := P2 _ hv
      rw [hςx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
      have h' := (mem_frameX Y t1 _).1 h
      rw [map_sub, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have heq : t2.lin = n * t1.lin * n' := by
    rw [he, hn, hn']
    group
  ext δ
  constructor
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n⁻¹, NRat_mul _ hm (NRat_inv _ hnN), n'⁻¹ * m', NRat_mul _ (NRat_inv _ hn'N) hm', ?_⟩
    rw [heq]
    group
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n, NRat_mul _ hm hnN, n' * m', NRat_mul _ hn'N hm', ?_⟩
    rw [heq]
    group

theorem normalsLemmaG3_holds : UnitaryNormalVectorCount := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 hσs ha ha' => ?_⟩
  obtain ⟨σ, hσ, s', hs', he⟩ := hσs
  have hT : 3 ≤ Tu D u ∧ 3 ≤ Tu D u' := by
    clear * - hc
    unfold Ctx at hc
    obtain ⟨-, -, -, h3, h3', -⟩ := hc.2.1
    exact ⟨h3, h3'⟩
  exact lemmaG3_of_coefficients Y hT.1 hT.2 t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'

end Formalism.L2.SG.NGCut.NormalVectorPairings
