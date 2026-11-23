import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
open Matrix

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem isId_rat {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (t : GTerm X u u (X.Fu u) (X.Fu u) what₂ what₂) (ht : t.isId) :
    (∀ a : Fin D.R.rS, t.lin (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1})) ∧
      t.lin (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX) := by
  have hin := Formalism.L2.SG.FourParts.isInS_of_isIdT ht
  have hS : Formalism.L2.SG.FourParts.InSF (lf D (X.Fu u)) t.frame :=
    (Formalism.L2.SG.FourParts.isInS_mk (Λ := t.lam) (F := lf D (X.Fu u))
      (P := Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u)
      (PI.InSClassConstW.inSFun_all _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩).1 hin
  have hfr : t.frame.fl = mapFlag t.rep.1.2 t.rep.2.2.1 (lf D (X.Fu u)).fl := by
    show (mapLF t.rep.1.2 (lf D (X.Fu u))).fl = _
    unfold mapLF
    rw [dif_pos t.rep.2.2.1]
    try rfl
  refine ⟨fun a => ?_, ?_⟩
  · have h := hS.1 a
    have e1 : t.frame.fl.e a = t.lin (X.eX a) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).e a) = t.rep.1.2 (X.eX a)
      rw [X.Fu_e u]
    have e2 : (lf D (X.Fu u)).fl.e a = X.eX a := by
      show (X.Fu u).e a = _
      rw [X.Fu_e u]
    have e3 : Xflag (lf D (X.Fu u)) a.val = Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h
  · have h := hS.2
    have e1 : t.frame.fl.z = t.lin (X.zu u) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).z) = t.rep.1.2 (X.zu u)
      rw [X.flagZVector u]
    have e2 : (lf D (X.Fu u)).fl.z = X.zu u := by
      show (X.Fu u).z = _
      rw [X.flagZVector u]
    have e3 : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range (X.Fu u).e) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h

theorem pt_srat {u : D.what₂.Word} {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}))
    (hz : n (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX)) : x ∈ Srat X u := by
  have hmem := ratLink_mem X hx
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  have hE : ∀ a : Fin D.R.rS, ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a ∈
      Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
    intro a
    have := crd_span' X (he a)
    rw [Set.image_image] at this
    show _ *ᵥ X.crd (X.eX a) ∈ _
    rw [mcrd X h3]
    exact this
  have hZ : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.zR u ∈
      Submodule.span X.B.I.E (Set.range X.eR) := by
    have := crd_span' X hz
    rw [← Set.range_comp] at this
    show _ *ᵥ X.crd (X.zu u) ∈ _
    rw [mcrd X h3]
    exact this
  refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.subset_closure ⟨fun v => ?_, ?_⟩⟩
  · have hG : ∀ y, uMat (x.1 v) *ᵥ Vanish2.rvHom X.B.I v y =
        Vanish2.rvHom X.B.I v ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      rw [Vanish2.rvHom_apply, Vanish2.rvHom_apply, h1 v]
      exact rv_mulVec X v _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact tr_flag (X.B.I.φ v) (Vanish2.rvHom X.B.I v) (rv_smul' X.B.I v) _ _ hG X.eR _ _ (hE a)
    · have := tr_flag (X.B.I.φ v) (Vanish2.rvHom X.B.I v) (rv_smul' X.B.I v) _ _ hG X.eR Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      unfold spanLt
      rw [← range_eq_image_lt]
      rwa [Set.image_univ] at this
  · have hG : ∀ y, X.B.I.fmat x.2 *ᵥ Vanish2.inclHom X.B.I y =
        Vanish2.inclHom X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      rw [Vanish2.inclHom_apply, Vanish2.inclHom_apply, h2]
      exact incl_mulVec X _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact tr_flag _ (Vanish2.inclHom X.B.I) (incl_smul' X.B.I) _ _ hG X.eR _ _ (hE a)
    · have := tr_flag _ (Vanish2.inclHom X.B.I) (incl_smul' X.B.I) _ _ hG X.eR Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      rwa [Set.image_univ] at this

theorem lin_eq_of_fst {x y : X.B.I.GA} {m n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hy : RatLink X y n) (h : x.1 = y.1) : m = n := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  obtain ⟨N, -, k1, -, k3⟩ := hy
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have e3 : ∀ A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
      X.B.I.P v * ((X.B.I.P v)⁻¹ * A * X.B.I.P v) * (X.B.I.P v)⁻¹ = A := by
    intro A
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hP]
  have e : (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v =
      (X.B.I.P v)⁻¹ * (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v := by
    rw [← h1 v, ← k1 v, h]
  have e2 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) =
      (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) := by
    rw [← e3 ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)),
      ← e3 ((N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)), e]
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    exact (X.B.I.φ v).injective (congrFun (congrFun e2 i) j)
  refine LinearEquiv.ext fun p => ?_
  rw [← toV_crd X (m p), ← toV_crd X (n p), h3, k3, hMN]

end Formalism.L2.SG.Pf.IdMeet

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

theorem idMeetKeyC_holds : IdMeetKeyC := by
  intro D X Y u hNeat ρ ρ' t ht hM
  obtain ⟨-, -, hk⟩ := hM
  obtain ⟨he, hz⟩ := isId_rat X t ht
  have hs : t.pt ∈ Srat X u := pt_srat X t.rep.2.1 he hz
  have hg : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) ∈ X.K2 := hk
  obtain ⟨hs1, hs2⟩ := sratComp_holds X u t.pt hs
  obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u t.pt (Subgroup.mem_inf.1 hs).1 hs1 hs2
  obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
  have hs2e : t.pt.2 = ν.2 * η.2 := by rw [hνη]; rfl
  obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ)⁻¹ ν.2 hν2
  have hLD := Formalism.L2.SG.Pf.Level.levelDec_of_psiDd (X := X) (u := u) (Formalism.L2.SG.Pf.psiDd_holds X)
  obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' := ⟨_, rfl⟩
  have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
      (h1 : X.B.I.Gf)) * X.xu u =
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) := by
    rw [hs2e, hh1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
    group
  have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
  have hρρ : ρ = ρ' := by
    refine (Y.colReps u ((Y.cs u).h ρ')).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
    show (Y.cs u).h ρ' = iotaF X u ηg⁻¹ * (Y.cs u).h ρ * h1
    rw [map_inv, hh1]
    group
  subst hρρ
  have hmem : ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ ∈ Ku X u Y.hK := by
    rw [← hh1]; exact hh1K
  have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ) ηg hmem
  have hη1' : η = 1 := by
    have := congrArg Subtype.val hη1
    rw [hηg] at this
    exact this
  have hsν : t.pt = ν := by rw [hνη, hη1', mul_one]
  have hsN := nilradical_rational_lattice D X Y u ρ t.pt (Formalism.L2.SG.Closed.level_subgroup_properties X)
    (by rw [hsν]; exact hνG) (by rw [hsν]; exact hν1) (by rw [hsν]; exact hν2) hg
  obtain ⟨x, n, hx, hx1, hn⟩ := hsN
  refine ⟨rfl, ?_⟩
  have hl : t.lin = n := lin_eq_of_fst X t.rep.2.1 hx hx1
  rw [hl]
  exact hn

end Formalism.L2.SG.Pf.IdMeet
