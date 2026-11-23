import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDensePf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem relIndex_eq_of_dense {G : Type*} [Group G] {R U U' : Subgroup G} (hRU : R ≤ U)
    (hd : ∀ x ∈ U, ∃ r ∈ R, r⁻¹ * x ∈ U') : U'.relIndex R = U'.relIndex U := by
  let f := Subgroup.quotientSubgroupOfEmbeddingOfLE U' hRU
  have hs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨r, hr, hrx⟩ := hd x x.2
      refine ⟨QuotientGroup.mk ⟨r, hr⟩, ?_⟩
      rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hrx
  show Nat.card (R ⧸ U'.subgroupOf R) = Nat.card (U ⧸ U'.subgroupOf U)
  exact Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hs⟩)

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c y : X.B.I.Gf) :
    y ∈ (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ X.K2 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : c⁻¹ * ((MulAut.conj c).toMonoidHom k) * c = k := by
      simp [MulAut.conj_apply]; group
    rw [e]; exact hk
  · intro h
    refine ⟨c⁻¹ * y * c, h, ?_⟩
    simp [MulAut.conj_apply]; group

theorem coe_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) =
      (fun y => c⁻¹ * y * c) ⁻¹' X.K2 := by
  ext y
  exact mem_conj_level_subgroup X hK c y

theorem rat_fst_inj {q s : X.B.I.GA} (hq : q ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (hs : s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)
    (h : q.1 = s.1) : q = s := by
  have h1 : (q⁻¹ * s).1 = 1 := by rw [Prod.fst_mul, Prod.fst_inv, h, inv_mul_cancel]
  have := Formalism.L2.SG.Pf.SlabCoverPf.finite_infinite_injective D X (q⁻¹ * s) (mul_mem (inv_mem hq) hs) h1
  exact (inv_mul_eq_one.1 this)

theorem mem_RcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.GA) :
    s ∈ RcS X u hK c ↔ s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ∧
      s.1 ∈ Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u) ∧ s.2 ∈ UcS X u hK c := by
  unfold RcS
  rw [Subgroup.mem_inf, Subgroup.mem_prod]

theorem relIndex_gc (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    (GcS X u hK c').relIndex (GcS X u hK c) =
      (UcS X u hK c').relIndex ((RcS X u hK c).map (MonoidHom.snd _ _)) := by
  let φ : RcS X u hK c →* X.B.I.Ginf := (MonoidHom.fst _ _).comp (RcS X u hK c).subtype
  let ψ : RcS X u hK c →* X.B.I.Gf := (MonoidHom.snd _ _).comp (RcS X u hK c).subtype
  have hφ : GcS X u hK c = φ.range := by
    unfold GcS
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hψ : (RcS X u hK c).map (MonoidHom.snd _ _) = ψ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcomap : (GcS X u hK c').comap φ = (UcS X u hK c').comap ψ := by
    ext r
    obtain ⟨r, hr⟩ := r
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    show r.1 ∈ GcS X u hK c' ↔ r.2 ∈ UcS X u hK c'
    obtain ⟨hrQ, hr1, -⟩ := (mem_RcS X u hK c r).1 hr
    constructor
    · rintro ⟨s, hs, hs1⟩
      obtain ⟨hsQ, -, hs2⟩ := (mem_RcS X u hK c' s).1 hs
      have e : s = r := rat_fst_inj X hsQ hrQ hs1
      rw [← e]; exact hs2
    · intro h2
      exact ⟨r, (mem_RcS X u hK c' r).2 ⟨hrQ, hr1, h2⟩, rfl⟩
  rw [hφ, hψ, ← Subgroup.index_comap, ← Subgroup.index_comap, hcomap]

theorem isOpen_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    IsOpen (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) := by
  rw [coe_conj_level_subgroup]
  exact (level_subgroup_isClopen X hK (Formalism.L2.SG.Closed.level_subgroup_properties X)).isOpen.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    IsCompact (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) := by
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK2 : IsCompact X.K2 :=
    (PI.WAU.Cpt.isCompact_Kset X.B.I).of_isClosed_subset (level_subgroup_isClopen X hK hKL).isClosed hKL.2.1
  have e : (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) =
      (fun k => c * k * c⁻¹) '' X.K2 := by
    rw [Subgroup.coe_map]
    rfl
  rw [e]
  exact hK2.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem relIndex_uc_ne_zero (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    (UcS X u hK c').relIndex (UcS X u hK c) ≠ 0 := by
  set N := Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u)
  set C := (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom
  set C' := (concreteLevelAdelicSubset X hK).map (MulAut.conj c').toMonoidHom
  have hU : UcS X u hK c = N ⊓ C := rfl
  have hU' : UcS X u hK c' = N ⊓ C' := rfl
  have hCC : C'.relIndex C ≠ 0 := by
    have : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_conj_level_subgroup X hK c)
    have ho : IsOpen ((C'.subgroupOf C : Subgroup C) : Set C) :=
      (isOpen_conj_level_subgroup X hK c').preimage continuous_subtype_val
    have := Subgroup.quotient_finite_of_isOpen (C'.subgroupOf C) ho
    exact Subgroup.index_ne_zero_of_finite
  have e1 : (N ⊓ C').relIndex (N ⊓ C) = C'.relIndex (N ⊓ C) := by
    rw [← Subgroup.inf_relIndex_right (N ⊓ C'), ← Subgroup.inf_relIndex_right C' (N ⊓ C)]
    congr 1
    ext y
    simp only [Subgroup.mem_inf]
    tauto
  rw [hU, hU', e1]
  intro h0
  exact hCC (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)

theorem dense_uc (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    ∀ x ∈ UcS X u hK c, ∃ y ∈ (RcS X u hK c).map (MonoidHom.snd _ _), y⁻¹ * x ∈ UcS X u hK c' := by
  intro x hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxK : c⁻¹ * x * c ∈ X.K2 := (mem_conj_level_subgroup X hK c x).1 hxC
  have hKo := (level_subgroup_isClopen X hK (Formalism.L2.SG.Closed.level_subgroup_properties X)).isOpen
  let O : Set X.B.I.Gf := {y | c⁻¹ * (x⁻¹ * y) * c ∈ X.K2 ∧ c'⁻¹ * (x⁻¹ * y) * c' ∈ X.K2}
  have hO : IsOpen O := by
    refine (hKo.preimage ?_).inter (hKo.preimage ?_)
    · exact (continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const
    · exact (continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const
  have hxO : x ∈ O := by
    refine ⟨?_, ?_⟩ <;> simpa using hK.1
  obtain ⟨ν, hνQ, hν1, hν2, hνO⟩ := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation D X u x hxN O hO hxO
  obtain ⟨hk1, hk2⟩ := hνO
  have hν2C : c⁻¹ * ν.2 * c ∈ X.K2 := by
    have e : c⁻¹ * ν.2 * c = (c⁻¹ * x * c) * (c⁻¹ * (x⁻¹ * ν.2) * c) := by group
    rw [e]; exact hK.2.1 _ hxK _ hk1
  have hνR : ν ∈ RcS X u hK c :=
    (mem_RcS X u hK c ν).2 ⟨hνQ, hν1, Subgroup.mem_inf.2 ⟨hν2, (mem_conj_level_subgroup X hK c _).2 hν2C⟩⟩
  refine ⟨ν.2, ⟨ν, hνR, rfl⟩, Subgroup.mem_inf.2 ⟨?_, (mem_conj_level_subgroup X hK c' _).2 ?_⟩⟩
  · exact mul_mem (inv_mem (show ν.2 ∈ Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u) from hν2)) hxN
  · have e : c'⁻¹ * (ν.2⁻¹ * x) * c' = (c'⁻¹ * (x⁻¹ * ν.2) * c')⁻¹ := by group
    rw [e]; exact hK.2.2.1 _ hk2

theorem indexTransferC_holds : IndexTransferC := by
  intro D X u hK g h
  set c := (g : X.B.I.Gf) * X.xu u
  set c' := (h : X.B.I.Gf) * X.xu u
  have hle : (RcS X u hK c).map (MonoidHom.snd _ _) ≤ UcS X u hK c := by
    rintro _ ⟨s, hs, rfl⟩
    exact ((mem_RcS X u hK c s).1 hs).2.2
  refine ⟨?_, relIndex_uc_ne_zero X u hK c c'⟩
  rw [relIndex_gc X u hK c c']
  exact relIndex_eq_of_dense hle (dense_uc X u hK c c')

end Formalism.L2.SG.Pf.IdMeet
