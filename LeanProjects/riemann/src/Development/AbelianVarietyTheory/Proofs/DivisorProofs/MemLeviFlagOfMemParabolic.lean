import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLevel

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mem_levi_flag_of_mem_parabolic (P : LevelP L.Pg L.r ℂ) {k : GA D V} (hk : k ∈ levG V β (flag1L L)) :
    k ∈ levG V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := by
    have : rTup β L (finE V k) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2.2
    exact Subgroup.mem_bot.1 this
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · unfold levChi
    rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem isPLevel_of_hasType (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ}
    (hF : HasType V β (withP L P) F) : IsPLevel V β L P F := by
  have h1 : HasType V β (flag1L L) F := fun k hk h => by
    rw [hF k (mem_levi_flag_of_mem_parabolic P hk).1, (mem_levi_flag_of_mem_parabolic P hk).2]
  refine ⟨h1, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p.1
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hm : κ ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    unfold levChi
    rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  funext h
  rw [level_action_spec h1 ⟨κ, hκ⟩ κ hκ h, hF κ hm, hc]
  field_simp

theorem postOn_actL_mem (g0 : G0 L.Pg L.r) {X : MMap M}
    (hT : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (actL V β L g0) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have hU : ∀ v, postOn M (actL V β L g0) X v = actG0 V β L g0 (X v) := fun _ => rfl
  by_cases hex : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hex.choose_spec
    have e : postOn M (actL V β L g0) X = (levChi V β (flagL L) hex.choose)⁻¹ • heckeOn M {hex.choose} X := by
      ext v g
      rw [hU, actG0, dif_pos hex]
      simp [heckeOn, postOn_apply, heckeLin_apply]
    rw [e]
    refine Submodule.smul_mem _ _ ?_
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT (fun k hk => ?_) fun v k hk g => ?_
    · rw [Finset.mem_singleton.1 hk]
      exact hκ.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.FlagAction.conj_mem_flag1 hκ hk
      simp only [heckeLin_apply, Finset.sum_singleton]
      rw [← h2, ← hT.lev v _ h1]
      group
  · have e : postOn M (actL V β L g0) X = 0 := by
      ext v g
      rw [hU, actG0, dif_neg hex]
      rfl
    rw [e]
    exact zero_mem _

theorem postOn_gaL_mem_goodPart (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    (hcomm : ∀ g F, HasType V β (flag1L L) F →
      gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F))
    (P : LevelP L.Pg L.r ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P)) (gaL V β L eG c) := by
  have hX1 : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    GlobalTheory.ProjectedLift.mult_mono (fun k hk => mem_levi_flag_of_mem_parabolic P hk) hX
  have hY : postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
    have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
      ext v h
      simp [gaL, postOn_apply]
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (postOn_actL_mem _ hX1)
  rw [mem_goodPart]
  refine ⟨?_, fun v => GlobalTheory.ProjectedLift.gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX1 v)⟩
  have hY' := (GlobalTheory.MultMem.mem_mult_iff ..).1 hY
  refine (GlobalTheory.MultMem.mem_mult_iff ..).2 ⟨hY'.aut, hY'.cusp, fun v => ?_, hY'.equiv, hY'.cont⟩
  have hP := isPLevel_of_hasType hL (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)
  have hQ : IsPLevel V β L P (gaL V β L eG c (X v)) := by
    refine ⟨hY'.lev v, fun p => ?_⟩
    have e1 : actL V β L p.1 (X v) = ((P.chi p : ℂˣ) : ℂ) • X v := hP.2 p
    have e2 := hcomm (eG.symm p.1) _ hP.1
    rw [MulEquiv.apply_symm_apply, e1, map_smul] at e2
    exact e2.symm
  exact hQ.hasType

end Act

theorem proj_mem_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ), ∀ U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)), postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U ∈ R.Wat i (sg0 D A) P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hv i P U hU
  have hL : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := h.βW i
    refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ hv
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := by
    rw [hs]; exact GlobalTheory.ProjectedLift.eC_conv R hr
  exact postOn_gaL_mem_goodPart (L := R.datWp i R.triv) hL R.eG _ hc
    ((GlobalTheory.ProjComm.proj_comm R h hr).2 i (sg0 D A)) P hU

end GlobalTheory.GoodProjLevel

end
