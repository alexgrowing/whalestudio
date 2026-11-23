import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.OccRowVec

open Representation

theorem exists_ne_zero_ann {G : Type} [Group G] {S A : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ G S) (ρ : Representation ℂ G A)
    (hirr : ∀ W : Submodule ℂ S, (∀ g, ∀ x ∈ W, σ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    {ι : Type} [Fintype ι] (Φ : ι → S →ₗ[ℂ] A) (hΦ : ∀ i g x, Φ i (σ g x) = ρ g (Φ i x))
    {U : A} (hU : U ∈ ⨆ i, LinearMap.range (Φ i)) (hU0 : U ≠ 0) :
    ∃ v : S, v ≠ 0 ∧ ∀ x : MonoidAlgebra ℂ G, ρ.asAlgebraHom x U = 0 → σ.asAlgebraHom x v = 0 := by
  classical
  haveI : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hU0
    have : (⨆ i, LinearMap.range (Φ i)) = ⊥ := by
      rw [iSup_eq_bot]
      intro i
      rw [LinearMap.range_eq_bot]
      ext x
      simp [Subsingleton.elim x 0]
    rw [this] at hU
    exact (Submodule.mem_bot ℂ).1 hU
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule := by
    haveI : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial
    refine { exists_pair_ne := exists_pair_ne _, eq_bot_or_eq_top := fun N => ?_ }
    let W : Submodule ℂ S :=
      { carrier := {s | σ.asModuleEquiv.symm s ∈ N}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          show σ.asModuleEquiv.symm (a + b) ∈ N
          rw [map_add]; exact N.add_mem ha hb
        smul_mem' := fun c a ha => by
          show σ.asModuleEquiv.symm (c • a) ∈ N
          rw [asModuleEquiv_symm_map_smul]; exact N.smul_mem _ ha }
    have hW : ∀ g, ∀ x ∈ W, σ g x ∈ W := by
      intro g x hx
      show σ.asModuleEquiv.symm (σ g x) ∈ N
      rw [asModuleEquiv_symm_map_rho]; exact N.smul_mem _ hx
    rcases hirr W hW with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have : σ.asModuleEquiv y ∈ W := by
        show σ.asModuleEquiv.symm (σ.asModuleEquiv y) ∈ N
        simpa using hy
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      simpa using this
    · right
      rw [eq_top_iff]
      intro y _
      have : σ.asModuleEquiv y ∈ W := by rw [h]; trivial
      simpa [W] using this
  let Φ' : ι → σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun i =>
    IntertwiningMap.equivLinearMapAsModule σ ρ ⟨Φ i, fun g => LinearMap.ext fun v => hΦ i g v⟩
  have hΦ' : ∀ i v, Φ' i (σ.asModuleEquiv.symm v) = ρ.asModuleEquiv.symm (Φ i v) := fun i v => rfl
  let Ψ : (ι → σ.asModule) →ₗ[MonoidAlgebra ℂ G] ρ.asModule := ∑ i, (Φ' i).comp (LinearMap.proj i)
  have hΨ : ∀ i w, Ψ (Pi.single i w) = Φ' i w := by
    intro i w
    simp [Ψ, Pi.single_apply, apply_ite]
  have hUr : ρ.asModuleEquiv.symm U ∈ LinearMap.range Ψ := by
    clear hU0
    induction hU using Submodule.iSup_induction' with
    | mem i y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact ⟨Pi.single i (σ.asModuleEquiv.symm v), by rw [hΨ, hΦ']⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker Ψ)
  obtain ⟨m, hm⟩ := hUr
  have hmem : m ∈ LinearMap.ker Ψ ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hmem
  have hΨc : Ψ c = ρ.asModuleEquiv.symm U := by
    rw [← hm, map_add, LinearMap.mem_ker.1 ha, zero_add]
  have hc0 : c ≠ 0 := by
    intro h
    apply hU0
    rw [h, map_zero] at hΨc
    have := congrArg ρ.asModuleEquiv hΨc
    simpa using this.symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc0
  refine ⟨σ.asModuleEquiv (c i), by simpa using hi, fun x hx => ?_⟩
  have hxc : x • c ∈ LinearMap.ker Ψ ⊓ C := by
    refine Submodule.mem_inf.2 ⟨?_, C.smul_mem x hc⟩
    rw [LinearMap.mem_ker, map_smul, hΨc]
    apply ρ.asModuleEquiv.injective
    rw [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, hx, map_zero]
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hxc
  rw [← asModuleEquiv_map_smul]
  have : x • c i = 0 := by
    have := congrFun hxc i
    simpa using this
  rw [this, map_zero]

end GlobalTheory.OccRowVec

namespace GlobalTheory.OccRowVec

open Representation

section FinRep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

noncomputable def finRep (π : Formalism.L2.NG.FinTyp L n) : Representation ℂ (Formalism.AUTREP.GAf L n) π.S where
  toFun h := (Formalism.L2.NG.rt L n h).restrict (fun f hf => π.stable h f hf)
  map_one' := by
    ext f x
    simp [LinearMap.restrict_apply, Formalism.IndefR.principalLevelFrame.rt_one]
  map_mul' a b := by
    ext f x
    simp [LinearMap.restrict_apply, Formalism.IndefR.principalLevelFrame.rt_rt]

theorem finRep_coe (π : Formalism.L2.NG.FinTyp L n) (h : Formalism.AUTREP.GAf L n) (f : π.S) :
    ((finRep π h f : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h f := rfl

theorem finRep_irr (π : Formalism.L2.NG.FinTyp L n) :
    ∀ W : Submodule ℂ π.S, (∀ g, ∀ x ∈ W, finRep π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hst : ∀ h, ∀ f ∈ W.map π.S.subtype, Formalism.L2.NG.rt L n h f ∈ W.map π.S.subtype := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨finRep π g x, hW g x hx, rfl⟩
  rcases π.irr (W.map π.S.subtype) (Submodule.map_subtype_le _ _) hst with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hxy⟩ := this
    have : y = x := Subtype.ext hxy
    subst this
    exact hy

end FinRep

theorem mult_lev {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V Sp} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem T h => exact h.lev
  | zero => intro v k _ g; simp
  | add T T' _ _ h h' => intro v k hk g; simp [h v k hk g, h' v k hk g, mul_add]
  | smul c T _ h => intro v k hk g; simp [h v k hk g, mul_left_comm]

theorem lev_triv {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (Lev.EAf D)) (P : LevelP Lc.Pg D.R.r ℂ)
    {x : GA D (Yc D 0)} (hx : x ∈ levS (Yc D 0) β (Lc.dat0 Lc.triv)) :
    x ∈ levS (Yc D 0) β (Lc.dat0 P) ∧ levChi (Yc D 0) β (Lc.dat0 P) x = 1 := by
  have hx' : x ∈ levG (Yc D 0) β (Lc.dat0 Lc.triv) := hx
  obtain ⟨hG, hpar, hr⟩ := mem_levA.1 hx'
  have hH : (Lc.dat0 Lc.triv).P.H = ⊥ := by
    simp [LevCh.dat0, datY, LevelP.triv] <;> rfl
  have hr1 : rTup β (Lc.dat0 Lc.triv) (finE (Yc D 0) x) = 1 := by
    have := hr
    rw [hH] at this
    exact (Subgroup.mem_bot).1 this
  have hr1' : rTup β (Lc.dat0 P) (finE (Yc D 0) x) = 1 := hr1
  refine ⟨?_, ?_⟩
  · show x ∈ levG (Yc D 0) β (Lc.dat0 P)
    refine mem_levA.2 ⟨hG, hpar, ?_⟩
    show rTup β (Lc.dat0 P) (finE (Yc D 0) x) ∈ (Lc.dat0 P).P.H
    rw [hr1']
    exact Subgroup.one_mem _
  · unfold levChi levFn
    rw [hr1', blockDiagonalExtendByOnePrimeField_one]
    simp [LevCh.dat0, datY]

theorem levChi_flag_triv {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (Lev.EAf D)) (x : GA D (Yc D 0)) :
    levChi (Yc D 0) β (flagL (Lc.dat0 Lc.triv)) x = 1 := by
  unfold levChi levFn
  simp only [flagL, withP, LevelP.full]
  unfold ext1
  split_ifs
  · simp [LevCh.dat0, datY]
    rfl
  · simp [LevCh.dat0, datY]
end GlobalTheory.OccRowVec

namespace GlobalTheory.OccRowVec

open Representation

theorem exists_vec_of_occRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ v ∈ (principalLevelFrame.FinTyp.conjT π).S, v ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ _ n PY π hπ
  obtain ⟨b, hb⟩ := hπ
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 hb
  have hU' : U ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ⊓
      principalLevelFrame.isotIn (principalLevelFrame.actM PY (R.MY 0)) (principalLevelFrame.Minf R.θ PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π) := hU
  obtain ⟨hgood, hiso⟩ := Submodule.mem_inf.1 hU'
  obtain ⟨hMult, hker⟩ := Submodule.mem_inf.1 hgood
  have he0 : postOn (R.MY 0) R.e0 U = U := by
    have := LinearMap.mem_ker.1 hker
    rw [LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  unfold principalLevelFrame.isotIn at hiso
  rw [iSup_subtype'] at hiso
  obtain ⟨sF, hsF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hiso
  rw [iSup_subtype'] at hsF
  have hΦ : ∀ (i : {x // x ∈ sF}) (g : Formalism.AUTREP.GAf D.host.E n) (x : (principalLevelFrame.FinTyp.conjT π).S),
      (i.1.1 : (principalLevelFrame.FinTyp.conjT π).S →ₗ[ℂ] MMap (R.MY 0)) (finRep (principalLevelFrame.FinTyp.conjT π) g x) =
        principalLevelFrame.actM PY (R.MY 0) g (i.1.1 x) := fun i g x => i.1.2.1 g x
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_ann (ι := {x // x ∈ sF}) (finRep (principalLevelFrame.FinTyp.conjT π))
    (principalLevelFrame.actM PY (R.MY 0)) (finRep_irr _) (fun i => i.1.1) hΦ hsF hU0
  refine ⟨(v : Formalism.AUTREP.GAf D.host.E n → ℂ), v.2, fun h => hv0 (Subtype.ext h), ?_, ?_⟩
  · intro κ hκ
    have hl := lev_triv R.toLevCh (R.βY 0) (R.levR F b) hκ
    have hU1 : principalLevelFrame.actM PY (R.MY 0) κ U = U := by
      apply MultilinearMap.ext
      intro w
      funext x
      rw [principalLevelFrame.actM_apply, mult_lev hMult w _ hl.1 x, hl.2, one_mul]
    have h1 := hv (MonoidAlgebra.of ℂ _ κ - 1) (by
      rw [map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, hU1, Module.End.one_apply, sub_self])
    rw [map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [one_smul]
    exact congrArg Subtype.val h1
  · intro κ hκ
    have hHas : ∀ w, HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) (U w) := by
      intro w k hk h
      have hl := lev_triv R.toLevCh (R.βY 0) (R.levR F b) (x := k) hk
      have hl0 := lev_triv R.toLevCh (R.βY 0) R.triv (x := k) hk
      show U w (h * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k * U w h
      rw [mult_lev hMult w _ hl.1 h, hl.2, hl0.2]
    have hchi : ∀ g, levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (PY.ψ (κ g)) = 1 := by
      intro g
      exact levChi_flag_triv R.toLevCh _ _
    have hU2 : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U = U := by
      apply MultilinearMap.ext
      intro w
      funext x
      have h1 := congrArg (fun T : MMap (R.MY 0) => T w x) he0
      simp only [postOn_apply] at h1
      rw [← h1]
      have hact : ∀ g, actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x = U w (x * PY.ψ (κ g)) := by
        intro g
        rw [level_action_spec (hHas w) ⟨_, hκ g⟩ (PY.ψ (κ g)) (hκ g) x, hchi g, inv_one, one_mul]
      have hL : (∑ g, RealDat.eC (A := A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U) w x =
          ∑ g, RealDat.eC (A := A) D.what₂.embLL g * U w (x * PY.ψ (κ g)) := by
        rw [MultilinearMap.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [MultilinearMap.smul_apply, Pi.smul_apply, principalLevelFrame.actM_apply, smul_eq_mul]
      have hR : R.e0 (U w) x =
          ∑ g, RealDat.eC (A := A) D.what₂.embLL g * actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x := by
        show (∑ g, RealDat.eC (A := A) D.what₂.embLL g • actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (U w) x = _
        rw [LinearMap.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
        rfl
      rw [hL, hR]
      exact Finset.sum_congr rfl fun g _ => by rw [hact g]
    have h1 := hv (∑ g, MonoidAlgebra.single (κ g) (RealDat.eC (A := A) D.what₂.embLL g) - 1) (by
      rw [map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply]
      simp only [asAlgebraHom_single, LinearMap.smul_apply]
      rw [hU2, sub_self])
    rw [map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      sub_eq_zero] at h1
    simp only [asAlgebraHom_single, LinearMap.smul_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    simpa [Submodule.coe_smul, finRep_coe] using h2

end GlobalTheory.OccRowVec
