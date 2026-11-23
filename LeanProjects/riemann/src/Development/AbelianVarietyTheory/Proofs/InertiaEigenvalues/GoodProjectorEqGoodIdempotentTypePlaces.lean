import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

section Act

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : Theta.GA D V → ℂ} (h : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ x
  have h1 : rTup β L (finE V κ) = 1 := hκ.2.2
  rw [h κ ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem⟩ x]
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, blockDiagonalExtendByOnePrimeField_one, one_mul]

end Act

theorem asAlgebraHom_eq_sum {G H M : Type} [Fintype G] [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (ε : G ≃ H) (a : MonoidAlgebra ℂ H) (z : M) : ρ.asAlgebraHom a z = ∑ g, a.coeff (ε g) • ρ (ε g) z := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    obtain ⟨h, rfl⟩ := ε.surjective h
    rw [Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem pi_induction {I : Type} [Finite I] [DecidableEq I] {H : I → Type} [∀ i, Group (H i)] (p : (∀ i, H i) → Prop) (h1 : p 1)
    (hm : ∀ a b, p a → p b → p (a * b)) (hs : ∀ i x, p (Pi.mulSingle i x)) (a : ∀ i, H i) : p a := by
  cases nonempty_fintype I
  rw [← Finset.noncommProd_mulSingle a]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun i _ => hs i _

open scoped Classical in

theorem exists_act {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z)
    (q : G0g D.nd → GAf D.host.E D.R.r → Prop) (q1 : q 1 1) (qm : ∀ a x b y, q a x → q b y → q (a * b) (x * y))
    (ql : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → q (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) x)
    (a : G0g D.nd) : ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z := by
  refine pi_induction (fun a : G0g D.nd => ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z) ?_ ?_ ?_ a
  · exact ⟨1, q1, fun z => by rw [map_one, map_one]; rfl⟩
  · rintro a b ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    exact ⟨x * y, qm _ _ _ _ hx hy, fun z => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx', hy']⟩
  · rintro ⟨k, v⟩ h
    obtain ⟨y, rfl⟩ := GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r h
    obtain ⟨x, hx⟩ : ∃ x, IsLiftAt (s k v) (j k v) y x := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r (s k v) _
    exact ⟨x, ql k v y x hx, hρ k v y x hx⟩

theorem levelChoiceData_eq_withLevel_trivial {D : D7} {T : Type} (C : LevCh D T) (P : LevelP C.Pg D.R.r ℂ) : C.dat0 P = withP (C.dat0 C.triv) P := rfl

theorem hasType_rows {D : D7} {T : Type} (C : LevCh D T) {Sp : D.what₂.Tau → _} (θ) (M : Mult.DSModel (Yc D 0) Sp)
    (P : LevelP C.Pg D.R.r ℂ) {Tm : Mult.MMap M}
    (h : Tm ∈ Mult.Mult θ M (levS _ (C.βY 0) (C.dat0 P)) (levChi _ (C.βY 0) (C.dat0 P))) (v : M.Vec) :
    HasType (Yc D 0) (C.βY 0) (flag1L (C.dat0 C.triv)) (Tm v) := by
  rw [levelChoiceData_eq_withLevel_trivial] at h
  exact hasType_flag1 (L := C.dat0 C.triv) (P := P) fun κ hκ x => principalLevelFrame.mult_lev h v κ hκ x

theorem levChi_flag {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (x : Theta.GA D V) : levChi V β (flagL L) x = 1 := by
  unfold levChi levFn
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V x)) = 1 := subgroupCharExtension_one_apply _ _
  have h3 : (flagL L).s = 0 := hs
  have h4 : (flagL L).Q = ∅ := hQ
  rw [h2, h3, h4]
  simp

theorem fix_of_lifts_comp {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {V : HSp D} {Sp : D.what₂.Tau → _} (P : principalLevelFrame.RowPsi V D.R.r) (M : Mult.DSModel V Sp) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0) (hQ : L.Q = ∅) (φ : GAf D.host.E D.R.r →* GAf D.host.E D.R.r)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM P M).comp φ)))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM P M).comp φ)) :
        Mult.MMap M) = ((principalLevelFrame.actM P M).comp φ) x z)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (cG : G0 L.Pg L.r ≃* G0g D.nd)
    (e : MonoidAlgebra ℂ (G0g D.nd)) (hc : ∀ g, e.coeff (cG (eG g)) = c g)
    (hl : ∀ k v y x, IsLiftAt (s k v) (j k v) y x →
      IsLevelLift V β L (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (P.ψ (φ x)))
    (Tm : Mult.MMap M) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM P M).comp φ))
    (hty : ∀ v, HasType V β (flag1L L) (Tm v)) (hfix : Mult.postOn M (gaL V β L eG c) Tm = Tm) :
    ρ.asAlgebraHom e ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  have key := exists_act ((principalLevelFrame.actM P M).comp φ) ρ hρ (fun a x => IsLevelLift V β L (cG.symm a) (P.ψ (φ x)))
    (by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_one φ, map_one P.ψ, map_one (finE V)]; exact one_mem _
      · rw [map_one φ, map_one P.ψ, map_one (finE V), rTup_one, map_one])
    (fun a x b y hx hy => by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V)]; exact mul_mem hx.2.1 hy.2.1
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V), rTup_mul hx.2.1 hy.2.1, hx.2.2, hy.2.2, map_mul])
    hl
  apply Subtype.ext
  rw [asAlgebraHom_eq_sum ρ (eG.trans cG).toEquiv, Submodule.coe_sum]
  apply MultilinearMap.ext
  intro v
  funext h
  have h1 : (∑ g : G, c g • actL V β L (eG g)) (Tm v) h = Tm v h :=
    congrFun (congrArg (fun U : Mult.MMap M => U v) hfix) h
  rw [LinearMap.sum_apply, Finset.sum_apply] at h1
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) h1
  obtain ⟨x, hx, hx'⟩ := key (cG (eG g))
  rw [MulEquiv.symm_apply_apply] at hx
  have h2 := level_action_spec (hty v) ⟨_, hx⟩ _ hx h
  rw [levChi_flag hs hQ, inv_one, one_mul] at h2
  have e1 : (eG.trans cG).toEquiv g = cG (eG g) := rfl
  rw [e1, hc, Submodule.coe_smul, hx']
  exact congrArg (c g * ·) h2.symm

theorem good_idem_fix_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∀ (c : GAf D.host.E D.R.r), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) → ∀ (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom))), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) = ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) x z) → ∀ (b : Bool) (Tm : Mult.MMap (R.MY 0)) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)), Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 → ρ.asAlgebraHom D.ntypes.e0 ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s j _ _ c hc ρ hρ b Tm hK hT
  obtain ⟨-, -, -, hco, -, -⟩ := hP.keep.grp
  exact fix_of_lifts_comp Y.PY (R.MY 0) (R.βY 0) (R.dat0 R.triv) rfl rfl (MulAut.conj c).toMonoidHom ρ hρ R.eG
    (RealDat.eC (A := A3.A) D.what₂.embLL) cG D.ntypes.e0 (fun g => (hco g).symm) hc Tm hK
    (fun v => hasType_rows R.toLevCh R.θ (R.MY 0) _ hT.1 v) (sub_eq_zero.1 (LinearMap.mem_ker.1 hT.2))

end GlobalTheory.RowGood

end
