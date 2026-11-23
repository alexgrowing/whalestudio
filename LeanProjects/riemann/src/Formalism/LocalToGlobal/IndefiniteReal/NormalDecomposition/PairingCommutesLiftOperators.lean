import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Formalism.LocalToGlobal.IndefiniteReal.MajAtEqZeroOfMemQpOfNe

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.U2

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR.Cx Formalism.IndefR.CxPass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section Lemmas

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

theorem lift_operators_embedding (hK : X.KFormL) (j : Fin m) (i : (A3.liftI j A3.A.fam.μ0).OpIx) (x : A3.fam3.amb3.FL j A3.A.fam.μ0) :
    liftHeckeOperators A3 X j i (X.jL j A3.A.fam.μ0 x) = X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i x) :=
  (X.jL_opL hK j A3.A.fam.μ0 (Sum.inl i) x).symm

theorem ext_jL (hK : X.KFormL) (j : Fin m) {f g : Module.End ℂ (X.FLC j A3.A.fam.μ0)}
    (h : ∀ x, f (X.jL j A3.A.fam.μ0 x) = g (X.jL j A3.A.fam.μ0 x)) : f = g :=
  (Basis.mk (hK j A3.A.fam.μ0).1 (hK j A3.A.fam.μ0).2.ge).ext fun k => by
    simp only [Basis.mk_apply]; exact h _

theorem pairing_commutes_lift_operators {s : ℕ} (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (j : Fin m) : PairCommF (liftHeckeOperators A3 X j) := by
  intro i i'
  refine ext_jL hK j fun x => ?_
  have hc : Commute ((A3.liftI j A3.A.fam.μ0).opAll i) ((A3.liftI j A3.A.fam.μ0).opAll i') :=
    (hok.lifts j A3.A.fam.μ0).comm i i'
  have e : (A3.liftI j A3.A.fam.μ0).opAll i ((A3.liftI j A3.A.fam.μ0).opAll i' x) =
      (A3.liftI j A3.A.fam.μ0).opAll i' ((A3.liftI j A3.A.fam.μ0).opAll i x) := LinearMap.congr_fun hc.eq x
  show liftHeckeOperators A3 X j i (liftHeckeOperators A3 X j i' (X.jL j A3.A.fam.μ0 x)) = liftHeckeOperators A3 X j i' (liftHeckeOperators A3 X j i (X.jL j A3.A.fam.μ0 x))
  calc liftHeckeOperators A3 X j i (liftHeckeOperators A3 X j i' (X.jL j A3.A.fam.μ0 x))
      = liftHeckeOperators A3 X j i (X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i' x)) :=
        congrArg _ (lift_operators_embedding hK j i' x)
    _ = X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i ((A3.liftI j A3.A.fam.μ0).opAll i' x)) :=
        lift_operators_embedding hK j i _
    _ = X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i' ((A3.liftI j A3.A.fam.μ0).opAll i x)) := congrArg _ e
    _ = liftHeckeOperators A3 X j i' (X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i x)) := (lift_operators_embedding hK j i' _).symm
    _ = liftHeckeOperators A3 X j i' (liftHeckeOperators A3 X j i (X.jL j A3.A.fam.μ0 x)) := congrArg _ (lift_operators_embedding hK j i x).symm

theorem adjoint_closed_lift_operators (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) (hK : X.KFormL)
    {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (j : Fin m) : AdjClosed (liftHeckeOperators A3 X j) := by
  intro i
  rcases i with p | k
  · obtain ⟨p', hp'⟩ := (hH j A3.A.fam.μ0).1.adj p
    exact ⟨Sum.inl p', X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j A3.A.fam.μ0 (Sum.inl (Sum.inl p))
      (Sum.inl (Sum.inl p')) fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH j A3.A.fam.μ0).2.adj k
    exact ⟨Sum.inr k', X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j A3.A.fam.μ0 (Sum.inl (Sum.inr k))
      (Sum.inl (Sum.inr k')) fun f f' => hk' f f'⟩

theorem opAll_goodR {s : ℕ} (hok : A3.fam3.Ok3 s) (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)
    (j : Fin m) (ℓ : Lvl K G) (hℓ : ℓ.X = A3.A.fam.X) (i : (A3.liftI j A3.A.fam.μ0).OpIx)
    {f : A3.fam3.amb3.FL j A3.A.fam.μ0} (hf : f ∈ BlockGood.goodR (A3.A.fam.L j A3.A.fam.μ0) ℓ) :
    (A3.liftI j A3.A.fam.μ0).opAll i f ∈ BlockGood.goodR (A3.A.fam.L j A3.A.fam.μ0) ℓ := by
  obtain ⟨y, rfl⟩ := hf
  have hO := okOp_opAll (hok.ok2.lifts j A3.A.fam.μ0) (hok.lifts j A3.A.fam.μ0) (hH j A3.A.fam.μ0).1
    (hH j A3.A.fam.μ0).2
  have hB : BlockHyp (A3.A.fam.L j A3.A.fam.μ0) ℓ A3.A.fam.v0 s :=
    ⟨hok.ok2.conj, hℓ ▸ hok.ok2.irr, hok.ok2.lifts j A3.A.fam.μ0⟩
  refine ⟨Matrix.mulVec (GroupActionMatrices.tVg (A3.A.fam.L j A3.A.fam.μ0) ℓ (A3.liftI j A3.A.fam.μ0).opAll i) y, ?_⟩
  apply (A3.A.fam.L j A3.A.fam.μ0).S.basis.equivFun.injective
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply]
  rw [GroupActionMatrices.equivFun_oM, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M y) (GroupActionMatrices.vE_tVg hB hO i)

theorem goodL_stable {s : ℕ} (hok : A3.fam3.Ok3 s) (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)
    (hK : X.KFormL) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (j : Fin m) :
    ∀ i, ∀ x ∈ goodL A3 X P0 ψ0 P1 ψ1 j, liftHeckeOperators A3 X j i x ∈ goodL A3 X P0 ψ0 P1 ψ1 j := by
  intro i x hx
  unfold goodL CxData.goodPartComplexPoints at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    rw [lift_operators_embedding hK]
    exact Submodule.subset_span ⟨_, opAll_goodR hok hH j _ rfl i hf, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Lemmas

theorem eigCOf : @EigCOfStatement K _ _ _ G _ _ Pl0 I0 Ty T m := by
  intro A3 X s P0 ψ0 P1 ψ1 Dc Sp Zsc hW gW hDec hok hK hJ hRZ hH hTh hU hG hL0 hO j
  have hD : OrthDecomp (liftHeckeOperators A3 X j) (goodL A3 X P0 ψ0 P1 ψ1 j) (IxL A3 X P0 ψ0 P1 ψ1 j) :=
    hDec _ _ (liftHeckeOperators A3 X j) (goodL A3 X P0 ψ0 P1 ψ1 j) (pairing_commutes_lift_operators hok hK j)
      (adjoint_closed_lift_operators hH hK hJ j) (goodL_stable hok hH hK P0 ψ0 P1 ψ1 j)
  have hDn : X.DnLevL (cvOf3 A3 P0 ψ0 P1 ψ1) false :=
    lift_descent_at_lower_type (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK hJ hRZ hU hG hL0
  have hGI : GoodIn (X.θ' j A3.A.fam.μ0) (goodL A3 X P0 ψ0 P1 ψ1 j) (goodW A3 X j) :=
    fun x hx => hDn j A3.A.fam.μ0 ⟨x, hx, rfl⟩
  exact liftsFull_adj hD (fun i x => hTh.intw j A3.A.fam.μ0 i x) hGI (hO j)

theorem sys_of_occ {I V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {op : I → Module.End ℂ V}
    (hc : Formalism.L2.Col.PairComm op) {S : (I → ℂ) → Prop} {W : Submodule ℂ V} (hW : W ≤ Formalism.L2.Col.eigSum op S)
    {c : I → ℂ} {w : V} (hw : ∀ i, op i w = c i • w) (hwW : w ∈ W) (hw0 : w ≠ 0) : S c := by
  by_contra hn
  have hdis := Formalism.L2.Col.disjoint_eigSum hc (C := fun c' => c' = c) (C' := S) (fun c' hc' hSc => hn (hc' ▸ hSc))
  exact hw0 ((Submodule.disjoint_def.mp hdis) w
    (Formalism.L2.Col.eigAt_le_eigSum (C := fun c' => c' = c) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hw)) (hW hwW))

theorem typ0Of : @ZeroTypeCondition K _ _ _ G _ _ Pl0 I0 Ty T m := by
  intro A3 X P0 ψ0 P1 ψ1 hW hTh hPW j x hx
  have hne : eigPart (hW j A3.A.fam.μ0) (fun i => A3.A.fam.v0.embedding (x i)) ⊓ goodW A3 X j ≠ ⊥ := hx.2
  obtain ⟨w, hwm, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle : goodW A3 X j ≤ Formalism.L2.Col.eigSum (hW j A3.A.fam.μ0) (fun c => ∃ p : A3.fam3.base3.Ix,
      cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) c) := by
    unfold goodW
    rw [← (hPW j).2]
    refine iSup_le fun p => inf_le_left.trans ?_
    rw [hTh.parts j p]
    exact Formalism.L2.Col.eigSum_mono fun c hc => ⟨p, hc⟩
  obtain ⟨p, y, hy, hyx⟩ := sys_of_occ (hTh.comm j) hle (mem_eigPart.mp (Submodule.mem_inf.mp hwm).1)
    (Submodule.mem_inf.mp hwm).2 hw0
  have hyx' : y = x := funext fun i => A3.A.fam.v0.embedding.injective (congrFun hyx i).symm
  subst hyx'
  exact ⟨p.1, p.2, hy⟩

theorem good_inf_eigSum_le {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    {op : I → Module.End ℂ A} (hc : Formalism.L2.Col.PairComm op) {good : Submodule ℂ A} {Ix : Set (I → ℂ)}
    (hD : OrthDecomp op good Ix) (S : (I → ℂ) → Prop) :
    good ⊓ Formalism.L2.Col.eigSum op S ≤ ⨆ c ∈ {c | c ∈ Ix ∧ S c}, eigPart op c ⊓ good := by
  rintro x ⟨hxg, hxS⟩
  have hpart : ∀ (T : (I → ℂ) → Prop) c, T c → eigPart op c ⊓ good ≤ Formalism.L2.Col.eigSum op T :=
    fun T c hc' y hy => Formalism.L2.Col.eigAt_le_eigSum hc' (Formalism.L2.Col.mem_eigAt_of_forall_apply (mem_eigPart.mp hy.1))
  have hL : (⨆ c ∈ {c | c ∈ Ix ∧ S c}, eigPart op c ⊓ good) ≤ Formalism.L2.Col.eigSum op S :=
    iSup₂_le fun c hc' => hpart S c hc'.2
  have hM : (⨆ c ∈ {c | c ∈ Ix ∧ ¬ S c}, eigPart op c ⊓ good) ≤ Formalism.L2.Col.eigSum op (fun c => ¬ S c) :=
    iSup₂_le fun c hc' => hpart _ c hc'.2
  have hsplit : good ≤ (⨆ c ∈ {c | c ∈ Ix ∧ S c}, eigPart op c ⊓ good) ⊔
      (⨆ c ∈ {c | c ∈ Ix ∧ ¬ S c}, eigPart op c ⊓ good) := by
    refine hD.span.trans (iSup₂_le fun c hc' => ?_)
    by_cases h : S c
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun c (_ : c ∈ {c | c ∈ Ix ∧ S c}) => eigPart op c ⊓ good) c ⟨hc', h⟩ le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun c (_ : c ∈ {c | c ∈ Ix ∧ ¬ S c}) => eigPart op c ⊓ good) c ⟨hc', h⟩ le_rfl)
  obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp (hsplit hxg)
  have hm1 : m ∈ Formalism.L2.Col.eigSum op S := by
    have e : m = (l + m) - l := by abel
    rw [e]; exact Submodule.sub_mem _ hxS (hL hl)
  have hdis := Formalism.L2.Col.disjoint_eigSum hc (C := S) (C' := fun c => ¬ S c) (fun c h h' => h' h)
  have hm0 : m = 0 := (Submodule.disjoint_def.mp hdis) m hm1 (hM hm)
  rw [hm0, add_zero]; exact hl

theorem eig0Of : @ZeroEigenvalueCondition K _ _ _ G _ _ Pl0 I0 Ty T m := by
  intro A3 X s P0 ψ0 P1 ψ1 hW hDec hok hK hJ hH hE j
  have hO : GroupActionMatrices.OkOp (A3.A.fam.L j A3.A.fam.μ0) (A3.liftI j A3.A.fam.μ0).opAll :=
    okOp_opAll (hok.ok2.lifts j A3.A.fam.μ0) (hok.lifts j A3.A.fam.μ0) (hH j A3.A.fam.μ0).1 (hH j A3.A.fam.μ0).2
  have : FiniteDimensional K (A3.fam3.amb3.FL j A3.A.fam.μ0) :=
    Module.Finite.of_basis (A3.A.fam.L j A3.A.fam.μ0).S.basis
  have hinj : Function.Injective (X.jL j A3.A.fam.μ0) :=
    inj_of_li (CxData.bL (A := A3.fam3.amb3) j A3.A.fam.μ0) (X.jL j A3.A.fam.μ0) (hK j A3.A.fam.μ0).1
  have hf : ∀ i v, X.jL j A3.A.fam.μ0 ((A3.liftI j A3.A.fam.μ0).opAll i v) = liftHeckeOperators A3 X j i (X.jL j A3.A.fam.μ0 v) :=
    fun i v => (lift_operators_embedding hK j i v).symm
  have hc3 : Formalism.L2.Col.PairComm (liftHeckeOperators A3 X j) := pairing_commutes_lift_operators hok hK j
  have hD : OrthDecomp (liftHeckeOperators A3 X j) (goodL A3 X P0 ψ0 P1 ψ1 j) (IxL A3 X P0 ψ0 P1 ψ1 j) :=
    hDec _ _ (liftHeckeOperators A3 X j) (goodL A3 X P0 ψ0 P1 ψ1 j) hc3 (adjoint_closed_lift_operators hH hK hJ j)
      (goodL_stable hok hH hK P0 ψ0 P1 ψ1 j)
  have hCL : ∀ c, cxSys A3.A.fam.v0.embedding (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j) c →
      c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j := by
    rintro c ⟨x, hx, rfl⟩; exact hx
  have hEq : ∀ c, eigPart (liftHeckeOperators A3 X j) c ⊓ goodL A3 X P0 ψ0 P1 ψ1 j ≤
      Formalism.L2.Col.eigAt (liftHeckeOperators A3 X j) c :=
    fun c y hy => Formalism.L2.Col.mem_eigAt_of_forall_apply (mem_eigPart.mp hy.1)
  have key : ∀ f ∈ BlockGood.goodR (A3.A.fam.L j A3.A.fam.μ0) (A3.A.fam.lvlA P0 ψ0),
      f ∈ X.Zl j A3.A.fam.μ0 ↔ f ∈ Formalism.L2.Col.eigSum (A3.liftI j A3.A.fam.μ0).opAll (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j) := by
    intro f hfg
    have hjg : X.jL j A3.A.fam.μ0 f ∈ goodL A3 X P0 ψ0 P1 ψ1 j := Submodule.subset_span ⟨f, hfg, rfl⟩
    have hZl : f ∈ X.Zl j A3.A.fam.μ0 ↔ X.jL j A3.A.fam.μ0 f ∈ (LinearMap.ker (X.θ' j A3.A.fam.μ0))ᗮ := by
      rw [LinearMap.orthogonal_ker]; rfl
    rw [hZl]
    have hLle : (⨆ c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j, eigPart (liftHeckeOperators A3 X j) c ⊓ goodL A3 X P0 ψ0 P1 ψ1 j) ≤
        Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (fun c => c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j) :=
      iSup₂_le fun c hc' => (hEq c).trans (Formalism.L2.Col.eigAt_le_eigSum hc')
    constructor
    · intro hk
      have h2 : X.jL j A3.A.fam.μ0 f ∈ (LinearMap.ker (X.θ' j A3.A.fam.μ0))ᗮ ⊓ goodL A3 X P0 ψ0 P1 ψ1 j := ⟨hk, hjg⟩
      rw [hE j] at h2
      have h1 := hLle h2
      have hq1 : X.jL j A3.A.fam.μ0 (f - Formalism.L2.Col.eigProj hO.comm hO.split (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j) f) ∈
          Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (cxSys A3.A.fam.v0.embedding fun x => ¬ eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j x) :=
        eigSum_le_comap_semi (X.jL j A3.A.fam.μ0) hf _ (Formalism.L2.Col.sub_eigProj_mem hO.comm hO.split _ f)
      have hq2 : X.jL j A3.A.fam.μ0 (f - Formalism.L2.Col.eigProj hO.comm hO.split (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j) f) ∈
          Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (fun c => c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j) := by
        have hs := Submodule.sub_mem _ h1 (Formalism.L2.Col.eigSum_mono hCL
          (eigSum_le_comap_semi (X.jL j A3.A.fam.μ0) hf _ (Formalism.L2.Col.eigProj_apply_mem hO.comm hO.split _ f)))
        convert hs using 1
        exact map_sub _ _ _
      have hd : Disjoint (Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (fun c => c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j))
          (Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (cxSys A3.A.fam.v0.embedding fun x => ¬ eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j x)) :=
        Formalism.L2.Col.disjoint_eigSum hc3 (by rintro c hcL ⟨x, hx, rfl⟩; exact hx hcL)
      have h0 := (Submodule.disjoint_def.mp hd) _ hq2 hq1
      have h00 : f - Formalism.L2.Col.eigProj hO.comm hO.split (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW j) f = 0 :=
        hinj (h0.trans (map_zero _).symm)
      rw [sub_eq_zero] at h00
      rw [h00]
      exact Formalism.L2.Col.eigProj_apply_mem hO.comm hO.split _ f
    · intro hC
      have h1 : X.jL j A3.A.fam.μ0 f ∈ Formalism.L2.Col.eigSum (liftHeckeOperators A3 X j) (fun c => c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j) :=
        Formalism.L2.Col.eigSum_mono hCL (eigSum_le_comap_semi (X.jL j A3.A.fam.μ0) hf _ hC)
      have h2 := good_inf_eigSum_le hc3 hD (fun c => c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j) ⟨hjg, h1⟩
      have hle : (⨆ c ∈ {c | c ∈ IxL A3 X P0 ψ0 P1 ψ1 j ∧ c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j},
          eigPart (liftHeckeOperators A3 X j) c ⊓ goodL A3 X P0 ψ0 P1 ψ1 j) ≤
          (LinearMap.ker (X.θ' j A3.A.fam.μ0))ᗮ ⊓ goodL A3 X P0 ψ0 P1 ψ1 j := by
        rw [hE j]
        exact iSup₂_le fun c hc' => le_iSup₂_of_le
          (f := fun c (_ : c ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j) => eigPart (liftHeckeOperators A3 X j) c ⊓ goodL A3 X P0 ψ0 P1 ψ1 j)
          c hc'.2 le_rfl
      exact (hle h2).1
  ext u
  exact ((BlockDat.mem_goodPart_iff (A3.A.fam.L j A3.A.fam.μ0) (A3.A.fam.lvlA P0 ψ0) (X.Zl j A3.A.fam.μ0) u).trans
    (key _ ⟨u, rfl⟩)).trans (BlockDat.mem_goodPart_iff (A3.A.fam.L j A3.A.fam.μ0) (A3.A.fam.lvlA P0 ψ0) _ u).symm

end Formalism.IndefR.U2
