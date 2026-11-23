import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EventuallyMemHeckeLevelAndIwahoriCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

private theorem fixOf {L : Type} [Field L] [NumberField L] [IsCMField L] (hU : GlobalTheory.BCT.Unr L) {n : ℕ} (hn : 1 ≤ n)
    {S : Set (GlobalTheory.BCT.Pl L)} (hS : GlobalTheory.BCT.IsSection S) {lam : InfinitePlace L → DomWeight n}
    {K' : ∀ w : GlobalTheory.BCT.Pl L, Subgroup (GlobalTheory.BCT.UL n w)}
    (hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) K')
    (π : Submodule ℂ (UA L n → ℂ)) (h1 : IsAutRepU π) (h2 : ∀ v, HasWeightAt π v.embedding (lam v))
    (h3 : π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev S K') ≠ ⊥) (w : GlobalTheory.BCT.Pl L) (hw : w ∈ S)
    (hs : IsSplitAt w) (τ : SmIrr (GLw n w)) (hc : Cp π w τ) :
    GlobalTheory.PRep.fixed (τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype) (K' w) ≠ ⊥ := by
  have hUL : GlobalTheory.BCT.UL n w = ⊤ := if_pos hs
  have hsurj : Function.Surjective (GlobalTheory.BCT.UL n w).subtype := fun g =>
    ⟨⟨g, hUL ▸ Subgroup.mem_top g⟩, rfl⟩
  let σ₁ : SmIrr (GlobalTheory.BCT.UL n w) :=
    { V := τ.V
      ρ := τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype
      smooth := fun v => (τ.smooth v).preimage continuous_subtype_val
      irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective τ.ρ _ hsurj τ.irred }
  obtain ⟨-, f, hf0, hfm, hf⟩ := hc
  let p : locU n w →* GlobalTheory.BCT.UL n w :=
    ((cLoc w).comp (locU n w).subtype).codRestrict (GlobalTheory.BCT.UL n w) fun x => hUL ▸ Subgroup.mem_top _
  exact GlobalTheory.T.localComponent_levelFixedVectors_ne_bot L hU n hn S hS lam K' hLev π h1 h2 h3 w hw σ₁
    ⟨p, fun x => rfl, σ₁.irred, f, hf0, hfm, fun x v => hf x v⟩

section Tf

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

private def tfOf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
    Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])

private theorem yEq {c : Coef l} {m : ℕ} (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ' : Submodule ℂ (UA L n → ℂ)) :
    (Submodule.pi Set.univ (fun _ => (hset Q τ₀).X.AF ξ) ⊓ fixd ((hset Q τ₀).X.raF d ((hset Q τ₀).τC ι)) (hset Q τ₀).UQ) ⊓
      Submodule.span ℂ {F : Fin (hset Q τ₀).m → (hset Q τ₀).X.Fn ℂ d | ∀ i ℓ, tfOf ι e (F i) ℓ ∈ σ'} = YOf Q ι τ₀ e ξ σ' := rfl

end Tf

private theorem wtY {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ') (hne : YOf Q ι τ₀ e ξ σ' ≠ ⊥) :
    ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual :=
  UpperTheory.V.Hi.partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne

private theorem wtZ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n)
    (lam' : InfinitePlace L → DomWeight n) (hlink : WtLink V ι lam lam')
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ')
    (h : ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual) :
    ∀ v, HasWeightAt σ' v.embedding (lam' v) :=
  (hlink σ' hσ').1 h

private def PwD {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (lam' : InfinitePlace L → DomWeight n)
    (π : Submodule ℂ (UA L n → ℂ)) : Prop := ∀ v, HasWeightAt π v.embedding (lam' v)

private theorem levLe {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) (hQ : IsEmpty Q.Q) {c : Coef l} {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) : (hset Q τ₀).lev K ≤ (hset Q τ₀).UQ := by
  unfold HSet.lev
  refine sup_le le_rfl (iSup_le fun q => ?_)
  exact (hQ.false q).elim

private theorem mainStep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (hτ : IsOpen (τ₀.ker : Set (KT n (wt s)))) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (b : ℕ)
    (hQ : IsEmpty Q.Q)
    (Pw : Submodule ℂ (UA L n → ℂ) → Prop)
    (hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → Pw σ')
    (Kf : Subgroup (finU L n))
    (hKf : ∀ k ∈ Kf, (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧
      τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b)
    {J' : Type} [Fintype J'] (σ : J' → Submodule ℂ (UA L n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) Kf ≤ ⨆ j, σ j) :
    (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) ≤
      ⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) := by
  intro F hF
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, haut, htr, hsurj, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  haveI := e.finiteDimensional
  have hJinf : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hRfin : ∀ k ∈ finU L n, infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    have h2 : (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
        (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (E := L) (n := n) (ι.toRingHom.comp e.res))) k = 1 :=
      funext fun y => by
        change GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb _ k) = 1
        rw [h1, map_one]
    unfold infRep
    rw [MonoidHom.comp_apply, h2, map_one]
  refine Dc.core3 (hset Q τ₀).X ξ ((hset Q τ₀).τC ι) (hset Q τ₀).UQ ((hset Q τ₀).X.I.I1 b) J (tfOf ι e)
    (fun x ℓ => ℓ ∘ₗ infRep ι lam x⁻¹) hJinf (fun k hk ℓ => ?_) hinj haut htr hsurj hsur ?_ Kf (fun k hk => ?_) Pw
    (fun σ' hσ' hne => hwtY σ' hσ' (by rw [← yEq ι e Q τ₀ ξ σ']; exact hne))
    σ hσ hind hcov F hF.1 hF.2
  · rw [hRfin _ ((finU L n).inv_mem hk)]
    rfl
  · filter_upwards [UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence l L Ω s n hn V Q c m τ₀ hτ
      ⟨fun q => (hQ.false q).elim, fun q => (hQ.false q).elim⟩ b] with k ⟨⟨u, hu, huk, hu1⟩, hk⟩
    refine ⟨⟨u, levLe Q hQ τ₀ _ hu, huk, ?_⟩, hk⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]
  · obtain ⟨⟨u, hu, huk, hu1⟩, hk'⟩ := hKf k hk
    refine ⟨⟨u, hu, huk, ?_⟩, hk'⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]

private theorem yIndep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    {J' : Type} (σ : J' → Submodule ℂ (UA L n → ℂ)) (hind : iSupIndep σ) :
    iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) := by
  obtain ⟨hinj, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ
    (MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))) (fun _ => rfl)
  let Tt : Fin m × Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →
      (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun t => (LinearMap.applyₗ t.2) ∘ₗ tfOf ι e ∘ₗ LinearMap.proj t.1
  refine Dc.indepOf σ hind _ Tt (fun i y hy t => ?_)
    (fun i y hy h0 => funext fun a => hinj (y a) (hy.1.1 a trivial) fun ℓ => h0 (a, ℓ))
  have hle : Submodule.span ℂ {F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ |
      ∀ a ℓ, toForm ι e (F a) ℓ ∈ σ i} ≤ (σ i).comap (Tt t) := Submodule.span_le.2 fun F hF => hF t.1 t.2
  exact hle hy.2

set_option Elab.async false in
theorem UpperTheory.V.Z.J.D.decomp :
    IndepS → Decomp := by
  intro hI l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ hτ lam' hlink b
  have hU := Dc.unrOf s
  obtain ⟨c0, hc0⟩ := Dc.exC (n := n) (s := s) τ₀ hτ
  have hcc := hc0 (c0 + b + 1) (by omega)
  have hfin : s.S.Finite := hV ▸ V.fin
  have hS := Dc.secRange s
  have hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n)
      (Dc.Kf s n (c0 + b + 1)) := Dc.levFam hfin
  obtain ⟨-, J', hJ', σ, hσ, hind, hsup, -⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors L hU n hn _ hS lam' _ hLev
  have hdec : IsDec (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) σ := ⟨hσ, hind, hsup⟩
  have hσind := hI L n _ hS lam' _ hLev J' σ hdec
  refine ⟨Set.range s.w, Dc.Kf s n (c0 + b + 1), J', hJ', σ, hS, hLev, fun w hw => Dc.Kf_notS hw, hdec,
    yIndep s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσind,
    fun i w hw => Dc.unramOf hU _ (hσ i).2.2 w hw,
    fun i w hw hs τ hc => fixOf hU hn hS hLev (σ i) (hσ i).1 (hσ i).2.1 (hσ i).2.2 w hw hs τ hc, ?_⟩
  have hQ := Dc.Q_empty hV Q
  have hgood : ∀ k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)),
      (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧
        (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := fun k hk =>
    Dc.goodOf hV Q τ₀ b hcc (by omega) (by omega) hU k hk
  have hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → PwD lam' σ' := fun σ' hσ' hne =>
    wtZ V ι lam lam' hlink σ' hσ' (wtY s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne)
  have hcov : ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → PwD lam' π →
      π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) ≤ ⨆ j, σ j := by
    intro π hπ hP φ hφ
    have h1 : φ ∈ GlobalTheory.BCT.forms (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) :=
      (le_iSup₂_of_le (f := fun (π : Submodule ℂ (UA L n → ℂ))
        (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam' v)) =>
          π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))))
        π ⟨hπ, hP⟩ le_rfl) hφ
    rw [← hsup] at h1
    have h2 : (⨆ i, σ i ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)))) ≤ ⨆ j, σ j :=
      iSup_mono fun i => inf_le_left
    exact h2 h1
  exact mainStep s n hn V Q c ι m τ₀ hτ lam d e ξ hξ b hQ
    (PwD lam') hwtY
    (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) hgood σ (fun j => (hσ j).1) hσind hcov
