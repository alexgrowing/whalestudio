import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PublishedInputsThirdLayer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlaceStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.PlaceRead.TupAt
section General
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.SeriesTie Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {D : D7}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
end General
section State
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P)
end State
theorem local_tuple_at_state : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  intro _ hL
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values)
  refine s1.trans (Step.of_all ?_)
  intro K B f T _ _ _ hOk w _ P x l ch tp _ hpsi _ _ side v hv hok
  have hV : ValsIn w.I := (hOk w.px w.I P.hX w.ok w.C_eq w.xi_range).1
  clear hOk s1
  have hψ : IsPsi ((Dof x).ntw.l (ch.twI v)) (ch.Q v) (tp.psi v) := by
    have h := tp.psi_is v hv
    rw [← ch.twI_l v] at h
    exact h
  have he : tp.psi v = T.psi v := congrFun hpsi v
  have ht := xi_mu x ch hv he
  have hr := fun PP => ram_mul x.m.z.R.C (ch.twI v) hψ PP
  rw [← ht] at hr
  refine ⟨fun PP hP => ?_, fun j ι hι => ?_⟩
  · obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP fun hu => (hψ.ram PP).1 (he ▸ hu :) hP
    exact splitK_of_prime (D := Dof x) PP h1 fun hd => h2 (Or.inl hd)
  · rw [tupT_muTw x hv]
    refine isTupOf x.m.z.lev.is l.b.ser.ex.good l.b.ser.ex.pin _ j _ hψ ht (fun PP hP => ?_) _ ?_ rfl
    · have hs : IsSplitPl (Dof x).host PP := by
        rcases (hr PP).1 ((x.m.z.lev.is.Q_ram _ PP).2 (Or.inl hP)) with h | h
        · obtain ⟨q, -, hq, e⟩ := isDelta_delAt x.m.z.R.C (ch.twI v)
          have h' := (hq PP).1 h
          refine l.a.elem.split PP (e.imp (fun e => ?_) fun e => ?_) <;> subst e <;> exact h'
        · exact hψ.split PP h
      refine (l.b.ser.ch _ PP hs).2 ?_
      obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 ((x.m.z.lev.Q _).le hP)
      exact l.sel.ge ⟨u, e⟩
    · refine chrEq_twVia side.psi hv hok l.b.ser.ex.good (fun PP h1 h2 => ?_) ι hι
      have hval : ValLL0 (Dof x) x.m.z.R.C := by rw [x.m.z.lev.C]; exact l.a.val
      obtain ⟨y, hy⟩ := val_delAt hval _ PP h2
      have hx := x.m.z.lev.xiH (x.m.z.R.mu ((Dof x).plEq v))
      obtain ⟨z, hz⟩ := hV.1 _ PP (hx ▸ not_not.1 fun hu => ((hr PP).1 hu).elim h2 h1 :)
      have hz' : (Dof x).what₂.embLL z = (((x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * tp.psi v).val PP : ℂˣ) : ℂ) :=
        hz.trans (congrArg (fun χ : HChar (Dof x).host.E => ((χ.val PP : ℂˣ) : ℂ)) (hx.symm.trans ht))
      refine ⟨y⁻¹ * (show (Dof x).what₂.LL from z), ?_⟩
      rw [map_mul, map_inv₀, hy]
      refine (congrArg _ hz').trans ?_
      rw [HChar.val_mul, Units.val_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]
end GlobalTheory.PlaceRead.TupAt
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_tuple_at_state : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  first | exact @_root_.GlobalTheory.PlaceRead.TupAt.local_tuple_at_state | exact _root_.GlobalTheory.PlaceRead.TupAt.local_tuple_at_state | (intros; apply _root_.GlobalTheory.PlaceRead.TupAt.local_tuple_at_state <;> assumption)
end
