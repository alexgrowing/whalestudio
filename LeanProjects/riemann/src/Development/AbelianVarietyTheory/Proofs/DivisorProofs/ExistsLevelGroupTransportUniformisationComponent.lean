import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItselfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMulStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_transport : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, hex⟩ := GlobalTheory.T.exists_levelChange_transporters_all_components p hp r h hr i v
  have uniq := GlobalTheory.T.unique_up_to_target_group p hp r h hr i v ψ
  have one := GlobalTheory.T.identity_transports_component_to_itself p hp r h hr i v ψ
  have comp := GlobalTheory.T.isLevelComponentTransport_comp p hp r h hr i v ψ
  have gam := GlobalTheory.T.isTransport_identity_of_mem_componentGroup p hp r h hr i v ψ
  obtain ⟨lmul, linj⟩ := GlobalTheory.T.levelAction_mul_and_faithful_finiteGroup p hp r h hr i
  have c8 := GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul p hp r h hr i v ψ
  choose act tr htr using fun (g : p.P.Gp) k => hex (r.lev i g⁻¹) k
  have lev1 : r.lev i 1 = 1 := by
    have e := lmul 1 1
    rw [mul_one] at e
    exact (mul_eq_left.1 e.symm)
  have levinv : ∀ g, r.lev i g⁻¹ = (r.lev i g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← lmul, inv_mul_cancel, lev1])
  have levmul : ∀ g g', r.lev i (g * g')⁻¹ = r.lev i g'⁻¹ * r.lev i g⁻¹ := fun g g' => by
    rw [mul_inv_rev, lmul]
  have hco : ∀ g g' k, IsTransp p r i v ψ (r.lev i (g * g')⁻¹) k (act g (act g' k)) (tr g (act g' k) * tr g' k) :=
    fun g g' k => by
      rw [levmul]
      exact comp _ _ _ _ _ _ _ (htr g' k) (htr g (act g' k))
  refine ⟨act, tr, fun k => ?_, fun g g' k => ?_, fun g k => (htr g k).1, fun g k γ => ?_, fun g g' k => ?_,
    fun g k hk hΓ => ?_, ⟨fun g k => (c8 _ _ _ _ (htr g k)).choose, fun F g k x hx h2 =>
      (c8 _ _ _ _ (htr g k)).choose_spec F x hx h2⟩, fun Lf hLf => ?_⟩
  · have e := htr 1 k
    rw [inv_one, lev1] at e
    exact (uniq _ _ _ _ _ _ e (one k)).1
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).1
  · constructor
    · intro hγ
      have e1 := comp _ _ _ _ _ _ _ (gam k γ hγ) (htr g k)
      rw [one_mul] at e1
      have := (uniq _ _ _ _ _ _ e1 (htr g k)).2
      simpa [mul_assoc] using this
    · intro hγ
      obtain ⟨k'', b, hb⟩ := hex (r.lev i g⁻¹)⁻¹ (act g k)
      have e1 := comp _ _ _ _ _ _ _ (htr g k) hb
      rw [mul_inv_cancel] at e1
      obtain ⟨hk'', hb1⟩ := uniq _ _ _ _ _ _ e1 (one k)
      rw [hk''] at hb hb1
      have e2 := comp _ _ _ _ _ _ _ (gam _ _ hγ) hb
      have e3 := comp _ _ _ _ _ _ _ (htr g k) e2
      rw [one_mul, mul_inv_cancel] at e3
      have hb2 := (uniq _ _ _ _ _ _ e3 (one k)).2
      rw [inv_one, mul_one] at hb1 hb2
      have key : γ = (b * tr g k)⁻¹ * (b * (tr g k * γ * (tr g k)⁻¹) * tr g k) := by group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb1) hb2
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).2
  · have e1 := gam k (tr g k) hΓ
    have e2 := htr g k
    rw [hk] at e2
    have e3 := IsTransp.eq_of_eq e2 e1
    have : g⁻¹ = 1 := linj _ e3
    simpa using this
  · have keyg : ∀ g, (r.lev i g⁻¹).symm = r.lev i g ^ (1 : ℤ) := fun g => by
      rw [zpow_one, levinv]
      rfl
    obtain rfl : Lf = fun k => lattice₂ D ((uAt r v i).X k).Λ := funext hLf
    refine ⟨ψ, fun k g hk => ⟨1, fun w => ?_⟩⟩
    beta_reduce at w ⊢
    have e2 := htr g k
    rw [hk] at e2
    obtain ⟨-, -, hm⟩ := e2
    obtain ⟨hw, e⟩ := hm w
    refine ⟨hw, e.trans (congrArg (ψ k) (congrFun (congrArg DFunLike.coe (keyg g)) _))⟩

end GlobalTheory.ShareOn

end
