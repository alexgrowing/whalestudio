import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNormsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop.LComm

variable {D : D7}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a : GA D V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, -, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ?_⟩
  have e2 := congrArg Subtype.val e
  have e3 := congrArg Units.val e2
  exact e3

set_option maxHeartbeats 2000000 in

theorem rdS_inj (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (h : ∀ y, rdS θ V hn S yc ψ y = rdS θ V hn S yc ψ' y) : ψ = ψ' := by
  funext c z
  obtain ⟨g, hg⟩ := exists_finM V hn (yc c)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    refine ⟨(c, 1, 1), Subgroup.one_mem _, ?_⟩
    simp [hg]
  have hp := hex.choose_spec
  have hc : hex.choose.1 = c := by
    apply hbij.1
    refine (DoubleCoset.eq _ _ _ _).mpr ?_
    have hr : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      Subgroup.mem_map.mpr ⟨_, hp.1, rfl⟩
    have hk : hex.choose.2.2.1 ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      ((S.U_eq _).1 hex.choose.2.2.2).1
    have he : (yc c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 * (yc hex.choose.1).1 *
        hex.choose.2.2.1 := Units.ext (hg.symm.trans hp.2)
    have hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      have : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 =
          (yc c).1 * (hex.choose.2.2.1)⁻¹ * ((yc hex.choose.1).1)⁻¹ := by rw [he]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (yc c).2 (Subgroup.inv_mem _ hk)) (Subgroup.inv_mem _ (yc _).2)
    exact ⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.mpr hr, ⟨_, hk⟩, Subgroup.mem_subgroupOf.mpr hex.choose.2.2.2, Subtype.ext he⟩
  set A : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ with hA
  have hAu : ∀ τ, IsUnit (A τ).det := by
    intro τ
    rw [hA, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)
  have hy : ∀ τ, IsUnit ((A τ)⁻¹ * z.1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hAu τ)).mul (z.2 τ)
  have key := congrFun (h ⟨fun τ => (A τ)⁻¹ * z.1 τ, hy⟩) g
  have hz : (fun τ => atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * ((A τ)⁻¹ * z.1 τ)) = z.1 := by
    funext τ
    show A τ * ((A τ)⁻¹ * z.1 τ) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hAu τ), Matrix.one_mul]
  unfold rdS at key
  rw [dif_pos hex, dif_pos hex] at key
  dsimp only at key
  rw [hz, atFr, atFr, dif_pos z.2, dif_pos z.2, hc] at key
  exact mul_left_cancel₀ (Units.ne_zero _) key

theorem chart0_inj {u : D.what₂.Word} (F : Forms0 D u) (θ : InfFam D) (ψ ψ' : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (h : ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ ψ y = (GlobalTheory.Core.Mi.chart0 F).rd θ ψ' y) : ψ = ψ' := by
  have := rdS_inj θ (D.sp.X 0) (rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij
    (fun c z => ψ c (F.val0.eY.symm z)) (fun c z => ψ' c (F.val0.eY.symm z)) (fun y => by
      have := h (F.val0.eY.symm y)
      unfold Chart.rd at this
      rw [show (GlobalTheory.Core.Mi.chart0 F).eY (F.val0.eY.symm y) = y from F.val0.eY.apply_symm_apply y] at this
      exact this)
  funext c y
  have h2 := congrFun (congrFun this c) (F.val0.eY y)
  simpa using h2

theorem iter_equiv {M β : Type} [NormedAddCommGroup M] [Module ℂ M] (S : β → M ≃ₗ[ℂ] M) (r : β → ℝ) (hr : ∀ b, 0 < r b)
    (hS : ∀ b φ, ‖S b φ‖ = r b * ‖φ‖) (ε : ℕ → β) (n : ℕ) :
    ∃ (A : M ≃ₗ[ℂ] M) (a : ℝ), 0 < a ∧ (∀ φ, ‖A φ‖ = a * ‖φ‖) ∧ ∀ φ, A φ = GlobalTheory.SeeSaw.iterS (fun b => S b) ε n φ := by
  induction n with
  | zero => exact ⟨LinearEquiv.refl ℂ M, 1, one_pos, fun φ => by simp, fun φ => rfl⟩
  | succ n ih =>
    obtain ⟨A, a, ha, h1, h2⟩ := ih
    refine ⟨A.trans (S (ε (2 * n))), r (ε (2 * n)) * a, mul_pos (hr _) ha, fun φ => ?_, fun φ => ?_⟩
    · rw [LinearEquiv.trans_apply, hS, h1, mul_assoc]
    · rw [LinearEquiv.trans_apply, h2]; rfl

theorem iterS_comm {α α' β : Type} (S : β → α → α) (S' : β → α' → α') (j : α → α') (h : ∀ b x, S' b (j x) = j (S b x))
    (ε : ℕ → β) (n : ℕ) (x : α) : GlobalTheory.SeeSaw.iterS S' ε n (j x) = j (GlobalTheory.SeeSaw.iterS S ε n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show S' _ (GlobalTheory.SeeSaw.iterS S' ε n (j x)) = j (S _ (GlobalTheory.SeeSaw.iterS S ε n x))
    rw [ih, h]

end GlobalTheory.MiTop.LComm
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MiTop.linkComm_of_laws : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), ∀ u (f : FamCh W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, col0 f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (col0 f t φ) y = (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = col0 f t φ) → LinkComm f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f k _ _ _ _ ι o ε S₀ hU hc ht hnd _ hinj hne h0 hsur n h
  have hall : ∀ η : ι → 𝓀[k]ˣ, ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧
      ∀ φ y, (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u (S φ)).1 y =
        o.S (fun _ => η) 0 ((chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) := by
    intro η
    obtain ⟨α⟩ := hne W.P.A3.A.μ0
    have hR := (ht W.P.A3.A.μ0).2.2.2.2
    refine GlobalTheory.T.levelPrime_operators_stepZero_scale_norms D u (F0 W u) W.Q.Rl.θ hc.inf hU (hc.x 0 (Nat.zero_le _)).cpt k ι o.p o.I o.q o.χ o.hχ (o.β 0) (o.Q 0)
      hnd hinj (fun φ y i => ?_) η (fun φ => ?_)
    · have := (hR.ram 0 (Nat.zero_le _) _ (h0 _ φ).1 α y).2 i
      rw [(h0 _ φ).2 α y] at this
      exact this
    · obtain ⟨h1, h2⟩ := hR.S₀ η _ (h0 _ φ).1
      obtain ⟨φ', e⟩ := hsur _ _ h1
      refine ⟨φ', fun y => ?_⟩
      have := h2 α y
      rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
      exact this
  choose S r hr hS hrd using hall
  have hS0 : ∀ t η φ, S₀ t η (col0 f t φ) = col0 f t (S η φ) := by
    intro t η φ
    obtain ⟨α⟩ := hne t
    obtain ⟨h1, h2⟩ := (ht t).2.2.2.2.S₀ η _ (h0 t φ).1
    obtain ⟨φ', e⟩ := hsur _ _ h1
    rw [e]
    congr 1
    apply (D.eMu u).injective
    apply Subtype.ext
    refine LComm.chart0_inj (F0 W u) W.Q.Rl.θ _ _ (fun y => ?_)
    have := h2 α y
    rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
    rw [this, hrd]
  obtain ⟨A, a, ha, hA, hA'⟩ := LComm.iter_equiv S r hr hS ε n
  refine ⟨A, a, o.cS n, ha, hA, ?_, fun t φ F => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ ?_
    refine Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne'
    exact Nat.cast_pos.2 Nat.card_pos
  · obtain ⟨t1, t2, t3, t4, t5⟩ := ht t
    rw [GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero D f.c k ι o (f.t t) ε (S₀ t) t1 t2 t3 t4 t5 n h _ (h0 t φ).1 F,
      LComm.iterS_comm (fun η φ => S η φ) (S₀ t) (col0 f t) (hS0 t) ε n φ, hA']
