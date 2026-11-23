import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLM
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Tensor

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockQuot ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real

namespace PositivityTheory.KRealA

theorem linePos_eq {P Q R S : ℕ} : @FockH1Action.linePos P Q R S = @linePos P Q R S := by
  funext l
  rcases l with ⟨_ | _, _ | _⟩ <;> rfl

theorem omAct_eq (P Q R S : ℕ) : FockH1Action.omAct P Q R S = omAct P Q R S := by
  simp only [FockH1Action.omAct, omAct, FockH1Action.omE, omE, FockH1Action.raiB, raiB, FockH1Action.lowB, lowB, linePos_eq]

theorem fockAction_first_eq (P Q R S : ℕ) : FockH1Action.fockAct1 P Q R S = fockAct1 P Q R S := by
  rw [FockH1Action.fockAct1, fockAct1, omAct_eq]

theorem fock_second_action_eq_derivation (P Q R S : ℕ) : FockH1Action.fockAct2 P Q R S = fockAct2 P Q R S := by
  rw [FockH1Action.fockAct2, fockAct2, omAct_eq]

section Image

variable {P Q R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (p : Pol P Q R S →ₗ[ℂ] V) (hp : Function.Surjective p)
  (act : Mat R S → Module.End ℂ V) (h : ∀ W f, act W (p f) = p (fockAct2 P Q R S W f))

def actL : Mat R S →ₗ[ℂ] Module.End ℂ V where
  toFun := act
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := hp v
    simp only [LinearMap.add_apply, h, map_add]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := hp v
    simp only [LinearMap.smul_apply, h, map_smul, RingHom.id_apply]

theorem actL_apply (W : Mat R S) : actL p hp act h W = act W := rfl

theorem actL_wt (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    p g ∈ wtSub (actL p hp act h) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actL_apply, h, hg a]
  simp

def gkImage : GKMod R S where
  V := V
  act := actL p hp act h
  lie X Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := hp v
    have e := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e ⊢
    rw [actL_apply, actL_apply, actL_apply, h, h, h, h, h, e, map_sub]
  kfin v := by
    obtain ⟨f, rfl⟩ := hp v
    obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
    refine ⟨W₀.map p, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    exact ⟨fockAct2 P Q R S X w, hst X hX w hw, (h X w).symm⟩
  wts v := by
    obtain ⟨f, rfl⟩ := hp v
    have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
    refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
      (motive := fun g => p g ∈ ⨆ μ : Ix R S → ℚ, wtSub (actL p hp act h) μ) hf ?_ ?_ ?_
    · intro μ g hg
      exact Submodule.mem_iSup_of_mem _ (actL_wt p hp act h μ g hg)
    · simp
    · intro g g' hg hg'
      rw [map_add]
      exact Submodule.add_mem _ hg hg'

end Image

theorem scalarEnd_of {R S : ℕ} (M : GKMod R S) (hi : Formalism.MainNotions.SchurIrreducible.IrrGK M) (hr : Module.rank ℂ M.V ≤ Cardinal.aleph0) :
    ScalarEnd M := by
  intro T hT
  have := hi.1
  let B : Subalgebra ℂ (Module.End ℂ M.V) := Subalgebra.centralizer ℂ {T}
  have hB : ∀ b : Module.End ℂ M.V, b ∈ B ↔ T * b = b * T := fun b => by
    simp only [B, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have hs : IsSimpleModule B M.V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases hi.2 (N.restrictScalars ℂ) (fun Z x hx => N.smul_mem (⟨M.act Z, (hB _).2 (hT Z)⟩ : B) hx) with h1 | h1
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff ℂ B M.V).1 h1)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff ℂ B M.V).1 h1)
  let g : Module.End B M.V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun b x => LinearMap.congr_fun ((hB b).1 b.2) x }
  obtain ⟨c, hc⟩ := PositivityTheory.KReal.schur_countable hr g
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  have e : g x = T x := rfl
  rw [← e, ← hc]
  simp

theorem rank_pol (P Q R S : ℕ) : Module.rank ℂ (Pol P Q R S) ≤ Cardinal.aleph0 := by
  rw [MvPolynomial.rank_eq_lift]
  exact (Cardinal.lift_id _).le.trans Cardinal.mk_le_aleph0

theorem thetaMk_first_action_trace {P Q R S : ℕ} (c : ℂ) (X : Mat P Q) (f : Pol P Q R S) :
    thMkC P Q R S c (fockAct1 P Q R S X f) = (c * X.trace) • thMkC P Q R S c f := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_iSup_of_mem X ⟨f, ?_⟩)
  simp [act1, chiTr, fockAction_first_eq]

theorem onePlaceD (D : RealData) (h : D.Hyp) :
    ∃ (N : GKMod D.R D.S) (p : Pol D.P D.Q D.R D.S →ₗ[ℂ] N.V) (p' : Pol D.P' D.Q' D.R D.S →ₗ[ℂ] N.V),
      IsLift ((D.κ : ℚ) / 2) 0 N p ∧ IsLift (-((D.κ : ℚ) / 2)) ((D.κ : ℚ) / 2) N p' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ ScalarEnd N := by
  obtain ⟨Pi, _, _, act, π, π', hπ, hπ', h1, h2, hn, hirr⟩ := PositivityTheory.KReal.coreLM D h
  have c1 : (((D.κ : ℚ) / 2 : ℚ) : ℂ) = (D.κ : ℂ) / 2 := by push_cast; rfl
  have c2 : ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) = -((D.κ : ℂ) / 2) := by push_cast; rfl
  let p : Pol D.P D.Q D.R D.S →ₗ[ℂ] Pi := π ∘ₗ thMkC _ _ _ _ _
  let p' : Pol D.P' D.Q' D.R D.S →ₗ[ℂ] Pi := π' ∘ₗ thMkC _ _ _ _ _
  have hp : Function.Surjective p := hπ.comp (Submodule.mkQ_surjective _)
  have hp' : Function.Surjective p' := hπ'.comp (Submodule.mkQ_surjective _)
  have ha : ∀ W f, act W (p f) = p (fockAct2 _ _ _ _ W f) := fun W f => by
    rw [← fock_second_action_eq_derivation]
    exact (h1 W _).symm
  have ha' : ∀ W f, act W (p' f) = p' (fockAct2 _ _ _ _ W f) + ((D.κ : ℂ) / 2 * W.trace) • p' f := fun W f => by
    rw [← fock_second_action_eq_derivation]
    refine (h2 W _).symm.trans ?_
    have e : PositivityTheory.KReal.opV' D W (thMkC _ _ _ _ _ f) =
        thMkC _ _ _ _ _ (FockH1Action.fockAct2 _ _ _ _ W f) + ((D.κ : ℂ) / 2 * W.trace) • thMkC _ _ _ _ _ f := rfl
    rw [e, map_add, map_smul]
    rfl
  have hI : Formalism.MainNotions.SchurIrreducible.IrrGK (gkImage p hp act ha) := ⟨hn, hirr⟩
  refine ⟨gkImage p hp act ha, p, p', ⟨hp, fun X f => ?_, fun Y f => ?_⟩, ⟨hp', fun X f => ?_, fun Y f => ?_⟩, hI,
    scalarEnd_of _ hI ((LinearMap.rank_le_of_surjective p hp).trans (rank_pol _ _ _ _))⟩
  · rw [c1]
    exact (congrArg π (thetaMk_first_action_trace _ X f)).trans (map_smul π _ _)
  · rw [Rat.cast_zero, zero_mul, zero_smul, add_zero]
    exact ha Y f
  · rw [c2]
    exact (congrArg π' (thetaMk_first_action_trace _ X f)).trans (map_smul π' _ _)
  · rw [c1]
    exact ha' Y f

theorem onePlace (a a' p q : ℕ) (κ : ℤ) (he : Even (a + a')) (hκ : ((a + a' : ℕ) : ℤ) < κ) (hκe : Even κ)
    (hE : 2 * (p + q) + 1 < (a - a') / 2) (hA : 2 * (p + q) + 1 < a') :
    ∃ (N : GKMod (a + a' - (p + q)) (p + q)) (π : Pol (a - p) p (a + a' - (p + q)) (p + q) →ₗ[ℂ] N.V)
      (π' : Pol q (a' - q) (a + a' - (p + q)) (p + q) →ₗ[ℂ] N.V),
      IsLift ((κ : ℚ) / 2) 0 N π ∧ IsLift (-((κ : ℚ) / 2)) ((κ : ℚ) / 2) N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ ScalarEnd N := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ κ by omega)
  obtain ⟨m, hm⟩ := he
  obtain ⟨n, hn⟩ := hκe
  have hD : RealData.Hyp ⟨a, a', p, q, k⟩ := by
    constructor <;> dsimp only <;> omega
  rw [Int.cast_natCast]
  exact onePlaceD ⟨a, a', p, q, k⟩ hD

end PositivityTheory.KRealA

end
