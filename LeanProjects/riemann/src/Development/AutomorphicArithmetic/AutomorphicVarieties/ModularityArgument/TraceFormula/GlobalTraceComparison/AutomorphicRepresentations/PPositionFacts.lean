import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocGLMemKglob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem cc (w : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := GlobalTheory.EulerTwU.cPl_cPl w

private theorem cont_thF : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

private theorem twist_int (v : Pl E) (x : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) n) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v n := by
  rw [GlobalTheory.EulerTwU.pc_thF]
  exact GlobalTheory.EulerTwSplit.theta_mem _ (conjLoc_spec _ v).2.2 h

private theorem twist_int_iff (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v n ↔
      GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) n := by
  refine ⟨fun h => ?_, twist_int v x⟩
  have h1 : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v))) (thF E n x) ∈
      KGL (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v)) n := by
    rw [cc]; exact h
  have h2 := twist_int (GlobalTheory.EulerTw.cPl E v) (thF E n x) h1
  rwa [GlobalTheory.EulerTwU.thF_thF] at h2

private theorem twist_away {u v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ u) (a : GLw n u) :
    GeneralLinearGroup.map (pLoc E v) (thF E n (locGL E n u a)) = 1 := by
  have e : GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv v) 1 = 1 := map_one _
  rw [GlobalTheory.EulerTwU.pc_thF, pLoc_locGL_of_ne h]
  exact (congrArg (thetaGL n (RingHom.id _)) e).trans (map_one _)

private theorem bad_finite (g : GL (Fin n) (Af E)) :
    {v : Pl E | GeneralLinearGroup.map (pLoc E v) g ∉ KGL v n}.Finite := by
  have h1 : ∀ x : Af E, ∀ᶠ v : Pl E in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E :=
    fun x => x.2.mono fun _ h => h
  have h2 := eventually_all.2 fun i => eventually_all.2 fun j => h1 (g.1 i j)
  have h3 := eventually_all.2 fun i => eventually_all.2 fun j => h1 ((g⁻¹).1 i j)
  have h4 : ∀ᶠ v : Pl E in cofinite, GeneralLinearGroup.map (pLoc E v) g ∈ KGL v n := by
    filter_upwards [h2, h3] with v a b
    rw [GlobalTheory.EulerTwRestr.mem_KGL_iff]
    exact ⟨fun i j => a i j, fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact b i j⟩
  exact eventually_cofinite.1 h4

private theorem comm_loc (w : Pl E) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E w) c = 1) : Commute (locGL E n w a) c := by
  show locGL E n w a * c = c * locGL E n w a
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

private theorem qj (w : Pl E) (b : Bool) (a : GLw n w) : qw n w b (jw n w b a) = a := by
  cases b
  · exact pLoc_locGL _ _
  · show GeneralLinearGroup.map (pLoc E w) (thF E n (thF E n (locGL E n w a))) = a
    rw [GlobalTheory.EulerTwU.thF_thF]
    exact pLoc_locGL _ _

private theorem comm_mapFactor_of_absIrr (w : Pl E) (b : Bool) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : qw n w b c = 1) : Commute (jw n w b a) c := by
  cases b
  · exact comm_loc w a c h
  · have h1 := (comm_loc w a (thF E n c) h).map (thF E n)
    rwa [GlobalTheory.EulerTwU.thF_thF] at h1

private theorem cont_j (w : Pl E) (b : Bool) : Continuous (jw n w b) := by
  cases b
  · exact GlobalTheory.CuspRep.CuspSub.continuous_locGL w
  · exact cont_thF.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

private theorem cont_q (w : Pl E) (b : Bool) : Continuous (qw (E := E) n w b) := by
  cases b
  · exact GlobalTheory.BCT.LocCpt.continuous_mapLoc w
  · exact (GlobalTheory.BCT.LocCpt.continuous_mapLoc w).comp cont_thF

end SlopeTestRemainingChoices

theorem slotFacts_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → SlotBasic := by
  intro hP E _ _ _ n S hS
  obtain ⟨-, hc, -, hs⟩ := hP E
  have hsplit : ∀ w : Pl E, IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w := fun w => (hc w).2
  have hsec : ∀ w : Pl E, w ∈ S → GlobalTheory.EulerTw.cPl E w ∈ S → GlobalTheory.EulerTw.cPl E w = w :=
    fun w => (hs S hS w).2
  have hor : ∀ w : Pl E, w ∈ S ∨ GlobalTheory.EulerTw.cPl E w ∈ S := fun w => (hs S hS w).1
  refine ⟨GlobalTheory.EulerTwU.thF_thF, cont_thF, fun w b => ⟨cont_j w b, cont_q w b, qj w b, comm_mapFactor_of_absIrr w b⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, bi⟩ ⟨k, bk⟩ ⟨hi, hi'⟩ ⟨hk, hk'⟩ hne a
    have hik : bi = bk → i ≠ k := fun e e' => hne (by rw [e, e'])
    cases bi <;> cases bk
    · exact pLoc_locGL_of_ne (hik rfl).symm a
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      exact (hsplit k).1 (hk' rfl) (hsec k hk0 (e0 ▸ hi0))
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      have e' : GlobalTheory.EulerTw.cPl E i = k := by rw [← e0, cc]
      exact (hsplit i).1 (hi' rfl) (hsec i hi0 (e' ▸ hk0))
    · show GeneralLinearGroup.map (pLoc E k) (thF E n (thF E n (locGL E n i a))) = 1
      rw [GlobalTheory.EulerTwU.thF_thF]
      exact pLoc_locGL_of_ne (hik rfl).symm a
  · intro g
    refine (((bad_finite g).prod (Set.finite_singleton false)).union
      ((bad_finite (thF E n g)).prod (Set.finite_singleton true))).subset ?_
    rintro ⟨w, b⟩ h
    cases b
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩
  · intro w hw g
    have hcw : GlobalTheory.EulerTw.cPl E w = w := by
      by_contra h
      exact hw ((hsplit w).2 h)
    have h1 := twist_int_iff w g
    rw [hcw] at h1
    exact h1
  · intro g
    have hL : g ∈ Lev S (fun w : Pl E => KGL w n) ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 g ∈ KGL i.1 n := by
      simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
    have hK : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ KGL w n := by
      simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
    rw [hL, hK]
    constructor
    · intro h w
      by_cases hw : w ∈ S
      · exact h (w, false) ⟨hw, by simp⟩
      · have hw' : GlobalTheory.EulerTw.cPl E w ∈ S := (hor w).resolve_left hw
        have hne : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) ≠ GlobalTheory.EulerTw.cPl E w := by
          rw [cc]
          exact fun e => hw (e ▸ hw')
        have h1 := (twist_int_iff (n := n) (GlobalTheory.EulerTw.cPl E w) g).1
          (h (GlobalTheory.EulerTw.cPl E w, true) ⟨hw', fun _ => (hsplit _).2 hne⟩)
        rwa [cc] at h1
    · rintro h ⟨w, b⟩ -
      cases b
      · exact h w
      · exact twist_int w g (h _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
