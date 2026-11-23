import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicLocalComponentsContinuousLevelsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemHeckeLevelOfLocalComponentsMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem cmp_not {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ¬ ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dif_neg h]
  rfl

private theorem cmp_cont (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L) :
    Continuous fun k : finU L n => cmp n w ((away l L n).rangeRestrict (k : UA L n)) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · simp only [cmp_of h]
    exact ((UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).1 w).comp continuous_subtype_val
  · simp only [cmp_not h]
    exact continuous_const

private theorem cmp_ev (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L)
    (U : Subgroup (GLw n w)) (hU : IsOpen (U : Set (GLw n w))) :
    ∀ᶠ k : finU L n in nhds 1, cmp n w ((away l L n).rangeRestrict (k : UA L n)) ∈ U := by
  refine (hU.preimage (cmp_cont l n w)).mem_nhds ?_
  change cmp n w ((away l L n).rangeRestrict ((1 : finU L n) : UA L n)) ∈ U
  rw [OneMemClass.coe_one, map_one, map_one]
  exact one_mem U

private theorem cmp_int {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (x : UA L n) (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) :
    cmp n w ((away l L n).rangeRestrict x) ∈ KO (w.adicCompletion L) (Fin n) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rwa [cmp_of h]
  · rw [cmp_not h]
    exact one_mem _

private theorem pi_mem_first_iwahori_filtration {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) (b : ℕ)
    (g : ∀ v, G v) (hg : ∀ v, g v ∈ (I v).I1 b) : g ∈ (piIwa I).I1 b := by
  choose x hx t ht y hy e using fun v => (iwMem _ (I v) b (g v)).2.1.1 (hg v)
  exact (iwMem _ (piIwa I) b g).2.1.2 ⟨x, fun v _ => hx v, t, fun v _ => ht v, y, fun v _ => hy v, funext e⟩

theorem UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ (K : (hset Q τ₀).Lev) (b : ℕ), ∀ᶠ k : finU L n in nhds 1, (∃ u : Ub n s, u ∈ (hset Q τ₀).lev K ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ hτ K b
  obtain ⟨hc, hK, hint⟩ := UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hτ
  have h1 : ∀ᶠ k : finU L n in nhds 1,
      (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict (k : UA L n)) : GV n (wt s)) ∈ U := by
    refine (hU.preimage (continuous_pi fun u : s.St => cmp_cont l n (s.w u))).mem_nhds ?_
    have h0 : (1 : KT n (wt s)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      exact one_mem τ₀.ker
    have e : (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict ((1 : finU L n) : UA L n)) : GV n (wt s)) = 1 := by
      funext u
      rw [OneMemClass.coe_one, map_one, map_one]
      rfl
    rw [Set.mem_preimage, e]
    exact h0
  have h2 := cmp_ev l n (s.w s.v0) _ (hK (s.w s.v0) 1)
  have h3 : ∀ᶠ k : finU L n in nhds 1, ∀ q : Q.Q, cmp n (Q.wq q) ((away l L n).rangeRestrict (k : UA L n)) ∈ K.1 q :=
    Filter.eventually_all.2 fun q => cmp_ev l n (Q.wq q) (K.1 q) (K.2 q).1
  have h4 : ∀ᶠ k : finU L n in nhds 1, ∀ v : V.frame.Vl,
      cLoc (s.w v.1) (k : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1) := by
    haveI : Finite V.frame.Vl := (hset Q τ₀).finV.finite
    refine Filter.eventually_all.2 fun v => ?_
    refine ((hK (s.w v.1) (b + 1)).preimage ((hc (s.w v.1)).comp continuous_subtype_val)).mem_nhds ?_
    change cLoc (s.w v.1) ((1 : finU L n) : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1)
    rw [OneMemClass.coe_one, map_one]
    exact one_mem _
  filter_upwards [hint, h1, h2, h3, h4] with k k0 k1 k2 k3 k4
  have hu : (away l L n).rangeRestrict (k : UA L n) ∈ Ub n s :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => cmp_int _ (k0 _), k2⟩
  refine ⟨⟨⟨_, hu⟩, UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K _ (fun w _ => cmp_int _ (k0 w)) k3, rfl, ?_⟩, ?_⟩
  · have : toKT n s ⟨_, hu⟩ ∈ Subtype.val ⁻¹' U := k1
    rw [hUe] at this
    exact this
  · exact pi_mem_first_iwahori_filtration (fun v : V.frame.Vl => glIwa ((s.w v.1).adicCompletion L) n) b _ fun v =>
      (glBridge ((s.w v.1).adicCompletion L) n ℂ 1).2.2.2.2.1 b (k4 v)
