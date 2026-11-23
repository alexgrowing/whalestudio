import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnramOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTraces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Mult

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

private theorem levOp_at (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (hfs : (Function.support fun q : G ⧸ K' => f q.out).Finite) (x : V) :
    levOp ρ K K' f LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ K', f q.out • ρ q.out x := by
  have hs : (Function.support fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hfs.subset fun q hq h0 => hq (by simp [h0])
  have h := (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) x).toAddMonoidHom.map_finsum hs
  simp only [levOp, LinearMap.smul_apply]
  exact congrArg _ h

private def cosetE (e : G ≃* H) (L : Subgroup H) : G ⧸ L.comap e.toMonoidHom ≃ H ⧸ L :=
  Quotient.congr e.toEquiv fun a b => by
    change QuotientGroup.leftRel _ a b ↔ QuotientGroup.leftRel L (e a) (e b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_comap]
    simp

private theorem cosetE_out (e : G ≃* H) (L : Subgroup H) (q : G ⧸ L.comap e.toMonoidHom) :
    ∃ k ∈ L, (cosetE e L q).out = e q.out * k := by
  have h : (QuotientGroup.mk (e q.out) : H ⧸ L) = cosetE e L q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h2 : (QuotientGroup.mk (cosetE e L q).out : H ⧸ L) = QuotientGroup.mk (e q.out) := by
    rw [h, QuotientGroup.out_eq']
  exact ⟨_, QuotientGroup.eq.1 h2.symm, by simp⟩

private theorem fixed_comap (e : G ≃* H) (ρ : Representation ℂ H V) (L : Subgroup H) :
    fixed (ρ.comp e.toMonoidHom) (L.comap e.toMonoidHom) = fixed ρ L := by
  refine Submodule.ext fun x => ⟨fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
  · have h1 := GlobalTheory.LGrp.mem_fixed.1 h (e.symm k) (by simpa [Subgroup.mem_comap] using hk)
    simpa using h1
  · exact GlobalTheory.LGrp.mem_fixed.1 h (e k) hk

private theorem levOp_tr (e : G ≃* H) (ρ : Representation ℂ H V) (K L : Subgroup H) (f : H → ℂ)
    (hr : ∀ k ∈ L, ∀ x, f (x * k) = f x) (hfin : (Function.support fun q : H ⧸ L => f q.out).Finite)
    {x : V} (hx : x ∈ fixed ρ L) :
    levOp (ρ.comp e.toMonoidHom) (K.comap e.toMonoidHom) (L.comap e.toMonoidHom) (fun g => f (e g)) LinearMap.id x =
      levOp ρ K L f LinearMap.id x := by
  have hval : ∀ q : G ⧸ L.comap e.toMonoidHom, f (e q.out) = f (cosetE e L q).out := fun q => by
    obtain ⟨k, hk, h⟩ := cosetE_out e L q
    rw [h, hr k hk]
  have hfin' : (Function.support fun q : G ⧸ L.comap e.toMonoidHom => f (e q.out)).Finite := by
    refine (hfin.preimage (cosetE e L).injective.injOn).subset fun q hq => ?_
    simp only [Set.mem_preimage, Function.mem_support] at hq ⊢
    rwa [← hval q]
  have hidx : (L.comap e.toMonoidHom).relIndex (K.comap e.toMonoidHom) = L.relIndex K := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  rw [levOp_at _ _ _ _ hfin', levOp_at ρ K L f hfin, hidx, ← finsum_comp_equiv (cosetE e L)]
  refine congrArg _ (finsum_congr fun q => ?_)
  obtain ⟨k, hk, h⟩ := cosetE_out e L q
  rw [hval q, h]
  congr 1
  have hk' := GlobalTheory.LGrp.mem_fixed.1 hx k hk
  rw [map_mul, Module.End.mul_apply, hk']
  rfl

private theorem dite_tr (A B : V →ₗ[ℂ] V) (P Q : Submodule ℂ V) (hPQ : P = Q) (hop : ∀ v ∈ P, A v = B v) :
    (if h : ∀ v ∈ P, A v ∈ P then LinearMap.trace ℂ P (A.restrict h) else 0) =
      if h : ∀ v ∈ Q, B v ∈ Q then LinearMap.trace ℂ Q (B.restrict h) else 0 := by
  subst hPQ
  by_cases h : ∀ v ∈ P, A v ∈ P
  · have h' : ∀ v ∈ P, B v ∈ P := fun v hv => hop v hv ▸ h v hv
    rw [dif_pos h, dif_pos h']
    congr 1
    ext x
    exact hop x.1 x.2
  · have h' : ¬ ∀ v ∈ P, B v ∈ P := fun hb => h fun v hv => (hop v hv).symm ▸ hb v hv
    rw [dif_neg h, dif_neg h']

private theorem twTr_tr (e : G ≃* H) (ρ : Representation ℂ H V) (K L : Subgroup H) (f : H → ℂ)
    (hr : ∀ k ∈ L, ∀ x, f (x * k) = f x) (hfin : (Function.support fun q : H ⧸ L => f q.out).Finite) :
    twTr (ρ.comp e.toMonoidHom) (K.comap e.toMonoidHom) (L.comap e.toMonoidHom) (fun g => f (e g)) LinearMap.id =
      twTr ρ K L f LinearMap.id := by
  unfold twTr
  exact dite_tr _ _ _ _ (fixed_comap e ρ L) fun v hv =>
    levOp_tr e ρ K L f hr hfin ((fixed_comap e ρ L) ▸ hv)

private theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) :
    (Function.support fun q : G ⧸ K => f q.out).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have himg : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) :=
    IsCompact.image hc continuous_quot_mk
  exact himg.finite_of_discrete.subset fun q hq => ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

private theorem trc_at [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (f : G → ℂ) (L : Subgroup G)
    (hLo : IsOpen (L : Set G)) (hLK : L ≤ K) (hf : IsHecke L f) (hfd : FiniteDimensional ℂ (fixed ρ L)) :
    twTr ρ K L f LinearMap.id = trc ρ K f := by
  have hle : L ≤ K ⊓ rStab f ⊓ rStab fun y => f y⁻¹ := fun k hk =>
    ⟨⟨hLK hk, fun x => (hf.2 k hk x).2⟩, fun x => by
      have := (hf.2 k⁻¹ (L.inv_mem hk) x⁻¹).1
      simpa using this⟩
  have hH : IsHecke (K ⊓ rStab f ⊓ rStab fun y => f y⁻¹) f := ⟨hf.1, fun k hk x => ⟨by
      have h1 : k⁻¹ ∈ rStab fun y => f y⁻¹ := Subgroup.inv_mem _ hk.2
      simpa using h1 x⁻¹, hk.1.2 x⟩⟩
  exact trLevel G K hKo hKc V ρ f _ L hLo hle (fun k hk => hk.1.1) hH hfd

private theorem smIrr_nonempty [TopologicalSpace G] : Nonempty (SmIrr G) :=
  ⟨{ V := ℂ
     ρ := 1
     smooth := fun v => by simp
     irred := (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩ }⟩

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hs : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hs]
  exact Subgroup.mem_top _

private def eSp (hs : IsSplitAt w) : GLw n w ≃* UL n w where
  toFun g := ⟨g, mem_UL hs g⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem continuous_eSp (hs : IsSplitAt w) : Continuous (eSp (n := n) hs) :=
  Continuous.subtype_mk continuous_id _

private def toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) : SmIrr (GLw n w) :=
  { V := σ.V
    ρ := σ.ρ.comp (eSp hs).toMonoidHom
    smooth := fun v => (σ.smooth v).preimage (continuous_eSp hs)
    irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ _ (eSp hs).surjective σ.irred }

private theorem comap_KL (hs : IsSplitAt w) : (KL n w).comap (eSp hs).toMonoidHom = KGL w n :=
  Subgroup.ext fun _ => Iff.rfl

private theorem fixed_toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) :
    fixed (toGL hs σ).ρ (KGL w n) = fixed σ.ρ (KL n w) := by
  rw [← comap_KL hs]
  exact fixed_comap (eSp hs) σ.ρ (KL n w)

private theorem cp_toGL (hs : IsSplitAt w) {π : Submodule ℂ (UA E n → ℂ)} {σ : SmIrr (UL n w)}
    (h : IsCompU π w σ) : Cp π w (toGL hs σ) := by
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := h
  refine ⟨(toGL hs σ).irred, f, hf0, hfm, fun x v => ?_⟩
  have he : eSp hs (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
  exact (congrArg (fun g => f (σ.ρ g v)) he).trans (hf x v)

private theorem tr_Z (hs : IsSplitAt w) (σ : SmIrr (UL n w)) (K' : Subgroup (UL n w))
    (hKo : IsOpen (K' : Set (UL n w))) (hKle : K' ≤ KL n w) (f : GLw n w → ℂ)
    (hf : IsHecke K' fun x : UL n w => f x.1) (hfd : FiniteDimensional ℂ (fixed σ.ρ K')) :
    twTr σ.ρ (KL n w) K' (fun x => f x.1) LinearMap.id = trc (toGL hs σ).ρ (KGL w n) f := by
  have h1 := twTr_tr (eSp hs) σ.ρ (KL n w) K' (fun x => f x.1) (fun k hk x => (hf.2 k hk x).2)
    (finite_cosets K' hKo _ hf.1)
  rw [comap_KL hs] at h1
  rw [← h1]
  have hc : HasCompactSupport f := by
    have h2 : HasCompactSupport ((fun x : UL n w => f x.1) ∘ (⟨(eSp hs).toEquiv, continuous_eSp hs, continuous_subtype_val⟩ : GLw n w ≃ₜ UL n w)) :=
      hf.1.comp_homeomorph _
    exact h2
  obtain ⟨ho, hcK⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  refine trc_at (KGL w n) ho hcK (toGL hs σ).ρ f (K'.comap (eSp hs).toMonoidHom)
    (hKo.preimage (continuous_eSp hs)) (fun k hk => hKle hk) ⟨hc, fun k hk x => ?_⟩ ?_
  · exact ⟨(hf.2 _ hk (eSp hs x)).1, (hf.2 _ hk (eSp hs x)).2⟩
  · have h3 : fixed (toGL hs σ).ρ (K'.comap (eSp hs).toMonoidHom) = fixed σ.ρ K' := fixed_comap (eSp hs) σ.ρ K'
    rw [h3]
    exact hfd

private theorem trace_test_function_eq (hs : IsSplitAt w) (σ : SmIrr (UL n w)) {B : Multiset ℂˣ} (hB : HasSatGL w (toGL hs σ).ρ B)
    (e : Ex (Fin (n + 1))) :
    twTr σ.ρ (KL n w) (KL n w) (fun y : UL n w => fn1 n w e y.1) LinearMap.id = ev1 n w e B := by
  have hH := (levelU E n w hs).2 _ (exAct E n w e).1
  have h1 := twTr_tr (eSp hs) σ.ρ (KL n w) (KL n w) (fun y : UL n w => fn1 n w e y.1)
    (fun k hk x => (hH.2 k hk x).2) (finite_cosets _ (unitHecke E n 0 0 w).1 _ hH.1)
  rw [comap_KL hs] at h1
  rw [← h1]
  exact trSph exAct splitLine E n w (toGL hs σ) B hB e

end Local

private theorem tr_dec {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : GlobalTheory.BCT.Unr E) {n : ℕ} (hn : 1 ≤ n)
    {S : Set (Pl E)} (hS : IsSection S) {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hLev : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') {ι : Type} [Fintype ι]
    {σ : ι → Submodule ℂ (UA E n → ℂ)} (hdec : IsDec S lam K' σ) (σ₀ : ι → ∀ w : Pl E, SmIrr (UL n w))
    (hc : ∀ i w, IsCompU (σ i) w (σ₀ i w)) (F : ∀ w : Pl E, UL n w → ℂ) (hF : GlobalTheory.BCT.IsTest (KL n) K' F) :
    trOn (forms S lam K') (hop S K' F) =
      dimW lam * ∑ i, ∏ᶠ w ∈ S, twTr (σ₀ i w).ρ (KL n w) (K' w) (F w) LinearMap.id := by
  obtain ⟨hσ, hind, hsup⟩ := hdec
  have hfd := (GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K' hLev).1
  have hM : ∀ i, FiniteDimensional ℂ ↥(σ i ⊓ fixed (RF E n) (globLev S K')) := fun i =>
    Submodule.finiteDimensional_of_le (hsup ▸ le_iSup (fun i => σ i ⊓ fixed (RF E n) (globLev S K')) i)
  have h1 := GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum _ ι (fun i => σ i ⊓ fixed (RF E n) (globLev S K')) (hop S K' F) hind hM
    (fun i => GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms E n S hS K' hLev F hF (σ i) (hσ i).1)
  rw [hsup] at h1
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    GlobalTheory.T.trace_hecke_levelVectors_eq_dim_mul_local_traces E hU n hn (σ i) (hσ i).1 S hS lam (hσ i).2.1 K' hLev (σ₀ i) (hc i) F hF

theorem evalD : EvalD := by
  intro E _ _ _ hU n hn S hS lam Z hZ K' hLev hKL ι _ σ hdec
  obtain ⟨-, hcc, -, hsec⟩ := places E
  have hsplit' : ∀ w : Pl E, IsSplitAt w → IsSplitAt (cPl w) := fun w h =>
    (hcc (cPl w)).2.2 (by rw [(hcc w).1]; exact ((hcc w).2.1 h).symm)
  have hnot : ∀ w ∈ S, IsSplitAt w → cPl w ∉ S := fun w hw h hc =>
    (hcc w).2.1 h ((hsec S hS w).2 hw hc)
  choose σ₀ hc hfd using fun i w => (GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn (σ i) (hdec.1 i).1 w).1
  have hne : ∀ i, ∀ w ∈ S, fixed (σ₀ i w).ρ (K' w) ≠ ⊥ := fun i w hw =>
    GlobalTheory.T.localComponent_levelFixedVectors_ne_bot E hU n hn S hS lam K' hLev (σ i) (hdec.1 i).1 (hdec.1 i).2.1 (hdec.1 i).2.2 w hw (σ₀ i w) (hc i w)
  have hline : ∀ i, ∀ w ∈ S, w ∉ Z → Module.finrank ℂ (fixed (σ₀ i w).ρ (KL n w)) = 1 ∧
      ∃ B, ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ₀ i w)).ρ B := fun i w hw hz => by
    have h0 := hne i w hw
    rw [hKL w hz] at h0
    by_cases hs : IsSplitAt w
    · obtain ⟨h1, B, hB⟩ := splitLine E n w (toGL hs (σ₀ i w)) (by rw [fixed_toGL]; exact h0)
      rw [fixed_toGL] at h1
      exact ⟨h1, B, fun _ => hB⟩
    · exact ⟨inertLine E hU n w hs (σ₀ i w) h0 (hfd i w _ (unitHecke E n 0 0 w).1), 0, fun h => absurd h hs⟩
  let B₀ : ι → Pl E → Multiset ℂˣ := fun i w =>
    Classical.epsilon fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ₀ i w)).ρ B
  have hB₀ : ∀ i, ∀ w ∈ S, w ∉ Z → ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ₀ i w)).ρ (B₀ i w) := fun i w hw hz =>
    Classical.epsilon_spec (p := fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ₀ i w)).ρ B) (hline i w hw hz).2
  let B : ι → Pl E → Multiset ℂˣ := fun i w => if w ∈ S then B₀ i w else inv (B₀ i (cPl w))
  have hBS : ∀ i, ∀ w ∈ S, B i w = B₀ i w := fun i w hw => if_pos hw
  have hBN : ∀ i w, w ∉ S → B i w = inv (B₀ i (cPl w)) := fun i w hw => if_neg hw
  let t : ι → ∀ w : Pl E, SmIrr (GLw n w) := fun i w =>
    if h : IsSplitAt w then toGL h (σ₀ i w) else Classical.choice smIrr_nonempty
  have ht : ∀ i w (h : IsSplitAt w), t i w = toGL h (σ₀ i w) := fun i w h => dif_pos h
  refine ⟨t, B, fun i => ⟨fun w hns => ?_, fun w hw => ?_, fun w hoff hs => ?_⟩, fun f hf T hT hd e₁ e₂ k => ?_⟩
  ·
    have hw : w ∈ S := by
      have hcw : cPl w = w := by
        by_contra h
        exact hns ((hcc w).2.2 h)
      rcases (hsec S hS w).1 with h | h
      · exact h
      · rwa [hcw] at h
    exact unramOf E n S (σ i) K' (hasLevel_of_fixed hS (hdec.1 i).2.2) w hw (hKL w fun h => hns (hZ w h).2)
  ·
    rw [ht i w (hZ w hw).2]
    exact cp_toGL _ (hc i w)
  ·
    by_cases hw : w ∈ S
    · rw [hBS i w hw]
      exact ⟨toGL hs (σ₀ i w), cp_toGL hs (hc i w), hB₀ i w hw hoff.1 hs⟩
    · have hcw : cPl w ∈ S := ((hsec S hS w).1).resolve_left hw
      have hsc := hsplit' w hs
      have hu := uConj E n (σ i) (cPl w) hsc (toGL hsc (σ₀ i (cPl w))) (B₀ i (cPl w))
        (cp_toGL hsc (hc i _)) (hB₀ i _ hcw hoff.2 hsc)
      rw [(hcc w).1] at hu
      rw [hBN i w hw]
      exact hu
  ·
    have hTs : ∀ w ∈ T, w ∈ S ∧ IsSplitAt w ∧ w ∉ Z := fun w hw =>
      ⟨(hT w hw).1, (hT w hw).2, Finset.disjoint_left.1 hd hw⟩
    have hfZ : ∀ w ∈ Z, famU Z T f e₁ e₂ k w = fun x => f w x.1 := fun w hw => by
      simp [famU, hw]
    have hfT : ∀ w ∈ T, famU Z T f e₁ e₂ k w = fun x => fn1 n w (((e₁ w).pow k).mul ((e₂ w).pow k)) x.1 := fun w hw => by
      simp [famU, hw, (hTs w hw).2.2]
    have hfO : ∀ w, w ∉ Z → w ∉ T → famU Z T f e₁ e₂ k w = (KL n w : Set _).indicator 1 := fun w h1 h2 => by
      simp [famU, h1, h2]
    have htest : GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h1 : w ∈ Z
        · rw [hfZ w h1]
          exact hf w h1
        · rw [hKL w h1]
          by_cases h2 : w ∈ T
          · rw [hfT w h2]
            exact (levelU E n w (hTs w h2).2.1).2 _ (exAct E n w _).1
          · rw [hfO w h1 h2]
            exact (unitHecke E n 0 0 w).2.1
      · refine Filter.eventually_cofinite.2 ((Z ∪ T).finite_toSet.subset fun w hw => ?_)
        by_contra h
        have h' : w ∉ Z ∧ w ∉ T := by simpa using h
        exact hw (hfO w h'.1 h'.2)
    refine ⟨htest, ?_⟩
    rw [tr_dec hU hn hS hLev hdec σ₀ hc _ htest]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [finprodSplit _ S Z T _ (fun w hw => (hZ w hw).1) (fun w hw => (hTs w hw).1) hd fun w hw h1 h2 => ?_]
    · refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_
      · rw [hfZ w hw, ht i w (hZ w hw).2]
        exact tr_Z _ _ _ (hLev.1 w).1 (hLev.1 w).2.1 _ (hf w hw) (hfd i w _ (hLev.1 w).1)
      · rw [val1, ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun w hw => ?_
        obtain ⟨hwS, hs, hz⟩ := hTs w hw
        have hinv : inv (inv (B₀ i w)) = B₀ i w := by simp [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
        rw [hfT w hw, hKL w hz, trace_test_function_eq hs (σ₀ i w) (hB₀ i w hwS hz hs), hBS i w hwS,
          hBN i _ (hnot w hwS hs), (hcc w).1, hinv]
        simp only [ev1, Ex.ev, Ex.ev_pow, mul_pow]
    · rw [hfO w h1 h2, hKL w h1, trUnit, (hline i w hw h1).1]
      simp

end UpperTheory.V.Z.Mult
