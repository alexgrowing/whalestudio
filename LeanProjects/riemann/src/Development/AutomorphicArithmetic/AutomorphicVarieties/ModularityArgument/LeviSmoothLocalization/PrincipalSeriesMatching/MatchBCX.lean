import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.EulerdShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SecDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CrossGOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

namespace BaseChangeUnramifiedMatching

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

private theorem cnt_zero (s : Multiset (IrrGL k)) (a : kˣ →* ℂˣ)
    (h : ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ¬ IsUnram (ξ * a)) : cnt s a = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ξ, hξ, rfl, hu⟩
  exact h ξ hξ hy hu

private theorem cnt_zero_of_unr (s : Multiset (IrrGL k)) (a : kˣ →* ℂˣ) (hs : ∀ y ∈ s, y.IsUnramChar)
    (ha : ¬ IsUnram a) : cnt s a = 0 := by
  refine cnt_zero s a fun ξ hξ hy hu => ?_
  obtain ⟨μ, hμ, e⟩ := hs _ hy
  rw [IrrGL.ofChar_inj.1 e] at hu
  exact ha (unr_cancel hμ hu)

private theorem exists_bad (s : Multiset (IrrGL k)) :
    ∃ T : Finset (kˣ →* ℂˣ), ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ξ ∈ T := by
  let g : IrrGL k → (kˣ →* ℂˣ) := fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1
  refine ⟨s.toFinset.image g, fun ξ hξ hy => Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hy, ?_⟩⟩
  have h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  change (if h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' then h.choose else 1) = ξ
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact (IrrGL.ofChar_inj.1 h2).symm

private theorem pol_one (s : Multiset (IrrGL k)) (h : cnt s 1 = 0) : pol s 1 = 1 := by
  obtain ⟨e0, ed, -, -⟩ := (polFacts k).2.2.2 s 1
  have e := eq_C_of_natDegree_eq_zero (ed.trans h)
  rw [← coeff_zero_eq_eval_zero] at e0
  rw [e, e0, C_1]

private theorem cnt_of_pol {s s' : Multiset (IrrGL k)} {a b : kˣ →* ℂˣ} (h : pol s a = pol s' b) : cnt s a = cnt s' b := by
  rw [← ((polFacts k).2.2.2 s a).2.1, h, ((polFacts k).2.2.2 s' b).2.1]

end Loc

private theorem comp_cancel {a : ℂ} (ha : a ≠ 0) {A B : ℂ[X]} (h : A.comp (C a * X) = B.comp (C a * X)) : A = B := by
  have e : (C a * X : ℂ[X]).comp (C a⁻¹ * X) = X := by
    simp only [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  have := congrArg (fun p => p.comp (C a⁻¹ * X)) h
  simpa only [comp_assoc, e, comp_X] using this

private theorem pair_prod (hO : PairGOps) (q : ℝ) (J : Finset ℕ) (A A' : ℕ → ℂ → ℂ) (β Q : ℕ → ℂ[X])
    (h : ∀ j ∈ J, PairG (A j) (A' j) (β j) q (Q j)) :
    PairG (∏ j ∈ J, A j) (∏ j ∈ J, A' j) (∏ j ∈ J, β j) q (∏ j ∈ J, Q j) := by
  induction J using Finset.induction_on with
  | empty => simpa using hO.1 q
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact hO.2.1 _ _ _ _ _ _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

open Classical in

private def pick {X : Type} (sat : X → Multiset ℂˣ → Prop) (w : X) : Multiset ℂˣ :=
  if h : ∃ B, sat w B then h.choose else 0

private theorem pick_spec {X : Type} {sat : X → Multiset ℂˣ → Prop} {w : X} {B : Multiset ℂˣ} (h : sat w B) :
    sat w (pick sat w) := by
  have h' : ∃ B, sat w B := ⟨B, h⟩
  rw [pick, dif_pos h']
  exact h'.choose_spec

private theorem sat_unique {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) (h' : (CG.mk σ).HasSat w B') : B = B' :=
  GlobalTheory.LFun.HasSatGL.unique ((CG.hasSat_mk σ w B).1 h) ((CG.hasSat_mk σ w B').1 h')

private theorem sat_card {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) : Multiset.card B = n :=
  GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk σ w B).1 h)

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem val_pow' {F : Type} [Field F] [NumberField F] (η : HChar F) (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

private theorem unr_pow {F : Type} [Field F] [NumberField F] (η : HChar F) (j : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (h : η.UnrAt v) : (η ^ j).UnrAt v := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    rw [unrAt_iff] at h ih ⊢
    intro x hx
    rw [pow_succ]
    change (η ^ j).loc v x * η.loc v x = 1
    rw [ih x hx, h x hx, one_mul]

section Core

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem places_nonempty (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [hQl.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨⟨Q, hQm.isPrime, hQ0⟩, hQl⟩⟩

private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private def above (S : Finset (HeightOneSpectrum (𝓞 K))) : Finset (HeightOneSpectrum (𝓞 L)) :=
  S.biUnion fun p => (Finset.univ : Finset (PlacesOver L p)).map (Function.Embedding.subtype _)

private theorem mem_above (S : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ above S ↔ w.under (𝓞 K) ∈ S := by
  simp only [above, Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 K) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

variable [IsTotallyComplex K] [IsTotallyComplex L] [IsGalois K L]

private theorem core (hd : (Module.finrank K L).Prime) {n : ℕ} (hn : 2 ≤ n) (σ : CuspSub K n) (τ : CuspSub L n) (η : HChar K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hK : GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S)
    (hM : ∀ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L, w.under (𝓞 K) ∈ S)
    (hη : ∀ p ∉ S, η.UnrAt p ∧ ∀ w : PlacesOver L p,
      IsPrimitiveRoot (η.val p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = Module.finrank K L)
    (hkey : ∀ p ∉ S, ∀ w : PlacesOver L p, ∃ B, (CG.mk σ).HasSat p B ∧ (CG.mk τ).HasSat w.1 (B.map (· ^ fdeg w)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (r : ℕ → ∀ u : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (u.adicCompletion K)))
    (sM : ∀ w : HeightOneSpectrum (𝓞 L), Multiset (IrrGL (w.adicCompletion L)))
    (hr : ∀ j u, SuppAt (σ.twist (η ^ j)) u (r j u)) (hsM : ∀ w, SuppAt τ w (sM w))
    (zK : ∀ j ∈ Finset.range (Module.finrank K L), ∀ u ∈ S, u ≠ v → cnt (r j u) 1 = 0)
    (zM : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ S → w.under (𝓞 K) ≠ v → cnt (sM w) 1 = 0) :
    ∏ j ∈ Finset.range (Module.finrank K L), pol (r j v) 1 = ∏ w : PlacesOver L v, (pol (sM w.1) 1).comp (X ^ fdeg w) := by
  have hOps := pairGOps
  have hCross : CrossG := crossGOf Inf.expAlg Inf.expIndep secDiff
  obtain ⟨c₀, hc₀⟩ := satBd K n σ
  obtain ⟨BK, hBK⟩ : ∃ BK, BK = pick (CG.mk σ).HasSat := ⟨_, rfl⟩
  obtain ⟨BM, hBM⟩ : ∃ BM, BM = pick (CG.mk τ).HasSat := ⟨_, rfl⟩
  have satK : ∀ p ∉ S, (CG.mk σ).HasSat p (BK p) := fun p hp => by
    obtain ⟨w⟩ := places_nonempty (L := L) p
    obtain ⟨B, h, -⟩ := hkey p hp w
    rw [hBK]
    exact pick_spec h
  have memSM := mem_above (L := L) S
  have satM : ∀ w ∉ above (L := L) S, (CG.mk τ).HasSat w (BM w) := fun w hw => by
    obtain ⟨B, -, h⟩ := hkey (w.under (𝓞 K)) (fun h => hw ((memSM w).2 h)) ⟨w, ⟨rfl⟩⟩
    rw [hBM]
    exact pick_spec h
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have sideK : ∀ j ∈ Finset.range (Module.finrank K L), ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S)
      (eulerLd K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S) β (Ideal.absNorm v.asIdeal : ℕ)
      (∏ u ∈ S, (pol (r j u) 1).comp (X ^ 1)) := fun j hj => by
    have e : (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) = cx fun p => (BK p).map (· * (η ^ j).val p) := by
      funext p
      simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, val_pow', Units.val_pow_eq_pow_val]
    rw [e]
    refine sideX K n hn (σ.twist (η ^ j)) S hK _ (fun p hp => ?_) (r j) _ (fun _ => 1) hq fun u hu => ⟨hr j u, fun h => ?_⟩
    · rw [← CG.twist_mk]
      exact (satK p hp).twist (unr_pow η j (hη p hp).1)
    · rw [pow_one, not_not.1 fun e => h (zK j hj u hu e)]
  choose! β hβ pK using sideK
  obtain ⟨β', hβ', pM⟩ := sideX L n hn τ (above S) (fun w hw => (memSM w).2 (hM w hw)) BM satM sM
    (Ideal.absNorm v.asIdeal) (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq fun w hw => ⟨hsM w, fun h => by
      have e : w.under (𝓞 K) = v := not_not.1 fun e => h (zM w ((memSM w).1 hw) e)
      subst e
      have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
      have := w.isMaximal
      have := (w.under (𝓞 K)).isMaximal
      rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.absNorm_pow_inertiaDeg]⟩
  obtain ⟨c, hc⟩ := regroupBC K L _ (S : Set (HeightOneSpectrum (𝓞 K))) (above S : Finset (HeightOneSpectrum (𝓞 L)))
    (cx BK) (cx BM) (fun p => ((η.val p : ℂˣ) : ℂ)) c₀ n hd (fun w => by simpa using memSM w)
    (fun p hp => by
      have hp' : p ∉ S := by simpa using hp
      have hs := satK p hp'
      refine ⟨by simp [cx, sat_card σ hs], fun b hb => ?_, fun w => ⟨?_, (hη p hp').2 w |>.2, ?_⟩⟩
      · obtain ⟨b₀, hb₀, rfl⟩ := Multiset.mem_map.1 hb
        have := hc₀ p _ hs b₀ hb₀
        rwa [Units.val_inv_eq_inv_val] at this
      · exact ((hη p hp').2 w).1.map_of_injective (f := Units.coeHom ℂ) Units.val_injective
      · obtain ⟨B, h1, h2⟩ := hkey p hp' w
        have hw : w.1 ∉ above (L := L) S := fun h => hp' (by simpa [under_eq] using (memSM w.1).1 h)
        rw [cx, cx, sat_unique σ (satK p hp') h1, sat_unique τ (satM w.1 hw) h2, Multiset.map_map, Multiset.map_map]
        exact Multiset.map_congr rfl fun b _ => by simp)
  have pK' := pair_prod hOps _ (Finset.range (Module.finrank K L)) _ _ β _ pK
  have pM' : PairG (∏ j ∈ Finset.range (Module.finrank K L), eulerL K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S)
      (∏ j ∈ Finset.range (Module.finrank K L), eulerLd K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S) β'
      (Ideal.absNorm v.asIdeal : ℕ) (∏ w ∈ above S, (pol (sM w) 1).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal)) :=
    hOps.2.2.1 _ _ _ _ _ _ _ c pM (fun s hs => by rw [Finset.prod_apply]; exact ((hc s).1 hs).symm)
      (fun s hs => by rw [Finset.prod_apply]; exact ((hc s).2 hs).symm)
  have e1 : ∏ w ∈ above S, (pol (sM w) 1).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal) =
      ∏ w : PlacesOver L v, (pol (sM w.1) 1).comp (X ^ fdeg w) := by
    have hsub : (Finset.univ : Finset (PlacesOver L v)).map (Function.Embedding.subtype _) ⊆ above S := fun w hw => by
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hw
      refine (memSM w.1).2 ?_
      change w.1.under (𝓞 K) ∈ S
      rw [under_eq]
      exact hv
    rw [← Finset.prod_subset hsub (fun w hw hw' => ?_), Finset.prod_map]
    · rfl
    · rw [pol_one _ (zM w ((memSM w).1 hw) fun e => hw' ?_), one_comp]
      exact Finset.mem_map.2 ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal e.symm⟩⟩, Finset.mem_univ _, rfl⟩
  have e2 : ∏ j ∈ Finset.range (Module.finrank K L), ∏ u ∈ S, (pol (r j u) 1).comp (X ^ 1) =
      ∏ j ∈ Finset.range (Module.finrank K L), pol (r j v) 1 := Finset.prod_congr rfl fun j hj => by
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => by rw [pol_one _ (zK j hj u hu hne), one_comp]), pow_one, comp_X]
  rw [e1] at pM'
  rw [e2] at pK'
  refine hCross _ _ _ _ _ _ _ (by exact_mod_cast hq) (Finset.prod_ne_zero_iff.2 hβ) hβ' ?_ ?_ pK' pM'
  · rw [eval_prod]
    exact Finset.prod_eq_one fun j _ => ((polFacts _).2.2.2 _ 1).1
  · rw [eval_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [eval_comp, eval_pow, eval_X, zero_pow (normVal K L v w 1).2.2.1.ne']
    exact ((polFacts _).2.2.2 _ 1).1

end Core

private theorem norm_units (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hd : (Module.finrank K L).Prime) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ T, ∀ (w : PlacesOver L u) (θ : (u.adicCompletion K)ˣ →* ℂˣ),
      IsSmoothChar θ → IsUnram (θ.comp (nm w)) → IsUnram θ := by
  obtain ⟨η, h1, h3⟩ := normCnt K L hd
  refine ⟨(Filter.eventually_cofinite.1 h1).toFinset, fun u hu w θ hθ hn => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu
  have hc := ((h3 u w).2.2 θ hθ).2.2 hn
  have hpos : 0 < ∑ w' : PlacesOver L u, fdeg w' := by
    have : 0 < fdeg w := (normVal K L u w 1).2.2.1
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun w' : PlacesOver L u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hj' := (Finset.mem_filter.1 hj).2
  exact unr_cancel ((unrAt_iff _ u).1 (unr_pow η j hu.1)) (mul_comm θ _ ▸ hj')

private theorem bc_key {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop) (satE : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ → Prop)
    (h : WeakBC sat satE) : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ w : PlacesOver L p,
      ∃ B, sat p B ∧ satE w.1 (B.map (· ^ fdeg w)) := by
  have hF := (Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 K)
  refine ⟨hF.toFinset, fun p hp w => ?_⟩
  rw [Set.Finite.mem_toFinset] at hp
  have hg : ∀ f : ℕ, normV w.1 = normV (w.1.under (𝓞 K)) ^ f →
      ∃ B, sat (w.1.under (𝓞 K)) B ∧ satE w.1 (B.map (· ^ f)) :=
    not_not.1 fun e => hp ⟨w.1, e, under_eq w⟩
  have hN : normV w.1 = normV (w.1.under (𝓞 K)) ^ fdeg w := by
    have e : ∀ {F : Type} [Field F] [NumberField F] (x : HeightOneSpectrum (𝓞 F)), normV x = Ideal.absNorm x.asIdeal :=
      fun x => by rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [e, e, under_eq, (normVal K L p w 1).2.2.2]
  obtain ⟨B, h1, h2⟩ := hg _ hN
  exact ⟨B, under_eq w ▸ h1, h2⟩

end BaseChangeUnramifiedMatching

open BaseChangeUnramifiedMatching in
theorem matchBCX : MatchBCX := by
  intro K L _ _ _ _ _ _ _ _ hd n hn π P hW η hη v s s' hs hs' θ hθ
  have h1 : 1 ≤ n := by omega
  obtain ⟨T, hT⟩ := norm_units K L hd
  obtain ⟨S₁, hkey⟩ := bc_key _ _ hW
  have FK := suppFacts K n h1 π
  have FM := suppFacts L n h1 P
  choose sK hsK using fun u => (FK u).1
  choose sM hsM using fun w => (FM w).1
  choose bK hbK using fun u => exists_bad (sK u)
  choose bM hbM using fun w => exists_bad (sM w)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S₀ ↔ u = v ∨ u ∈ S₁ ∨ u ∈ T ∨
      u ∈ (Filter.eventually_cofinite.1 hη).toFinset ∨ u ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∨
      ∃ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L, w.under (𝓞 K) = u :=
    ⟨insert v (S₁ ∪ (T ∪ ((Filter.eventually_cofinite.1 hη).toFinset ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∪
      (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L).image fun w => w.under (𝓞 K))))), fun u => by simp⟩
  obtain ⟨χ, hχv, hχ⟩ := globTw K L v θ hθ S₀
    (fun u => (Finset.range (Module.finrank K L)).biUnion fun j => (bK u).image (· * (η ^ j).loc u)) bM
  obtain ⟨ξ, hξ⟩ := normLoc K L χ
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ χ.UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset, fun u => by simp⟩
  have good : ∀ u ∉ S₀, u ∉ S₁ ∧ u ∉ T ∧ η.UnrAt u ∧ ∀ w : PlacesOver L u,
      IsPrimitiveRoot (η.val u) (fdeg w) ∧ Fintype.card (PlacesOver L u) * fdeg w = Module.finrank K L := fun u hu => by
    have a : u ∉ S₁ := fun h => hu ((hS₀ u).2 (by tauto))
    have b : u ∉ T := fun h => hu ((hS₀ u).2 (by tauto))
    have c : u ∉ (Filter.eventually_cofinite.1 hη).toFinset := fun h => hu ((hS₀ u).2 (by tauto))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at c
    exact ⟨a, b, c⟩
  choose tK htK using fun u => suppTw K n h1 π u χ _ (hsK u)
  choose rK hrK using fun j u => suppTw K n h1 (π.twist χ) u (η ^ j) _ (htK u).1
  choose tM htM using fun w => suppTw L n h1 P w ξ _ (hsM w)
  have main := core hd hn (π.twist χ) (P.twist ξ) η S
    (fun u hu => (hS _).2 (Or.inl ((hS₀ _).2 (by tauto))))
    (fun w hw => (hS _).2 (Or.inl ((hS₀ _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩))))))))
    (fun p hp => by
      have := good p fun h => hp ((hS p).2 (Or.inl h))
      exact this.2.2)
    (fun p hp w => by
      have h0 : p ∉ S₀ := fun h => hp ((hS p).2 (Or.inl h))
      have hu : χ.UnrAt p := not_not.1 fun h => hp ((hS p).2 (Or.inr h))
      obtain ⟨B, b1, b2⟩ := hkey p (good p h0).1 w
      obtain ⟨u1, v1⟩ := (hξ p w).2.1 hu
      refine ⟨B.map (· * χ.val p), ?_, ?_⟩
      · rw [← CG.twist_mk]
        exact b1.twist hu
      · rw [← CG.twist_mk]
        have := b2.twist u1
        rw [v1, Multiset.map_map] at this
        rw [Multiset.map_map]
        convert this using 2
        simp [mul_pow])
    v ((hS _).2 (Or.inl ((hS₀ _).2 (Or.inl rfl)))) rK tM (fun j u => (hrK j u).1) (fun w => (htM w).1)
    (fun j hj u hu hne => by
      have e : cnt (rK j u) 1 = cnt (sK u) (χ.loc u * ((η ^ j).loc u * 1)) :=
        cnt_of_pol (by rw [(hrK j u).2.1, (htK u).2.1])
      rw [e, mul_one]
      by_cases h0 : u ∈ S₀
      · refine cnt_zero _ _ fun ζ hζ hy hun => (hχ u h0 hne).1 (ζ * (η ^ j).loc u) ?_ ?_
        · exact Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_image.2 ⟨ζ, hbK u ζ hζ hy, rfl⟩⟩
        · rwa [mul_assoc, mul_comm ((η ^ j).loc u)]
      · obtain ⟨w⟩ := places_nonempty (L := L) u
        obtain ⟨B, b1, -⟩ := hkey u (good u h0).1 w
        refine cnt_zero_of_unr _ _ ((FK u).2.2.2.1 _ B (hsK u) b1) fun h => ((hS u).1 hu).resolve_left h0 ?_
        exact (unrAt_iff χ u).2 (unr_cancel ((unrAt_iff _ u).1 (unr_pow η j (good u h0).2.2.1)) (mul_comm (χ.loc u) _ ▸ h)))
    (fun w hu hne => by
      have e : cnt (tM w) 1 = cnt (sM w) (ξ.loc w * 1) := cnt_of_pol ((htM w).2.1 1)
      rw [e, mul_one, (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 K) ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ _ h0 hne).2 ⟨w, ⟨rfl⟩⟩ ζ (hbM w ζ hζ hy)
      · obtain ⟨B, -, b2⟩ := hkey _ (good _ h0).1 ⟨w, ⟨rfl⟩⟩
        exact cnt_zero_of_unr _ _ ((FM w).2.2.2.1 _ _ (hsM w) b2) fun h => ((hS _).1 hu).resolve_left h0
          ((unrAt_iff χ _).2 (hT _ (good _ h0).2.1 _ _ (GlobalTheory.HeckeComp.smooth_loc χ _) h)))
  obtain ⟨μ, hμ, hχθ⟩ : ∃ μ, IsUnram μ ∧ χ.loc v = θ * μ :=
    ⟨χ.loc v * θ⁻¹, hχv, by rw [mul_comm (χ.loc v), mul_inv_cancel_left]⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂˣ, a = μ (unif (v.adicCompletion K)) := ⟨_, rfl⟩
  have eL : ∀ j, pol (rK j v) 1 = (pol s (θ * (η ^ j).loc v)).comp (C (a : ℂ) * X) := fun j => by
    rw [(hrK j v).2.1, (htK v).2.1, (FK v).2.1 _ _ (hsK v) hs, ha, ← ((polFacts _).2.2.2 s _).2.2.2 μ hμ, hχθ, mul_one,
      mul_right_comm]
  have eR : ∀ w : PlacesOver L v, (pol (tM w.1) 1).comp (X ^ fdeg w) =
      ((pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w)).comp (C (a : ℂ) * X) := fun w => by
    obtain ⟨n1, n2⟩ := (normVal K L v w μ).1 hμ
    have e0 : pol (tM w.1) 1 = (pol (s' w) (θ.comp (nm w))).comp (C ((a : ℂ) ^ fdeg w) * X) := by
      have e1 : (θ * μ).comp (nm w) = θ.comp (nm w) * μ.comp (nm w) := rfl
      have e2 : (((μ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ) = (a : ℂ) ^ fdeg w := by
        rw [MonoidHom.comp_apply, n2, ← ha, Units.val_pow_eq_pow_val]
      rw [(htM w.1).2.1, (hξ v w).1, (FM w.1).2.1 _ _ (hsM w.1) (hs' w), mul_one, hχθ, e1,
        ((polFacts _).2.2.2 _ _).2.2.2 _ n1, e2]
    rw [e0, comp_assoc, comp_assoc]
    congr 1
    simp [mul_pow]
  refine comp_cancel a.ne_zero ?_
  rw [Polynomial.prod_comp, Polynomial.prod_comp, Finset.prod_congr rfl fun j _ => (eL j).symm,
    Finset.prod_congr rfl fun w _ => (eR w).symm]
  exact main

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
