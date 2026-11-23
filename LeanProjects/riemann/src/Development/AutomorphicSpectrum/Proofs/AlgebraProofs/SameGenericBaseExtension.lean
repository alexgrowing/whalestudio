import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPull
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChain
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullPreserve
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XRelabelBundle
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.CkPullBirat

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Numbers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {S : Type} (cls : S → K → ℤ)
    (H : MvPolynomial S ℤ) {Q Q' : List (K → ℤ)} (p : Q.Perm Q') (W : Ideal (MRing ι O)) :
    classNum cls H Q W = classNum cls H Q' W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [PairNumberRelabel.vNumL_perm W (p.append_left _)]

theorem classList_map_perm {K₁ K₂ : Type} {S : Type} (cls : S → K₂ → ℤ) (e : K₁ → K₂)
    (μ : S →₀ ℕ) :
    ((classList cls μ).map (· ∘ e)).Perm (classList (fun s => cls s ∘ e) μ) := by
  rw [← Multiset.coe_eq_coe]
  unfold classList
  rw [← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, Multiset.map_map]
  rfl

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

theorem pairNum_relabel (hσ : ∀ v, (σ v).1 = e v.1) (P : Ideal (MRing ι₁ O)) {n : ℕ}
    (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
    (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) {S : Type} (cls : S → K₂ → ℤ) (μ : S →₀ ℕ) :
    pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs
        (classList cls μ) =
      pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs
        (classList (fun s => cls s ∘ e) μ) := by
  rw [PairNumberRelabel.map_rename_eq, PairNumberRelabel.pairNum_map e σ hσ]
  unfold pairNum
  simp only [classNum_perm _ _ (classList_map_perm cls e μ)]

theorem rootTerm_relabel (hσ : ∀ v, (σ v).1 = e v.1) (P : Ideal (MRing ι₁ O)) {n : ℕ}
    (x : Fin n → K₂ → ℤ) (G : MvPolynomial (Fin n) ℤ) {S : Type} (cls : S → K₂ → ℤ)
    (μ : S →₀ ℕ) (a : O) :
    cycEval (fun W => classNum x G (classList cls μ) W) (divCycle (P.map (rename σ)) (C a)) =
      cycEval (fun W => classNum (fun i => x i ∘ e) G (classList (fun s => cls s ∘ e) μ) W)
        (divCycle P (C a)) := by
  rw [PairNumberRelabel.map_rename_eq]
  unfold cycEval
  rw [← finsum_comp_equiv (PairNumberRelabel.idealEquiv (R := O) σ)]
  refine finsum_congr fun W => ?_
  rw [PairNumberRelabel.idealEquiv_apply, ← rename_C σ a, PairNumberRelabel.divCycle_map σ e hσ]
  beta_reduce
  rw [PairNumberRelabel.classNum_map e σ hσ, classNum_perm _ _ (classList_map_perm cls e μ)]

end Numbers

section Assoc

variable {K K' K₁ : Type} (ι : K → Type) (ι' : K' → Type) (ι₁ : K₁ → Type)

def assocEquiv : (Σ k : (K ⊕ K') ⊕ K₁, Sum.elim (Sum.elim ι ι') ι₁ k) ≃
    (Σ k : K ⊕ (K' ⊕ K₁), Sum.elim ι (Sum.elim ι' ι₁) k) where
  toFun
    | ⟨.inl (.inl k), i⟩ => ⟨.inl k, i⟩
    | ⟨.inl (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
    | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl (.inl k), i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inl (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr k, i⟩
  left_inv := by rintro ⟨(k | k) | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | k | k, i⟩ <;> rfl

theorem assocEquiv_fst (v) : (assocEquiv ι ι' ι₁ v).1 = Equiv.sumAssoc K K' K₁ v.1 := by
  obtain ⟨(k | k) | k, i⟩ := v <;> rfl

variable {ι ι' ι₁}

theorem join_assoc {Ω : Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (z₁ : (Σ k, ι₁ k) → Ω) :
    joinCoord x (joinCoord z z₁) ∘ assocEquiv ι ι' ι₁ = joinCoord (joinCoord x z) z₁ := by
  funext v
  obtain ⟨(k | k) | k, i⟩ := v <;> rfl

theorem pullDeg_assoc (a : K → ℤ) :
    pullDeg (K' := K' ⊕ K₁) a ∘ Equiv.sumAssoc K K' K₁ =
      pullDeg (K' := K₁) (pullDeg (K' := K') a) := by
  funext k
  obtain (k | k) | k := k <;> rfl

def assocChart (s : ∀ k : K ⊕ (K' ⊕ K₁), Sum.elim ι (Sum.elim ι' ι₁) k) :
    ∀ k : (K ⊕ K') ⊕ K₁, Sum.elim (Sum.elim ι ι') ι₁ k
  | .inl (.inl k) => s (.inl k)
  | .inl (.inr k) => s (.inr (.inl k))
  | .inr k => s (.inr (.inr k))

theorem assocChart_spec (s : ∀ k : K ⊕ (K' ⊕ K₁), Sum.elim ι (Sum.elim ι' ι₁) k) (k) :
    assocEquiv ι ι' ι₁ ⟨k, assocChart s k⟩ =
      ⟨Equiv.sumAssoc K K' K₁ k, s (Equiv.sumAssoc K K' K₁ k)⟩ := by
  obtain (k | k) | k := k <;> rfl

end Assoc

theorem closure_closure {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {V : Type}
    [AddCommGroup V] [Module Ω V] (R R' : Subalgebra O Ω) (h : R ≤ R') (L : AddSubgroup V) :
    AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e},
      v = a • e} = AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ L, v = a • e} := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro v ⟨a, ha, e, he, rfl⟩
    refine PositivityTheory.Xgn.A_pull_preserve.smul_mem R' L a ha e (AddSubgroup.closure_mono ?_ he)
    rintro v ⟨b, hb, e, he, rfl⟩
    exact ⟨b, h hb, e, he, rfl⟩
  · apply AddSubgroup.closure_mono
    rintro v ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, AddSubgroup.subset_closure ⟨1, one_mem _, e, he, (one_smul _ _).symm⟩, rfl⟩

theorem relabel {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K₁ : Type} [Fintype K₁]
    [DecidableEq K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {K₂ : Type} [Fintype K₂]
    [DecidableEq K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    (y₁ : (Σ k, ι₁ k) → Ω) (hy : y ∘ σ = y₁) :
    pointIdeal O y = (pointIdeal O y₁).map (rename σ) ∧ fnField O y = fnField O y₁ ∧
    (∀ (s₁ : ∀ k, ι₁ k) (s₂ : ∀ k, ι₂ k), (∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) →
      mseg y s₂ = mseg y₁ s₁ ∧ chartRing O (mseg y) s₂ = chartRing O (mseg y₁) s₁) ∧
    ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E₁ : ChartBundle O (mseg y₁) N V),
      ∃ E₂ : ChartBundle O (mseg y) N V,
        (∀ (s₁ : ∀ k, ι₁ k) (s₂ : ∀ k, ι₂ k), (∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) →
          E₂.lat s₂ = E₁.lat s₁) ∧
        ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K₂ → ℤ),
          IsFlagFrame y₁ E₁ w (fun i => b i ∘ e) → IsFlagFrame y E₂ w b := by
  subst hy
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.Xgn.t_relabel_bundle O Ω K₁ ι₁ K₂ ι₂ e σ hσ y
  exact ⟨h1, h2, fun s₁ s₂ hs => ⟨PositivityTheory.Xgn.A_relabel_bundle.mseg_eq e σ y hs,
    PositivityTheory.Xgn.A_relabel_bundle.chartRing_eq O e σ hσ y hs⟩, h3⟩

theorem pull_pull {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type}
    [Field Ω] [Algebra O Ω] {K K' K₁ : Type} [Fintype K] [Fintype K'] [Fintype K₁]
    {ι : K → Type} {ι' : K' → Type} {ι₁ : K₁ → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    [∀ k, Fintype (ι₁ k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (z₁ : (Σ k, ι₁ k) → Ω)
    {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V)
    (EB : ChartBundle O (mseg (joinCoord x z)) N V)
    (E₁ : ChartBundle O (mseg (joinCoord (joinCoord x z) z₁)) N V)
    (E₂ : ChartBundle O (mseg (joinCoord x (joinCoord z z₁))) N V)
    (hp : IsPull O x z E EB) (hp₁ : IsPull O (joinCoord x z) z₁ EB E₁)
    (hc : ∀ s, mseg (joinCoord x (joinCoord z z₁)) s =
        mseg (joinCoord (joinCoord x z) z₁) (assocChart s) ∧
      chartRing O (mseg (joinCoord x (joinCoord z z₁))) s =
        chartRing O (mseg (joinCoord (joinCoord x z) z₁)) (assocChart s))
    (hl : ∀ s, E₂.lat s = E₁.lat (assocChart s)) :
    IsPull O x (joinCoord z z₁) E E₂ := by
  intro s hs
  have hs₁ : mseg (joinCoord (joinCoord x z) z₁) (assocChart s) ≠ 0 := (hc s).1 ▸ hs
  have hs₀ := PositivityTheory.Xgn.A_pull_preserve.below_ne _ _ _ hs₁
  rw [hl s, hp₁ _ hs₁, hp _ hs₀, (hc s).2,
    closure_closure _ _ (JoinPullbackAlt.chartRing_le_join O _ _ _ hs₁)]
  rfl

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O (joinCoord x z) d N EB E'B k (fun j => pullDeg (K' := K') (L j)) Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O (joinCoord x z) d N EB G (fun j => pullDeg (K' := K') (L j)) Q a = rootNum O x d N E G L Q a) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hsB : SameGeneric O (joinCoord x z) EB E'B :=
    (PositivityTheory.Xgn.t_pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hp hp').2.1 hEE'
  have hself : SameGeneric O (joinCoord x z) EB EB := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
      fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  obtain ⟨K₁, _, _, ι₁, _, z₁, F, w, b, hm₁, hb₁, hF⟩ :=
    GlobalTheory.CompanionTheory.Ar.CommonFlag.main O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hm N 1 V ![EB, E'B]
      (Fin.forall_fin_two.2 ⟨hself, hsB⟩)
  have hq : IsPull O (joinCoord x z) z₁ EB (F 0) := (hF 0).1
  have hq' : IsPull O (joinCoord x z) z₁ E'B (F 1) := (hF 1).1
  have hM₁ : IsModelOver (pointIdeal O (joinCoord (joinCoord x z) z₁)) d :=
    ((BundleExamples.isModelOver_iff O _ d).mp hm₁).2
  have hs₁ : SameGeneric O (joinCoord (joinCoord x z) z₁) (F 0) (F 1) :=
    (PositivityTheory.Xgn.t_pull_preserve O Ω _ _ _ N V EB E'B K₁ ι₁ z₁ (F 0) (F 1) hq hq').2.1 hsB
  obtain ⟨b₂, rfl⟩ : ∃ b₂ : Fin 2 → Fin N → K ⊕ (K' ⊕ K₁) → ℤ,
      b = fun j i => b₂ j i ∘ Equiv.sumAssoc K K' K₁ :=
    ⟨fun j i => b j i ∘ (Equiv.sumAssoc K K' K₁).symm, by
      funext j i k
      simp⟩
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω _ _ (joinCoord (joinCoord x z) z₁)
    ϖ hϖ d hM₁ N V (F 0) (F 1) hs₁ w w _ _ (hF 0).2 (hF 1).2 (fun i j hij => by
      simp [Finsupp.single_apply, hij.ne])
  have hσ := assocEquiv_fst ι ι' ι₁
  obtain ⟨hI, hK, hc, hE⟩ := relabel (O := O) (Equiv.sumAssoc K K' K₁) (assocEquiv ι ι' ι₁) hσ
    (joinCoord x (joinCoord z z₁)) _ (join_assoc x z z₁)
  obtain ⟨G, hG, hGf⟩ := hE N V (F 0)
  obtain ⟨G', hG', hGf'⟩ := hE N V (F 1)
  have hr : IsPull O x (joinCoord z z₁) E G := pull_pull x z z₁ E EB (F 0) G hp hq
    (fun s => hc _ _ (assocChart_spec s)) (fun s => hG _ _ (assocChart_spec s))
  have hr' : IsPull O x (joinCoord z z₁) E' G' := pull_pull x z z₁ E' E'B (F 1) G' hp' hq'
    (fun s => hc _ _ (assocChart_spec s)) (fun s => hG' _ _ (assocChart_spec s))
  have hM₂ : IsModelOver (pointIdeal O (joinCoord x (joinCoord z z₁))) d := by
    rw [hI]
    exact PairNumberRelabel.isModelOver_map _ _ hσ _ d hM₁
  have hm₂ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
      (mcIdeal O (joinCoord x (joinCoord z z₁))) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hW.1.map Sum.inl, hM₂⟩
  have hfp₂ : IsFlagPair ϖ (joinCoord x (joinCoord z z₁)) G G' w w (b₂ 0) (b₂ 1)
      (fun i => rename (assocEquiv ι ι' ι₁) (f i)) (fun i => rename (assocEquiv ι ι' ι₁) (g i)) := by
    refine ⟨hGf w _ hfp.flag, hGf' w _ hfp.flag', hfp.sameFlag, fun i => ?_, fun i => ?_⟩
    · rw [hI]
      exact PairNumberRelabel.isVerticalDivisor_map _ _ hσ _ ϖ _ _ _ (hfp.vertical i)
    · rw [aeval_rename, aeval_rename, join_assoc]
      exact hfp.generic i
  obtain ⟨A₁, B₁⟩ := GlobalTheory.T.same_generic_flag_difference O Ω _ _ (joinCoord x z) ϖ hϖ d hm N V EB E'B hsB
    K₁ ι₁ z₁ hm₁ hb₁ (F 0) (F 1) hq hq' w w _ _ f g hfp
  obtain ⟨A₂, B₂⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V E E' hEE'
    (K' ⊕ K₁) (Sum.elim ι' ι₁) (joinCoord z z₁) hm₂ (hK.trans (hb₁.trans hb)) G G' hr hr'
    w w _ _ _ _ hfp₂
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c P hsym hP hcd q L Q hQ a ha => ?_⟩
  · rw [A₁ k hk1 hk2 q _ Q hQ, A₂ k hk1 hk2 q L Q hQ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hI, pairNum_relabel _ _ hσ]
    simp only [pullDeg_assoc]
  · rw [B₁ c P hsym hP hcd q _ Q hQ a ha, B₂ c P hsym hP hcd q L Q hQ a ha]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hI, rootTerm_relabel _ _ hσ]
    simp only [pullDeg_assoc]

end GlobalTheory.CompanionTheory.Ar.CkPullBirat
