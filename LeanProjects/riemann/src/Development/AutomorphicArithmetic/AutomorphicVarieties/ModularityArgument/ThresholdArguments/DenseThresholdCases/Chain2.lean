import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SuppMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainSeedRes

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)
theorem UpperTheory.V.Ws.deep_tower_residue_chain_exists :
    CohomologyHyp → _root_.UpperTheory.V.Ws.SeedIIAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx2 D → T₀.Ok → T₀.Two → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hP hS Ω _ _ _ l _ c D T₀ hC hO hT hL ι 𝔞 c₀ hc₀
  have hG : D.Good := hC.1
  have hF : T₀.Fit := ⟨hO, Or.inl ⟨hC, hT⟩⟩
  have ha : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hrt := (Chain.rtFacts D hG T₀ hO _ _ ha).1
  obtain ⟨s₀, hs₀, ho₀⟩ := Chain.exists_residual_datum_over_restriction_to_rationals hP D T₀ hF _ _ ha c₀ hc₀.res ⟨hc₀.supp, fun _ => hc₀.flag⟩
  have hq₀ := goodQ D hG T₀ hF _ _ ha _ c₀ s₀ hc₀ hrt ho₀ hs₀
  obtain ⟨W, s, -, -, hW, hs, -, hsQ, -, hsP, -, -, hsA⟩ :=
    gysinAl hP D T₀ hF _ _ ha ∅ (by simp) s₀ s₀ hs₀ hs₀ (hq₀ ∅).2.1 (hq₀ ∅).2.1
  obtain ⟨T₁, h01, hL1, hD⟩ := diesEx D hG T₀ hL hO W hW
  refine ⟨T₁, h01, hL1, fun T h1 hdeep => ?_⟩
  have h0 : T₀.Le T := (leFit D hG T₀ T₁ h01).2.2.2.2.2.2 T h1
  obtain ⟨lO, lT, -, -, lF, -⟩ := leFit D hG T₀ T h0
  have tO := lO hO
  have tT := lT hT
  have tF := lF hF
  have hDT : ∀ w ∈ W, Dies l w T.F := fun w hw θ h1' h2 =>
    (IntermediateField.fixingSubgroup_antitone h1.le).trans (hD w hw θ h1' h2)
  obtain ⟨c₁, h, Q, hQ, hQV, hQE⟩ := hS Ω l c D T hC tO tT hdeep ι
  refine ⟨c₁, h, Q, hQ, fun c₀' ho hr => ?_⟩
  obtain ⟨sR, sV, sE⟩ := _root_.UpperTheory.V.Ws.Chain.isRes_map_red_and_inV_ent_map_red_of_map_residue D T ι 𝔞 h Q hQ
  have sV := sV hQV
  obtain ⟨c₃, r₃, o₃⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s hs (Or.inr (Or.inl hsQ.1))
  obtain ⟨t, rt, ot⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s₀ (hq₀ W).1 (Or.inr (Or.inr hs₀))
  have hsP' : s.In nP := ⟨fun g => supp_mono (by decide) (hsQ.1 g), hsQ.2⟩
  have hsM : Supp nM s.r := fun g => supp_mono (by decide) (hsQ.1 g)
  obtain ⟨-, f2, f3, f4, -, -, f7, -⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s s₀ c₃ t hs (hq₀ W).1 r₃ rt o₃ ot
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s₀ s t c₃ (hq₀ W).1 hs rt r₃ ot o₃
  obtain rfl : c₀' = t := g8 c₀ _ hc₀.res.pair ho₀ c₀' hr ho
  have q₃ : Supp qQ c₃.r := f2 _ hsQ.1
  have i₃ : c₃.In nP := f3 hsP'
  have m₃ : Supp nM c₃.r := f2 _ hsM
  have p₃ : c₃.SamePs c₀' := f4 hsP' (hq₀ W).2.1 hsP
  have a₃ : Ent c₃.r (-wAl) := (f7 hsM).1 hsA
  obtain ⟨-, i₀, g₀⟩ := goodQ D hG T tF _ _ ha (resQ T₀.F T₀.g0) c₀ c₀' (h0.pr ▸ hc₀) (h0.pr ▸ hrt) ho hr ∅
  have ok : (T.fr ∅).Ok (𝔞.red c) := (std hP D T tF ∅ c le_rfl).2 _ _ ha
  have hmu : ∀ v, ∀ s ∈ (T.fr ∅).Mu v, s ∈ (T.fr ∅).Gv v := fun v s hs => hs.1
  have hrb := (Chain.rtFacts D hG T tO _ _ ha).2
  obtain ⟨c₄', r₄', u₄', n₄', e₄'⟩ := Chain.levi (T.fr ∅) _ hmu c₃ r₃ m₃
  obtain ⟨c₄, r₄, e₄, n₄⟩ := Chain.movePs (T.fr ∅) _ ok.mul hmu
    (fun v s hs => (hrb _ _).2 (tT.atL _ (T.ovl v) s hs)) c₄' r₄' u₄' n₄' fun v => (Q.map (𝔞.red c₁)).n v 2 0
  have u₄ : Supp {-wAl} c₄.r := e₄ ▸ u₄'
  have m₄ : Supp nM c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have v₄ : Supp vV c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have al : c₃.SameAl c₄ := ⟨fun g => by rw [e₄, e₄'.1], fun v => ((n₄ v).2.1.trans (e₄'.2 v)).symm⟩
  have a₄ : Ent c₄.r (-wAl) := by
    obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).2 m₃).1 a₃
    exact ((Chain.entIff (T.fr ∅) (𝔞.red c) c₄ r₄).2 m₄).2 ⟨g, al.1 g ▸ hg⟩
  have G₀ : (T.fr ∅).Good (𝔞.red c) c₀' := g₀.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have G₃ : (T.fr ∅).Good (𝔞.red c) c₃ := by
    by_cases hp : Ent c₃.r (-wPs)
    · exact Or.inl ⟨hp, Or.inr a₃⟩
    rcases g₀ with x | x
    · obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₀' hr).1 i₀.1).1 x.1
      exact absurd (((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).1 i₃.1).2 ⟨g, p₃.1 g ▸ hg⟩) hp
    refine Or.inr (Or.inr (Or.inl ⟨⟨fun g i j hij hw => ?_, fun v => ⟨i₃.2 v, p₃.2 v ▸ (x.1.2 v).2⟩⟩, a₃⟩))
    by_cases hq : wt i j = -wPs
    · by_contra hne
      exact hp ⟨g, i, j, hq, hne⟩
    · exact q₃ g i j hij (by revert hw hq; revert i j; decide)
  have G₄ : (T.fr ∅).Good (𝔞.red c) c₄ :=
    Or.inr (Or.inr (Or.inl ⟨⟨v₄, fun v => ⟨(n₄ v).1, (n₄ v).2.2 ▸ (sV.2 v).2⟩⟩, a₄⟩))
  have Gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := by
    rcases hQE with x | x
    · exact Or.inr (Or.inr (Or.inl ⟨sV, sE _ x⟩))
    refine Or.inr (Or.inr (Or.inr ⟨sV, sE _ x.1, sE _ x.2, fun v => ?_⟩))
    obtain ⟨g, hg, hne⟩ := tT.bigL _ (T.ovl v)
    exact ⟨g, hg, fun h1 => hne (by rw [(hrb _ _).1 h1, one_pow])⟩
  have L₁ := lineP (T.fr ∅) _ ok c₀' c₃ hr r₃ i₀ i₃ ⟨fun g => (p₃.1 g).symm, fun v => (p₃.2 v).symm⟩
  have L₂ := lineM (T.fr ∅) _ ok c₃ c₄ r₃ r₄ m₃ m₄ al
  have L₃ := lineP (T.fr ∅) _ ok c₄ _ r₄ sR ⟨fun g => supp_mono (by decide) (v₄ g), fun v => (n₄ v).1⟩
    ⟨fun g => supp_mono (by decide) (sV.1 g), fun v => (sV.2 v).1⟩
    ⟨fun g => (v₄ g 2 0 (by decide) (by decide)).trans (sV.1 g 2 0 (by decide) (by decide)).symm, fun v => (n₄ v).2.2⟩
  exact ⟨G₀, ((Relation.ReflTransGen.single ⟨G₃, L₁⟩).tail ⟨G₄, L₂⟩).tail ⟨Gs, L₃⟩⟩
end
