import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemLevelOfLocalDepth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOutRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TInVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCompOfEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedOfSplitDistinctCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCompEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocSubD

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem compD :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w → ∀ W : Sig.Lev (Kw w),
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ (g * x) = φ g) →
        ∀ ψ : Fin n → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w W ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw W φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, _root_.UpperTheory.V.Z.Sym.W.local_sub_d_statement H _ n W ψ hψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap W _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap W ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap W ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _
private theorem mem_level_of_local_depth {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S₀ S : Finset (Plc L)} {c : ℕ}
    (hS : Places ((S₀ : Set (Plc L)) ∪ S)) (hd : Disjoint S₀ S) {w : Plc L} (hw : w ∈ S₀) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (deep c w).J n) : x ∈ lev (lev (Kall L n) S₀ (deep c)) S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (deep c w)).2.2.2.2.2 n).2.2.2 hJ
  have key : ∀ w' ∈ (S₀ : Set (Plc L)) ∪ S, w' ≠ w → cLoc w' x = 1 := fun w' hw' e => by
    have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' (Or.inl hw) h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    exact MonoidHom.mem_ker.1 (this w' rfl)
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨⟨hk, fun w' hw' => ?_⟩, fun w' hw' => ?_⟩
  · by_cases e : w' = w
    · subst e; exact hJ
    · rw [Subgroup.mem_comap, key w' (Or.inl hw') e]
      exact one_mem _
  · rw [Subgroup.mem_comap, key w' (Or.inr hw') fun e => Finset.disjoint_left.1 hd hw (e ▸ hw')]
    exact one_mem _
private theorem outW :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ (S₀ : Finset (Plc L)) (c : ℕ) (U : Subgroup (UA L n)), U = lev (Kall L n) S₀ (deep c) → IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
          ∀ S : Finset (Plc L), Places ((S₀ : Set (Plc L)) ∪ S) → Disjoint S₀ S → Places (S : Set (Plc L)) → (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
          ∀ (ψ : ∀ w : Plc L, Fin n → (Kw w)ˣ →* ℂˣ) (φ : UA L n → V), φ ≠ 0 → IsAF R (lev U S iw) φ →
          (∀ w ∈ S, (∀ i, ∀ u ∈ UpperTheory.V.Hi.Uo (Kw w), ψ w i u = 1) ∧ (∀ i i', i ≠ i' → ψ w i ≠ ψ w i' ∧ ψ w i ≠ ψ w i' * absPow (Kw w) 1) ∧
            EigT φ w (iw w) (ψ w)) → (∀ w ∈ S₀, (∀ i, IsSmoothChar (ψ w i)) ∧ EigT φ w (deep c w) (ψ w)) →
          ∃ σ ∈ A, (∀ w ∈ S₀, CompSub σ w (ψ w)) ∧ ∀ w ∈ S, CompSub σ w (ψ w) := by
  intro H L _ _ _ unr n hn V _ _ _ R hR S₀ c U eU hU
  obtain ⟨A, hA, hA', h⟩ := UpperTheory.V.Z.Sym.U.finFamU L n V R hR U hU
  refine ⟨A, hA, hA', fun S hP hd hS hK ψ φ h0 hφ hψ hψ0 => ?_⟩
  obtain ⟨π, φ₁, hπ, h1, hφ₁, hc, he⟩ := proj L n V R hR _ ((cof L n).2.2.1 U hU S iw) φ h0 hφ
  have hcs : ∀ w ∈ S, CompSub π w (ψ w) := fun w hw =>
    _root_.UpperTheory.V.Z.Sym.Al.comp_sub_of_eigen_vector_fixed_by_j H L unr n hn V π hπ w (hS.split w hw) φ₁ h1 hc (fun x hx hJ => hφ₁.level x (mem_lev hS hK hw hx hJ)) (ψ w)
      (fun i => (unrSmooth _).1 _ ((hψ w hw).1 i)) fun d hd => he _ _ _ _ ((hψ w hw).2.2 d hd)
  have hc0 : ∀ w ∈ S₀, CompSub π w (ψ w) := fun w hw =>
    compD H L unr n hn V π hπ w (hP.split w (Or.inl hw)) (deep c w) φ₁ h1 hc
      (fun x hx hJ => hφ₁.level x (eU ▸ mem_level_of_local_depth hP hd hw hx hJ)) (ψ w) (hψ0 w hw).1 fun d hd => he _ _ _ _ ((hψ0 w hw).2 d hd)
  obtain ⟨φ₂, h2, hc2, hφ₂⟩ := raise L n V R π hπ U hU.1 S hS
    (fun w hw => ⟨hK w hw, _root_.UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters H L n π w (ψ w) (hS.split w hw) (hcs w hw) (hψ w hw).1 (hψ w hw).2.1⟩) iw φ₁ h1 hc hφ₁
  obtain ⟨σ, hσ, ht⟩ := h π hπ φ₂ h2 hφ₂ hc2
  refine ⟨σ, hσ, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨a, τ, b, c⟩ := hc0 w hw
    exact ⟨a, τ, ht w τ b, c⟩
  · obtain ⟨a, τ, b, c⟩ := hcs w hw
    exact ⟨a, τ, ht w τ b, c⟩
private theorem smo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ : Fin 2 → kˣ →* ℂˣ}
    (h : ∀ i, IsSmoothChar (ψ i)) : ∀ i, IsSmoothChar ((![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹] : Fin 3 → kˣ →* ℂˣ) i) := by
  have h1 : IsSmoothChar (ψ 0 / ψ 1) := by
    rw [div_eq_mul_inv]
    exact (h 0).mul (h 1).inv
  intro i
  fin_cases i
  · exact h1
  · have := h1.mul h1.inv
    rwa [mul_inv_cancel] at this
  · exact h1.inv
private theorem unram_of {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) (h : ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ lev (Kall L n) S V, RU L n u φ = φ) (w : Plc L)
    (hw : ∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : IsUnramU σ w := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨φ, h1, h2, fun x hx hK => h3 x ?_⟩
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨((factor L n w).2.2.2.2.1 x hx).2 hK, fun w' hw' => ?_⟩
  have := (factor L n w').2.2.1 w (hw w' hw').symm hx
  simp only [away, Subgroup.mem_iInf] at this
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
  exact one_mem _
private theorem pigeon {X I : Type} (A : Set X) (hA : A.Finite) (P : X → I → Prop)
    (h : ∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) : ∃ x ∈ A, ∀ i, P x i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf using fun x : A => hn x.1 x.2
  haveI := hA.fintype
  obtain ⟨x, hx, h1⟩ := h (Finset.univ.image f)
  exact hf ⟨x, hx⟩ (h1 _ (Finset.mem_image_of_mem f (Finset.mem_univ _)))
theorem UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Sym.W.SpecOutS → UpperTheory.V.Z.Sym.W.AdLiftW := by
  classical
  intro H hS L _ _ _ unr S₀ P hdis hpl htwo π hπ j hj hwt hunr ψ hψ hP
  have mono : ∀ {T : Set (Plc L)}, T ⊆ (S₀ : Set (Plc L)) ∪ P → Places T := fun h =>
    ⟨fun w hw => hpl.split w (h hw), hpl.inj.mono h⟩
  obtain ⟨c₀, hc₀⟩ := hS L unr S₀ (mono Set.subset_union_left) htwo j hj
  have hd : ∀ p : S₀ × Fin 2, ∃ c₁ : ℕ, ∀ c ≥ c₁, ∀ u ∈ UpperTheory.V.Hi.Uc (Kw p.1.1) (c + 1), ψ p.1.1 p.2 u = 1 := fun p =>
    smoothDepth _ _ ((hψ p.1.1 (Or.inl p.1.2)).1 p.2)
  choose c₁ hc₁ using hd
  obtain ⟨c, hc, hc'⟩ : ∃ c, c₀ ≤ c ∧ ∀ p, c₁ p ≤ c :=
    ⟨max c₀ (Finset.univ.sup c₁), le_max_left _ _, fun p => (Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _)⟩
  obtain ⟨U₂, hU₂, hm⟩ := hc₀ c hc
  obtain ⟨⟨f3, c3⟩, -⟩ := contE (InfinitePlace L) j
  obtain ⟨-, f2, c2⟩ := contE (InfinitePlace L) (2 * j + 1)
  have hU₃ : IsLevel (lev (Kall L 3) S₀ (deep c)) := (cof L 3).2.2.1 _ (cof L 3).2.1 _ _
  obtain ⟨A₃, hA₃, hA₃', h₃⟩ := outW H L unr 3 (by norm_num) _ _ c3 S₀ c _ rfl hU₃
  obtain ⟨A₂, hA₂, hA₂', h₂⟩ := _root_.UpperTheory.V.Z.Sym.Al.outRep_alt H L unr 2 (by norm_num) _ _ (c2 0) _ hU₂
  let Gd : Plc L → Prop := fun w => locU 2 w ⊓ Kall L 2 ≤ U₂ ∧ locU 3 w ⊓ Kall L 3 ≤ lev (Kall L 3) S₀ (deep c)
  have hG : ∀ᶠ w in Filter.cofinite, Gd w := ((cof L 2).2.2.2 _ hU₂).and ((cof L 3).2.2.2 _ hU₃)
  let Q : Submodule ℂ (UA L 3 → ℂ) ⊕ Submodule ℂ (UA L 2 → ℂ) → Plc L → Prop := fun x w =>
    x.elim (fun σ => CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹])
      fun σ => ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2
  obtain ⟨x, hx, hQ⟩ := pigeon (I := {w // w ∈ P ∧ Gd w}) (Sum.inl '' {σ ∈ A₃ | ∀ w ∈ S₀, CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]} ∪ Sum.inr '' A₂) (((hA₃.subset (Set.sep_subset _ _)).image _).union (hA₂.image _))
    (fun x w => Q x w.1) fun S => by
      let S₁ : Finset (Plc L) := S.image Subtype.val
      have h1 : ∀ w ∈ S₁, w ∈ P ∧ Gd w := fun w hw => by
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hw
        exact y.2
      have hn : ∀ w ∈ S₁, w ∉ S₀ := fun w hw h => Set.disjoint_left.1 hdis h (h1 w hw).1
      have hsub : ((S₀ : Set (Plc L)) ∪ S₁) ⊆ (S₀ : Set (Plc L)) ∪ P := Set.union_subset_union_right _ fun w hw => (h1 w hw).1
      have hp1 : Places (S₁ : Set (Plc L)) := mono fun w hw => Or.inr (h1 w hw).1
      let W : ∀ w : Plc L, Sig.Lev (Kw w) := fun w => if w ∈ S₀ then deep c w else iw w
      have W0 : ∀ w ∈ S₀, W w = deep c w := fun w hw => if_pos hw
      have W1 : ∀ w ∈ S₁, W w = iw w := fun w hw => if_neg (hn w hw)
      obtain ⟨e, φ, h0, hAF, hE⟩ := _root_.UpperTheory.V.Z.Sym.Al.inVec_alt H L π hπ j hwt (S₀ ∪ S₁) (by rw [Finset.coe_union]; exact mono hsub)
        (fun w hw => hunr w fun w' hw' => hw w' (Finset.mem_union_left _ hw')) W ψ fun w hw => by
          rcases Finset.mem_union.1 hw with hw | hw
          · exact ⟨hψ w (Or.inl hw), fun i => by rw [W0 w hw]; exact hc₁ (⟨w, hw⟩, i) c (hc' _)⟩
          · exact ⟨hψ w (Or.inr (h1 w hw).1), fun i => by rw [W1 w hw]; exact (hP w (h1 w hw).1).1 i⟩
      have hle : lev (lev (Kall L 2) S₀ (deep c)) S₁ iw ≤ lev (Kall L 2) (S₀ ∪ S₁) W := by
        intro u hu
        simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf] at hu ⊢
        refine ⟨hu.1.1, fun w hw => ?_⟩
        rcases Finset.mem_union.1 hw with hw | hw
        · rw [W0 w hw]; exact hu.1.2 w hw
        · rw [W1 w hw]; exact hu.2 w hw
      rcases hm S₁ (Finset.disjoint_right.2 hn) (mono hsub) (fun w hw => (h1 w hw).2.1) (fun w => ψ w 0 / ψ w 1) e φ h0
        ⟨hAF.left, hAF.inf, fun u hu => hAF.level u (hle hu)⟩
        (fun w hw => eigTS L _ φ w _ _ (W0 w hw ▸ hE w (Finset.mem_union_left _ hw)))
        (fun w hw => eigTS L _ φ w _ _ (W1 w hw ▸ hE w (Finset.mem_union_right _ hw))) with ⟨φ', a0, a1, a3, a2⟩ | ⟨φ', a0, a1, a2⟩
      · obtain ⟨σ, hσ, hs0, hs⟩ := h₃ S₁ (mono hsub) (Finset.disjoint_right.2 hn) hp1 (fun w hw => (h1 w hw).2.2) (fun w => ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) φ' a0 a1
          (fun w hw => ⟨(regUnl _ _ (hP w (h1 w hw).1).2).1.1, (regUnl _ _ (hP w (h1 w hw).1).2).1.2, a2 w hw⟩)
          fun w hw => ⟨smo (hψ w (Or.inl hw)).1, a3 w hw⟩
        exact ⟨.inl σ, Or.inl ⟨σ, ⟨hσ, hs0⟩, rfl⟩, fun i hi => hs i.1 (Finset.mem_image_of_mem _ hi)⟩
      · obtain ⟨φ'', ψ', b0, b1, b2⟩ := UpperTheory.V.Z.Sym.Al.refine L _ _ U₂ hU₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) _ φ' a0 a1 a2
        obtain ⟨σ, hσ, hs⟩ := h₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) ψ' φ'' b0 b1
          fun w hw => ⟨(b2 w hw).1, (regUnl _ _ (hP w (h1 w hw).1).2).2 _ (b2 w hw).2.1, (b2 w hw).2.2⟩
        exact ⟨.inr σ, Or.inr ⟨σ, hσ, rfl⟩, fun i hi =>
          ⟨ψ' i.1, hs i.1 (Finset.mem_image_of_mem _ hi), (b2 i.1 (Finset.mem_image_of_mem _ hi)).2.1⟩⟩
  rcases hx with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · exact Or.inl ⟨σ, (hA₃' σ hσ.1).1, unram_of _ _ _ (hA₃' σ hσ.1).2, hσ.2, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
  · exact Or.inr ⟨σ, hA₂' σ hσ, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
end
