import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

private theorem twOrb_conj' (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) :
    twOrb θ K (g⁻¹ * δ * θ g) f = twOrb θ K δ f := by
  rw [GlobalTheory.TwOrbConj.twOrb_eq, GlobalTheory.TwOrbConj.twOrb_eq]
  refine (finsum_congr fun q => ?_).trans
    (finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) =>
      GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out q)) (GlobalTheory.TwOrbConj.dcEquiv θ K δ g))
  obtain ⟨t, k, ht, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) K (g * Quotient.out q)
  rw [GlobalTheory.TwOrbConj.summand_twist]
  show _ = GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out (DoubleCoset.mk (twCent θ δ) K (g * Quotient.out q)))
  rw [he, GlobalTheory.TwOrbConj.summand_rep θ K δ f _ ht hk]

private theorem cptPart_map_equiv (e : G ≃* G') (hc : Continuous e) (hc' : Continuous e.symm) (T : Subgroup G) :
    cptPart (T.map e.toMonoidHom) = (cptPart T).map e.toMonoidHom := by
  let h : G ≃ₜ G' := { e.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers (e t) : Set G')) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    have hz : (Subgroup.zpowers (e t) : Set G') = h '' (Subgroup.zpowers t : Set G) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨t ^ m, ⟨m, rfl⟩, by simp [h]⟩
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, by simp [h]⟩
    rw [hz, ← h.image_closure, h.isCompact_image]
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

private theorem twCent_map (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (hθ : ∀ x, e (θ x) = θ' (e x)) (δ : G) :
    twCent θ' (e δ) = (twCent θ δ).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, GlobalTheory.TwOrbConj.mem_twCent, GlobalTheory.TwOrbConj.mem_twCent]
  constructor
  · intro h
    apply e.injective
    simp [map_mul, hθ, h]
  · intro h
    have := congrArg e h
    simpa [map_mul, hθ] using this

private theorem summand_map (e : G ≃* G') (hc : Continuous e) (hc' : Continuous e.symm) (θ : G →* G) (θ' : G' →* G')
    (hθ : ∀ x, e (θ x) = θ' (e x)) (K : Subgroup G) (δ : G) (f : G → ℂ) (f' : G' → ℂ) (hf : ∀ x, f x = f' (e x)) (y : G) :
    GlobalTheory.TwOrbConj.summand θ' (K.map e.toMonoidHom) (e δ) f' (e y) = GlobalTheory.TwOrbConj.summand θ K δ f y := by
  unfold GlobalTheory.TwOrbConj.summand
  congr 1
  · have hconj : (K.map e.toMonoidHom).map (MulAut.conj (e y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext k
      simp [MulAut.conj_apply]
    rw [twCent_map e θ θ' hθ, hconj, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv e hc hc',
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  · refine (GlobalTheory.BCT.OrbProd.avg_comp_equiv (e.subgroupMap K) _).symm.trans (congrArg avg (funext fun k => ?_))
    simp [hf, hθ, map_mul]

private theorem dc_equiv (e : G ≃* G') {T K : Subgroup G} {T' K' : Subgroup G'}
    (hT : T' = T.map e.toMonoidHom) (hK : K' = K.map e.toMonoidHom) :
    ∃ E : DoubleCoset.Quotient (T : Set G) (K : Set G) ≃ DoubleCoset.Quotient (T' : Set G') (K' : Set G'),
      ∀ q, ∃ t ∈ T', ∃ k ∈ K', Quotient.out (E q) = t * e (Quotient.out q) * k := by
  have mT : ∀ x, x ∈ T → e x ∈ T' := fun x hx => hT ▸ ⟨x, hx, rfl⟩
  have mK : ∀ x, x ∈ K → e x ∈ K' := fun x hx => hK ▸ ⟨x, hx, rfl⟩
  have mT' : ∀ x, x ∈ T' → e.symm x ∈ T := fun x hx => by
    rw [hT] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have mK' : ∀ x, x ∈ K' → e.symm x ∈ K := fun x hx => by
    rw [hK] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  let F : DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set G') (K' : Set G') :=
    fun q => DoubleCoset.mk T' K' (e (Quotient.out q))
  have hF : Function.Bijective F := by
    constructor
    · intro q₁ q₂ h
      obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 h
      rw [← DoubleCoset.out_eq' T K q₁, ← DoubleCoset.out_eq' T K q₂, DoubleCoset.eq]
      refine ⟨e.symm t, mT' t ht, e.symm k, mK' k hk, e.injective ?_⟩
      simp [he]
    · intro p
      refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out p))
      show DoubleCoset.mk T' K' (e (Quotient.out (DoubleCoset.mk T K (e.symm (Quotient.out p))))) = p
      rw [he]
      conv_rhs => rw [← DoubleCoset.out_eq' T' K' p]
      rw [DoubleCoset.eq]
      refine ⟨(e a)⁻¹, T'.inv_mem (mT a ha), (e b)⁻¹, K'.inv_mem (mK b hb), ?_⟩
      simp [mul_assoc]
  refine ⟨Equiv.ofBijective F hF, fun q => ?_⟩
  obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul T' K' (e (Quotient.out q))
  exact ⟨a, ha, b, hb, he⟩

private theorem twOrb_map (e : G ≃* G') (hc : Continuous e) (hc' : Continuous e.symm) (θ : G →* G) (θ' : G' →* G')
    (hθ : ∀ x, e (θ x) = θ' (e x)) (K : Subgroup G) (δ : G) (f : G → ℂ) (f' : G' → ℂ) (hf : ∀ x, f x = f' (e x)) :
    twOrb θ K δ f = twOrb θ' (K.map e.toMonoidHom) (e δ) f' := by
  rw [GlobalTheory.TwOrbConj.twOrb_eq, GlobalTheory.TwOrbConj.twOrb_eq]
  obtain ⟨F, hF⟩ := dc_equiv e (twCent_map e θ θ' hθ δ) (K := K) (K' := K.map e.toMonoidHom) rfl
  rw [← finsum_comp_equiv F]
  refine finsum_congr fun q => ?_
  obtain ⟨t, ht, k, hk, he⟩ := hF q
  rw [he, GlobalTheory.TwOrbConj.summand_rep θ' _ _ f' _ ht hk, summand_map e hc hc' θ θ' hθ K δ f f' hf]

private theorem clSum_map (e : G ≃* G') (hc : Continuous e) (hc' : Continuous e.symm) (θ : G →* G) (θ' : G' →* G')
    (hθ : ∀ x, e (θ x) = θ' (e x)) (K : Subgroup G) (S : Set G) (S' : Set G') (hS : ∀ x, x ∈ S ↔ e x ∈ S')
    (hS' : ∀ g x, x ∈ S' → g⁻¹ * x * θ' g ∈ S') (f : G → ℂ) (f' : G' → ℂ) (hf : ∀ x, f x = f' (e x)) :
    clSum θ K S 1 f = clSum θ' (K.map e.toMonoidHom) S' 1 f' := by
  let F' : G' → ℂ := fun x => if x ∈ S' then twOrb θ' (K.map e.toMonoidHom) x f' else 0
  have hF' : ∀ g x, F' (g⁻¹ * x * θ' g) = F' x := by
    intro g x
    have hm : g⁻¹ * x * θ' g ∈ S' ↔ x ∈ S' := by
      refine ⟨fun h => ?_, hS' g x⟩
      have := hS' g⁻¹ _ h
      simpa [mul_assoc] using this
    simp only [F', hm, twOrb_conj']
  let L : TwCl θ' → ℂ := Quot.lift F' (by rintro x y ⟨g, rfl⟩; exact (hF' g x).symm)
  have hL : ∀ c : TwCl θ', L c = F' c.rep := by
    intro c
    conv_lhs => rw [← GlobalTheory.BCT.StTwTens.mkC_rep _ c]
    rfl
  let M : TwCl θ ≃ TwCl θ' :=
    { toFun := Quot.map e (by rintro x y ⟨g, rfl⟩; exact ⟨e g, by simp [hθ]⟩)
      invFun := Quot.map e.symm (by
        rintro x y ⟨g, rfl⟩
        refine ⟨e.symm g, e.injective ?_⟩
        simp [hθ])
      left_inv := fun c => by
        refine Quot.inductionOn c fun x => ?_
        exact congrArg (Quot.mk _) (e.symm_apply_apply x)
      right_inv := fun c => by
        refine Quot.inductionOn c fun x => ?_
        exact congrArg (Quot.mk _) (e.apply_symm_apply x) }
  calc clSum θ K S 1 f = ∑ᶠ c, L (M c) := by
        refine finsum_congr fun c => ?_
        have hM : M c = GlobalTheory.BCT.StTwTens.mkC θ' (e c.rep) := by
          conv_lhs => rw [← GlobalTheory.BCT.StTwTens.mkC_rep _ c]
          rfl
        rw [hM]
        show _ = F' (e c.rep)
        simp only [F', hS, Pi.one_apply, one_mul]
        rw [twOrb_map e hc hc' θ θ' hθ K c.rep f f' hf]
    _ = ∑ᶠ c, L c := finsum_comp_equiv M (f := L)
    _ = clSum θ' (K.map e.toMonoidHom) S' 1 f' := by
        refine finsum_congr fun c => ?_
        rw [hL]
        simp only [F', Pi.one_apply, one_mul]

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem stTw2_swap (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ)
    (φ' : GLw b w × GLw a w → ℂ) (h : ∀ y, φ y = φ' (y.2, y.1)) :
    stTw2 a b w Q₁ Q₂ φ = stTw2 b a w Q₂ Q₁ φ' := by
  have hK : (KGL w b).prod (KGL w a) =
      ((KGL w a).prod (KGL w b)).map (MulEquiv.prodComm : GLw a w × GLw b w ≃* GLw b w × GLw a w).toMonoidHom := by
    ext ⟨x, y⟩
    rw [Subgroup.mem_map_equiv]
    simp [Subgroup.mem_prod, and_comm]
  unfold stTw2
  rw [hK]
  have hc : Continuous (MulEquiv.prodComm : GLw a w × GLw b w ≃* GLw b w × GLw a w) := continuous_swap
  have hc' : Continuous (MulEquiv.prodComm : GLw a w × GLw b w ≃* GLw b w × GLw a w).symm := continuous_swap
  refine clSum_map (MulEquiv.prodComm : GLw a w × GLw b w ≃* GLw b w × GLw a w) hc hc'
    ((thL a w).prodMap (thL b w)) ((thL b w).prodMap (thL a w)) (fun _ => rfl) ((KGL w a).prod (KGL w b))
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂}
    {y | (nrmL b w y.1).val.charpoly = Q₂ ∧ (nrmL a w y.2).val.charpoly = Q₁} (fun x => ?_) ?_ φ φ' h
  · exact and_comm
  · rintro g x ⟨h₁, h₂⟩
    exact ⟨(GlobalTheory.BCT.StTwTens.nrmL_charpoly_twConj b w g.1 x.1).trans h₁,
      (GlobalTheory.BCT.StTwTens.nrmL_charpoly_twConj a w g.2 x.2).trans h₂⟩

private theorem geomSt2_swap {a b : ℕ} (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a)
    (l₂ : InfinitePlace E → DomWeight b) (Φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (Φ' : ∀ w : Pl E, GLw b w × GLw a w → ℂ) (h : ∀ w ∈ S, ∀ y, Φ w y = Φ' w (y.2, y.1)) :
    PositivityTheory.Rg.BcB.G8.geomSt2 S l₁ l₂ Φ = PositivityTheory.Rg.BcB.G8.geomSt2 S l₂ l₁ Φ' := by
  unfold PositivityTheory.Rg.BcB.G8.geomSt2
  refine finsum_mem_eq_of_bijOn Prod.swap ⟨?_, Prod.swap_injective.injOn, ?_⟩ ?_
  · rintro p ⟨h₁, h₂, h₃⟩
    exact ⟨h₂, h₁, h₃.symm⟩
  · rintro p ⟨h₁, h₂, h₃⟩
    exact ⟨p.swap, ⟨h₂, h₁, h₃.symm⟩, Prod.swap_swap p⟩
  · intro p _
    have hP : ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (Φ w) =
        ∏ᶠ w ∈ S, stTw2 b a w (atPl w p.2) (atPl w p.1) (Φ' w) :=
      finprod_mem_congr rfl fun w hw => stTw2_swap a b w _ _ _ _ (h w hw)
    simp only [Prod.fst_swap, Prod.snd_swap, hP]
    ring

private theorem infOfWeight_inj {n : ℕ} {l l' : DomWeight n} (h : infOfWeight l = infOfWeight l') : l = l' := by
  have key : ∀ l : DomWeight n, (infOfWeight l).map Complex.re =
      ((List.ofFn fun k : Fin n => (l.w k : ℝ) + (((n : ℝ) - 1) / 2 - (k : ℕ)) : List ℝ) : Multiset ℝ) := by
    intro l
    unfold infOfWeight
    rw [Multiset.map_map, Fin.univ_val_map]
    congr 2
    funext k
    simp
  have anti : ∀ l : DomWeight n, (List.ofFn fun k : Fin n => (l.w k : ℝ) + (((n : ℝ) - 1) / 2 - (k : ℕ))).Pairwise (· > ·) := by
    intro l
    rw [List.pairwise_ofFn]
    intro i j hij
    have h1 : l.w j ≤ l.w i := l.anti hij.le
    have h2 : (l.w j : ℝ) ≤ l.w i := by exact_mod_cast h1
    have h3 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    show (l.w j : ℝ) + (((n : ℝ) - 1) / 2 - (j : ℕ)) < (l.w i : ℝ) + (((n : ℝ) - 1) / 2 - (i : ℕ))
    linarith
  have hp := Multiset.coe_eq_coe.1 ((key l).symm.trans ((congrArg _ h).trans (key l')))
  have he := List.Perm.eq_of_pairwise (fun a b _ _ (hab : a > b) (hba : b > a) => absurd hab (not_lt.2 hba.le)) (anti l) (anti l') hp
  have hf := List.ofFn_injective he
  cases l with | mk w₁ a₁ => cases l' with | mk w₂ a₂ =>
  have : w₁ = w₂ := by
    funext k
    have := congrFun hf k
    simp only [add_left_inj] at this
    exact_mod_cast this
  subst this
  rfl

private theorem infOfWeight_zero (l : DomWeight 0) : infOfWeight l = 0 := by
  simp [infOfWeight]

private theorem domWeight_zero (l l' : DomWeight 0) : l = l' := by
  cases l
  cases l'
  congr
  exact Subsingleton.elim _ _

private theorem gl_zero_eq_one_alt (w : Pl E) (x : GLw 0 w) : x = 1 := by
  apply Units.ext
  exact Subsingleton.elim _ _

private theorem hint_subsingleton {H : Type} [Group H] [Subsingleton H] (K : Subgroup H) (u : H → ℂ) :
    hint K u = u 1 := by
  unfold hint
  have h1 : rStab u ⊓ K = ⊤ := Subsingleton.elim _ _
  have h2 : (rStab u ⊓ K).relIndex K = 1 := by rw [h1]; simp
  rw [h2]
  haveI : Unique (H ⧸ (rStab u ⊓ K)) := Unique.mk' _
  rw [finsum_unique]
  simp only [Nat.cast_one, inv_one, one_mul]
  exact congrArg u (Subsingleton.elim _ _)

private theorem blk_left (n : ℕ) (w : Pl E) (x : GLw 0 w) (g : GLw n w) (X : Matrix (Fin 0) (Fin n) (w.adicCompletion E)) :
    blk (Nat.zero_add n) w (x, g) X = g := by
  have he : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr (Nat.zero_add n))).symm i = Sum.inr i := by
    intro i
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr (Nat.zero_add n)))
      (finSumFinEquiv.trans (finCongr (Nat.zero_add n))) (Matrix.fromBlocks x.val (x.val * X) 0 g.val) = g.val := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, he, Matrix.fromBlocks_apply₂₂]
  unfold blk
  simp only [hM]
  rw [dif_pos g.isUnit]
  exact Units.ext rfl

private theorem blk_right (n : ℕ) (w : Pl E) (g : GLw n w) (x : GLw 0 w) (X : Matrix (Fin n) (Fin 0) (w.adicCompletion E)) :
    blk (Nat.add_zero n) w (g, x) X = g := by
  have he : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr (Nat.add_zero n))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    show (i : ℕ) = ((finSumFinEquiv (m := n) (n := 0) (Sum.inl i) : Fin (n + 0)) : ℕ)
    rw [finSumFinEquiv_apply_left]
    rfl
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr (Nat.add_zero n)))
      (finSumFinEquiv.trans (finCongr (Nat.add_zero n))) (Matrix.fromBlocks g.val (g.val * X) 0 x.val) = g.val := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, he, Matrix.fromBlocks_apply₁₁]
  unfold blk
  simp only [hM]
  rw [dif_pos g.isUnit]
  exact Units.ext rfl

private theorem ctMu_swap (n : ℕ) (w : Pl E) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (x x' : GLw 0 w)
    (g : GLw n w) : ctMu (Nat.zero_add n) w χ f (x, g) = ctMu (Nat.add_zero n) w χ f (g, x') := by
  obtain rfl := gl_zero_eq_one_alt w x
  obtain rfl := gl_zero_eq_one_alt w x'
  haveI : Subsingleton (Multiplicative (Matrix (Fin 0) (Fin n) (w.adicCompletion E))) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin n) (w.adicCompletion E)))
  haveI : Subsingleton (Multiplicative (Matrix (Fin n) (Fin 0) (w.adicCompletion E))) :=
    inferInstanceAs (Subsingleton (Matrix (Fin n) (Fin 0) (w.adicCompletion E)))
  unfold ctMu ct
  rw [hint_subsingleton, hint_subsingleton]
  simp only [blk_left, blk_right]
  simp

private theorem geomSt2_congr {a b : ℕ} (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a)
    (l₂ : InfinitePlace E → DomWeight b) (Φ Φ' : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (h : ∀ w ∈ S, Φ w = Φ' w) :
    PositivityTheory.Rg.BcB.G8.geomSt2 S l₁ l₂ Φ = PositivityTheory.Rg.BcB.G8.geomSt2 S l₁ l₂ Φ' := by
  unfold PositivityTheory.Rg.BcB.G8.geomSt2
  refine finsum_mem_congr rfl fun p _ => ?_
  rw [finprod_mem_congr rfl fun w hw => by rw [h w hw]]

theorem ends : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Ends := by
  intro E _ _ _ n a b h hab μ e S l₁ l₂ lam l₀ f Φ Φ' hw hΦ hΦ'
  rcases hab with rfl | rfl
  · obtain rfl : b = n := by omega
    have hl : l₂ = lam := funext fun v => infOfWeight_inj (by
      have := hw v
      simpa [infOfWeight_zero] using this)
    have hl0 : l₁ = l₀ := funext fun v => domWeight_zero _ _
    subst hl hl0
    refine geomSt2_swap S l₁ l₂ Φ Φ' fun w hw' y => ?_
    rw [hΦ w hw', hΦ' w hw']
    by_cases hs : IsSplitAt w
    · simp only [if_pos hs]
      exact ctMu_swap b w _ _ _ _ _
    · simp only [if_neg hs]
      have hm : y ∈ K2 0 b w ↔ (y.2, y.1) ∈ K2 b 0 w := by
        simp [K2, Subgroup.mem_prod, and_comm]
      simp only [Set.indicator, SetLike.mem_coe, hm, Pi.one_apply]
  · obtain rfl : a = n := by omega
    have hl : l₁ = lam := funext fun v => infOfWeight_inj (by
      have := hw v
      simpa [infOfWeight_zero] using this)
    have hl0 : l₂ = l₀ := funext fun v => domWeight_zero _ _
    subst hl hl0
    refine geomSt2_congr S l₁ l₂ Φ Φ' fun w hw' => ?_
    rw [hΦ w hw', hΦ' w hw']

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
