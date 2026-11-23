import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

section Fubini
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]

def piProdSplit (α β : ι → Type*) [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)] :
    (∀ i, α i × β i) ≃ᵐ (∀ i, α i) × (∀ i, β i) where
  toEquiv := Equiv.arrowProdEquivProdArrow ι α β
  measurable_toFun := (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst).prodMk
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd)
  measurable_invFun := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

theorem measurePreserving_piProdSplit (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] : MeasurePreserving (piProdSplit α β) (.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (piProdSplit α β).measurable
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, show piProdSplit α β ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi, forall_and]; rfl]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

theorem integral_prod_mul_of_split {μ : ∀ i, Measure (α i)} {ν : ∀ i, Measure (β i)} {ρ : ∀ i, Measure (γ i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (ρ i)]
    {g : ∀ i, α i × β i → γ i} (hg : ∀ i, MeasurePreserving (g i) ((μ i).prod (ν i)) (ρ i))
    {p : ∀ i, γ i → α i} (hp : ∀ i, Measurable (p i)) (hpg : ∀ i a b, p i (g i (a, b)) = a)
    {F : ∀ i, γ i → ℂ} (hF : ∀ i, Integrable (F i) (ρ i))
    {H : (∀ i, α i) → ℂ} (hH : Measurable H) (hb : ∀ a, ‖H a‖ ≤ 1) :
    Integrable (fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) (Measure.pi ρ) ∧
    Integrable (fun a : ∀ i, α i => (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a) (Measure.pi μ) ∧
    ∫ e, (∏ i, F i (e i)) * H (fun i => p i (e i)) ∂(Measure.pi ρ) =
      ∫ a, (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a ∂(Measure.pi μ) := by
  have hI : Integrable (fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) (Measure.pi ρ) :=
    (Integrable.fintype_prod_dep hF).mul_bdd
      (hH.comp (measurable_pi_lambda _ fun i => (hp i).comp (measurable_pi_apply i))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => hb _)
  have hΘ := (measurePreserving_pi _ _ hg).comp (measurePreserving_piProdSplit μ ν).symm
  have hJ := (hΘ.integrable_comp hI.aestronglyMeasurable).2 hI
  have key : ∀ a : ∀ i, α i, ∫ b, ((fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) ∘
      ((fun a i => g i (a i)) ∘ (piProdSplit α β).symm)) (a, b) ∂(Measure.pi ν) =
      (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a := fun a => by
    rw [← integral_fintype_prod_eq_prod (fun i b => F i (g i (a i, b))), ← integral_mul_const]
    congr 1
    funext b
    show (∏ i, F i (g i (a i, b i))) * H (fun i => p i (g i (a i, b i))) = _
    simp only [hpg]
  refine ⟨hI, ?_, ?_⟩
  · simpa only [key] using hJ.integral_prod_left
  · rw [← hΘ.map_eq, integral_map hΘ.measurable.aemeasurable (hΘ.map_eq.symm ▸ hI.aestronglyMeasurable)]
    simp only [← key]
    exact integral_prod _ hJ

theorem measurePreserving_elim {A B C k : Type*} [Fintype A] [Fintype B] [Fintype C] [MeasurableSpace k]
    (ν : Measure k) [SigmaFinite ν] (e : A ⊕ B ≃ C) :
    MeasurePreserving (fun (p : (A → k) × (B → k)) c => Sum.elim p.1 p.2 (e.symm c))
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : C => ν) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : A ⊕ B => ν))
  convert h using 1
  funext p c
  obtain ⟨a | b, rfl⟩ := e.surjective c <;>
    simp [MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi_symm]

end Fubini

section Step
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}

variable (n c n') in

abbrev KeptVar : Type _ := {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs}

variable (n c n') in

abbrev FreeVar : Type _ := {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (c / 2 + 1) rs}

open Classical in
variable (n c n') in

def stepVarEquiv : KeptVar n c n' ⊕ FreeVar n c n' ≃ StepVar n c n' where
  toFun := Sum.elim (fun rs => ⟨rs.1, Or.inr rs.2⟩) fun rs => ⟨rs.1, Or.inl rs.2⟩
  invFun rs := if h : Kept rs.1 then .inl ⟨rs.1, h⟩ else .inr ⟨rs.1, rs.2.resolve_right h⟩
  left_inv := by
    rintro (rs | rs)
    · exact dif_pos rs.2
    · exact dif_neg fun h => Kept.not_free h rs.2
  right_inv rs := by by_cases h : Kept rs.1 <;> simp [h]

def joinVars (p : (KeptVar n c n' → k) × (FreeVar n c n' → k)) : StepVar n c n' → k :=
  fun rs => Sum.elim p.1 p.2 ((stepVarEquiv n c n').symm rs)

def keptPart (e : StepVar n c n' → k) : KeptVar n c n' → k := fun rs => e ⟨rs.1, Or.inr rs.2⟩

omit [Field k] in

theorem keptPart_joinVars (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) : keptPart (joinVars (w, f)) = w := by
  funext rs
  exact congrArg (Sum.elim w f) ((stepVarEquiv n c n').symm_apply_apply (.inl rs))

theorem stepPt_joinVars (x₀ : Matrix n n' k) (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) :
    stepPt x₀ (joinVars (w, f)) = affPt (c / 2 + 1) x₀ f + keptPt w := by
  rw [stepPt_eq]
  congr 2
  · funext rs
    exact congrArg (Sum.elim w f) ((stepVarEquiv n c n').symm_apply_apply (.inr rs))
  · exact keptPart_joinVars w f

theorem ch_add_keptPt (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (w : KeptVar n c n' → k) :
    ch (z + keptPt w) = ch z := by
  simp [ch, keptPt, Kept]

theorem stepPt_col (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n) {i : Fin (c + 1)} (hi : i.val = c / 2) :
    stepPt x₀ e (.inl r) (.inr i) = keptPt (keptPart e) (.inl r) (.inr i) := by
  rw [stepPt_eq, Matrix.add_apply, affPt, Matrix.add_apply, of_apply, dif_neg (by simp [Free, hi])]
  simp [basePt]; rfl

theorem stepPt_row (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (s : n') {l : Fin c} (hl : l.val = c / 2) :
    stepPt x₀ e (.inr l) (.inl s) = keptPt (keptPart e) (.inr l) (.inl s) := by
  rw [stepPt_eq, Matrix.add_apply, affPt, Matrix.add_apply, of_apply, dif_neg (by simp [Free, hl])]
  simp [basePt]; rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosedEmbedding_stepPt (x₀ : Matrix n n' k) :
    Topology.IsClosedEmbedding (stepPt x₀ : (StepVar n c n' → k) → _) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z rs => z rs.1.1 rs.1.2 - basePt c x₀ rs.1.1 rs.1.2) (fun e => ?_)
    (continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const)
    (continuous_const.add (continuous_matrix fun r s => ?_))
  · funext rs
    simp only [stepPt, Matrix.add_apply, of_apply, add_sub_cancel_left]
    exact dif_pos rs.2
  · simp only [of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const

theorem continuous_keptPt : Continuous (keptPt : (KeptVar n c n' → k) → _) := by
  refine continuous_matrix fun r s => ?_
  simp only [keptPt, of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [MeasurableSpace k] [BorelSpace k]

open Classical in
omit [DecidableEq n] [DecidableEq n'] in

theorem integrable_step {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) (x₀ : Matrix n n' k) :
    Integrable (fun e : StepVar n c n' → k => Φ (stepPt x₀ e) * (ψ (-ch (stepPt x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h := isClosedEmbedding_stepPt (c := c) x₀
  refine Continuous.integrable_of_hasCompactSupport ((hΦ.1.continuous.comp h.continuous).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_finset_sum _ fun i _ => h.continuous.matrix_elem _ _).neg))) ?_
  exact (hΦ.2.comp_isClosedEmbedding h).mul_right

end Step

variable {k : Type*} [Field k] (G : Grid k)

abbrev KeptVars : Type _ :=
  ∀ j : Fin (G.m - 1), KeptVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k

variable {G}

def keptCol (w : KeptVars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) : k :=
  keptPt (w j) (.inl r) (.inr ⟨(G.m - 2 - j) / 2, by omega⟩)

def keptRow (x : ColArgs G) (w : KeptVars G) (j : ℕ) (s : Fin (topRank G j)) : k :=
  if h : j < G.m - 1 then ∑ l : Fin (G.m - 2 - j),
    if l.val = (G.m - 2 - j) / 2 then keptPt (w ⟨j, h⟩) (.inr l) (.inl s) else 0
  else x j (topLast G (j + 1)) s

def pairPhase (x : ColArgs G) (w : KeptVars G) : k :=
  ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, keptRow x w (j + 1) r * keptCol w j r else 0

theorem keptCol_eq (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Even (G.m - 2 - j)) (r : Fin (topRank G (j + 1))) :
    keptCol w j r = w j ⟨(.inl r, .inr ⟨(G.m - 2 - j) / 2, by omega⟩), hj, rfl⟩ := dif_pos _

theorem keptRow_eq (x : ColArgs G) (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Odd (G.m - 2 - j))
    (s : Fin (topRank G j)) : keptRow x w j s =
      w j ⟨(.inr ⟨(G.m - 2 - j) / 2, by have := hj.pos; omega⟩, .inl s), hj, rfl⟩ := by
  rw [keptRow, dif_pos j.2, Finset.sum_eq_single ⟨(G.m - 2 - j) / 2, by have := hj.pos; omega⟩, if_pos rfl]
  · exact dif_pos _
  · exact fun l _ hl => if_neg fun h => hl (Fin.ext h)
  · simp

theorem phase_eq (x : ColArgs G) (e : Vars G) :
    phase x e = ∑ j : Fin (G.m - 1), ch (stepPt (x j) (e j)) + pairPhase x fun j => keptPart (e j) := by
  rw [phase, Finset.sum_add_distrib, pairPhase]
  congr 1
  refine Finset.sum_congr rfl fun j _ => if_congr Iff.rfl (Finset.sum_congr rfl fun r _ => ?_) rfl
  congr 1
  · unfold rowVar keptRow
    split_ifs
    · refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with hl
      · exact stepPt_row _ _ _ hl
      · rfl
    · rfl
  · exact stepPt_col _ _ _ rfl

variable (hs : 1 ≤ G.s)

def stepDatum (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (j : Fin (G.m - 1))
    (z : Matrix (Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1)) k) : ℂ :=
  φ (.theta G.m j) (z.reindex (frame (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega))
    (frame (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega)))ᵀ

def lastMap (hm : 0 < G.m) (x : ColArgs G) : Matrix (Fin (G.rank (G.m, G.m - 1 + 1))) (Fin (G.rank (G.m, G.m - 1))) k :=
  (x (G.m - 1)).submatrix (Fin.castLE (by have := topRank_add hs (G.m - 1 + 1); omega))
    (Fin.cast (by have := topRank_add hs (G.m - 1); omega))

theorem downMap_last (hm : 0 < G.m) (x : ColArgs G) (e : Vars G) : downMap hs x e (G.m - 1) = lastMap hs hm x := by
  rw [downMap, dif_neg (lt_irrefl _), dif_pos (by omega)]; rfl

theorem pureTensor_fill (hm : 0 < G.m) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    G.lines₂ (oppositePath G.m) φ (fill hs x y e) = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) *
      φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ * ∏ j : Fin (G.m - 1), stepDatum hs φ j (stepPt (x j) (e j)) := by
  have h1 : ∀ (m : ℕ) (f : ℕ → ℂ), ((List.range m).map f).prod = ∏ i ∈ Finset.range m, f i := fun m f => rfl
  have h2 : ∀ f : ℕ → ℂ, ∏ i ∈ Finset.range G.m, f i = f (G.m - 1) * ∏ j : Fin (G.m - 1), f j := fun f => by
    rw [mul_comm, ← Finset.prod_range, ← Finset.prod_range_succ, Nat.sub_add_cancel hm]
  rw [Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_reverse, List.map_reverse,
    List.prod_reverse, List.map_map, List.map_map, h1, h1, mul_assoc]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => congrArg (φ (.ex i G.m)) (fill_ex hs x y e i)
  · rw [h2]
    simp only [Function.comp_apply, fill_theta, downMap_last hs hm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [downMap, dif_pos j.2]; rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stepDatum_mem_SB {φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ} (j : Fin (G.m - 1))
    (hφ : φ (.theta G.m j) ∈ SB _) : stepDatum hs φ j ∈ SB _ := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have key : ∀ {A B C D : Type} (a : A ≃ C) (b : B ≃ D),
      Topology.IsClosedEmbedding fun z : Matrix A B k => (z.reindex a b)ᵀ := fun a b =>
    Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ.reindex a.symm b.symm) (fun z => by simp)
      (continuous_id.matrix_transpose.matrix_reindex _ _) (continuous_id.matrix_reindex _ _).matrix_transpose
  exact ⟨hφ.1.comp_continuous (key _ _).continuous, hφ.2.comp_isClosedEmbedding (key _ _)⟩

theorem continuous_pairPhase (x : ColArgs G) : Continuous (pairPhase x) := by
  refine continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · refine continuous_finset_sum _ fun r _ => Continuous.mul ?_
      ((continuous_keptPt.comp (continuous_apply j)).matrix_elem _ _)
    unfold keptRow
    split_ifs with h
    · refine continuous_finset_sum _ fun l _ => ?_
      split_ifs
      · exact (continuous_keptPt.comp (continuous_apply (⟨_, h⟩ : Fin (G.m - 1)))).matrix_elem _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

open Classical in
variable (G) in

def keptVol : Measure (KeptVars G) := Measure.pi fun _ => Measure.pi fun _ => ν

def contractIntegrand (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    (w : KeptVars G) : ℂ :=
  (∏ j : Fin (G.m - 1), flatStep ψ ν (stepDatum hs φ j) (x j) (w j)) * (ψ (-pairPhase x w) : ℂ)

variable {ψ}

theorem flatTensor_pureTensor [ν.IsAddHaarMeasure] (hm : 0 < G.m) (hψ : Continuous ψ)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) (x : ColArgs G) (y : RowArgs G) :
    Integrable (flatIntegrand hs ψ (G.lines₂ (oppositePath G.m) φ) x y) (varsVol G ν) ∧
    Integrable (contractIntegrand hs ψ ν φ x) (keptVol G ν) ∧
    flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y =
      (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ *
        ∫ w, contractIntegrand hs ψ ν φ x w ∂(keptVol G ν) := by
  classical
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hchar : ∀ (s : Finset (Fin (G.m - 1))) (f : Fin (G.m - 1) → k),
      (ψ (-∑ j ∈ s, f j) : ℂ) = ∏ j ∈ s, (ψ (-f j) : ℂ) := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_add, AddChar.map_add_eq_mul,
        Circle.coe_mul, ih]
  obtain ⟨h1, h2, h3⟩ := integral_prod_mul_of_split
    (g := fun j : Fin (G.m - 1) => joinVars (k := k) (n := Fin (topRank G (j + 1))) (c := G.m - 2 - j)
      (n' := Fin (topRank G j)))
    (fun j => measurePreserving_elim ν (stepVarEquiv _ _ _))
    (p := fun j => keptPart) (fun j => measurable_pi_lambda _ fun _ => measurable_pi_apply _)
    (fun j => keptPart_joinVars)
    (fun j => by convert integrable_step hψ ν (stepDatum_mem_SB hs j (hφ j j.2)) (x j))
    (H := fun w => (ψ (-pairPhase x w) : ℂ))
    (continuous_subtype_val.comp (hψ.comp (continuous_pairPhase x).neg)).measurable (fun w => (Circle.norm_coe _).le)
  have e1 : flatIntegrand hs ψ (G.lines₂ (oppositePath G.m) φ) x y = fun e =>
      ((∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ) *
      ((∏ j : Fin (G.m - 1), stepDatum hs φ j (stepPt (x j) (e j)) * (ψ (-ch (stepPt (x j) (e j))) : ℂ)) *
        (ψ (-pairPhase x fun j => keptPart (e j)) : ℂ)) := by
    funext e
    rw [flatIntegrand, pureTensor_fill hs hm, phase_eq, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hchar,
      Finset.prod_mul_distrib]
    ring
  simp only [stepPt_joinVars, ch_add_keptPt] at h2 h3
  rw [flatTensor, e1, integral_const_mul]
  unfold varsVol keptVol contractIntegrand flatStep opE
  refine ⟨Integrable.const_mul (by convert h1) _, by convert h2, congrArg _ (by convert h3)⟩

end GlobalTheory.FunObj
