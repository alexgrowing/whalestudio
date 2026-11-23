import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeFiniteCohomologyGeneratorBound
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

def PStep (lenO : ℕ∞) (m : ℕ) (c : ℝ) (A B : Submodule O FF) (isGen : Prop) : Prop :=
  B ≤ A ∧ ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module O Q) (ob : ↥A →ₗ[O] Q),
    (∀ x : ↥A, ob x = 0 ↔ (x : FF) ∈ B) ∧
    (isGen → ∃ s : Finset Q, s.card ≤ m ∧ Submodule.span O (↑s : Set Q) = ⊤) ∧
    (¬ isGen → ∃ L kO : ℕ, Module.length O Q ≤ (L : ℕ∞) ∧ lenO = kO ∧ (L : ℝ) ≤ c * kO)

theorem PStep.congr {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF} {p q : Prop} (hpq : p ↔ q)
    (h : PStep lenO m c A B p) : PStep lenO m c A B q := by
  obtain ⟨hle, Q, i1, i2, ob, hk, hg, hl⟩ := h
  exact ⟨hle, Q, i1, i2, ob, hk, fun hq => hg (hpq.2 hq), fun hq => hl (fun hp => hq (hpq.1 hp))⟩

def PChain (lenO : ℕ∞) (m : ℕ) (c : ℝ) (A B : Submodule O FF) (ng nl : ℕ) : Prop :=
  ∃ (k : ℕ) (Fl : ℕ → Submodule O FF) (gen : Finset ℕ),
    Fl 0 = A ∧ Fl k = B ∧ gen ⊆ Finset.range k ∧ gen.card ≤ ng ∧ k - gen.card ≤ nl ∧
    ∀ i < k, PStep lenO m c (Fl i) (Fl (i + 1)) (i ∈ gen)

theorem PChain.refl (lenO : ℕ∞) (m : ℕ) (c : ℝ) (A : Submodule O FF) : PChain lenO m c A A 0 0 :=
  ⟨0, fun _ => A, ∅, rfl, rfl, Finset.empty_subset _, by simp, by simp,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem PChain.mono {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF} {ng nl ng' nl' : ℕ}
    (h : PChain lenO m c A B ng nl) (h1 : ng ≤ ng') (h2 : nl ≤ nl') : PChain lenO m c A B ng' nl' := by
  obtain ⟨k, Fl, gen, h0, hk, hsub, hg, hl, hs⟩ := h
  exact ⟨k, Fl, gen, h0, hk, hsub, hg.trans h1, hl.trans h2, hs⟩

theorem PChain.le {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF} {ng nl : ℕ}
    (h : PChain lenO m c A B ng nl) : B ≤ A := by
  obtain ⟨k, Fl, gen, h0, hk, -, -, -, hs⟩ := h
  have key : ∀ i, i ≤ k → Fl i ≤ Fl 0 := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; exact ((hs j (by omega)).1).trans (ih (by omega))
  rw [← hk, ← h0]
  exact key k le_rfl

theorem PChain.trans {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B C : Submodule O FF} {ng nl ng' nl' : ℕ}
    (h₁ : PChain lenO m c A B ng nl) (h₂ : PChain lenO m c B C ng' nl') :
    PChain lenO m c A C (ng + ng') (nl + nl') := by
  obtain ⟨k₁, F₁, g₁, h0₁, hk₁, hs₁, hg₁, hl₁, hst₁⟩ := h₁
  obtain ⟨k₂, F₂, g₂, h0₂, hk₂, hs₂, hg₂, hl₂, hst₂⟩ := h₂
  let Fl : ℕ → Submodule O FF := fun i => if i ≤ k₁ then F₁ i else F₂ (i - k₁)
  let gen : Finset ℕ := g₁ ∪ g₂.map (addRightEmbedding k₁)
  have hFl₁ : ∀ i, i ≤ k₁ → Fl i = F₁ i := fun i hi => if_pos hi
  have hFl₂ : ∀ i, k₁ ≤ i → Fl i = F₂ (i - k₁) := by
    intro i hi
    by_cases h : i ≤ k₁
    · have hik : i = k₁ := le_antisymm h hi
      rw [hik]
      show (if k₁ ≤ k₁ then F₁ k₁ else F₂ (k₁ - k₁)) = F₂ (k₁ - k₁)
      rw [if_pos le_rfl, Nat.sub_self, hk₁, h0₂]
    · exact if_neg h
  have hdisj : Disjoint g₁ (g₂.map (addRightEmbedding k₁)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hb
    have hx := Finset.mem_range.1 (hs₁ ha)
    rw [addRightEmbedding_apply] at hx
    omega
  have hmem₁ : ∀ i, i < k₁ → (i ∈ gen ↔ i ∈ g₁) := by
    intro i hi
    simp only [gen, Finset.mem_union, Finset.mem_map, addRightEmbedding_apply]
    constructor
    · rintro (h | ⟨x, -, rfl⟩)
      · exact h
      · exact absurd hi (by omega)
    · exact fun h => Or.inl h
  have hmem₂ : ∀ i, k₁ ≤ i → (i ∈ gen ↔ i - k₁ ∈ g₂) := by
    intro i hi
    simp only [gen, Finset.mem_union, Finset.mem_map, addRightEmbedding_apply]
    constructor
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact absurd (Finset.mem_range.1 (hs₁ h)) (by omega)
      · rwa [Nat.add_sub_cancel]
    · intro h
      exact Or.inr ⟨i - k₁, h, by omega⟩
  have c1 : g₁.card ≤ k₁ := by simpa using Finset.card_le_card hs₁
  have c2 : g₂.card ≤ k₂ := by simpa using Finset.card_le_card hs₂
  have hc : gen.card = g₁.card + g₂.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map]
  refine ⟨k₁ + k₂, Fl, gen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFl₁ 0 (Nat.zero_le _), h0₁]
  · rw [hFl₂ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hk₂]
  · intro i hi
    simp only [gen, Finset.mem_union, Finset.mem_map, addRightEmbedding_apply] at hi
    rw [Finset.mem_range]
    rcases hi with h | ⟨x, hx, rfl⟩
    · have := Finset.mem_range.1 (hs₁ h); omega
    · have := Finset.mem_range.1 (hs₂ hx); omega
  · rw [hc]; omega
  · rw [hc]; omega
  · intro i hi
    by_cases h : i < k₁
    · rw [hFl₁ i h.le, hFl₁ (i + 1) h]
      exact (hst₁ i h).congr (hmem₁ i h).symm
    · push Not at h
      rw [hFl₂ i h, hFl₂ (i + 1) (by omega), show i + 1 - k₁ = (i - k₁) + 1 by omega]
      exact (hst₂ (i - k₁) (by omega)).congr (hmem₂ i h).symm

theorem iter_chain {lenO : ℕ∞} {m : ℕ} {c : ℝ} {ι : Type} (P : ι → Submodule O FF → Prop)
    (Q : ι → Prop) (hmono : ∀ i A B, B ≤ A → P i A → P i B) (A₀ : Submodule O FF) (a b : ℕ)
    (hstep : ∀ i, Q i → ∀ A, A ≤ A₀ → ∃ B, PChain lenO m c A B a b ∧ P i B) :
    ∀ L : List ι, (∀ i ∈ L, Q i) → ∀ A, A ≤ A₀ →
      ∃ B, PChain lenO m c A B (L.length * a) (L.length * b) ∧ ∀ i ∈ L, P i B := by
  intro L
  induction L with
  | nil =>
    intro _ A _
    exact ⟨A, by simpa using PChain.refl lenO m c A, by simp⟩
  | cons i L ih =>
    intro hQ A hA
    obtain ⟨B₁, h1, hP1⟩ := hstep i (hQ i (by simp)) A hA
    obtain ⟨B₂, h2, hP2⟩ := ih (fun j hj => hQ j (by simp [hj])) B₁ (h1.le.trans hA)
    refine ⟨B₂, (h1.trans h2).mono (le_of_eq (by simp only [List.length_cons]; ring))
      (le_of_eq (by simp only [List.length_cons]; ring)), ?_⟩
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hmono _ _ _ h2.le hP1
    · exact hP2 j hj

end Chain

def evens (n d : ℕ) [NeZero n] : Finset (ZMod n) :=
  Finset.univ.filter fun c : ZMod n => (c.val + d) % 2 = 0

theorem parity_succ {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (c : ZMod n) :
    ((c + 1).val + d) % 2 ≠ (c.val + d) % 2 := by
  obtain ⟨j, hj⟩ := hn
  have hn0 : n ≠ 0 := NeZero.ne n
  have : Fact (1 < n) := ⟨by omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  have hc := ZMod.val_lt c
  by_cases h : c.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]; omega
  · have h' : c.val + 1 = n := by omega
    rw [h', Nat.mod_self]; omega

theorem two_mul_card_evens_le {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) :
    2 * (evens n d).card ≤ n := by
  have hodd : (evens n d).card ≤
      (Finset.univ.filter fun c : ZMod n => ¬ (c.val + d) % 2 = 0).card := by
    refine Finset.card_le_card_of_injOn (fun c => c + 1) ?_ ?_
    · intro c hc
      have hc' : (c.val + d) % 2 = 0 := by simpa [evens] using hc
      have := parity_succ hn d c
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    · intro a _ b _ hab
      exact add_right_cancel hab
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod n))) (fun c : ZMod n => (c.val + d) % 2 = 0)
  rw [Finset.card_univ, ZMod.card] at htot
  unfold evens at hodd ⊢
  omega

def aN (l H : ℕ) : ℕ := ⌈aR l H⌉₊

def cocyclesToWachVectorsExponent (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η) +
    2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

def EB (l h η S : ℕ) : ℝ :=
  (3 * (aN l (h + η) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) + 3 * lam l (h + η)

def wachVectorSubmoduleChainExponent (l h η S : ℕ) : ℝ :=
  (h : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) + 2 * EB l h η S + 3 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) +
    3 * (S : ℝ) + 3 + 2 * lam l (h + η)

def sigC (l h η : ℕ) : ℕ := ⌈(((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) + 1⌉₊

def lenC (r m l H S : ℕ) : ℝ := (r : ℝ) * (S : ℝ) + 2 * (m : ℝ) * cD l H

theorem expC_of (l : ℕ) (hl : 11 ≤ l) (h η S s e : ℕ) (hs : (s : ℝ) ≤ cocyclesToWachVectorsExponent l h η S)
    (he : (e : ℝ) ≤ wachVectorSubmoduleChainExponent l h η S) : ExpC l h η S (e + s) := by
  have hlam := one_le_lam l (h + η) (by omega)
  have haR := aR_nonneg l (h + η) (by omega)
  refine ⟨aN l (h + η), h, (s : ℝ) - 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η - 2 + lam l (h + η), EB l h η S,
    (e : ℝ) - S - EB l h η S - Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) + 2 - lam l (h + η), le_rfl, ?_, ?_,
    le_rfl, ?_, ?_⟩
  · exact (Nat.ceil_lt_add_one haR).le
  · unfold cocyclesToWachVectorsExponent at hs; linarith
  · unfold wachVectorSubmoduleChainExponent at he; linarith
  · push_cast; linarith

def EG (l h η S : ℕ) : ℝ :=
  (3 * (aN l (h + η) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def wachVectorLiftingExponent (l h η S : ℕ) : ℝ :=
  (h : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) + ((S : ℝ) + 1) / ((l : ℝ) - 1) + (S : ℝ) + EG l h η S +
    2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) + 6 + lam l (h + η)

def B6 (l h η S : ℕ) : ℝ := (S : ℝ) + EG l h η S + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) + lam l (h + η)

theorem bound_three_five_add_six_le (l : ℕ) (hl : 11 ≤ l) (h η S : ℕ) :
    wachVectorLiftingExponent l h η S + B6 l h η S ≤ wachVectorSubmoduleChainExponent l h η S := by
  have hlam := one_le_lam l (h + η) (by omega)
  have hl1 : (1 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hS : ((S : ℝ) + 1) / ((l : ℝ) - 1) ≤ (S : ℝ) + 1 := div_le_self (by positivity) hl1
  unfold wachVectorLiftingExponent B6 wachVectorSubmoduleChainExponent EB EG
  linarith

section Steps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem kerChain_of_pchain {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {FF : Type}
    [AddCommGroup FF] [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (n m : ℕ) (c : ℝ) (e : ℕ)
    (Bs : Submodule O FF) (ng nl : ℕ) (hng : ng ≤ 4 * n) (hnl : nl ≤ 3 * n / 2)
    (h : PChain (lenOl PD (O := O)) m c ⊤ Bs ng nl)
    (hB : ∀ x ∈ Bs, ((PD.p : O) ^ e) • (g x : G → T₂.V) ∈ F.ImF PD) : KerChain PD F g n m c e := by
  obtain ⟨k, Fl, gen, h0, hk, hsub, hg, hl, hs⟩ := h
  refine ⟨k, Fl, gen, hg.trans hng, hl.trans hnl, h0, hsub, fun i hi => ?_, fun x hx => ?_⟩
  · obtain ⟨hle, Q, i1, i2, ob, hker, hgen, hlen⟩ := hs i hi
    exact ⟨hle, Q, i1, i2, ob, hker, hgen, hlen⟩
  · exact hB x (by rw [← hk]; exact hx)

def QPowSmulMemPullback (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (η : ℕ) (x : W.DD T) :
    Prop :=
  Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1 ∧ Formalism.MainNotions.CrystallineLiftingInputs.InI W T c x

def RhoCoc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (M η σ : ℕ)
    (w : W.DD T) (κ : G → T.V) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.InI W T c w ∧ ∃ (hκ : κ ∈ latticeCocycles T.L) (z : W.DD T) (x : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T c 1 M η σ w z ∧ (x : W.DD T × W.DD T).1 = z ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T M (x : W.DD T × W.DD T).2 ∧
    W.clK T x = Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))

def CocyclesToWachVectorsBound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s : ℕ, (s : ℝ) ≤ cocyclesToWachVectorsExponent PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₂ n 0 ∧
        (m = 0 → F₂ = ⊤) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ s) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ s) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

def WachVectorSubmoduleChainBound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ e : ℕ, (e : ℝ) ≤ wachVectorSubmoduleChainExponent PD.p (hpar n b S) η S ∧
    ∀ c ∈ evens n d, ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF]
      [Module.Finite O FF] (Fs : Submodule O FF) (w : ↥Fs →ₗ[O] W.DD T₂),
      (∀ f : ↥Fs, QPowSmulMemPullback W T₂ c η (w f)) →
      (∃ (F' : Submodule O FF) (hF' : F' ≤ Fs),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) Fs F' 6 3 ∧
        ∀ (f : ↥F') (j : ℕ), ∃ u : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c u ∧
          Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (j + e)) • w (Submodule.inclusion hF' f) - W.map F u)) ∧
      (m = 0 → ∀ (f : ↥Fs) (j : ℕ), ∃ u : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c u ∧
          Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (j + e + 3 * S)) • w f - W.map F u))

def RhoLift [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ c ∈ evens n d,
    ∀ (w : W.DD T₂) (u : W.DD T₁) (κ : G → T₂.V) (k : ℕ),
      Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c u →
      RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η (sigC PD.p (hpar n b S) η) w κ →
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ k) • w - W.map F u) →
      ((PD.p : O) ^ k) • κ ∈ F.ImF PD

theorem coboundary_le_image {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) :
    latticeCoboundaries T₂.L ≤ F.ImF (PD := PD) := by
  unfold LatHom.ImF
  exact le_sup_right

theorem smul_mem_of_sum {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {ι : Type}
    (s : Finset ι) (κ : ι → G → T₂.V) (x : G → T₂.V) (a b : ℕ)
    (hκ : ∀ c ∈ s, ((PD.p : O) ^ a) • κ c ∈ F.ImF PD)
    (hx : ((PD.p : O) ^ b) • x - (∑ c ∈ s, κ c) ∈ latticeCoboundaries T₂.L ∨
      ((PD.p : O) ^ b) • x + (∑ c ∈ s, κ c) ∈ latticeCoboundaries T₂.L) :
    ((PD.p : O) ^ (a + b)) • x ∈ F.ImF PD := by
  have hsumI : ((PD.p : O) ^ a) • (∑ c ∈ s, κ c) ∈ F.ImF PD := by
    rw [Finset.smul_sum]
    exact Submodule.sum_mem _ hκ
  rw [pow_add, mul_smul]
  rcases hx with h1 | h1
  · have := Submodule.add_mem _ (Submodule.smul_mem _ ((PD.p : O) ^ a) (coboundary_le_image F h1)) hsumI
    rwa [← smul_add, sub_add_cancel] at this
  · have := Submodule.sub_mem _ (Submodule.smul_mem _ ((PD.p : O) ^ a) (coboundary_le_image F h1)) hsumI
    rwa [← smul_sub, add_sub_cancel_right] at this

section Closure

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem inPN_smul {k : ℕ} {x : W.DD T} (a : O) (h : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T k x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T k (a • x) := by
  obtain ⟨y, hy, hΔ, rfl⟩ := h
  refine ⟨a • y, ?_, fun δ hδ => by rw [map_smul, hΔ δ hδ], smul_comm a (W.π₀ ^ k) y⟩
  rw [← algebraMap_smul (LetA O n) a y]
  exact (W.N T).smul_mem _ hy

theorem inPN_add {k : ℕ} {x x' : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T k x)
    (h' : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T k x') : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T k (x + x') := by
  obtain ⟨y, hy, hΔ, rfl⟩ := h
  obtain ⟨y', hy', hΔ', rfl⟩ := h'
  exact ⟨y + y', (W.N T).add_mem hy hy', fun δ hδ => by rw [map_add, hΔ δ hδ, hΔ' δ hδ],
    (smul_add _ _ _).symm⟩

theorem dl_smul {i : ZMod n} {x : W.DD T} (a : O) (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x) :=
  ⟨by rw [smul_comm (letE i : LetA O n) a x, h.1], fun δ hδ => by rw [map_smul, h.2 δ hδ]⟩

theorem dl_add {i : ZMod n} {x x' : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x)
    (h' : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x') : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (x + x') :=
  ⟨by rw [smul_add, h.1, h'.1], fun δ hδ => by rw [map_add, h.2 δ hδ, h'.2 δ hδ]⟩

theorem pow_smul_mem_mul {M : Type} [AddCommGroup M] [Module (LetA O n) M]
    (N : Submodule (LetA O n) M) {a r : LetA O n} {x : M} {k K : ℕ} (hK : k ≤ K)
    (h : a ^ k • x ∈ N) : (a * r) ^ K • x ∈ N := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hK
  have e : (a * r) ^ (k + t) = (a ^ t * r ^ (k + t)) * a ^ k := by ring
  rw [e, mul_smul]
  exact N.smul_mem _ h

theorem polesFin_smul {x : W.DD T} (a : O) (h : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T x) :
    Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T (a • x) := by
  obtain ⟨k, k', hk⟩ := h
  refine ⟨k, k', ?_⟩
  rw [smul_comm _ a x, ← algebraMap_smul (LetA O n) a]
  exact (W.N T).smul_mem _ hk

theorem polesFin_add {x x' : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T x)
    (h' : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T x') : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T (x + x') := by
  obtain ⟨k₁, k₁', h₁⟩ := h
  obtain ⟨k₂, k₂', h₂⟩ := h'
  refine ⟨max k₁ k₂, max k₁' k₂', ?_⟩
  have e₁ := Finset.prod_range_mul_prod_Ico (Formalism.MainNotions.LiftingTheory.pk W) (le_max_left k₁ k₂)
  have e₂ := Finset.prod_range_mul_prod_Ico (Formalism.MainNotions.LiftingTheory.pk W) (le_max_right k₁ k₂)
  rw [smul_add]
  refine (W.N T).add_mem ?_ ?_
  · rw [← e₁]; exact pow_smul_mem_mul (W.N T) (le_max_left _ _) h₁
  · rw [← e₂]; exact pow_smul_mem_mul (W.N T) (le_max_right _ _) h₂

theorem inI_smul {i : ZMod n} {x : W.DD T} (a : O) (h : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T i (a • x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨dl_smul W T a h1, polesFin_smul W T a h2, ?_⟩
  have e : W.γ T (a • x) - a • x = a • (W.γ T x - x) := by rw [map_smul, smul_sub]
  rw [e]
  exact inPN_smul W T a h3

theorem inI_add {i : ZMod n} {x x' : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i x)
    (h' : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i x') : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i (x + x') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨dl_add W T h1 h1', polesFin_add W T h2 h2', ?_⟩
  have e : W.γ T (x + x') - (x + x') = (W.γ T x - x) + (W.γ T x' - x') := by
    rw [map_add]; abel
  rw [e]
  exact inPN_add W T h3 h3'

end Closure

def Hyp6 (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (x : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x

def WachVectorLiftingBound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ e₂ : ℕ, (e₂ : ℝ) ≤ wachVectorLiftingExponent PD.p (hpar n b S) η S ∧
    ∀ c ∈ evens n d, ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF]
      [Module.Finite O FF] (Fs : Submodule O FF) (w : ↥Fs →ₗ[O] W.DD T₂),
      (∀ f : ↥Fs, QPowSmulMemPullback W T₂ c η (w f)) →
      (∃ (F' : Submodule O FF) (hF' : F' ≤ Fs) (y : ↥F' →ₗ[O] W.DD T₁),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) Fs F' 3 1 ∧
        ∀ f : ↥F', Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (y f) ∧
          Hyp6 W T₂ c (((PD.p : O) ^ e₂) • w (Submodule.inclusion hF' f) - W.map F (y f))) ∧
      (m = 0 → ∃ y : ↥Fs →ₗ[O] W.DD T₁, ∀ f : ↥Fs, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (y f) ∧
          Hyp6 W T₂ c (((PD.p : O) ^ (e₂ + S)) • w f - W.map F (y f)))

def LatticeBoundSix [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ e₆ : ℕ, (e₆ : ℝ) ≤ B6 PD.p (hpar n b S) η S ∧
    ∀ c ∈ evens n d, ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF]
      [Module.Finite O FF] (Fs : Submodule O FF) (w : ↥Fs →ₗ[O] W.DD T₂),
      (∀ f : ↥Fs, Hyp6 W T₂ c (w f)) →
      (∃ (F' : Submodule O FF) (hF' : F' ≤ Fs),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) Fs F' 3 2 ∧
        ∀ f : ↥F', ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
          Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ e₆) • w (Submodule.inclusion hF' f) - W.map F x)) ∧
      (m = 0 → ∀ f : ↥Fs, ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
          Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e₆ + 2 * S)) • w f - W.map F x))

theorem lattice_bound_three_six_of [NeZero n] (W : LocWach PD LL O v n) (h345 : WachVectorLiftingBound W) (h6 : LatticeBoundSix W) :
    WachVectorSubmoduleChainBound W := by
  intro d T₁ T₂ F b S η m hset
  obtain ⟨e₂, he₂, H345⟩ := h345 d T₁ T₂ F b S η m hset
  obtain ⟨e₆, he₆, H6⟩ := h6 d T₁ T₂ F b S η m hset
  have hl : 11 ≤ PD.p := hset.2.1
  refine ⟨e₆ + e₂, ?_, ?_⟩
  · have := bound_three_five_add_six_le PD.p hl (hpar n b S) η S
    push_cast
    linarith
  intro c hc FF _ _ _ _ Fs w hw
  obtain ⟨⟨F₁, h₁, y, hch₁, hy⟩, hy0⟩ := H345 c hc FF Fs w hw
  refine ⟨?_, fun hm f j => ?_⟩
  · let w' : ↥F₁ →ₗ[O] W.DD T₂ := ((PD.p : O) ^ e₂) • (w ∘ₗ Submodule.inclusion h₁) -
      ((W.map F).restrictScalars O) ∘ₗ y
    have hw' : ∀ f : ↥F₁, w' f = ((PD.p : O) ^ e₂) • w (Submodule.inclusion h₁ f) -
        W.map F (y f) := fun f => rfl
    obtain ⟨⟨F₂, h₂, hch₂, hx⟩, -⟩ :=
      H6 c hc FF F₁ w' (fun f => by rw [hw']; exact (hy f).2)
    refine ⟨F₂, h₂.trans h₁, hch₁.trans hch₂, fun f j => ?_⟩
    obtain ⟨x, hxI, hxP⟩ := hx f
    have hyI := (hy (Submodule.inclusion h₂ f)).1
    refine ⟨((PD.p : O) ^ j) • (((PD.p : O) ^ e₆) • y (Submodule.inclusion h₂ f) + x),
      inI_smul W T₁ _ (inI_add W T₁ (inI_smul W T₁ _ hyI) hxI), ?_⟩
    have hinc : Submodule.inclusion h₁ (Submodule.inclusion h₂ f) =
        Submodule.inclusion (h₂.trans h₁) f := rfl
    have key : ((PD.p : O) ^ (j + (e₆ + e₂))) • w (Submodule.inclusion (h₂.trans h₁) f) -
        W.map F (((PD.p : O) ^ j) • (((PD.p : O) ^ e₆) • y (Submodule.inclusion h₂ f) + x)) =
        ((PD.p : O) ^ j) • (((PD.p : O) ^ e₆) • w' (Submodule.inclusion h₂ f) - W.map F x) := by
      rw [hw', hinc, LinearMap.map_smul_of_tower, map_add, LinearMap.map_smul_of_tower]
      module
    rw [key]
    exact inPN_smul W T₂ _ hxP
  · obtain ⟨y0, hy0'⟩ := hy0 hm
    let w'' : ↥Fs →ₗ[O] W.DD T₂ := ((PD.p : O) ^ (e₂ + S)) • w -
      ((W.map F).restrictScalars O) ∘ₗ y0
    have hw'' : ∀ f : ↥Fs, w'' f = ((PD.p : O) ^ (e₂ + S)) • w f - W.map F (y0 f) := fun f => rfl
    obtain ⟨x, hxI, hxP⟩ :=
      (H6 c hc FF Fs w'' (fun f => by rw [hw'']; exact (hy0' f).2)).2 hm f
    refine ⟨((PD.p : O) ^ j) • (((PD.p : O) ^ (e₆ + 2 * S)) • y0 f + x),
      inI_smul W T₁ _ (inI_add W T₁ (inI_smul W T₁ _ (hy0' f).1) hxI), ?_⟩
    have key : ((PD.p : O) ^ (j + (e₆ + e₂) + 3 * S)) • w f -
        W.map F (((PD.p : O) ^ j) • (((PD.p : O) ^ (e₆ + 2 * S)) • y0 f + x)) =
        ((PD.p : O) ^ j) • (((PD.p : O) ^ (e₆ + 2 * S)) • w'' f - W.map F x) := by
      rw [hw'', LinearMap.map_smul_of_tower, map_add, LinearMap.map_smul_of_tower]
      module
    rw [key]
    exact inPN_smul W T₂ _ hxP

def LemmaGs [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
          Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (i - 2),
        x ∈ FilCris PD T₂.ρ (b i : ℤ) →
        ((PD.p : LL) ^ (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (hpar n b S + η) +
          ((b (i - 1) + S : ℕ) : ℝ) - (b i : ℝ)⌉ : ℤ)) • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F i

theorem lemmaG_of_sharp [NeZero n] (W : LocWach PD LL O v n) (h : LemmaGs W) :
    Formalism.MainNotions.CrystallineLiftingInputs.LemmaG W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨E, hE, hx⟩ := h d T₁ T₂ F b S η m hS i hi
  have hl : 11 ≤ PD.p := hS.2.1
  have hlam := one_le_lam PD.p (hpar n b S + η) (by omega)
  exact ⟨E, by linarith, hx⟩

def NDl (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O (W.DD T) where
  carrier := {x | x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x}
  zero_mem' := ⟨(W.N T).zero_mem, by simp [Formalism.MainNotions.CrystallineLiftingInputs.DL]⟩
  add_mem' := fun ha hb => ⟨(W.N T).add_mem ha.1 hb.1, dl_add W T ha.2 hb.2⟩
  smul_mem' := fun a x hx => ⟨by rw [← algebraMap_smul (LetA O n) a x]; exact (W.N T).smul_mem _ hx.1,
    dl_smul W T a hx.2⟩

def PhiPullΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O (W.DD T) :=
  Submodule.span O {y | ∃ a ∈ W.AΔ, ∃ x ∈ NDl W T (i - 1), y = a • W.φD T x}

def LemmaDN [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
    ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ NDl W T₂ i ∧
      ∃ L kO : ℕ, Module.length O (↥(NDl W T₂ i) ⧸
          ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧
        (L : ℝ) ≤ lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S * kO

theorem lattice_bounds_of_local [NeZero n] (W : LocWach PD LL O v n) (h12 : CocyclesToWachVectorsBound W) (h36 : WachVectorSubmoduleChainBound W)
    (hR : RhoLift W) : LocalLiftingConditions W := by
  intro d T₁ T₂ F b S η m hset
  obtain ⟨s, hs, H12⟩ := h12 d T₁ T₂ F b S η m hset
  obtain ⟨e, he, H36⟩ := h36 d T₁ T₂ F b S η m hset
  have hR' := hR d T₁ T₂ F b S η m hset
  have hl : 11 ≤ PD.p := hset.2.1
  have hn : Even n := hset.2.2.1
  refine ⟨e + s, expC_of PD.p hl _ η S s e hs he, ?_, ?_⟩
  · intro FF _ _ _ _ g _
    obtain ⟨F₂, w, hch12, -, hhyp, hcls⟩ := H12 FF g
    obtain ⟨Fs, hch36, hP⟩ := iter_chain (lenO := lenOl PD (O := O)) (m := m)
      (c := lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S)
      (fun c Bs => ∀ (f : FF) (hf : f ∈ F₂), f ∈ Bs → ∀ j : ℕ, ∃ u : W.DD T₁,
        Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c u ∧
        Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (j + e)) • w c ⟨f, hf⟩ - W.map F u))
      (fun c => c ∈ evens n d) (fun c A Bs hBA hA f hf hfB => hA f hf (hBA hfB)) F₂ 6 3
      (fun c hc A hA => by
        obtain ⟨⟨F', hF', hch, hPc⟩, -⟩ :=
          H36 c hc FF A ((w c).comp (Submodule.inclusion hA)) (fun f => hhyp c hc _)
        exact ⟨F', hch, fun f _ hfF j => hPc ⟨f, hfF⟩ j⟩)
      (evens n d).toList (fun c hc => Finset.mem_toList.1 hc) F₂ le_rfl
    have hcard := two_mul_card_evens_le hn d
    rw [Finset.length_toList] at hch36
    refine kerChain_of_pchain F g n m _ (e + s) Fs _ _ ?_ ?_ (hch12.trans hch36) ?_
    · omega
    · omega
    · intro f hf
      have hf2 : f ∈ F₂ := hch36.le hf
      obtain ⟨κ, hκ, hsum⟩ := hcls ⟨f, hf2⟩
      refine smul_mem_of_sum F (evens n d) κ _ e s (fun c hc => ?_) hsum
      obtain ⟨u, hu, hpn⟩ := hP c (Finset.mem_toList.2 hc) f hf2 hf 0
      rw [zero_add] at hpn
      exact hR' c hc (w c ⟨f, hf2⟩) u (κ c) e hu (hκ c hc) hpn
  · intro hm z hz
    obtain ⟨F₂, w, -, h0, hhyp, hcls⟩ :=
      H12 O (LinearMap.toSpanSingleton O ↥(latticeFiniteCocycles PD T₂.L) ⟨z, hz⟩)
    have h1 : (1 : O) ∈ F₂ := by rw [h0 hm]; trivial
    obtain ⟨κ, hκ, hsum⟩ := hcls ⟨1, h1⟩
    have hg1 : ((LinearMap.toSpanSingleton O ↥(latticeFiniteCocycles PD T₂.L) ⟨z, hz⟩ 1 : ↥(latticeFiniteCocycles PD T₂.L)) :
        G → T₂.V) = z := by
      simp [LinearMap.toSpanSingleton_apply]
    rw [hg1] at hsum
    rw [show e + s + 3 * S = (e + 3 * S) + s by omega]
    refine smul_mem_of_sum F (evens n d) κ z (e + 3 * S) s (fun c hc => ?_) hsum
    obtain ⟨u, hu, hpn⟩ := (H36 c hc O F₂ (w c) (fun f => hhyp c hc f)).2 hm ⟨1, h1⟩ 0
    rw [zero_add] at hpn
    exact hR' c hc (w c ⟨1, h1⟩) u (κ c) (e + 3 * S) hu (hκ c hc) hpn

end Steps

def cocyclesToWachVectorsBoundAtGoodExtensions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], CocyclesToWachVectorsBound ((HW l).W K 1 LL hg)

def wachVectorSubmoduleChainBoundAtGoodExtensions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], WachVectorSubmoduleChainBound ((HW l).W K 1 LL hg)

def rhoLift (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], RhoLift ((HW l).W K 1 LL hg)

theorem lattice_bounds_of_three_parts (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h12 : cocyclesToWachVectorsBoundAtGoodExtensions D HW F) (h36 : wachVectorSubmoduleChainBoundAtGoodExtensions D HW F) (hR : rhoLift D HW F) : localLiftingConditionsGlobal D HW F := by
  intro l _ K LL hg _
  exact lattice_bounds_of_local _ (h12 l K LL hg) (h36 l K LL hg) (hR l K LL hg)

def wachVectorLiftingBoundAtGoodExtensions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], WachVectorLiftingBound ((HW l).W K 1 LL hg)

def steps6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LatticeBoundSix ((HW l).W K 1 LL hg)

theorem lattice_bounds_of_four_parts (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h12 : cocyclesToWachVectorsBoundAtGoodExtensions D HW F) (h345 : wachVectorLiftingBoundAtGoodExtensions D HW F) (h6 : steps6 D HW F) (hR : rhoLift D HW F) :
    localLiftingConditionsGlobal D HW F := by
  intro l _ K LL hg _
  exact lattice_bounds_of_local _ (h12 l K LL hg) (lattice_bound_three_six_of _ (h345 l K LL hg) (h6 l K LL hg)) (hR l K LL hg)

theorem lattice_bounds_of_admissible (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ)
    (h : admitted D HW F Cm CR CA CB CK → cocyclesToWachVectorsBoundAtGoodExtensions D HW F ∧ wachVectorSubmoduleChainBoundAtGoodExtensions D HW F ∧ rhoLift D HW F) :
    admitted D HW F Cm CR CA CB CK → localLiftingConditionsGlobal D HW F := fun hA =>
  lattice_bounds_of_three_parts D HW F (h hA).1 (h hA).2.1 (h hA).2.2

theorem stmt_of_lemmas (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ)
    (h : admitted D HW F Cm CR CA CB CK → cocyclesToWachVectorsBoundAtGoodExtensions D HW F ∧ wachVectorSubmoduleChainBoundAtGoodExtensions D HW F ∧ rhoLift D HW F) :
    Stmt D HW F Cm 25 CR CA CB CK :=
  stmt_of_stepsAdm D HW F Cm CR CA CB CK (lattice_bounds_of_admissible D HW F Cm CR CA CB CK h)

end Formalism.MainNotions.RamifiedCoefficientChains.S9
