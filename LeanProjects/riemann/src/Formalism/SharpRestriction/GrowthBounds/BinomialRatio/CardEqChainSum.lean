import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Chains

variable {N r : ℕ}

theorem strip_iff {nu mu : Fin r → ℤ} {g : ℕ} : Strip nu mu g ↔ HStrip mu nu g := by
  unfold Strip HStrip
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a h => h2 a ⟨a.1 + 1, h⟩ rfl, ?_⟩
    rw [Finset.sum_sub_distrib]; exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun i j hij => ?_, ?_⟩
    · have h : i.1 + 1 < r := hij ▸ j.2
      have hj : j = ⟨i.1 + 1, h⟩ := Fin.ext hij.symm
      rw [hj]; exact h2 i h
    · rw [← Finset.sum_sub_distrib]; exact h3

theorem anti_of_step {f : Fin r → ℤ} (h : ∀ (a : Fin r) (ha : a.1 + 1 < r), f ⟨a.1 + 1, ha⟩ ≤ f a) : Antitone f := by
  have H : ∀ (d a : ℕ) (ha : a < r) (hb : a + d < r), f ⟨a + d, hb⟩ ≤ f ⟨a, ha⟩ := by
    intro d
    induction d with
    | zero => intro a ha hb; exact le_rfl
    | succ d ih =>
      intro a ha hb
      exact le_trans (h ⟨a + d, by omega⟩ hb) (ih a ha (by omega))
  intro a b hab
  have hab' : a.1 ≤ b.1 := hab
  have hb : b = ⟨a.1 + (b.1 - a.1), by have := b.2; omega⟩ := Fin.ext (by simp; omega)
  rw [hb]
  exact H _ a.1 a.2 _

theorem hstrip_anti {nu mu : Fin r → ℤ} {b : ℕ} (h : HStrip nu mu b) : Antitone nu ∧ Antitone mu :=
  ⟨anti_of_step fun a ha => le_trans (h.1 _) (h.2.1 a ha), anti_of_step fun a ha => le_trans (h.2.1 a ha) (h.1 a)⟩

def pathOf (LL : ChainLetters N) (ka : Fin (N + 1) → Fin r → ℤ) (h : IsChain LL ka) :
    PPath r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg where
  mu := ka
  zero := h.1
  dom := fun i => by
    induction i using Fin.cases with
    | zero => rw [h.1]; exact fun _ _ _ => le_rfl
    | succ i =>
      have h2 := h.2 i
      by_cases hv : LL.vec i = true
      · rw [if_pos hv] at h2; exact (hstrip_anti (strip_iff.1 h2)).2
      · rw [if_neg hv] at h2; exact (hstrip_anti (strip_iff.1 h2)).1
  step := fun i => by
    have h2 := h.2 i
    by_cases hv : LL.vec i = true
    · rw [if_pos hv] at h2
      rw [if_pos (show (⟨LL.vec⟩ : Letters (Fin N)).vec i = true from hv)]; exact strip_iff.1 h2
    · rw [if_neg hv] at h2
      rw [if_neg (show ¬ (⟨LL.vec⟩ : Letters (Fin N)).vec i = true from hv)]; exact strip_iff.1 h2

theorem chain_of_path (LL : ChainLetters N) (P : PPath r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg) : IsChain LL P.mu := by
  refine ⟨P.zero, fun i => ?_⟩
  have h2 := P.step i
  by_cases hv : LL.vec i = true
  · rw [if_pos (show (⟨LL.vec⟩ : Letters (Fin N)).vec i = true from hv)] at h2
    rw [if_pos hv]; exact strip_iff.2 h2
  · rw [if_neg (show ¬ (⟨LL.vec⟩ : Letters (Fin N)).vec i = true from hv)] at h2
    rw [if_neg hv]; exact strip_iff.2 h2

theorem ppath_ext {Lt : Letters (Fin N)} {B : Fin N → ℕ} {P P' : PPath r N Lt B} (h : P.mu = P'.mu) : P = P' := by
  cases P; cases P'; simp only at h; subst h; rfl

end Chains

section Span

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem mem_span_iInter {b : ι → V} (hli : LinearIndependent R b) {q : ℕ} (s : Fin q → Set ι) {G : V}
    (hG : G ∈ Submodule.span R (Set.range b)) (h : ∀ k, G ∈ Submodule.span R (b '' s k)) :
    G ∈ Submodule.span R (b '' {x | ∀ k, x ∈ s k}) := by
  rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at hG
  obtain ⟨l, -, hl⟩ := hG
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨l, ?_, hl⟩
  rw [Finsupp.mem_supported]
  intro x hx k
  obtain ⟨lk, hlk, hk⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 (h k)
  have : lk = l := hli (hk.trans hl.symm)
  subst this
  exact (Finsupp.mem_supported R _).1 hlk hx

end Span

section A3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]
  {Lt : Letters (Fin N)} {B : Fin N → ℕ}

abbrev TIdx (r N : ℕ) (Lt : Letters (Fin N)) (B : Fin N → ℕ) :=
  {x : PPath r N Lt B × (ℤ → Finset (Fin r)) // IsSt x.1.mu x.2}

theorem single_cond
    (hspan : Submodule.span O {G | ∃ P : PPath r N Lt B, ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧ G = Psi O P.mu I} =
      Pol O r B)
    (hA3 : ∀ th M : Fin N → ℤ, Formalism.MainNotions.CovariantDegrees.A3at O N r Lt B th M) (Bd : ℤ)
    (hBd : ∀ (P : PPath r N Lt B) (I : ℤ → Finset (Fin r)), IsSt P.mu I → ∀ i a, -Bd ≤ P.mu i a ∧ P.mu i a ≤ Bd)
    (i : Fin N) (Mz : ℤ) (G : MvPolynomial (Fin N × Fin r) O) (hG : G ∈ Pol O r B) :
    lam1S Lt {j | j ≤ i} G ≤ ((Mz : ℤ) : WithBot ℤ) ↔
      G ∈ Submodule.span O ((fun x : TIdx r N Lt B => Psi O x.1.1.mu x.1.2) '' {x | x.1.1.mu i.succ 0 ≤ Mz}) := by
  have hall : ∀ i' : Fin N, (((-Bd : ℤ)) : WithTop ℤ) ≤ valS Lt {j | j ≤ i'} G ∧
      lam1S Lt {j | j ≤ i'} G ≤ ((Bd : ℤ) : WithBot ℤ) := by
    have h := hA3 (fun _ => -Bd) (fun _ => Bd)
    unfold Formalism.MainNotions.CovariantDegrees.A3at at h
    have hmem : G ∈ (Submodule.span O {G | ∃ P : PPath r N Lt B, ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧
        (∀ i : Fin N, (fun _ => -Bd) i ≤ P.mu i.succ (lastIdx r) ∧ P.mu i.succ 0 ≤ (fun _ => Bd) i) ∧
          G = Psi O P.mu I} : Set _) := by
      rw [← hspan] at hG
      refine Submodule.span_mono ?_ hG
      rintro _ ⟨P, I, h1, rfl⟩
      exact ⟨P, I, h1, fun i => ⟨(hBd P I h1 _ _).1, (hBd P I h1 _ _).2⟩, rfl⟩
    rw [← h] at hmem
    exact hmem.2
  have h := hA3 (fun _ => -Bd) (fun i' => if i' = i then Mz else Bd)
  unfold Formalism.MainNotions.CovariantDegrees.A3at at h
  constructor
  · intro hl
    have h1 : G ∈ {G : MvPolynomial (Fin N × Fin r) O | G ∈ Pol O r B ∧ ∀ i' : Fin N,
        (((fun _ => -Bd) i' : ℤ) : WithTop ℤ) ≤ valS Lt {j | j ≤ i'} G ∧
          lam1S Lt {j | j ≤ i'} G ≤ (((fun i' => if i' = i then Mz else Bd) i' : ℤ) : WithBot ℤ)} := by
      refine ⟨hG, fun i' => ⟨(hall i').1, ?_⟩⟩
      by_cases hi : i' = i
      · subst hi; simpa using hl
      · simpa [hi] using (hall i').2
    rw [h] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨P, I, h1, h2, rfl⟩
    exact ⟨⟨(P, I), h1⟩, by simpa using (h2 i).2, rfl⟩
  · intro hs
    have h1 : G ∈ (Submodule.span O {G | ∃ P : PPath r N Lt B, ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧
        (∀ i' : Fin N, (fun _ => -Bd) i' ≤ P.mu i'.succ (lastIdx r) ∧
          P.mu i'.succ 0 ≤ (fun i' => if i' = i then Mz else Bd) i') ∧ G = Psi O P.mu I} : Set _) := by
      refine Submodule.span_mono ?_ hs
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.1.1, x.1.2, x.2, fun i' => ⟨(hBd x.1.1 x.1.2 x.2 _ _).1, ?_⟩, rfl⟩
      by_cases hi : i' = i
      · subst hi; simpa using hx
      · simpa [hi] using (hBd x.1.1 x.1.2 x.2 i'.succ 0).2
    rw [← h] at h1
    simpa using (h1.2 i).2

theorem clear_den {σ : Type} (F : MvPolynomial σ (KK O)) :
    ∃ (d : O) (G : MvPolynomial σ O), d ≠ 0 ∧ MvPolynomial.map (algebraMap O (KK O)) G = d • F := by
  classical
  obtain ⟨sd, hsd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (F.support.image fun m => F.coeff m)
  have hc : ∀ m, ∃ y : O, m ∈ F.support → algebraMap O (KK O) y = (sd : O) • F.coeff m := by
    intro m
    by_cases hm : m ∈ F.support
    · obtain ⟨y, hy⟩ := hsd _ (Finset.mem_image_of_mem _ hm)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose g hg using hc
  refine ⟨sd, ∑ m ∈ F.support, monomial m (g m), nonZeroDivisors.coe_ne_zero sd, ?_⟩
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_monomial, smul_monomial, hg m hm]

end A3

section Zero

variable {K : Type} [Field K] {N r : ℕ} [NeZero r]

theorem chWt_zero (LL : ChainLetters N) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) : chWt LL 0 c m = 0 := by
  unfold chWt
  simp

theorem ycond_zero_top (LL : ChainLetters N) (M : WithTop ℤ) (h : (0 : WithTop ℤ) ≤ M) :
    YCond K (r := r) LL 0 M = ⊤ := by
  refine le_antisymm le_top (le_sSup ⟨?_, fun c d x _ => Submodule.mem_top⟩)
  intro x _
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m _
  show ((chWt LL 0 0 m : ℤ) : WithTop ℤ) ≤ M
  rw [chWt_zero]
  exact_mod_cast h

theorem ycond_zero_bot (LL : ChainLetters N) (M : WithTop ℤ) (h : ¬ (0 : WithTop ℤ) ≤ M) :
    YCond K (r := r) LL 0 M = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun S hS => ?_
  intro x hx
  have h1 := hS.1 hx
  rw [MvPolynomial.mem_restrictSupport_iff] at h1
  rw [Submodule.mem_bot, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro m hm
  have h2 : ((chWt LL 0 0 m : ℤ) : WithTop ℤ) ≤ M := h1 (by exact_mod_cast hm)
  rw [chWt_zero] at h2
  exact h (by exact_mod_cast h2)

end Zero

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

abbrev Tx (r : ℕ) (LL : ChainLetters N) := TIdx r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg

def psiR (R : Type) [CommRing R] (LL : ChainLetters N) (x : Tx r LL) : MvPolynomial (Fin N × Fin r) R :=
  Psi R x.1.1.mu x.1.2

theorem psiR_map (LL : ChainLetters N) (x : Tx r LL) :
    MvPolynomial.map (algebraMap O (KK O)) (psiR O LL x) = psiR (KK O) LL x :=
  Formalism.MainNotions.G.Joints.StandardMonomialSpace.Psi_map _ _ _

theorem psiK_li (LL : ChainLetters N) (hli : LinearIndependent O (psiR (r := r) O LL)) :
    LinearIndependent (KK O) (psiR (r := r) (KK O) LL) := by
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  let φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap
  have h1 : LinearIndependent O (φ ∘ psiR (r := r) O LL) :=
    hli.map' φ (LinearMap.ker_eq_bot.2 (MvPolynomial.map_injective _ hinj))
  have h2 : (φ ∘ psiR (r := r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x
  rw [h2] at h1
  exact (LinearIndependent.iff_fractionRing O (KK O)).1 h1

theorem psiK_mem [CharZero (KK O)] (LL : ChainLetters N) (hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg)
    (x : Tx r LL) : psiR O LL x ∈ Pol O r LL.deg ∧ psiR (KK O) LL x ∈ Pol (KK O) r LL.deg := by
  have h1 : psiR O LL x ∈ Pol O r LL.deg := hrange ▸ Submodule.subset_span ⟨x, rfl⟩
  refine ⟨h1, ?_⟩
  rw [← psiR_map]
  exact (map_mem_Pol_iff _ (IsFractionRing.injective O (KK O)) _ _).2 h1

theorem tx_finite [CharZero (KK O)] (LL : ChainLetters N) (hli : LinearIndependent O (psiR (r := r) O LL))
    (hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg) : Finite (Tx r LL) := by
  have hfd : FiniteDimensional (KK O) (Pol (KK O) r LL.deg) := homogeneous_multidegree_findim LL.deg
  have hle : Submodule.span (KK O) (Set.range (psiR (r := r) (KK O) LL)) ≤ Pol (KK O) r LL.deg :=
    Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (psiK_mem LL hrange x).2)
  have : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range (psiR (r := r) (KK O) LL))) :=
    Submodule.finiteDimensional_of_le hle
  exact Module.Finite.finite_basis (Module.Basis.span (psiK_li LL hli))

theorem exists_bound {Lt : Letters (Fin N)} {B : Fin N → ℕ} [Finite (TIdx r N Lt B)] :
    ∃ Bd : ℤ, ∀ (P : PPath r N Lt B) (I : ℤ → Finset (Fin r)), IsSt P.mu I →
      ∀ i a, -Bd ≤ P.mu i a ∧ P.mu i a ≤ Bd := by
  obtain ⟨Bd, hBd⟩ := (Set.finite_range
    (fun y : TIdx r N Lt B × Fin (N + 1) × Fin r => |y.1.1.1.mu y.2.1 y.2.2|)).bddAbove
  exact ⟨Bd, fun P I h i a => abs_le.1 (hBd ⟨((⟨(P, I), h⟩ : TIdx r N Lt B), i, a), rfl⟩)⟩

def sK (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (k : Fin q) : Set (Tx r LL) :=
  {x | ((x.1.1.mu (finPos N (J k)) 0 : ℤ) : WithTop ℤ) ≤ M k}

theorem one_cond [CharZero (KK O)] (D : Formalism.BasicNotions.D7) (LL : ChainLetters N)
    (hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg)
    (hspan : Submodule.span O {G | ∃ P : PPath r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg,
      ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧ G = Psi O P.mu I} = Pol O r LL.deg)
    (hA3 : ∀ th M : Fin N → ℤ, Formalism.MainNotions.CovariantDegrees.A3at O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg th M) (Bd : ℤ)
    (hBd : ∀ (P : PPath r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg) (I : ℤ → Finset (Fin r)), IsSt P.mu I →
      ∀ i a, -Bd ≤ P.mu i a ∧ P.mu i a ≤ Bd)
    {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N)
    (k : Fin q) (G : MvPolynomial (Fin N × Fin r) O) (hG : G ∈ Pol O r LL.deg) :
    MvPolynomial.map (algebraMap O (KK O)) G ∈ YCond (KK O) (r := r) LL (J k) (M k) ↔
      G ∈ Submodule.span O (psiR O LL '' sK LL J M k) := by
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  cases hM : M k with
  | top =>
    have hs : sK (r := r) LL J M k = Set.univ := by
      ext x; simp only [sK, Set.mem_ofPred_eq, hM, le_top, Set.mem_univ]
    rw [ycond_top, hs, Set.image_univ, hrange]
    exact ⟨fun _ => hG, fun _ => Submodule.mem_top⟩
  | coe Mz =>
    rcases Nat.eq_zero_or_pos (J k) with h0 | hpos
    · have hmu : ∀ x : Tx r LL, x.1.1.mu (finPos N (J k)) 0 = 0 := by
        intro x
        have h00 : finPos N (J k) = 0 := by rw [h0]; apply Fin.ext; simp [finPos]
        rw [h00, x.1.1.zero]; rfl
      rw [h0]
      by_cases hz : (0 : WithTop ℤ) ≤ (Mz : WithTop ℤ)
      · have hs : sK (r := r) LL J M k = Set.univ := by
          ext x
          simp only [sK, Set.mem_ofPred_eq, hM, hmu x, Set.mem_univ, iff_true]
          exact_mod_cast hz
        rw [ycond_zero_top _ _ hz, hs, Set.image_univ, hrange]
        exact ⟨fun _ => hG, fun _ => Submodule.mem_top⟩
      · have hs : sK (r := r) LL J M k = ∅ := by
          ext x
          simp only [sK, Set.mem_ofPred_eq, hM, hmu x, Set.mem_empty_iff_false, iff_false]
          intro h; exact hz (by exact_mod_cast h)
        rw [ycond_zero_bot _ _ hz, hs, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
        exact map_eq_zero_iff _ (MvPolynomial.map_injective _ hinj)
    · obtain ⟨i, hi⟩ : ∃ i : Fin N, J k = i.val + 1 :=
        ⟨⟨J k - 1, by have := hJ k; omega⟩, by simp only; omega⟩
      have hfp : finPos N (J k) = i.succ := by
        apply Fin.ext
        have := i.2
        simp only [finPos, hi, Fin.val_succ]
        omega
      have hS : {l : Fin N | (l : ℕ) < J k} = {j | j ≤ i} := by
        ext l
        simp only [Set.mem_ofPred_eq, hi, Fin.le_def]
        omega
      have hs : sK (r := r) LL J M k = {x | x.1.1.mu i.succ 0 ≤ Mz} := by
        ext x
        simp only [sK, Set.mem_ofPred_eq, hM, hfp]
        exact WithTop.coe_le_coe
      rw [mem_ycond_iff D LL (J k) Mz, Formalism.MainNotions.G.Joints.StandardMonomialSpace.lowest_degree_map_of_injective _ hinj, hS,
        single_cond hspan hA3 Bd hBd i Mz G hG, hs]
      rfl

def sAll (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Set (Tx r LL) :=
  {x | ∀ k, x ∈ sK LL J M k}

theorem map_span (LL : ChainLetters N) (s : Set (Tx r LL)) (G : MvPolynomial (Fin N × Fin r) O)
    (hG : G ∈ Submodule.span O (psiR O LL '' s)) :
    MvPolynomial.map (algebraMap O (KK O)) G ∈ Submodule.span (KK O) (psiR (KK O) LL '' s) := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact Submodule.subset_span ⟨y, hy, (psiR_map LL y).symm⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem span_eq_Yjt [CharZero (KK O)] (LL : ChainLetters N) (hli : LinearIndependent O (psiR (r := r) O LL))
    (hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg)
    {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (hC1 : ∀ (k : Fin q) (G : MvPolynomial (Fin N × Fin r) O), G ∈ Pol O r LL.deg →
      (MvPolynomial.map (algebraMap O (KK O)) G ∈ YCond (KK O) (r := r) LL (J k) (M k) ↔
        G ∈ Submodule.span O (psiR O LL '' sK LL J M k))) :
    Submodule.span (KK O) (psiR (KK O) LL '' sAll LL J M) = Yjt (KK O) (r := r) LL J M := by
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show psiR (KK O) LL x ∈ Yjt (KK O) (r := r) LL J M
    rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf]
    refine ⟨(psiK_mem LL hrange x).2, fun k => ?_⟩
    rw [← psiR_map]
    exact (hC1 k _ (psiK_mem LL hrange x).1).2 (Submodule.subset_span ⟨x, hx k, rfl⟩)
  · intro F hF
    obtain ⟨d, G, hd, hG⟩ := clear_den F
    have hdF : d • F ∈ Yjt (KK O) (r := r) LL J M := by
      rw [← algebraMap_smul (KK O) d F]; exact Submodule.smul_mem _ _ hF
    rw [← hG, Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hdF
    have hGP : G ∈ Pol O r LL.deg := (map_mem_Pol_iff _ hinj _ G).1 hdF.1
    have hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M) :=
      mem_span_iInter hli (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hdF.2 k))
    have h1 := map_span LL _ G hGs
    rw [hG, ← algebraMap_smul (KK O) d F] at h1
    exact (Submodule.smul_mem_iff _ (fun h0 => hd (hinj (by rw [h0, map_zero])))).1 h1

omit [NeZero r] in
theorem fiber_card (LL : ChainLetters N) (s : Set (Tx r LL)) (hs : ∀ x y : Tx r LL, x.1.1.mu = y.1.1.mu → x ∈ s → y ∈ s)
    (x0 : {x : Tx r LL // x ∈ s}) :
    Nat.card {y : {x : Tx r LL // x ∈ s} // y.1.1.1.mu = x0.1.1.1.mu} =
      Nat.card {I : ℤ → Finset (Fin r) // IsSt x0.1.1.1.mu I} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => (⟨y.1.1.1.2, by have h := y.1.1.2; rw [y.2] at h; exact h⟩ :
      {I : ℤ → Finset (Fin r) // IsSt x0.1.1.1.mu I})) ⟨?_, ?_⟩)
  · intro y y' h
    have hI : y.1.1.1.2 = y'.1.1.1.2 := congrArg Subtype.val h
    have hP : y.1.1.1.1 = y'.1.1.1.1 := ppath_ext (y.2.trans y'.2.symm)
    exact Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext hP hI)))
  · rintro ⟨I, hI⟩
    exact ⟨⟨⟨⟨(x0.1.1.1, I), hI⟩, hs x0.1 _ rfl x0.2⟩, rfl⟩, rfl⟩

theorem card_eq_chainSum (hSt : StWeylAt) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    [Finite (Tx r LL)] :
    (Nat.card {x : Tx r LL // x ∈ sAll LL J M} : ℚ) = chainSum (r := r) LL J M := by
  classical
  unfold chainSum
  have : Fintype {x : Tx r LL // x ∈ sAll LL J M} := Fintype.ofFinite _
  let π : {x : Tx r LL // x ∈ sAll LL J M} → (Fin (N + 1) → Fin r → ℤ) := fun x => x.1.1.1.mu
  have hsupp : (Function.support fun ka : Fin (N + 1) → Fin r → ℤ =>
      if IsChain LL ka ∧ ChainOK J M ka then wdim (ka (Fin.last N)) else 0) ⊆ ↑(Finset.univ.image π) := by
    intro ka hka
    rw [Function.mem_support] at hka
    by_cases hC : IsChain LL ka ∧ ChainOK J M ka
    · rw [if_pos hC] at hka
      have hcard : (Nat.card {I : ℤ → Finset (Fin r) // IsSt ka I} : ℚ) = wdim (ka (Fin.last N)) :=
        hSt r N _ LL.deg (pathOf LL ka hC.1)
      have hne : Nat.card {I : ℤ → Finset (Fin r) // IsSt ka I} ≠ 0 := by
        intro h0
        apply hka
        rw [← hcard, h0, Nat.cast_zero]
      obtain ⟨⟨I, hI⟩⟩ := (Nat.card_ne_zero.1 hne).1
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨⟨⟨(pathOf LL ka hC.1, I), hI⟩, hC.2⟩, rfl⟩
    · rw [if_neg hC] at hka; exact absurd rfl hka
  rw [finsum_eq_sum_of_support_subset _ hsupp, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_image π Finset.univ]
  push_cast
  refine Finset.sum_congr rfl fun ka hka => ?_
  obtain ⟨x0, -, rfl⟩ := Finset.mem_image.1 hka
  have hC : IsChain LL (π x0) ∧ ChainOK J M (π x0) := ⟨chain_of_path LL x0.1.1.1, x0.2⟩
  rw [if_pos hC]
  have hcard : (Nat.card {I : ℤ → Finset (Fin r) // IsSt (π x0) I} : ℚ) = wdim (π x0 (Fin.last N)) :=
    hSt r N _ LL.deg x0.1.1.1
  rw [← hcard]
  congr 1
  rw [← fiber_card LL (sAll LL J M) (fun x y hxy hx k => by
    have := hx k
    simp only [sK, Set.mem_ofPred_eq] at this ⊢
    rw [← hxy]; exact this) x0, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem dimY_of {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (hSt : StWeylAt) :
    DimYAt := by
  intro p _ O _ _ _ S N r _ LL q J M hJ
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  have hY := span_eq_Yjt LL hli' hrange J M hC1
  have hliC : LinearIndependent (KK O) (fun x : {x : Tx r LL // x ∈ sAll LL J M} => psiR (KK O) LL x.1) :=
    (psiK_li LL hli').comp _ Subtype.val_injective
  have hrangeC : Set.range (fun x : {x : Tx r LL // x ∈ sAll LL J M} => psiR (KK O) LL x.1) =
      psiR (KK O) LL '' sAll LL J M := by
    ext F
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hfr : Module.finrank (KK O) (Yjt (KK O) (r := r) LL J M) = Nat.card {x : Tx r LL // x ∈ sAll LL J M} := by
    rw [← hY, ← hrangeC]
    exact Module.finrank_eq_nat_card_basis (Module.Basis.span hliC)
  rw [hfr]
  exact card_eq_chainSum hSt LL J M

end Main

end Formalism.MainNotions.ColumnSystems.Pf
