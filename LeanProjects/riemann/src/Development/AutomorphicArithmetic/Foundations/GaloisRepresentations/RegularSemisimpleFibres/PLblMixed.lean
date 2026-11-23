import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem perm_lift {α β : Type*} (f : α → β) {m m' : List β} (h : m.Perm m') :
    ∀ l : List α, l.map f = m' → ∃ l' : List α, l'.Perm l ∧ l'.map f = m := by
  induction h with
  | nil => intro l hl; exact ⟨l, .refl _, hl⟩
  | cons b _ ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨l', hp, hm⟩ := ih l hl.2
      exact ⟨a :: l', hp.cons a, by simp [hm, hl.1]⟩
  | swap a b t =>
    intro l hl
    match l, hl with
    | u :: v :: l, hl =>
      simp only [List.map_cons, List.cons.injEq] at hl
      exact ⟨v :: u :: l, .swap _ _ _, by simp [hl.1, hl.2.1, hl.2.2]⟩
  | trans _ _ ih₁ ih₂ =>
    intro l hl
    obtain ⟨l₂, hp₂, hm₂⟩ := ih₂ l hl
    obtain ⟨l₁, hp₁, hm₁⟩ := ih₁ l₂ hm₂
    exact ⟨l₁, hp₁.trans hp₂, hm₁⟩

private theorem pairwise_filter_sym {α : Type*} (r : α → α → Prop) (p : α → Prop) [DecidablePred p] (l : List α)
    (h : (Multiset.filter p (l : Multiset α)).Pairwise r) :
    (l.filter fun b => decide (p b)).Pairwise fun y z => r y z ∨ r z y := by
  obtain ⟨l', hl', hp⟩ := h
  rw [Multiset.filter_coe, Multiset.coe_eq_coe] at hl'
  exact (List.Perm.pairwise_iff (fun h => h.symm) hl').2 (hp.imp Or.inl)

private theorem inert_both {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hIn : ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) k)), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩)
    (θ : AlgebraicClosure 𝓀[k] →* ℂ) (y z : IrrGL k) (hy : y.IsCusp) (hz : z.IsCusp)
    (hy' : UpperTheory.Zero.LLC.DZ y) (hz' : UpperTheory.Zero.LLC.DZ z) (cy cz : ℕ)
    (ty : ∀ γ, LinearMap.trace ℂ _ (levelZero y.rep γ) = cusp θ y.1 cy γ)
    (tz : ∀ γ, LinearMap.trace ℂ _ (levelZero z.rep γ) = cusp θ z.1 cz γ)
    (h : y.1 = z.1) (hc : cusp θ y.1 cz = cusp θ y.1 cy) : y.Inert z ∧ z.Inert y := by
  obtain ⟨m, X⟩ := y
  obtain ⟨m', Y⟩ := z
  obtain rfl : m = m' := h
  have e : ∀ γ, LinearMap.trace ℂ _ (levelZero X.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero Y.rep.ρ γ) := fun γ => by
    have h1 := ty γ
    have h2 := tz γ
    exact h1.trans ((congrFun hc γ).symm.trans h2.symm)
  exact ⟨hIn m X Y hy hz hy' hz' e, hIn m Y X hz hy hz' hy' fun γ => (e γ).symm⟩

private theorem core {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (hG : Group1) (hCF : CuspFrob) (hUF : UnlFull) (hJP : JDPair) (hJC : JDChar) (hLF : LblFull)
    (hIn : ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) k)), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩)
    (θ : AlgebraicClosure 𝓀[k] →* ℂ) (hθ : Inj θ) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hsm : IsSmooth π) (hirr : π.IsIrreducible)
    (s : Multiset (IrrGL k)) (hs : HasSupport π s) (hU : GlobalTheory.RoadU.Unlinked s)
    (hP : (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z)
    (m : ℕ) (x : Fin m → IrrGL k) (c : Fin m → ℕ) (hxs : Finset.univ.val.map x = s)
    (hx : ∀ a, (x a).IsCusp ∧ UpperTheory.Zero.LLC.DZ (x a) ∧ Reg (Nat.card 𝓀[k]) (x a).1 (c a) ∧
        ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).1 (c a) γ)
    (hL : HasLbl θ π ⟨Nat.card 𝓀[k], [], List.ofFn fun a => ((x a).1, c a)⟩) :
    ∃ a : Lbl, HasLbl θ π a ∧ a.Apart ∧ ∀ p ∈ a.L, ∃ y ∈ s, y.1 = p.1 := by
  obtain ⟨⟨hq2, -, hOk⟩, -, hn, -⟩ := hL
  have hpos : ∀ a, 0 < (x a).1 := fun a => (hOk _ (List.mem_ofFn.2 ⟨a, rfl⟩)).1
  set q := Nat.card 𝓀[k] with hq
  let c₁ : Fin m → ℕ := fun a => if (x a).1 = 1 then c a % (q - 1) else c a
  have hc₁ : ∀ a, cusp θ (x a).1 (c₁ a) = cusp θ (x a).1 (c a) := by
    intro a
    by_cases h : (x a).1 = 1
    · refine hCF 𝓀[k] θ hθ (x a).1 (c a) (c₁ a) 0 (hpos a) ?_
      simp only [c₁, if_pos h, h, ← hq, pow_one, pow_zero, mul_one]
      exact Nat.mod_modEq _ _
    · simp only [c₁, if_neg h]
  have hreg : ∀ a, Reg q (x a).1 (c₁ a) := by
    intro a
    by_cases h : (x a).1 = 1
    · intro i h0 h1
      omega
    · simp only [c₁, if_neg h]
      exact (hx a).2.2.1
  let f : IrrGL k × ℕ → ℕ × ℕ := fun t => (t.1.1, t.2)
  let T₀ : List (IrrGL k × ℕ) := List.ofFn fun a => (x a, c₁ a)
  have hmem : ∀ t ∈ T₀, ∃ a, t = (x a, c₁ a) := fun t ht => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 ht
    exact ⟨a, rfl⟩
  have hmemL : ∀ p ∈ T₀.map f, ∃ a, p = ((x a).1, c₁ a) := fun p hp => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
    obtain ⟨a, rfl⟩ := hmem t ht
    exact ⟨a, rfl⟩
  obtain ⟨D, hD, hDn, hDp⟩ := hG (T₀.map f) (fun p hp => by
    obtain ⟨a, rfl⟩ := hmemL p hp
    exact hpos a)
  obtain ⟨T, hTp, hTm⟩ := perm_lift f hDp T₀ rfl

  let x' : Fin T.length → IrrGL k := fun a => (T.get a).1
  let c' : Fin T.length → ℕ := fun a => (T.get a).2
  have hmap : Finset.univ.val.map x' = s := by
    rw [← hxs, Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe]
    have e1 : List.ofFn x' = T.map Prod.fst := by
      conv_rhs => rw [← List.ofFn_get T, List.map_ofFn]
      rfl
    have e2 : List.ofFn x = T₀.map Prod.fst := by
      simp only [T₀, List.map_ofFn]
      rfl
    rw [e1, e2]
    exact hTp.map _
  have hofn : List.ofFn (fun a => ((x' a).1, c' a)) = expand D ++ (T₀.map f).filter fun p => 2 ≤ p.1 := by
    rw [← hTm]
    conv_rhs => rw [← List.ofFn_get T, List.map_ofFn]
    rfl
  have hdegP : GlobalTheory.Shin.deg (expand D ++ (T₀.map f).filter fun p => 2 ≤ p.1) = GlobalTheory.Shin.deg (T₀.map f) := by
    unfold GlobalTheory.Shin.deg
    exact (hDp.map _).sum_eq
  have hdeg₀ : GlobalTheory.Shin.deg (T₀.map f) = n := by
    rw [hn]
    show _ = GlobalTheory.Shin.deg [] + GlobalTheory.Shin.deg _
    simp only [GlobalTheory.Shin.deg, T₀, List.map_ofFn, List.map_nil, List.sum_nil, zero_add]
    rfl
  have hd' : ∑ a, (x' a).1 = n := by
    rw [← hdeg₀, ← hdegP, ← hofn]
    simp only [GlobalTheory.Shin.deg, List.map_ofFn, List.sum_ofFn]
    rfl
  have heq := hUF k n V π T.length x' hd' (by rw [hmap]; exact hs) (by rw [hmap]; exact hU)
  have key : ∀ t ∈ T, ∀ γ, LinearMap.trace ℂ _ (levelZero t.1.rep γ) = cusp θ t.1.1 t.2 γ := by
    intro t ht
    obtain ⟨b, rfl⟩ := hmem t (hTp.mem_iff.1 ht)
    intro γ
    exact ((hx b).2.2.2 γ).trans (congrFun (hc₁ b) γ).symm
  have htr : ∀ a γ, LinearMap.trace ℂ _ (levelZero (x' a).rep γ) = cusp θ (x' a).1 (c' a) γ :=
    fun a => key (T.get a) (List.get_mem _ _)
  have hLm : ∀ p ∈ (T₀.map f).filter (fun p => 2 ≤ p.1), ∃ a, p = ((x a).1, c a) ∧ 2 ≤ (x a).1 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    obtain ⟨a, rfl⟩ := hmemL p hp1
    have h2 : 2 ≤ (x a).1 := by simpa using hp2
    refine ⟨a, ?_, h2⟩
    have : (x a).1 ≠ 1 := by omega
    simp only [c₁, if_neg this]
  let a₀ : Lbl := ⟨q, D, (T₀.map f).filter fun p => 2 ≤ p.1⟩
  have hOk₀ : a₀.Ok := by
    refine ⟨hq2, fun p hp => (hD p hp).1, fun p hp => ?_⟩
    obtain ⟨a, rfl, -⟩ := hLm p hp
    exact ⟨hpos a, (hx a).2.2.1⟩
  obtain ⟨hJ1, hJ2⟩ := hJP 𝓀[k] θ hθ a₀ hOk₀ rfl
  have hrk : n = a₀.rk := by
    rw [← hJ1]
    exact (hdegP.trans hdeg₀).symm
  have hch := (hJC 𝓀[k] θ hθ).2 a₀ hOk₀ rfl
  rw [← hrk] at hJ2 hch
  have hMeets : Meets (levelZero π) (JD θ a₀.D a₀.L n) :=
    hLF k θ n V π hsm hirr T.length x' c' hd' heq htr _ hch (by rw [hofn]; exact hJ2)
  refine ⟨a₀, ⟨hOk₀, rfl, hrk, hMeets⟩, ⟨?_, hDn, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, ha⟩ := hmemL _ (hD p hp).2
    have h1 : (x a).1 = 1 := (Prod.ext_iff.1 ha).1.symm
    have h2 : p.2 = c₁ a := (Prod.ext_iff.1 ha).2
    show p.2 < q - 1
    rw [h2]
    simp only [c₁, if_pos h1]
    exact Nat.mod_lt _ (by have : 2 ≤ q := hq2; omega)
  · intro p hp
    obtain ⟨a, rfl, h2⟩ := hLm p hp
    exact h2
  · have hs₀ : s = ((T₀.map Prod.fst : List _) : Multiset _) := by
      rw [← hxs, Fin.univ_val_map]
      simp only [T₀, List.map_ofFn]
      rfl
    rw [hs₀] at hP
    have h1 := pairwise_filter_sym _ _ _ hP
    rw [List.filter_map, List.pairwise_map] at h1
    show ((T₀.map f).filter _).Pairwise _
    rw [List.filter_map, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ h1
    intro t₁ t₂ m₁ m₂ hh heq i hcong
    obtain ⟨m₁, r₁⟩ := List.mem_filter.1 m₁
    obtain ⟨m₂, r₂⟩ := List.mem_filter.1 m₂
    obtain ⟨a, rfl⟩ := hmem t₁ m₁
    obtain ⟨b, rfl⟩ := hmem t₂ m₂
    have ra : 2 ≤ (x a).1 := by simpa using r₁
    have rb : 2 ≤ (x b).1 := by simpa using r₂
    have na : (x a).1 ≠ 1 := by omega
    have nb : (x b).1 ≠ 1 := by omega
    have hcong' : c b ≡ c a * q ^ i [MOD q ^ (x a).1 - 1] := by
      have : c₁ b ≡ c₁ a * q ^ i [MOD q ^ (x a).1 - 1] := hcong
      simpa only [c₁, if_neg na, if_neg nb] using this
    have := inert_both hIn θ (x a) (x b) (hx a).1 (hx b).1 (hx a).2.1 (hx b).2.1 (c a) (c b) (hx a).2.2.2 (hx b).2.2.2
      heq (hCF 𝓀[k] θ hθ (x a).1 (c a) (c b) i (hpos a) hcong')
    exact hh.elim (· this.1) (· this.2)
  · intro p hp
    obtain ⟨a, rfl, -⟩ := hLm p hp
    exact ⟨x a, by rw [← hxs]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a), rfl⟩

theorem UpperTheory.Gal.InertialTypesAlt.lblMixed :
    LblOf → Group1 → CuspFrob → InertOf → UnlFull → JDPair → JDChar → LblFull → LblMixed := by
  intro hOf hG hCF hIn hUF hJP hJC hLF E Ω _ _ _ _ _ A v hv g _ i hi θ hθ n τ hM
  haveI : CharZero (v.adicCompletion E) :=
    charZero_of_injective_algebraMap (R := E) (algebraMap E (v.adicCompletion E)).injective
  obtain ⟨hDZ, s, hs, hU, hP⟩ := hM
  have e₀ := IrrGL.equivOf τ.ρ τ.smooth τ.irred
  have hs' : HasSupport τ.ρ s := hs.of_equiv e₀.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv e₀.symm hDZ
  obtain ⟨m, x, c, hxs, hx, hL⟩ := hOf (v.adicCompletion E) θ hθ n τ.V τ.ρ s hs' hfix
  obtain ⟨a, h1, h2, h3⟩ := core hG hCF hUF hJP hJC hLF (hIn E Ω A v hv g i hi) θ hθ n τ.ρ τ.smooth τ.irred s hs' hU hP
    m x c hxs hx hL
  exact ⟨a, s, h1, h2, hs', h3⟩
