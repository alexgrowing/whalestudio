import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSplit

section Ext

variable {O M M' : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']

theorem mem_of_pow_smul_mem (c : O) (W : Submodule O M) (h2 : ∀ x : M, c • x ∈ W → x ∈ W) (k : ℕ) (x : M)
    (h : c ^ k • x ∈ W) : x ∈ W := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    refine ih (h2 _ ?_)
    rw [smul_smul, ← pow_succ']
    exact h

theorem exists_ext (c : O) (W : Submodule O M) (ρ₀ : W →ₗ[O] M')
    (h1 : ∀ x : M, ∃ w ∈ W, ∃ z, x = w + c • z) (h2 : ∀ x : M, c • x ∈ W → x ∈ W)
    (hS : ∀ y : M', (∀ k : ℕ, ∃ z, y = c ^ k • z) → y = 0)
    (hC : ∀ y : ℕ → M', (∀ k, ∃ z, y (k + 1) - y k = c ^ k • z) → ∃ L, ∀ k, ∃ z, L - y k = c ^ k • z) :
    ∃ ρ : M →ₗ[O] M', ∀ w : W, ρ w = ρ₀ w := by
  have hD : ∀ (k : ℕ) (w w' : W) (t : M), (w : M) - w' = c ^ k • t → ∃ z, ρ₀ w - ρ₀ w' = c ^ k • z := by
    intro k w w' t h
    have ht : t ∈ W := mem_of_pow_smul_mem c W h2 k t (h ▸ W.sub_mem w.2 w'.2)
    refine ⟨ρ₀ ⟨t, ht⟩, ?_⟩
    rw [← map_sub, ← map_smul]
    congr 1
    exact Subtype.ext (by simpa using h)
  have hA : ∀ (k : ℕ) (x : M), ∃ (w : W) (z : M), x = w + c ^ k • z := by
    intro k
    induction k with
    | zero => exact fun x => ⟨0, x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨w, z, e⟩ := ih x
      obtain ⟨w', hw', z', e'⟩ := h1 z
      refine ⟨w + c ^ k • ⟨w', hw'⟩, z', ?_⟩
      rw [e]
      nth_rw 1 [e']
      simp only [Submodule.coe_add, Submodule.coe_smul]
      module
  let Rel : M → M' → Prop := fun x y =>
    ∀ (k : ℕ) (w : W) (z : M), x = w + c ^ k • z → ∃ z', y - ρ₀ w = c ^ k • z'
  have hE : ∀ x, ∃ y, Rel x y := by
    intro x
    choose w z hwz using fun k => hA k x
    obtain ⟨L, hL⟩ := hC (fun k => ρ₀ (w k)) (fun k => hD k _ _ (z k - c • z (k + 1)) (by
      have e : (w (k + 1) : M) + c ^ (k + 1) • z (k + 1) = w k + c ^ k • z k := (hwz (k + 1)).symm.trans (hwz k)
      linear_combination (norm := module) e))
    refine ⟨L, fun k v t e => ?_⟩
    obtain ⟨a, ha⟩ := hL k
    obtain ⟨b, hb⟩ := hD k (w k) v (t - z k) (by
      have e' : (w k : M) + c ^ k • z k = v + c ^ k • t := (hwz k).symm.trans e
      linear_combination (norm := module) e')
    refine ⟨a + b, ?_⟩
    rw [smul_add, ← ha, ← hb]
    abel
  have hU : ∀ x y y', Rel x y → Rel x y' → y = y' := by
    intro x y y' h h'
    refine sub_eq_zero.1 (hS _ fun k => ?_)
    obtain ⟨w, z, e⟩ := hA k x
    obtain ⟨a, ha⟩ := h k w z e
    obtain ⟨b, hb⟩ := h' k w z e
    refine ⟨a - b, ?_⟩
    rw [smul_sub, ← ha, ← hb]
    abel
  have hW : ∀ w : W, Rel w (ρ₀ w) := by
    intro w k v t e
    exact hD k w v t (by rw [e]; abel)
  have hL : ∀ (a : O) x x' y y', Rel x y → Rel x' y' → Rel (a • x + x') (a • y + y') := by
    intro a x x' y y' h h' k v t e
    obtain ⟨w, z, e1⟩ := hA k x
    obtain ⟨w', z', e2⟩ := hA k x'
    obtain ⟨p, hp⟩ := h k w z e1
    obtain ⟨p', hp'⟩ := h' k w' z' e2
    obtain ⟨b, hb⟩ := hD k (a • w + w') v (t - a • z - z') (by
      rw [e1, e2] at e
      simp only [Submodule.coe_add, Submodule.coe_smul]
      linear_combination (norm := module) e)
    refine ⟨a • p + p' + b, ?_⟩
    rw [map_add, map_smul] at hb
    rw [smul_add, smul_add, ← hb, smul_comm, ← hp, ← hp', smul_sub]
    abel
  choose ρ hρ using hE
  have h0 : ρ 0 = 0 := by
    have e : Rel 0 0 := by simpa using hW 0
    exact hU _ _ _ (hρ 0) e
  refine ⟨{ toFun := ρ, map_add' := ?_, map_smul' := ?_ }, fun w => hU _ _ _ (hρ w) (hW w)⟩
  · intro x x'
    have := hL 1 x x' _ _ (hρ x) (hρ x')
    simp only [one_smul] at this
    exact hU _ _ _ (hρ _) this
  · intro a x
    have := hL a x 0 _ _ (hρ x) (hρ 0)
    simp only [add_zero, h0] at this
    exact hU _ _ _ (hρ _) this

end Ext

end GlobalTheory.CompanionTheory.LatSplit

namespace GlobalTheory.CompanionTheory.LatSplit

section Basic

variable {O N : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N] [Module O N]

theorem exists_basic_irreducible (ϖ : O) (hϖ : Irreducible ϖ)
    (ht : ∀ (a : O) (n : N), a ≠ 0 → a • n = 0 → n = 0) :
    ∃ P : Submodule O N, Module.Free O P ∧ (∀ n, ∃ p ∈ P, ∃ z, n = p + ϖ • z) ∧
      ∀ n, ϖ • n ∈ P → n ∈ P := by
  classical
  let I : Ideal O := Ideal.span {ϖ}
  haveI hI : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  let B := Module.Basis.ofVectorSpace (O ⧸ I) (N ⧸ (I • ⊤ : Submodule O N))
  let q : N →ₗ[O] N ⧸ (I • ⊤ : Submodule O N) := Submodule.mkQ _
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hmem : ∀ x : N, x ∈ (I • ⊤ : Submodule O N) ↔ ∃ z, x = ϖ • z := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, trivial, rfl⟩
  choose e he using fun j => hq (B j)
  have hstar : ∀ (s : Finset _) (g : _ → O), (∑ i ∈ s, g i • e i) ∈ (I • ⊤ : Submodule O N) →
      ∀ i ∈ s, ϖ ∣ g i := by
    intro s g h i hi
    have h0 : q (∑ i ∈ s, g i • e i) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h
    rw [map_sum] at h0
    have h1 : ∑ i ∈ s, (Ideal.Quotient.mk I (g i)) • B i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, he]
      rfl
    have h2 := linearIndependent_iff'.1 B.linearIndependent s _ h1 i hi
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have hall : ∀ (s : Finset _) (t : ℕ) (g : _ → O), (∑ i ∈ s, g i • e i) = 0 → ∀ i ∈ s, ϖ ^ t ∣ g i := by
    intro s t
    induction t with
    | zero => simp
    | succ t ih =>
      intro g h i hi
      have h1 := hstar s g (by rw [h]; exact Submodule.zero_mem _)
      have h2 : ∀ i, ∃ g', i ∈ s → g i = ϖ * g' := fun i => by
        by_cases hi : i ∈ s
        · obtain ⟨g', hg'⟩ := h1 i hi
          exact ⟨g', fun _ => hg'⟩
        · exact ⟨0, fun h => absurd h hi⟩
      choose g' hg' using h2
      have h3 : ∑ i ∈ s, g' i • e i = 0 := by
        refine ht ϖ _ hϖ.ne_zero ?_
        rw [Finset.smul_sum, ← h]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hg' i hi, mul_smul]
      rw [hg' i hi, pow_succ']
      exact mul_dvd_mul_left _ (ih g' h3 i hi)
  have hli : LinearIndependent O e := by
    refine linearIndependent_iff'.2 fun s g h i hi => ?_
    by_contra hne
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
    have h1 := hall s (n + 1) g h i hi
    have h2 : ϖ ^ n * ϖ ∣ ϖ ^ n * 1 := by
      rw [← pow_succ, mul_one, ← hu]
      exact Dvd.dvd.mul_right h1 _
    exact hϖ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 h2))
  refine ⟨Submodule.span O (Set.range e), Module.Free.of_basis (Module.Basis.span hli), ?_, ?_⟩
  · intro n
    have h1 : q n ∈ Submodule.span O (Set.range B) := by
      rw [← Submodule.restrictScalars_span O (O ⧸ I) Ideal.Quotient.mk_surjective, Submodule.restrictScalars_mem,
        B.span_eq]
      trivial
    have h2 : Set.range B = q '' Set.range e := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun j => (he j).symm)
    rw [h2, ← Submodule.map_span] at h1
    obtain ⟨p, hp, hpq⟩ := h1
    have h3 : n - p ∈ (I • ⊤ : Submodule O N) := (Submodule.Quotient.eq _).1 hpq.symm
    obtain ⟨z, hz⟩ := (hmem _).1 h3
    exact ⟨p, hp, z, by rw [← hz]; abel⟩
  · intro n hn
    obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hn
    have h1 := hstar f.support f (by
      have : (∑ i ∈ f.support, f i • e i) = ϖ • n := hf
      rw [this]
      exact (hmem _).2 ⟨n, rfl⟩)
    have h2 : ∀ i, ∃ g', i ∈ f.support → f i = ϖ * g' := fun i => by
      by_cases hi : i ∈ f.support
      · obtain ⟨g', hg'⟩ := h1 i hi
        exact ⟨g', fun _ => hg'⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose g' hg' using h2
    have h3 : n - ∑ i ∈ f.support, g' i • e i = 0 := by
      refine ht ϖ _ hϖ.ne_zero ?_
      have : ϖ • ∑ i ∈ f.support, g' i • e i = ϖ • n := by
        rw [Finset.smul_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_) hf
        change ϖ • g' i • e i = f i • e i
        rw [hg' i hi, mul_smul]
      rw [smul_sub, this, sub_self]
    rw [sub_eq_zero.1 h3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basic (ht : ∀ (a : O) (n : N), a ≠ 0 → a • n = 0 → n = 0) (c : O) (hc : c ≠ 0) :
    ∃ P : Submodule O N, Module.Free O P ∧ (∀ n, ∃ p ∈ P, ∃ z, n = p + c • z) ∧
      ∀ n, c • n ∈ P → n ∈ P := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨P, hF, h1, h2⟩ := exists_basic_irreducible ϖ hϖ ht
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
  have hA : ∀ (k : ℕ) (n : N), ∃ p ∈ P, ∃ z, n = p + ϖ ^ k • z := by
    intro k
    induction k with
    | zero => exact fun n => ⟨0, P.zero_mem, n, by simp⟩
    | succ k ih =>
      intro n
      obtain ⟨p, hp, z, e⟩ := ih n
      obtain ⟨p', hp', z', e'⟩ := h1 z
      refine ⟨p + ϖ ^ k • p', P.add_mem hp (P.smul_mem _ hp'), z', ?_⟩
      rw [e]
      nth_rw 1 [e']
      module
  refine ⟨P, hF, fun n => ?_, fun n hn => ?_⟩
  · obtain ⟨p, hp, z, e⟩ := hA k n
    refine ⟨p, hp, (u : O) • z, ?_⟩
    rw [e, ← hu, smul_smul]
  · refine mem_of_pow_smul_mem ϖ P h2 k n ?_
    rw [← hu, mul_comm, mul_smul]
    exact P.smul_mem _ hn

end Basic

end GlobalTheory.CompanionTheory.LatSplit

namespace GlobalTheory.CompanionTheory.LatSplit

section Sec

variable {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M]

theorem exists_section (M' : Submodule O M) (c : O) (hc : c ≠ 0)
    (ht : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ M' → x ∈ M')
    (hS : ∀ y : M', (∀ k : ℕ, ∃ z : M', y = c ^ k • z) → y = 0)
    (hC : ∀ y : ℕ → M', (∀ k, ∃ z : M', y (k + 1) - y k = c ^ k • z) → ∃ L : M', ∀ k, ∃ z : M', L - y k = c ^ k • z) :
    ∃ s : (M ⧸ M') →ₗ[O] M, ∀ n, M'.mkQ (s n) = n := by
  obtain ⟨P, hF, h1, h2⟩ := exists_basic (N := M ⧸ M') (fun a n ha h => by
    obtain ⟨x, rfl⟩ := M'.mkQ_surjective n
    refine (Submodule.Quotient.mk_eq_zero _).2 (ht a x ha ((Submodule.Quotient.mk_eq_zero _).1 ?_))
    simpa using h) c hc
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property M'.mkQ P.subtype (Submodule.mkQ_surjective _)
  have hσ' : ∀ p : P, M'.mkQ (σ p) = p := fun p => LinearMap.congr_fun hσ p
  let W : Submodule O M := P.comap M'.mkQ
  let π : W →ₗ[O] P := M'.mkQ.restrict fun x hx => hx
  have hπ : ∀ w : W, (π w : M ⧸ M') = M'.mkQ w := fun w => rfl
  let ρ₀ : W →ₗ[O] M' := (W.subtype - σ ∘ₗ π).codRestrict M' fun w => by
    have : M'.mkQ ((w : M) - σ (π w)) = 0 := by rw [map_sub, hσ', hπ, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  have hρ₀ : ∀ w : W, (ρ₀ w : M) = w - σ (π w) := fun w => rfl
  obtain ⟨ρ, hρ⟩ := exists_ext c W ρ₀ (fun x => by
      obtain ⟨p, hp, z, e⟩ := h1 (M'.mkQ x)
      obtain ⟨z', rfl⟩ := M'.mkQ_surjective z
      refine ⟨x - c • z', ?_, z', by abel⟩
      change M'.mkQ (x - c • z') ∈ P
      rw [map_sub, map_smul, e, add_sub_cancel_right]
      exact hp)
    (fun x hx => h2 _ (by
      have : M'.mkQ (c • x) ∈ P := hx
      rwa [map_smul] at this)) hS hC
  have hker : ∀ x ∈ M', ((ρ x : M') : M) = x := by
    intro x hx
    have hxW : x ∈ W := by
      change M'.mkQ x ∈ P
      rw [show M'.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx]
      exact P.zero_mem
    have h0 : π ⟨x, hxW⟩ = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 hx)
    have h3 := hρ ⟨x, hxW⟩
    change ρ x = _ at h3
    rw [h3, hρ₀, h0]
    simp
  refine ⟨M'.liftQ (LinearMap.id - M'.subtype ∘ₗ ρ) ?_, fun n => ?_⟩
  · intro x hx
    simp [LinearMap.mem_ker, hker x hx, sub_eq_zero]
  · obtain ⟨x, rfl⟩ := M'.mkQ_surjective n
    have h4 : M'.mkQ ((ρ x : M') : M) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (ρ x).2
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, map_sub]
    simpa using h4

end Sec

end GlobalTheory.CompanionTheory.LatSplit

namespace GlobalTheory.CompanionTheory.LatSplit

theorem nonempty_grSplit : ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → LatBase γ l m → Nonempty (GrSplit O γ m) := by
  intro O A _ _ _ _ _ I γ l m hdiv h
  have hc : (l : O) ≠ 0 := by
    intro h0
    have hl : (l : A) = 0 := by rw [← map_natCast (algebraMap O A), h0, map_zero]
    have h1 : (1 : A) ∈ pdP γ m := h.tf.tf m 1 (by rw [hl, zero_mul]; exact Ideal.zero_mem _)
    rw [h.tf.nil] at h1
    have h2 : (1 : A) = 0 := h1
    exact h.prime.ne_top (by rw [Ideal.eq_top_iff_one, h2]; exact I.zero_mem)
  have hsm : ∀ (k : ℕ) (x : A), ((l : O) ^ k) • x = (l : A) ^ k * x := by
    intro k x
    rw [Algebra.smul_def, map_pow, map_natCast]
  have htf : ∀ (r k : ℕ) (x : A), (l : A) ^ k * x ∈ pdP γ r → x ∈ pdP γ r := by
    intro r k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      exact h.tf.tf r x (ih _ (by rw [← mul_assoc, ← pow_succ]; exact hx))
  let L : ℕ → Submodule O A := fun r => (pdP γ r).restrictScalars O
  have hv : ∀ (r k : ℕ) (z : L r), (((l : O) ^ k • z : L r) : A) = (l : A) ^ k * z := fun r k z => hsm k z
  have hI : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(l : A)} ^ n • ⊤ : Submodule A A) ↔ ∃ t, x = (l : A) ^ n * t := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, mul_comm _ _⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, mul_comm _ _⟩
  have ht : ∀ (r : ℕ) (a : O) (x : A), a ≠ 0 → a • x ∈ L r → x ∈ L r := by
    intro r a x ha hx
    obtain ⟨k, b, hb⟩ := hdiv a ha
    refine htf r k x ?_
    rw [← hsm, hb, mul_comm, mul_smul]
    exact (L r).smul_mem _ hx
  have hsec : ∀ r, ∃ s : (A ⧸ L r) →ₗ[O] A, ∀ n, (L r).mkQ (s n) = n := by
    intro r
    refine exists_section (L r) (l : O) hc (ht r) ?_ ?_
    · intro y hy
      refine Subtype.ext (h.cpl.toIsHausdorff.haus _ fun n => ?_)
      obtain ⟨z, hz⟩ := hy n
      rw [SModEq.zero, hI]
      exact ⟨z, by rw [← hv, ← hz]⟩
    · intro y hy
      have hz' : ∀ b, ∃ z : L r, (y (b + 1) : A) - y b = (l : A) ^ b * z := fun b => by
        obtain ⟨z, hz⟩ := hy b
        exact ⟨z, by rw [← hv]; exact congrArg Subtype.val hz⟩
      have hcau : ∀ {a b : ℕ}, a ≤ b → (y a : A) ≡ y b [SMOD (Ideal.span {(l : A)} ^ a • ⊤ : Submodule A A)] := by
        intro a b hab
        induction b, hab using Nat.le_induction with
        | base => rfl
        | succ b hab ih =>
          refine ih.trans ?_
          rw [SModEq.sub_mem, hI]
          obtain ⟨z, hz⟩ := hz' b
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
          refine ⟨-((l : A) ^ d * z), ?_⟩
          rw [← neg_sub, hz, pow_add]
          ring
      obtain ⟨Lim, hLim⟩ := h.cpl.toIsPrecomplete.prec hcau
      have hl : ∀ n, ∃ t, Lim - y n = (l : A) ^ n * t := fun n => by
        obtain ⟨t, ht'⟩ := (hI _ _).1 ((SModEq.sub_mem).1 (hLim n))
        exact ⟨-t, by rw [← neg_sub, ht']; ring⟩
      have hLm : Lim ∈ pdP γ r := h.closed r Lim fun n => by
        obtain ⟨t, ht'⟩ := hl n
        refine Submodule.mem_sup.2 ⟨(l : A) ^ n * t, Ideal.mem_span_singleton.2 (Dvd.intro _ rfl), y n, (y n).2, ?_⟩
        rw [← ht']
        abel
      refine ⟨⟨Lim, hLm⟩, fun k => ?_⟩
      obtain ⟨t, ht'⟩ := hl k
      have htm : t ∈ pdP γ r := htf r k t (by rw [← ht']; exact (pdP γ r).sub_mem hLm (y k).2)
      exact ⟨⟨t, htm⟩, Subtype.ext (by rw [hv]; exact ht')⟩
  choose s hs using hsec
  have hmk : ∀ (r : ℕ) (x : A), (L r).mkQ x = 0 ↔ x ∈ L r := fun r x => Submodule.Quotient.mk_eq_zero _
  have hanti : ∀ r, pdP γ (r + 1) ≤ pdP γ r := fun r =>
    Ideal.span_mono fun z ⟨q, h1, h2, h3⟩ => ⟨q, h1, by omega, h3⟩
  have hflat : ∀ r, Module.Flat O ((L r).map (L (r + 1)).mkQ) := by
    intro r
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff _).1 hx
    obtain ⟨y, -, hy⟩ := x.2
    have h0 : a • (x : A ⧸ L (r + 1)) = 0 := congrArg Subtype.val hax
    rw [← hy, ← map_smul, hmk] at h0
    have h1 := ht _ a y (nonZeroDivisors.ne_zero ha) h0
    exact (Submodule.mem_bot _).2 (Subtype.ext (by rw [← hy]; exact (hmk _ _).2 h1))
  have hν : ∀ (r : ℕ) (n : (L r).map (L (r + 1)).mkQ), s (r + 1) n ∈ pdP γ r := by
    rintro r ⟨_, y, hy, rfl⟩
    have h1 : s (r + 1) ((L (r + 1)).mkQ y) - y ∈ pdP γ (r + 1) := (hmk _ _).1 (by rw [map_sub, hs, sub_self])
    have h2 := (pdP γ r).add_mem (hanti r h1) hy
    simpa using h2
  exact ⟨{ N := fun i => ↥((L i).map (L (i + 1)).mkQ)
           flat := fun i => hflat i
           ν := fun i => s (i + 1) ∘ₗ Submodule.subtype _
           mem := fun i n => hν i n
           inj := fun i n hn => Subtype.ext (by rw [← hs (i + 1) n]; exact (hmk _ _).2 hn)
           surj := fun i x hx => ⟨⟨(L (i + 1)).mkQ x, Submodule.mem_map_of_mem hx⟩,
             (hmk _ _).1 (by
               change (L (i + 1)).mkQ (x - s (i + 1) ((L (i + 1)).mkQ x)) = 0
               rw [map_sub, hs, sub_self])⟩
           nil := h.tf.nil }⟩

end GlobalTheory.CompanionTheory.LatSplit
