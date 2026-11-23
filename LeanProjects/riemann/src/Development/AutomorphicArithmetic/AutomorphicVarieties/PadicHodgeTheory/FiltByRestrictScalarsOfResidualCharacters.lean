import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def Reach {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) (U : Submodule A V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = U ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

private theorem reach_bot {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Reach ρ S ⊥ :=
  ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

private theorem reach_step {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {κ : G →* Aˣ} (hκ : κ ∈ S) {x : V} (hx : ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) :
    Reach ρ S (U ⊔ Submodule.span A {x}) := by
  obtain ⟨n, F, h0, hn, hs⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span A {x}, by simp [h0], by simp, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have h1 : i ≤ n := hi.le
    have h2 : i + 1 ≤ n := hi
    simp only [h1, h2, if_true]
    exact hs i hi
  · have h2 : ¬ (i + 1 ≤ i) := by omega
    simp only [h2, le_refl, if_true, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem reach_fin {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {T : Set V} (hT : T.Finite) :
    (∀ x ∈ T, ∃ κ ∈ S, ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) → Reach ρ S (U ⊔ Submodule.span A T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro _
    simpa using h
  | @insert a s ha hs ih =>
    intro hall
    have hr := ih (fun y hy => hall y (Set.mem_insert_of_mem a hy))
    obtain ⟨κ, hκ, hk⟩ := hall a (Set.mem_insert a s)
    have hr2 := reach_step hr hκ (x := a) (fun g => Submodule.mem_sup_left (hk g))
    have e : U ⊔ Submodule.span A (insert a s) = U ⊔ Submodule.span A s ⊔ Submodule.span A {a} := by
      rw [Submodule.span_insert]
      ac_rfl
    rw [e]
    exact hr2

theorem UpperTheory.filtBy_restrictScalars_of_residual_characters :
    ∀ {G E B V : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] [AddCommGroup V] [Module B V] [Module E V] [IsScalarTower E B V] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ (ρ : Representation B G V) (S : Set (G →* Eˣ)) {ι : Type} [Finite ι] (x : ι → V) (κ : ι → G →* Eˣ), Submodule.span B (Set.range x) = ⊤ → (∀ j, κ j ∈ S) → (∀ g j, ρ g (x j) - ((κ j g : Eˣ) : E) • x j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V)) → FiltBy (resCoef E ρ) S := by
  intro G E B V _ _ _ _ _ _ _ _ _ π hπ ρ S ι _ x κ hx hκ hstep
  have hnil : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.mpr (hπ a ha)
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule E V, ∀ k,
      M k = ((RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V)).restrictScalars E :=
    ⟨_, fun _ => rfl⟩
  have hMm : ∀ k v, v ∈ M k ↔ v ∈ (RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V) := by
    intro k v
    rw [hM, Submodule.restrictScalars_mem]
  have down : ∀ p, Reach (resCoef E ρ) S (M (p + 1)) → Reach (resCoef E ρ) S (M p) := by
    intro p h
    have hfg : (((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E).FG := IsNoetherian.noetherian _
    obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hfg
    have hsub : ∀ a ∈ s, a ∈ (RingHom.ker (π : B →+* E)) ^ p := fun a ha => by
      have : a ∈ ((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E := hs ▸ Submodule.subset_span ha
      exact this
    have hTf : (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)).Finite :=
      hsf.image2 _ Set.finite_univ
    have hr := reach_fin (ρ := resCoef E ρ) (S := S) h hTf (by
      rintro y ⟨a, ha, j, -, rfl⟩
      refine ⟨κ j, hκ j, fun g => ?_⟩
      rw [hMm]
      show ρ g (a • x j) - ((κ j g : Eˣ) : E) • (a • x j) ∈
        ((RingHom.ker (π : B →+* E)) ^ (p + 1) • (⊤ : Submodule B V))
      rw [map_smul, smul_comm ((κ j g : Eˣ) : E) a, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hsub a ha) (hstep g j))
    have claim : ∀ n ∈ Submodule.span B (Set.range x), ∀ a ∈ (RingHom.ker (π : B →+* E)) ^ p,
        a • n ∈ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro a ha
        have ha' : a ∈ Submodule.span E s := by
          rw [hs]
          exact ha
        clear ha
        induction ha' using Submodule.span_induction with
        | mem b hb => exact Submodule.subset_span ⟨b, hb, j, trivial, rfl⟩
        | zero => simp
        | add b c _ _ hb hc =>
          rw [add_smul]
          exact add_mem hb hc
        | smul c b _ hb =>
          rw [smul_assoc]
          exact Submodule.smul_mem _ c hb
      | zero => intro a _; simp
      | add y z _ _ hy hz =>
        intro a ha
        rw [smul_add]
        exact add_mem (hy a ha) (hz a ha)
      | smul b y _ hy =>
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (Ideal.mul_mem_right b _ ha)
    have e : M p = M (p + 1) ⊔ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      apply le_antisymm
      · intro v hv
        apply Submodule.mem_sup_right
        rw [hMm] at hv
        refine Submodule.smul_induction_on hv ?_ ?_
        · intro a ha n _
          exact claim n (by rw [hx]; trivial) a ha
        · intro y z hy hz
          exact add_mem hy hz
      · refine sup_le ?_ ?_
        · intro v hv
          rw [hMm] at hv ⊢
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ p)) hv
        · rw [Submodule.span_le]
          rintro y ⟨a, ha, j, -, rfl⟩
          show a • x j ∈ M p
          rw [hMm]
          exact Submodule.smul_mem_smul (hsub a ha) trivial
    rw [e]
    exact hr
  have base : M N = ⊥ := by
    rw [hM, hN, Submodule.zero_eq_bot, Submodule.bot_smul, Submodule.restrictScalars_bot]
  have all : ∀ k, Reach (resCoef E ρ) S (M (N - k)) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, base]
      exact reach_bot _ _
    | succ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · have e : N - k = (N - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact down _ ih
      · have e : N - (k + 1) = N - k := by omega
        rw [e]
        exact ih
  have top : M 0 = ⊤ := by
    rw [hM, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.restrictScalars_top]
  have fin := all N
  rw [Nat.sub_self, top] at fin
  exact fin
