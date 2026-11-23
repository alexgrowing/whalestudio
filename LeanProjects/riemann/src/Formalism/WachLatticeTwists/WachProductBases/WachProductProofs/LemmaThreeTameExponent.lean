import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CompsOfMemMap

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Finset

theorem lemma_three_psi_operator : ProductBasisPsiOperator := by
  intro ℓ _ A _ φA ε X Q H c ι pr aa hpr hε hU hX hQ hc i
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hinj : Function.Injective φA := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (0 : A) = ∑ j : Fin ℓ, ε ^ (j : ℕ) *
        φA ((fun j : Fin ℓ => if (j : ℕ) = 0 then a else 0) j) := by
      rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
      · simp [ha]
      · intro j hj
        have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        simp [this]
    have h2 : (0 : A) = ∑ j : Fin ℓ, ε ^ (j : ℕ) * φA ((0 : Fin ℓ → A) j) := by simp
    have h3 := congrFun ((hU 0).unique h1 h2) ⟨0, hℓ⟩
    simpa using h3
  have hbb : ∀ a ∈ (⨅ i, aa i), Q ^ H * a ∈ Ideal.map φA (⨅ i, aa i) := by
    intro a ha
    obtain ⟨e, he⟩ := (hU (Q ^ H * a)).exists
    have hmem : ∀ j, e j ∈ (⨅ i, aa i) := by
      intro j
      rw [Ideal.mem_iInf]
      intro i'
      obtain ⟨i, rfl⟩ := hpr i'
      exact LIFT.comp_mem φA ε (aa (pr i)) hℓ hε hU (hQ i a ((Ideal.mem_iInf.1 ha) i)) e he j
    rw [he]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hmem j))
  have := LIFT.xHKills_proof ℓ A φA ε X Q H c (⨅ i, aa i) hinj hε hU hX hbb (Ideal.mem_iInf.2 hc)
  exact Ideal.mem_iInf.1 this i

section MComps

variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A)
  {D' D : Type} [AddCommGroup D'] [Module A D'] [AddCommGroup D] [Module A D] (Φ : D' →+ D)
  (N'' : Submodule A D')

def MComps (ℓ : ℕ) (x : D) : Prop :=
  ∃ m : Fin ℓ → D', (∀ j, m j ∈ N'') ∧ x = ∑ j : Fin ℓ, ε ^ (j : ℕ) • Φ (m j)

theorem mcomps_zero : MComps ε Φ N'' ℓ 0 := ⟨0, fun _ => N''.zero_mem, by simp⟩

theorem mcomps_add {x y : D} (hx : MComps ε Φ N'' ℓ x) (hy : MComps ε Φ N'' ℓ y) :
    MComps ε Φ N'' ℓ (x + y) := by
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨m', hm', rfl⟩ := hy
  refine ⟨m + m', fun j => N''.add_mem (hm j) (hm' j), ?_⟩
  simp [map_add, smul_add, sum_add_distrib]

variable (hΦ : ∀ (a : A) (x : D'), Φ (a • x) = φA a • Φ x)
include hΦ

theorem mcomps_smul_phi (s : A) {x : D} (hx : MComps ε Φ N'' ℓ x) :
    MComps ε Φ N'' ℓ (φA s • x) := by
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨fun j => s • m j, fun j => N''.smul_mem s (hm j), ?_⟩
  rw [smul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [hΦ, smul_comm]

theorem mcomps_smul_eps (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) {x : D} (hx : MComps ε Φ N'' ℓ x) :
    MComps ε Φ N'' ℓ (ε • x) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨(Fin.cons (ε • m (Fin.last k)) (fun i => m i.castSucc) : Fin (k + 1) → D'), ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using N''.smul_mem ε (hm (Fin.last k))
    · simpa using hm j.castSucc
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, hΦ, hε, pow_zero, one_mul, smul_add, smul_sum, smul_smul]
    rw [add_comm]
    congr 1
    · rw [← pow_succ']
    · refine sum_congr rfl fun i _ => ?_
      rw [← pow_succ']

theorem mcomps_smul_pow (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) (n : ℕ) {x : D}
    (hx : MComps ε Φ N'' ℓ x) : MComps ε Φ N'' ℓ (ε ^ n • x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_smul]
    exact mcomps_smul_eps φA ε Φ N'' hΦ hℓ hε ih

theorem mcomps_sum {κ : Type} (s : Finset κ) (f : κ → D) (h : ∀ i ∈ s, MComps ε Φ N'' ℓ (f i)) :
    MComps ε Φ N'' ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ => mcomps_add ε Φ N'') (mcomps_zero ε Φ N'') h

theorem mcomps_smul (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (r : A) {x : D} (hx : MComps ε Φ N'' ℓ x) : MComps ε Φ N'' ℓ (r • x) := by
  obtain ⟨e, he⟩ := (hU r).exists
  rw [he, sum_smul]
  refine mcomps_sum φA ε Φ N'' hΦ _ _ fun i _ => ?_
  rw [mul_smul]
  exact mcomps_smul_pow φA ε Φ N'' hΦ hℓ hε _ (mcomps_smul_phi φA ε Φ N'' hΦ _ hx)

theorem mcomps_Φ (hℓ : 0 < ℓ) {n : D'} (hn : n ∈ N'') : MComps ε Φ N'' ℓ (Φ n) := by
  refine ⟨fun i => if (i : ℕ) = 0 then n else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hn
    · exact N''.zero_mem
  · rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
    · simp
    · intro i hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]

theorem mcomps_of_mem_span (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : D} (hx : x ∈ Submodule.span A (Φ '' (N'' : Set D'))) : MComps ε Φ N'' ℓ x := by
  let T : Submodule A D :=
    { carrier := {x | MComps ε Φ N'' ℓ x}
      add_mem' := fun ha hb => mcomps_add ε Φ N'' ha hb
      zero_mem' := mcomps_zero ε Φ N''
      smul_mem' := fun r _ hx => mcomps_smul φA ε Φ N'' hΦ hℓ hε hU r hx }
  have hle : Submodule.span A (Φ '' (N'' : Set D')) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    exact mcomps_Φ φA ε Φ N'' hΦ hℓ hn
  exact hle hx

end MComps

theorem lemma_three_key_inclusion : ProductBasisInclusion := by
  intro O A _ _ _ S D' D _ _ _ _ Φ N₂' N'' N₂ N' M h aa' g hU hΦ hinj hle haa hP52 hP51 hg
  obtain ⟨e, he⟩ := (hU (S.Q ^ (M + h) * g)).exists
  suffices hs : ∀ j, e j ∈ aa' by
    rw [he]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hs j))
  intro j
  rw [haa]
  intro n hn
  have h1 : (S.Q ^ (M + h) * g) • Φ n ∈ Submodule.span A (Φ '' (N'' : Set D')) := by
    have : (S.Q ^ (M + h) * g) • Φ n = S.Q ^ h • (g • (S.Q ^ M • Φ n)) := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact hP51 _ (hg _ (hP52 n hn))
  obtain ⟨m, hm, hx⟩ := mcomps_of_mem_span (S.φ : A →+* A) S.ε Φ N'' hΦ S.hℓ.pos S.φ_ε hU h1
  have h2 : (S.Q ^ (M + h) * g) • Φ n = ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • Φ (e j • n) := by
    conv_lhs => rw [he]
    rw [Finset.sum_smul]
    refine sum_congr rfl fun j _ => ?_
    rw [hΦ, mul_smul]
  have h3 : ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • Φ ((fun j => e j • n - m j) j) = 0 := by
    simp only [map_sub, smul_sub, sum_sub_distrib]
    rw [← h2, ← hx, sub_self]
  have h4 := hinj (fun j => e j • n - m j)
    (fun j => N₂'.sub_mem (N₂'.smul_mem _ hn) (hle (hm j))) h3 j
  have h5 : e j • n = m j := sub_eq_zero.1 h4
  rw [h5]
  exact hm j

theorem lemma_three_a_holds : Lemma3a := by
  intro O A _ _ _ S ι pr D₁ D₂ _ _ _ _ _ _ _ _ W₁ W₂ F M h H c hU hP1 hP2 hH hc
  let aa : ι → Ideal A := fun i =>
    { carrier := {a | F.Kills i a}
      add_mem' := by
        intro a b ha hb n hn
        obtain ⟨x, hx, hfx⟩ := ha n hn
        obtain ⟨y, hy, hfy⟩ := hb n hn
        exact ⟨x + y, (W₁.N i).add_mem hx hy, by rw [map_add, hfx, hfy, add_smul]⟩
      zero_mem' := fun n _ => ⟨0, (W₁.N i).zero_mem, by simp⟩
      smul_mem' := by
        intro r a ha n hn
        obtain ⟨x, hx, hfx⟩ := ha n hn
        exact ⟨r • x, (W₁.N i).smul_mem r hx, by rw [map_smul, hfx, smul_smul, smul_eq_mul]⟩ }
  have key : ∀ i, ∀ a ∈ aa i, S.Q ^ H * a ∈ Ideal.map (S.φ : A →+* A) (aa (pr i)) := by
    intro i a ha
    have h0 := lemma_three_key_inclusion O A S D₂ D₂ (W₂.φ i).toAddMonoidHom (W₂.N (pr i))
      ((W₁.N (pr i)).map (F.f (pr i))) (W₂.N i) ((W₁.N i).map (F.f i)) (M i) (h i) (aa (pr i)) a hU
      (W₂.φ_smul i)
      (fun m _ hm => by
        have := (W₂.etale i).1 (a₁ := m) (a₂ := 0) (by simpa using hm)
        intro j
        rw [this]; rfl)
      (by
        rintro _ ⟨x, hx, rfl⟩
        exact F.N_le _ x hx)
      (fun b => Iff.rfl)
      (hP2.1 i)
      (by
        rintro _ ⟨x, hx, rfl⟩
        have hle : (Submodule.span A (W₁.φ i '' (W₁.N (pr i) : Set D₁))).map (F.f i) ≤
            Submodule.span A ((W₂.φ i).toAddMonoidHom ''
              (((W₁.N (pr i)).map (F.f (pr i)) : Submodule A D₂) : Set D₂)) := by
          rw [Submodule.map_span]
          apply Submodule.span_mono
          rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨F.f (pr i) x, ⟨x, hx, rfl⟩, (F.φ_comm i x).symm⟩
        rw [← map_smul]
        exact hle ⟨_, hP1.2 i x hx, rfl⟩)
      (fun n hn => ha n hn)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hH i)
    rw [hk, pow_add, mul_comm (S.Q ^ (M i + h i)), mul_assoc]
    exact Ideal.mul_mem_left _ _ h0
  have : Fact S.ℓ.Prime := ⟨S.hℓ⟩
  exact lemma_three_psi_operator S.ℓ A (S.φ : A →+* A) S.ε S.X S.Q H c ι pr aa pr.surjective S.φ_ε hU S.φ_X key
    (fun i => by
      have : S.ε - 1 = S.π := by simp [HidaSetting.ε]
      rw [this]
      exact hc i)

theorem lemma_three_tame_exponent : ProductBasisTameExponent := by
  intro A _ aa π π' w ℓ e s' H hℓ hes hπ' hH
  set a := ⌈((e * H : ℕ) : ℚ) / ((ℓ - 1 : ℕ) : ℚ)⌉₊ with ha_def
  have ha : H ≤ s' * a := by
    have h1 : ((e * H : ℕ) : ℚ) / ((ℓ - 1 : ℕ) : ℚ) ≤ a := Nat.le_ceil _
    have hpos : (0 : ℚ) < ((ℓ - 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 0 < ℓ - 1)
    rw [div_le_iff₀ hpos] at h1
    have h2 : e * H ≤ a * (ℓ - 1) := by exact_mod_cast h1
    rw [← hes] at h2
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h
        simp at hes
        omega
      · exact h
    exact Nat.le_of_mul_le_mul_left (by linarith [h2, mul_comm a (e * s'), mul_assoc e s' a]) he
  rw [hπ', mul_pow, ← pow_mul]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha
  rw [hk, pow_add]
  exact aa.mul_mem_left _ (aa.mul_mem_right _ hH)

theorem lemma_three_invariants : ProductBasisInvariants := by
  intro O A _ _ _ Δ _ _ D₁ D₂ _ _ _ _ _ _ _ _ ρ₁ ρ₂ f N₁ N₂ a hunit hN₁ hf ha hk n hn hinv
  obtain ⟨n₁, hn₁, hfn⟩ := hk n hn
  obtain ⟨r, hr⟩ := hunit.exists_left_inv
  refine ⟨r • ∑ d, ρ₁ d n₁, ?_, ?_, ?_⟩
  · exact N₁.smul_of_tower_mem r (N₁.sum_mem fun d _ => hN₁ d _ hn₁)
  · intro d
    rw [map_smul, map_sum]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  · rw [LinearMap.map_smul_of_tower, map_sum]
    simp only [hf, hfn, ha, hinv]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hr, one_smul]

end Formalism.RepresentationBoundsCohomology.N1
