import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
import Formalism.WindowSums.PowerSeriesRelationList

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

private theorem assoc_prod_lemma {O : Type} [CommMonoid O] (s : Finset ℤ) (f : ℤ → O) (y : O)
    (e : ℤ → ℕ) (h : ∀ b ∈ s, Associated (f b) (y ^ e b)) :
    Associated (∏ b ∈ s, f b) (y ^ ∑ b ∈ s, e b) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨1, by simp⟩
  · intro b s hb ih h
    rw [Finset.prod_insert hb, Finset.sum_insert hb, pow_add]
    exact (h b (Finset.mem_insert_self b s)).mul_mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private theorem prod_dvd_lemma_2 {O : Type} [CommRing O] [IsDomain O] (S : Finset ℤ) (c : ℤ → O)
    (hc : ∀ a ∈ S, ∀ b ∈ S, c a = c b → a = b) (h : O[X])
    (hr : ∀ a ∈ S, h.eval (c a) = 0) : (∏ a ∈ S, (X - C (c a))) ∣ h := by
  classical
  by_cases h0 : h = 0
  · rw [h0]
    exact dvd_zero _
  have hle : S.val.map c ≤ h.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map_on (fun a ha b hb hab => hc a ha b hb hab) S.nodup)]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
    exact (mem_roots h0).2 (hr a ha)
  have h1 := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 (S.val.map c)).2 hle
  rw [Multiset.map_map] at h1
  exact h1

theorem lagrange_annihilation : StatLagrange := by
  intro ℓ _ O _ _ S₁ S₂ c sg hdisj hassoc
  classical
  by_cases hE0 : ((ℓ : O) ^ lagE ℓ sg S₁ S₂) = 0
  · rw [hE0, map_zero]
    exact Ideal.zero_mem _
  have hK : ∀ a ∈ S₁, (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) +
      (∑ b ∈ S₁.erase a, (sg + padicValInt ℓ (a - b))) ≤ lagE ℓ sg S₁ S₂ := by
    intro a ha
    unfold lagE
    exact Finset.le_sup (f := fun a => (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) +
      ∑ b ∈ S₁.erase a, (sg + padicValInt ℓ (a - b))) ha
  have hinj : ∀ a ∈ S₁, ∀ b ∈ S₁, c a = c b → a = b := by
    intro a ha b hb hcab
    by_contra hne
    have h1 := hassoc a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hne
    rw [hcab, sub_self] at h1
    have h2 : (ℓ : O) ^ (sg + padicValInt ℓ (a - b)) = 0 := h1.eq_zero_iff.1 rfl
    apply hE0
    refine pow_eq_zero_of_le ?_ h2
    calc sg + padicValInt ℓ (a - b) ≤ ∑ x ∈ S₁.erase a, (sg + padicValInt ℓ (a - x)) :=
          Finset.single_le_sum (f := fun x => sg + padicValInt ℓ (a - x))
            (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨fun h => hne h.symm, hb⟩)
      _ ≤ (∑ x ∈ S₂, (sg + padicValInt ℓ (a - x))) +
            ∑ x ∈ S₁.erase a, (sg + padicValInt ℓ (a - x)) := Nat.le_add_left _ _
      _ ≤ lagE ℓ sg S₁ S₂ := hK a ha
  have hw : ∀ a, ∃ w : O, a ∈ S₁ → (∏ b ∈ S₂, (c a - c b)) * (∏ b ∈ S₁.erase a, (c a - c b)) * w =
      (ℓ : O) ^ lagE ℓ sg S₁ S₂ := by
    intro a
    by_cases ha : a ∈ S₁
    · have h2 : Associated (∏ b ∈ S₂, (c a - c b))
          ((ℓ : O) ^ ∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) :=
        assoc_prod_lemma S₂ (fun b => c a - c b) (ℓ : O) (fun b => sg + padicValInt ℓ (a - b))
          (fun b hb => hassoc a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb)
            (fun h => Finset.disjoint_left.1 hdisj ha (by rw [h]; exact hb)))
      have h1 : Associated (∏ b ∈ S₁.erase a, (c a - c b))
          ((ℓ : O) ^ ∑ b ∈ S₁.erase a, (sg + padicValInt ℓ (a - b))) :=
        assoc_prod_lemma (S₁.erase a) (fun b => c a - c b) (ℓ : O)
          (fun b => sg + padicValInt ℓ (a - b))
          (fun b hb => hassoc a (Finset.mem_union_left _ ha) b
            (Finset.mem_union_left _ (Finset.mem_of_mem_erase hb))
            (fun h => Finset.ne_of_mem_erase hb h.symm))
      obtain ⟨u, hu⟩ := h2.mul_mul h1
      refine ⟨(u : O) * (ℓ : O) ^ (lagE ℓ sg S₁ S₂ - ((∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) +
        ∑ b ∈ S₁.erase a, (sg + padicValInt ℓ (a - b)))), fun _ => ?_⟩
      rw [← mul_assoc, hu, ← pow_add, ← pow_add, Nat.add_sub_of_le (hK a ha)]
    · exact ⟨0, fun h => absurd h ha⟩
  choose w hw using hw
  obtain ⟨q, hq⟩ : ∃ q : O[X], ∀ a ∈ S₁, q.eval (c a) = w a * ∏ b ∈ S₁.erase a, (c a - c b) := by
    refine ⟨∑ a' ∈ S₁, C (w a') * ∏ b ∈ S₁.erase a', (X - C (c b)), fun a ha => ?_⟩
    rw [eval_finset_sum, Finset.sum_eq_single a]
    · simp [eval_prod]
    · intro a' _ hne
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne.symm, ha⟩) (by simp),
        mul_zero]
    · intro h
      exact absurd ha h
  obtain ⟨r, hr⟩ := prod_dvd_lemma_2 S₁ c hinj
    ((∏ b ∈ S₂, (X - C (c b))) * q - C ((ℓ : O) ^ lagE ℓ sg S₁ S₂)) (fun a ha => by
      rw [eval_sub, sub_eq_zero, eval_mul, hq a ha, eval_C, ← hw a ha, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      ring)
  rw [Ideal.mem_span_pair]
  exact ⟨-r, q, by linear_combination hr⟩

theorem lagrange_resolvent_kills_class : StatLagrangeKill := by
  intro ℓ _ O _ _ S₁ S₂ c sg P _ _ g hdisj hassoc h1 h2 x
  obtain ⟨p₁, p₂, hp⟩ := Ideal.mem_span_pair.1 (lagrange_annihilation ℓ O S₁ S₂ c sg hdisj hassoc)
  have h3 : aeval g (C ((ℓ : O) ^ lagE ℓ sg S₁ S₂)) = 0 := by
    rw [← hp, map_add, map_mul, map_mul, h1, h2, mul_zero, mul_zero, add_zero]
  rw [aeval_C, Algebra.algebraMap_eq_smul_one] at h3
  have h4 : (((ℓ : O) ^ lagE ℓ sg S₁ S₂) • (1 : Module.End O P)) x = (0 : Module.End O P) x := by
    rw [h3]
  exact h4

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]

theorem GPair.kills_mul (P : GPair G D) {a : A} (b : A) (h : P.Kills a) : P.Kills (b * a) := by
  unfold GPair.Kills at h ⊢
  intro n hn
  rw [mul_smul]
  exact P.N'.smul_mem b (h n hn)

theorem GPair.kills_of_dvd (P : GPair G D) {a b : A} (hab : a ∣ b) (h : P.Kills a) : P.Kills b := by
  obtain ⟨k, rfl⟩ := hab
  rw [mul_comm]
  exact P.kills_mul k h

theorem dvd_pow_of_val {c : ℤ_[ℓ]} (hc : c ≠ 0) {v : ℕ} (hv : c.valuation = v) :
    c ∣ (ℓ : ℤ_[ℓ]) ^ v := by
  have h := PadicInt.unitCoeff_spec hc
  rw [hv] at h
  refine ⟨↑(PadicInt.unitCoeff hc)⁻¹, ?_⟩
  calc (ℓ : ℤ_[ℓ]) ^ v
      = ((PadicInt.unitCoeff hc : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v) * ↑(PadicInt.unitCoeff hc)⁻¹ := by
        rw [mul_comm (PadicInt.unitCoeff hc : ℤ_[ℓ]), mul_assoc, Units.mul_inv, mul_one]
    _ = c * ↑(PadicInt.unitCoeff hc)⁻¹ := by rw [← h]

theorem GPair.kills_pow_of_dvd (P : GPair G D) {c : ℤ_[ℓ]} {v : ℕ} {a : A}
    (hc : c ∣ (ℓ : ℤ_[ℓ]) ^ v) (h : P.Kills (algebraMap ℤ_[ℓ] A c * a)) :
    P.Kills ((ℓ : A) ^ v * a) := by
  obtain ⟨k, hk⟩ := hc
  rw [show (ℓ : A) ^ v = algebraMap ℤ_[ℓ] A ((ℓ : ℤ_[ℓ]) ^ v) by simp, hk, map_mul,
    mul_comm (algebraMap ℤ_[ℓ] A c), mul_assoc]
  exact P.kills_mul _ h

end

theorem unit_lemma_case_b_holds : StatWB := by
  intro ℓ _ A _ _ G D _ _ _ _ P s H hs h2 hv hK
  let Bs : Formalism.LIFT.Base ℓ A :=
    { φA := AlgHom.id _ _, γA := G.γ, X := G.X, Q := 1, u := G.u
      comm := fun _ => rfl
      φX := by simp
      γX := G.γX
      γQ := ⟨0, by simp, by simp⟩ }
  let W (N : Submodule A D) (hN : ∀ x ∈ N, ∃ x' ∈ N, P.γ x - x = G.X • x') : Formalism.LIFT.WD Bs 0 D :=
    { N := N, φ := LinearMap.id, γ := P.γ
      φ_smul := fun _ _ => rfl
      γ_smul := P.γ_smul
      comm := fun _ => rfl
      X_inj := P.X_inj
      Q_bij := by
        have : (fun x : D => (1 : A) • x) = id := by funext x; simp
        show Function.Bijective (fun x : D => (1 : A) • x)
        rw [this]; exact Function.bijective_id
      φ_N := fun x hx => by simpa using hx
      γ_N := hN }
  let f : Formalism.LIFT.Hom (W P.N' P.γ_N') (W P.N P.γ_N) :=
    { f := LinearMap.id, φ_comm := fun _ => rfl, γ_comm := fun _ => rfl, N_le := fun x hx => P.le hx }
  have key := Formalism.LIFT.lift_WBTail ℓ A Bs 0 D D (W P.N' P.γ_N') (W P.N P.γ_N) f s H hs h2 hv
    (fun n hn => ⟨G.X ^ H • n, hK n hn, rfl⟩)
  intro n hn
  obtain ⟨n₁, hn₁, h⟩ := key n hn
  have h' : n₁ = ((ℓ : ℤ_[ℓ]) ^ eWB ℓ H s) • n := h
  have e : ((ℓ : ℤ_[ℓ]) ^ eWB ℓ H s) • n = ((ℓ : A) ^ eWB ℓ H s) • n := by
    rw [← algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ eWB ℓ H s) n, map_pow, map_natCast]
  rw [← e, ← h']
  exact hn₁

theorem add_mul_pow_exists {A : Type} [CommRing A] (a X t : A) (k : ℕ) :
    ∃ t', (a + X * t) ^ k = a ^ k + X * t' := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨t', ht'⟩ := ih
    refine ⟨a ^ k * t + t' * (a + X * t), ?_⟩
    rw [pow_succ, ht', pow_succ]
    ring

theorem descent_reduces_level : StatDescentStep := by
  intro ℓ _ A _ _ G D _ _ _ _ P c j h
  obtain ⟨t, ht⟩ := G.γX
  obtain ⟨t', ht'⟩ := add_mul_pow_exists (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) G.X t (j + 1)
  unfold GPair.Kills at h ⊢
  intro n hn
  obtain ⟨n₂, hn₂N, hn₂⟩ := P.γ_N n hn
  obtain ⟨m, hmN, hm⟩ := P.γ_N' _ (h n hn)
  have hγ : G.γ (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) = algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1) *
      ((algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) ^ (j + 1) + G.X * t') := by
    rw [map_mul, map_pow, AlgHom.commutes, ht, mul_pow, ht']
    ring
  rw [P.γ_smul, hγ] at hm
  have hγn : P.γ n = n + G.X • n₂ := by
    rw [← hn₂]
    abel
  rw [hγn] at hm
  have hw : (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) ^ (j + 1) • n₂ + t' • n + (G.X * t') • n₂ ∈ P.N :=
    P.N.add_mem (P.N.add_mem (P.N.smul_mem _ hn₂N) (P.N.smul_mem _ hn)) (P.N.smul_mem _ hn₂N)
  have hx : (algebraMap ℤ_[ℓ] A (c * ((G.u : ℤ_[ℓ]) ^ (j + 1) - 1)) * G.X ^ j) • n =
      m - (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) •
        ((algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) ^ (j + 1) • n₂ + t' • n + (G.X * t') • n₂) := by
    refine sub_eq_zero.1 (P.X_inj _ ?_)
    simp only [map_mul, map_sub, map_pow, map_one]
    linear_combination (norm := module) hm
  rw [hx]
  exact P.N'.sub_mem hmN (h _ hw)

theorem mem_span_of_frobenius_mem_span : StatDescent := by
  intro ℓ _ A _ _ G D _ _ _ _ P s j hjs h
  have key : ∀ d i, i + d = s → P.Kills (algebraMap ℤ_[ℓ] A
      (∏ k ∈ Finset.Ioc i s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      subst hi
      simpa using h
    | succ d ih =>
      intro i hi
      have h1 := ih (i + 1) (by omega)
      have h2 := descent_reduces_level ℓ A G D P
        (∏ k ∈ Finset.Ioc (i + 1) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) i h1
      have h3 : ∏ k ∈ Finset.Ioc i s, ((G.u : ℤ_[ℓ]) ^ k - 1) =
          (∏ k ∈ Finset.Ioc (i + 1) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * ((G.u : ℤ_[ℓ]) ^ (i + 1) - 1) := by
        rw [← Finset.prod_Ioc_consecutive _ (by omega : i ≤ i + 1) (by omega : i + 1 ≤ s),
          Nat.Ioc_succ_singleton, Finset.prod_singleton, mul_comm]
      rw [h3]
      exact h2
  exact key (s - j) j (by omega)

end Formalism.RepresentationBoundsCohomology.N2
