import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA.UnivNorm

theorem norm_nat_eq {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicAlgCl.norm_extends l (n : ℚ_[l])]; simp

theorem norm_l_lt_one {l : ℕ} [Fact l.Prime] : ‖(l : Qbar l)‖ < 1 := by
  rw [norm_nat_eq]; exact Padic.norm_p_lt_one

theorem norm_nat_of_coprime {l : ℕ} [Fact l.Prime] {n : ℕ} (h : n.Coprime l) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_nat_eq]; exact Padic.norm_natCast_eq_one_iff.2 h.symm

def Bd {l : ℕ} [Fact l.Prime] {n : Type} (δ : ℝ) (X : Matrix n n (Qbar l)) : Prop := ∀ i k, ‖X i k‖ ≤ δ

theorem Bd.mul {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] {a b : ℝ} {X Y : Matrix n n (Qbar l)} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Bd a X) (hY : Bd b Y) : Bd (a * b) (X * Y) := fun i k => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun j _ => ?_
  rw [norm_mul]; exact mul_le_mul (hX i j) (hY j k) (norm_nonneg _) ha

theorem Bd.add {l : ℕ} [Fact l.Prime] {n : Type} {a : ℝ} {X Y : Matrix n n (Qbar l)}
    (hX : Bd a X) (hY : Bd a Y) : Bd a (X + Y) := fun i k =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i k) (hY i k))

theorem exists_open_ker {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]
    (M : Γ →* Matrix n n (Qbar l)) (hcop : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    (hc : ∀ i k, Continuous fun s => M s i k) (h1 : ∀ s, Bd 1 (M s)) :
    ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ ∀ s ∈ N, M s = 1 := by
  have hinv : ∀ g, M g * M g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ g, M g⁻¹ * M g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  let N : ∀ ε : ℝ, 0 < ε → Subgroup Γ := fun ε hε =>
    { carrier := {s | Bd ε (M s - 1)}
      one_mem' := fun i k => by simp [hε.le]
      mul_mem' := fun {a b} ha hb => by
        have e : M (a * b) - 1 = M a * (M b - 1) + (M a - 1) := by rw [map_mul, mul_sub, mul_one]; abel
        have := Bd.mul zero_le_one hε.le (h1 a) hb
        rw [one_mul] at this
        show Bd ε _
        rw [e]; exact this.add ha
      inv_mem' := fun {a} ha i k => by
        have e : M a⁻¹ - 1 = -(M a⁻¹ * (M a - 1)) := by rw [mul_sub, mul_one, hinv', neg_sub]
        have := Bd.mul zero_le_one hε.le (h1 a⁻¹) ha i k
        rw [one_mul] at this
        rw [e, Matrix.neg_apply, norm_neg]; exact this }
  have hn : ∀ ε hε, (N ε hε).Normal := fun ε hε => ⟨fun a ha g => by
    have e : M (g * a * g⁻¹) - 1 = M g * (M a - 1) * M g⁻¹ := by
      rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hinv]
    have := Bd.mul (mul_nonneg zero_le_one hε.le) zero_le_one (Bd.mul zero_le_one hε.le (h1 g) ha) (h1 g⁻¹)
    rw [one_mul, mul_one] at this
    show Bd ε _
    rw [e]; exact this⟩
  have ho : ∀ ε hε, IsOpen (N ε hε : Set Γ) := fun ε hε => by
    have e : (N ε hε : Set Γ) = ⋂ i, ⋂ k, (fun s => M s i k) ⁻¹' Metric.closedBall ((1 : Matrix n n (Qbar l)) i k) ε := by
      ext s
      simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      (IsUltrametricDist.isOpen_closedBall _ hε.ne').preimage (hc i k)
  have hc0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have step : ∀ ε hε, ε ≤ ‖(l : Qbar l)‖ → ∀ s ∈ N ε hε, s ∈ N (‖(l : Qbar l)‖ * ε) (mul_pos hc0 hε) := by
    intro ε hε hle s hs
    have h2 : Bd ‖(l : Qbar l)‖ (∑ i ∈ Finset.range l, M s ^ i) := by
      have e : ∑ i ∈ Finset.range l, M s ^ i = ∑ i ∈ Finset.range l, (M (s ^ i) - 1) + (l : Matrix n n (Qbar l)) := by
        simp [Finset.sum_sub_distrib]
      rw [e]
      refine Bd.add (fun i k => ?_) (fun i k => ?_)
      · rw [Matrix.sum_apply]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0.le fun j _ =>
          (((N ε hε).pow_mem hs j) i k).trans hle
      · rw [Matrix.natCast_apply]; split_ifs <;> simp
    have h3 : s ^ l ∈ N _ (mul_pos hc0 hε) := by
      show Bd _ _
      rw [map_pow, ← geom_sum_mul]
      exact Bd.mul hc0.le hε.le h2 hs
    have := hn _ (mul_pos hc0 hε)
    have h4 : (QuotientGroup.mk s : Γ ⧸ N _ (mul_pos hc0 hε)) ^ l = 1 := (QuotientGroup.eq_one_iff _).2 h3
    have h5 : (QuotientGroup.mk s : Γ ⧸ N _ (mul_pos hc0 hε)) ^ (N _ (mul_pos hc0 hε)).index = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.pow_index_mem _ s)
    exact (QuotientGroup.eq_one_iff _).1 ((pow_eq_one_iff_of_coprime (hcop _ this (ho _ (mul_pos hc0 hε)))).1 ⟨h5, h4⟩)
  refine ⟨N _ hc0, hn _ hc0, ho _ hc0, fun s hs => ?_⟩
  have hk : ∀ k : ℕ, s ∈ N (‖(l : Qbar l)‖ ^ (k + 1)) (pow_pos hc0 _) := fun k => by
    induction k with
    | zero => show Bd _ _; rw [zero_add, pow_one]; exact hs
    | succ k ih =>
      have := step _ (pow_pos hc0 _) (pow_le_of_le_one hc0.le norm_l_lt_one.le k.succ_ne_zero) s ih
      show Bd _ _
      rw [pow_succ']; exact this
  rw [← sub_eq_zero]
  ext i k
  by_contra hne
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) (norm_l_lt_one (l := l))
  exact absurd ((hk m i k).trans (pow_le_pow_of_le_one hc0.le norm_l_lt_one.le m.le_succ)) (not_le.2 hm)

theorem exists_cob_of_index {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (ρ : Γ → Matrix (Fin 2) (Fin 2) (Qbar l))
    (z : Γ → Fin 2 → Qbar l) (N : Subgroup Γ) (hN : N.index.Coprime l) (h0 : ∀ s ∈ N, z s = 0)
    (hz : ∀ s i, ‖z s i‖ ≤ 1) (hc : ∀ s t, z (s * t) = z s + ρ s *ᵥ z t) :
    ∃ v : Fin 2 → Qbar l, (∀ i, ‖v i‖ ≤ 1) ∧ ∀ j, z j = ρ j *ᵥ v - v := by
  have hn1 := norm_nat_of_coprime hN
  have hn0 : (N.index : Qbar l) ≠ 0 := fun h => by simp [h] at hn1
  have : N.FiniteIndex := ⟨fun h => hn0 (by simp [h])⟩
  let : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hq : ∀ a b : Γ, (a : Γ ⧸ N) = b → z b = z a := fun a b h => by
    have := hc a (a⁻¹ * b)
    rwa [mul_inv_cancel_left, h0 _ (QuotientGroup.eq.1 h), Matrix.mulVec_zero, add_zero] at this
  set S := ∑ ω : Γ ⧸ N, z ω.out with hS
  have key : ∀ g, (N.index : Qbar l) • z g + ρ g *ᵥ S = S := fun g => by
    have e1 : ∑ ω : Γ ⧸ N, z (g * ω.out) = S := by
      rw [hS, ← Equiv.sum_comp (MulAction.toPerm g) fun ω : Γ ⧸ N => z ω.out]
      refine Finset.sum_congr rfl fun ω _ => hq _ _ ?_
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      exact (MulAction.Quotient.coe_smul_out N g ω).symm
    conv_rhs => rw [← e1]
    simp only [hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hS, Matrix.mulVec_sum]
    rw [Nat.cast_smul_eq_nsmul, Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨-((N.index : Qbar l)⁻¹ • S), fun i => ?_, fun j => ?_⟩
  · rw [Pi.neg_apply, norm_neg, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hn1, inv_one, one_mul, hS, Finset.sum_apply]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ω _ => hz _ i
  · have := eq_sub_of_add_eq (key j)
    rw [Matrix.mulVec_neg, Matrix.mulVec_smul, neg_sub_neg, ← smul_sub, ← this, inv_smul_smul₀ hn0]

theorem exists_pow_fix {K C : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C] (T : Module.End K C) :
    ∃ E, 0 < E ∧ ∀ d, 0 < d → ∀ c, (T ^ d) c = c → (T ^ E) c = c := by
  have hm : ∀ d m c, (T ^ d) c = c → (T ^ (d * m)) c = c := fun d m c h => by
    induction m with
    | zero => simp
    | succ m ih => rw [mul_add, mul_one, pow_add, Module.End.mul_apply, h, ih]
  obtain ⟨_, ⟨E, hE, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian K C)
    {U | ∃ n, 0 < n ∧ U = LinearMap.eqLocus (T ^ n) LinearMap.id} ⟨_, 1, one_pos, rfl⟩
  refine ⟨E, hE, fun d hd c hc => ?_⟩
  have h1 : LinearMap.eqLocus (T ^ E) LinearMap.id ≤ LinearMap.eqLocus (T ^ (E * d)) LinearMap.id := fun x hx => hm E d x hx
  have h2 := eq_of_le_of_not_lt h1 (hmax _ ⟨E * d, mul_pos hE hd, rfl⟩)
  have h3 : c ∈ LinearMap.eqLocus (T ^ (E * d)) LinearMap.id := by rw [mul_comm]; exact hm d E c hc
  rw [← h2] at h3
  exact h3

theorem isClosed_submodule {l : ℕ} [Fact l.Prime] (U : Submodule (Qbar l) (Fin 2 → Qbar l)) :
    IsClosed (U : Set (Fin 2 → Qbar l)) := by
  refine isClosed_of_closure_subset fun b hb => ?_
  by_contra h
  obtain ⟨f, h1, h2⟩ := U.exists_le_ker_of_notMem h
  exact h1 (closure_minimal (t := {x | f x = 0}) h2 (isClosed_eq f.continuous_on_pi continuous_const) hb)

theorem sum_eq_orderOf_smul {X C : Type} [Group X] [Fintype X] [AddCommMonoid C] (h : X) (f : X → C)
    (hf : ∀ x, f (x * h) = f x) [Fintype (X ⧸ Subgroup.zpowers h)] :
    ∑ x, f x = orderOf h • ∑ ω : X ⧸ Subgroup.zpowers h, f ω.out := by
  classical
  have h1 : ∀ x, ∀ t ∈ Subgroup.zpowers h, f (x * t) = f x := fun x t ht => by
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ht)
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, hf, ih (pow_mem (Subgroup.mem_zpowers h) n)]
  have h2 : Function.Bijective fun p : (X ⧸ Subgroup.zpowers h) × Subgroup.zpowers h => p.1.out * (p.2 : X) := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨fun x => ⟨(x, ⟨(x : X ⧸ Subgroup.zpowers h).out⁻¹ * x, QuotientGroup.eq.1 (QuotientGroup.out_eq' _)⟩), by simp⟩, ?_⟩
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  rw [← h2.sum_comp f, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [h1 _ _ (Subtype.prop _), Finset.sum_const, Finset.card_univ, Fintype.card_zpowers]

theorem sum_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (M : Type) [AddCommMonoid M] (Y : ∀ r : ℕ, Γ → (ZMod (l ^ r))ˣ → M), (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → ∀ r s, Y 0 s 1 = ∑ x, Y r s x := by
  intro l _ Γ _ M _ Y h r s
  induction r with
  | zero =>
    have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (ZMod (l ^ 0))ˣ := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact (Fintype.sum_subsingleton (fun x => Y 0 s x) 1).symm
  | succ r ih =>
    rw [ih, h r s]
    exact Finset.sum_fiberwise _ _ _

theorem eq_zero_of_gen : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (l : ℕ) [Fact l.Prime] (ρ : Γ →* GL (Fin 2) (Qbar l)) (z : Γ → Fin 2 → Qbar l) (I J : Subgroup Γ) (γ : Γ), IsClosed (I : Set Γ) → J ≤ I → γ ∈ I → (∀ i, Continuous fun s => z s i) → (∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z t) → z γ = 0 → (∀ j ∈ J, z j = 0) → I ≤ (Subgroup.zpowers γ ⊔ J).topologicalClosure → ∀ s ∈ I, z s = 0 := by
  intro Γ _ _ _ l _ ρ z I J γ hI hJI hγ hz hc h0 hJ hgen s hs
  have h1 : z 1 = 0 := hJ 1 J.one_mem
  let S : Subgroup Γ :=
    { carrier := {s | s ∈ I ∧ z s = 0}
      one_mem' := ⟨I.one_mem, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨I.mul_mem ha.1 hb.1, by rw [hc a ha.1 b hb.1, ha.2, hb.2]; simp⟩
      inv_mem' := fun {a} ha => ⟨I.inv_mem ha.1, by
        have := hc a⁻¹ (I.inv_mem ha.1) a ha.1
        rw [inv_mul_cancel, h1, ha.2] at this
        simpa using this.symm⟩ }
  have hS : IsClosed (S : Set Γ) := hI.inter (isClosed_eq (continuous_pi hz) continuous_const)
  exact (Subgroup.topologicalClosure_minimal (Subgroup.zpowers γ ⊔ J) (t := S)
    (sup_le (Subgroup.zpowers_le.2 ⟨hγ, h0⟩) fun j hj => ⟨hJI hj, hJ j hj⟩) hS (hgen hs)).2

theorem exists_cob_of_coprime : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (l : ℕ) [Fact l.Prime] (ρ : Γ →* GL (Fin 2) (Qbar l)) (z : Γ → Fin 2 → Qbar l) (J : Subgroup Γ), (∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l) → (∀ i k, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i k) → (∀ s i k, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i k‖ ≤ 1) → (∀ i, Continuous fun s => z s i) → (∀ s i, ‖z s i‖ ≤ 1) → (∀ s ∈ J, ∀ t ∈ J, z (s * t) = z s + (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z t) → ∃ v : Fin 2 → Qbar l, (∀ i, ‖v i‖ ≤ 1) ∧ ∀ j ∈ J, z j = (ρ j : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v - v := by
  intro Γ _ _ _ l _ ρ z J hcop hρc hρ1 hzc hz1 hc
  have h1 : z 1 = 0 := by simpa using hc 1 J.one_mem 1 J.one_mem
  let M : J →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
    { toFun := fun s => Matrix.fromBlocks (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) (Matrix.of fun i _ => z s i) 0 1
      map_one' := by
        rw [← Matrix.fromBlocks_one]
        congr 1
        · simp
        · ext i k; simp [h1]
      map_mul' := fun s t => by
        rw [Matrix.fromBlocks_multiply]
        congr 1
        · simp
        · ext i k
          fin_cases i <;> simp [hc s s.2 t t.2, Matrix.mul_apply, Matrix.mulVec, dotProduct, add_comm]
        · simp
        · simp }
  obtain ⟨N, hn, ho, hN⟩ := exists_open_ker M hcop
    (by
      rintro (i | i) (k | k)
      · exact (hρc i k).comp continuous_subtype_val
      · exact (hzc i).comp continuous_subtype_val
      · exact continuous_const
      · exact continuous_const)
    (by
      rintro s (i | i) (k | k)
      · exact hρ1 s i k
      · exact hz1 s i
      · simp [M]
      · simp [M])
  obtain ⟨v, hv, hv'⟩ := exists_cob_of_index (fun s : J => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (fun s => z s) N
    (hcop N hn ho) (fun s hs => funext fun i => by simpa [M] using congrFun (congrFun (hN s hs) (.inl i)) (.inr ()))
    (fun s => hz1 s) (fun s t => hc s s.2 t t.2)
  exact ⟨v, hv, fun j hj => hv' ⟨j, hj⟩⟩

theorem exists_conj_norm : ∀ (Γ : Type) [Group Γ] (K : Type) [Field K] (X : Type) [Monoid X] (ρ : Γ →* GL (Fin 2) K) (κ : Γ →* X) (Y : Γ → X → Fin 2 → K) (I J : Subgroup Γ) (γ φ : Γ) (N : ℕ) (x : X) (v : Fin 2 → K), ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) K)) κ Y → (∀ s ∈ I, κ s = 1) → J ≤ I → γ ∈ I → (∀ j ∈ J, φ * j * φ⁻¹ ∈ J) → (∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ N * j) → (∀ j ∈ J, Y j x = (ρ j : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v) → ∃ v' : Fin 2 → K, (∀ j ∈ J, Y j (x * κ φ) = (ρ j : Matrix (Fin 2) (Fin 2) K) *ᵥ v' - v') ∧ Y γ (x * κ φ) - (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v' - v') = (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ∑ i ∈ Finset.range N, ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ i) *ᵥ (Y γ x - (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v)) := by
  intro Γ _ K _ X _ ρ κ Y I J γ φ N x v hY hκ hJI hγ hJ ⟨j₁, hj₁, e⟩ hv
  set R : Γ → Matrix (Fin 2) (Fin 2) K := fun s => (ρ s : Matrix (Fin 2) (Fin 2) K) with hR
  have hm : ∀ s t w, R (s * t) *ᵥ w = R s *ᵥ (R t *ᵥ w) := fun s t w => by
    simp only [hR, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hp : ∀ n, R (γ ^ n) = R γ ^ n := fun n => by simp only [hR, map_pow, Units.val_pow_eq_pow_val]
  have h1 : ∀ w, R 1 *ᵥ w = w := fun w => by simp [hR]
  let z : Γ → Fin 2 → K := fun t => Y t x - (R t *ᵥ v - v)
  have hz0 : ∀ j ∈ J, z j = 0 := fun j hj => sub_eq_zero.2 (hv j hj)
  have hzc : ∀ s ∈ I, ∀ t, z (s * t) = z s + R s *ᵥ z t := fun s hs t => by
    simp only [z]
    rw [hY s t x, hκ s hs, mul_one, hm, Matrix.mulVec_sub, Matrix.mulVec_sub]; abel
  have hzp : ∀ n, z (γ ^ n) = (∑ i ∈ Finset.range n, R γ ^ i) *ᵥ z γ := fun n => by
    induction n with
    | zero => simpa using hz0 1 J.one_mem
    | succ n ih => rw [pow_succ, hzc _ (I.pow_mem hγ n), ih, hp, Finset.sum_range_succ, Matrix.add_mulVec]
  have key : ∀ s, φ * s * φ⁻¹ ∈ I → Y s (x * κ φ) - (R s *ᵥ (R φ⁻¹ *ᵥ (v + Y φ x)) - R φ⁻¹ *ᵥ (v + Y φ x))
      = R φ⁻¹ *ᵥ z (φ * s * φ⁻¹) := fun s hs => by
    have a1 := hY φ s x
    have a2 := hY (φ * s * φ⁻¹) φ x
    rw [inv_mul_cancel_right, hκ _ hs, mul_one, a1] at a2
    have a3 : Y s (x * κ φ) = R φ⁻¹ *ᵥ (Y (φ * s * φ⁻¹) x + R (φ * s * φ⁻¹) *ᵥ Y φ x - Y φ x) := by
      rw [← a2, add_sub_cancel_left, ← hm, inv_mul_cancel, h1]
    have a4 : ∀ w, R φ⁻¹ *ᵥ (R (φ * s * φ⁻¹) *ᵥ w) = R s *ᵥ (R φ⁻¹ *ᵥ w) := fun w => by
      rw [← hm, ← hm, mul_assoc φ, inv_mul_cancel_left]
    simp only [z, a3, Matrix.mulVec_sub, Matrix.mulVec_add, a4]; abel
  refine ⟨R φ⁻¹ *ᵥ (v + Y φ x), fun j hj => ?_, ?_⟩
  · have := key j (hJI (hJ j hj))
    rw [hz0 _ (hJ j hj), Matrix.mulVec_zero] at this
    exact sub_eq_zero.1 this
  · have := key γ (e ▸ I.mul_mem (I.pow_mem hγ N) (hJI hj₁))
    rw [e, hzc _ (I.pow_mem hγ N), hz0 _ hj₁, Matrix.mulVec_zero, add_zero, hzp] at this
    rw [← Matrix.mulVec_mulVec]
    exact this

theorem mem_of_orbit_sums : ∀ (l : ℕ) [Fact l.Prime] (u : ∀ r : ℕ, (ZMod (l ^ r))ˣ), (∀ k : ℕ, ∃ r, l ^ k ∣ orderOf (u r)) → ∀ (Wo : Submodule (Qbar l) (Fin 2 → Qbar l)) (T : Matrix (Fin 2) (Fin 2) (Qbar l)), (∀ w ∈ Wo, T *ᵥ w ∈ Wo) → ∀ (b : Fin 2 → Qbar l) (a : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ r x i, ‖a r x i‖ ≤ 1) → (∀ r x, a r (x * u r) - T *ᵥ a r x ∈ Wo) → (∀ r, b - ∑ x, a r x ∈ Wo) → b ∈ Wo := by
  classical
  intro l _ u hu Wo T hT b a ha hrel hb
  let S : Module.End (Qbar l) ((Fin 2 → Qbar l) ⧸ Wo) := Wo.mapQ Wo (Matrix.toLin' T) fun w hw => hT w hw
  obtain ⟨E, hE, hfix⟩ := exists_pow_fix S
  have h1 : ∀ r n x, Wo.mkQ (a r (x * u r ^ n)) = (S ^ n) (Wo.mkQ (a r x)) := fun r n x => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, pow_succ', Module.End.mul_apply, ← ih]
      exact (Submodule.Quotient.eq Wo).2 (hrel r _)
  have h2 : ∀ r x, Wo.mkQ (a r (x * u r ^ E)) = Wo.mkQ (a r x) := fun r x => by
    rw [h1]
    refine hfix (orderOf (u r)) (orderOf_pos _) _ ?_
    rw [← h1, pow_orderOf_eq_one, mul_one]
  have hE0 : 0 < ‖(E : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hE.ne')
  refine (isClosed_submodule Wo).closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hE0 hε) (norm_l_lt_one (l := l))
  obtain ⟨r, hr⟩ := hu k
  let : Fintype ((ZMod (l ^ r))ˣ ⧸ Subgroup.zpowers (u r ^ E)) := Fintype.ofFinite _
  have h3 := sum_eq_orderOf_smul (u r ^ E) (fun x => Wo.mkQ (a r x)) (h2 r)
  set o := orderOf (u r ^ E) with ho
  set y := ∑ ω : (ZMod (l ^ r))ˣ ⧸ Subgroup.zpowers (u r ^ E), a r ω.out with hy
  have h4 : l ^ k ∣ E * o := hr.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one]))
  have h5 : ‖(o : Qbar l)‖ < ε := by
    obtain ⟨m, hm⟩ := h4
    have : ‖(E : Qbar l)‖ * ‖(o : Qbar l)‖ ≤ ‖(l : Qbar l)‖ ^ k := by
      rw [← norm_mul, ← Nat.cast_mul, hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ m)
    exact lt_of_mul_lt_mul_left (this.trans_lt hk) hE0.le
  refine ⟨b - o • y, ?_, ?_⟩
  · rw [← map_sum, ← map_sum, ← map_nsmul] at h3
    have := Wo.add_mem (hb r) ((Submodule.Quotient.eq Wo).1 h3)
    rwa [sub_add_sub_cancel] at this
  · rw [dist_eq_norm, sub_sub_cancel, ← Nat.cast_smul_eq_nsmul (Qbar l), norm_smul]
    refine (mul_le_of_le_one_right (norm_nonneg _) ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)).trans_lt h5
    rw [hy, Finset.sum_apply]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ω _ => ha r _ i

theorem frob_mulVec_cob : ∀ (Γ : Type) [Group Γ] (K : Type) [Field K] (ρ : Γ →* GL (Fin 2) K) (J : Subgroup Γ) (γ φ : Γ) (N : ℕ), (∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ N * j) → ∀ u : Fin 2 → K, (∀ j ∈ J, ((ρ j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u) → (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ∑ i ∈ Finset.range N, ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ i) *ᵥ (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u) = ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u) - ((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u := by
  intro Γ _ K _ ρ J γ φ N ⟨j, hj, e⟩ u hu
  have e1 : ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u =
      (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e1, Matrix.mulVec_mulVec, Matrix.mul_assoc, geom_sum_mul, mul_sub, mul_one, Matrix.sub_mulVec]
  congr 1
  conv_lhs => rw [← hu j hj]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_pow_eq_pow_val, ← map_pow, ← Units.val_mul, ← Units.val_mul,
    ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_assoc, ← e, mul_assoc, inv_mul_cancel_left]

theorem exists_pow_dvd_orderOf : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ), 2 ≤ N → ∀ (u : ∀ r : ℕ, (ZMod (l ^ r))ˣ), (∀ r, ((u r : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = (N : ZMod (l ^ r))) → ∀ k : ℕ, ∃ r, l ^ k ∣ orderOf (u r) := by
  intro l hl N hN u hu k
  have hp : l.Prime := hl.out
  by_contra h
  push Not at h
  have hM : 0 < l ^ k * (l - 1) := mul_pos (pow_pos hp.pos k) (Nat.sub_pos_of_lt hp.one_lt)
  set M := l ^ k * (l - 1) with hMd
  set r := N ^ M + 1 with hr
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h1 : orderOf (u r) ∣ l ^ (r - 1) * (l - 1) := by
    rw [← Nat.totient_prime_pow hp (Nat.succ_pos _), ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  obtain ⟨d₁, d₂, h2, h3, h4⟩ := exists_dvd_and_dvd_of_dvd_mul h1
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h5 : a ≤ k := by
    by_contra h6
    exact h r (h4 ▸ (pow_dvd_pow l (not_le.1 h6).le).mul_right d₂)
  have h6 : u r ^ M = 1 := orderOf_dvd_iff_pow_eq_one.1 (h4 ▸ mul_dvd_mul (pow_dvd_pow l h5) h3)
  have h7 : ((N ^ M : ℕ) : ZMod (l ^ r)) = ((1 : ℕ) : ZMod (l ^ r)) := by
    rw [Nat.cast_pow, ← hu r, ← Units.val_pow_eq_pow_val, h6, Units.val_one, Nat.cast_one]
  have h8 : 1 < N ^ M := Nat.one_lt_pow hM.ne' hN
  have h9 := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' h8.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h7).symm)
  have h10 := Nat.lt_pow_self (n := r) hp.one_lt
  omega

theorem norm_mulVec_le {l : ℕ} [Fact l.Prime] {A : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hA : ∀ i k, ‖A i k‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin 2) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  show ‖∑ k, A i k * v k‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]; exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

theorem norm_sub_le_one {l : ℕ} [Fact l.Prime] {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

def cobSp {Γ K : Type} [Group Γ] [Field K] (ρ : Γ → Matrix (Fin 2) (Fin 2) K) (J : Subgroup Γ) (γ : Γ) :
    Submodule K (Fin 2 → K) where
  carrier := {w | ∃ u, (∀ j ∈ J, ρ j *ᵥ u = u) ∧ w = ρ γ *ᵥ u - u}
  zero_mem' := ⟨0, fun j _ => Matrix.mulVec_zero _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    refine ⟨u + u', fun j hj => by rw [Matrix.mulVec_add, hu j hj, hu' j hj], ?_⟩
    rw [Matrix.mulVec_add]; abel
  smul_mem' := by
    rintro a _ ⟨u, hu, rfl⟩
    refine ⟨a • u, fun j hj => by rw [Matrix.mulVec_smul, hu j hj], ?_⟩
    rw [Matrix.mulVec_smul, smul_sub]

theorem sub_mem_cobSp {Γ K : Type} [Group Γ] [Field K] {ρ : Γ → Matrix (Fin 2) (Fin 2) K} {J : Subgroup Γ} {γ : Γ}
    {v v' : Fin 2 → K} (y : Fin 2 → K) (h : ∀ j ∈ J, ρ j *ᵥ v - v = ρ j *ᵥ v' - v') :
    (y - (ρ γ *ᵥ v - v)) - (y - (ρ γ *ᵥ v' - v')) ∈ cobSp ρ J γ := by
  refine ⟨v' - v, fun j hj => ?_, ?_⟩
  · rw [Matrix.mulVec_sub, eq_add_of_sub_eq (h j hj)]; abel
  · rw [Matrix.mulVec_sub]; abel

theorem univNorm_unram_of_orderOf : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (κ : ∀ r : ℕ, G ℚ Ω →* (ZMod (l ^ r))ˣ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ r s, orderOf (κ r s) = orderOf (cycMod ℚ Ω l r s)) → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (κ r) (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y 0 s 1 = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c κ Y hκo hW hWO hYc hYO hSh hpush q hq
  obtain ⟨B, hB⟩ := exists_isPlaceOver (F := ℚ) Ω q
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨-, hJn, hJcop, -, ⟨γ, hγ⟩, hrel⟩ := GlobalTheory.Published.TameQuotient_holds ℚ Ω l B q hB hq
  obtain ⟨-, hcj, -⟩ := hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec B hγ.1⟩ hφ hγ
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := ℚ) B l
  have hγI := hγ.1
  have hgen := hγ.2
  set J := GlobalTheory.TameQuot.ineKer ℚ B l with hJ
  have hc1 : ∀ j ∈ J, φ * j * φ⁻¹ ∈ J := fun j hj =>
    hJn.conj_mem ⟨j, Ine_le_Dec B (hJI hj)⟩ hj ⟨φ, hφ.1⟩
  have hc2 : ∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ normV q * j :=
    ⟨(γ ^ normV q)⁻¹ * (φ * γ * φ⁻¹), by simpa using hcj, by rw [mul_inv_cancel_left]⟩
  have hκ : ∀ r, ∀ s ∈ Ine (F := ℚ) B, κ r s = 1 := fun r s hs => by
    rw [← orderOf_eq_one_iff, hκo, GlobalTheory.StringRepresentationDecomposition.cycMod_eq_one_of_mem_Ine r hq hB hs, orderOf_one]
  have hu : ∀ r, ((cycMod ℚ Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = (normV q : ZMod (l ^ r)) := fun r => by
    change PadicInt.toZModPow r ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = _
    rw [cycZ_of_isFrob hq hB hφ, map_natCast]
  have hW1 : ∀ s i k, ‖mat W s i k‖ ≤ 1 := fun s i k => norm_le_one_of_mem_coefO c ⟨_, hWO s i k⟩
  have hY1 : ∀ r s x i, ‖Y r s x i‖ ≤ 1 := fun r s x i => norm_le_one_of_mem_coefO c ⟨_, hYO r s x i⟩
  have hWc : ∀ i k, Continuous fun s => mat W s i k := fun i k =>
    Continuous.matrix_elem (A := fun s => mat W s) (Units.continuous_val.comp hW) i k
  have hcoc : ∀ r x, ∀ s ∈ Ine (F := ℚ) B, ∀ t, Y r (s * t) x = Y r s x + mat W s *ᵥ Y r t x := fun r x s hs t => by
    rw [hSh r s t x, hκ r s hs, mul_one]
  have hmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by
    simp only [mat, map_mul, Units.val_mul]
  choose v hv1 hv using fun r x => exists_cob_of_coprime (G ℚ Ω) l W (fun s => Y r s x) J hJcop hWc hW1 (hYc r x)
    (fun s i => hY1 r s x i) (fun s hs t _ => hcoc r x s (hJI hs) t)
  have hb : Y 0 γ 1 - (mat W γ *ᵥ v 0 1 - v 0 1) ∈ cobSp (mat W) J γ := by
    refine mem_of_orbit_sums l (fun r => κ r φ) (fun k => by
        simpa only [hκo] using exists_pow_dvd_orderOf l (normV q) (GlobalTheory.WeilDeligne.one_lt_normV q) (fun r => cycMod ℚ Ω l r φ) hu k) _
      (mat W φ⁻¹ * ∑ i ∈ Finset.range (normV q), mat W γ ^ i) ?_ _
      (fun r x => Y r γ x - (mat W γ *ᵥ v r x - v r x)) ?_ ?_ ?_
    · rintro _ ⟨u, hu', rfl⟩
      refine ⟨mat W φ⁻¹ *ᵥ u, fun j hj => ?_, frob_mulVec_cob (G ℚ Ω) (Qbar l) W J γ φ _ hc2 u hu'⟩
      have e : j * φ⁻¹ = φ⁻¹ * (φ * j * φ⁻¹) := by group
      rw [Matrix.mulVec_mulVec, ← hmul, e, hmul, ← Matrix.mulVec_mulVec, hu' _ (hc1 j hj)]
    · intro r x i
      exact norm_sub_le_one (hY1 r γ x i) (norm_sub_le_one (norm_mulVec_le (hW1 γ) (hv1 r x) i) (hv1 r x i))
    · intro r x
      obtain ⟨v', h1, h2⟩ := exists_conj_norm (G ℚ Ω) (Qbar l) _ W (κ r) (Y r) (Ine (F := ℚ) B) J γ φ (normV q) x
        (v r x) (hSh r) (hκ r) hJI hγI hc1 hc2 (hv r x)
      have h3 := sub_mem_cobSp (ρ := mat W) (γ := γ) (Y r γ (x * κ r φ))
        (fun j hj => (hv r (x * κ r φ) j hj).symm.trans (h1 j hj))
      rw [h2] at h3
      exact h3
    · intro r
      have hs := sum_level l (G ℚ Ω) _ Y hpush r
      have e : ∀ s, mat W s *ᵥ (∑ x, v r x) - ∑ x, v r x = ∑ x, (mat W s *ᵥ v r x - v r x) := fun s => by
        rw [Matrix.mulVec_sum, Finset.sum_sub_distrib]
      have h3 := sub_mem_cobSp (ρ := mat W) (γ := γ) (J := J) (v := v 0 1) (v' := ∑ x, v r x) (Y 0 γ 1)
        (fun j hj => by
          rw [e, ← hv 0 1 j hj]
          exact (hs j).trans (Finset.sum_congr rfl fun x _ => hv r x j hj))
      rw [Finset.sum_sub_distrib, ← hs, ← e]
      exact h3
  obtain ⟨w, hw, hb⟩ := hb
  refine ⟨B, hB, v 0 1 + w, fun s hs => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_gen (G ℚ Ω) l W (fun s => Y 0 s 1 - (mat W s *ᵥ (v 0 1 + w) - (v 0 1 + w))) (Ine (F := ℚ) B) J γ
    (isClosed_Ine B) hJI hγI (fun i => ?_) (fun s hs t _ => ?_) ?_ (fun j hj => ?_) hgen s hs
  · show Continuous fun s => Y 0 s 1 i - (∑ k, mat W s i k * (v 0 1 + w) k - (v 0 1 + w) i)
    exact (hYc 0 1 i).sub ((continuous_finset_sum _ fun k _ => (hWc i k).mul continuous_const).sub continuous_const)
  · show _ = _ + mat W s *ᵥ _
    rw [hcoc 0 1 s hs t, hmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub]; abel
  · show Y 0 γ 1 - _ = 0
    rw [eq_add_of_sub_eq hb, Matrix.mulVec_add]; abel
  · show Y 0 j 1 - _ = 0
    rw [hv 0 1 j hj, Matrix.mulVec_add, hw j hj]; abel

theorem univNorm_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y 0 s 1 = mat W s *ᵥ v - v :=
  fun l _ Ω _ _ _ W c Y => univNorm_unram_of_orderOf l Ω W c (fun r => (cycMod ℚ Ω l r)⁻¹) Y
    (fun r s => by rw [MonoidHom.inv_apply, orderOf_inv])

theorem univNorm_unram' : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r) (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y 0 s 1 = mat W s *ᵥ v - v :=
  fun l _ Ω _ _ _ W c Y => univNorm_unram_of_orderOf l Ω W c (fun r => cycMod ℚ Ω l r) Y (fun _ _ => rfl)

end GlobalTheory.KA.UnivNorm

end
