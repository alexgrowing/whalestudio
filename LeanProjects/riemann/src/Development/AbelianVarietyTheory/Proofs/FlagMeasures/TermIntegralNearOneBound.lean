import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuadricCharacterLeakSharesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPowSmulMemOfIsLat

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FibU

theorem exists_reps {W : Type} [AddCommGroup W] (A P : AddSubgroup W) (h : P.relIndex A ≠ 0) :
    ∃ R : Finset W, (∀ w ∈ R, w ∈ A) ∧ ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ P := by
  have hf : Finite (A ⧸ P.addSubgroupOf A) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (A ⧸ P.addSubgroupOf A)
  refine ⟨Finset.univ.image fun c : A ⧸ P.addSubgroupOf A => ((c.out : A) : W), ?_, ?_⟩
  · intro w hw
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hw
    exact c.out.2
  · intro w hw
    have key : ∀ c : A ⧸ P.addSubgroupOf A, w - ((c.out : A) : W) ∈ P ↔
        c = QuotientAddGroup.mk (⟨w, hw⟩ : A) := by
      intro c
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simp [neg_add_eq_sub]
    refine ⟨_, ⟨Finset.mem_image.2 ⟨QuotientAddGroup.mk (⟨w, hw⟩ : A), Finset.mem_univ _, rfl⟩,
      (key _).2 rfl⟩, ?_⟩
    rintro x ⟨hx, hx'⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    rw [(key c).1 hx']

theorem relIndex_ne_zero {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (Λ : Submodule R W)
    (hΛ : Λ.FG) (c : R) [Finite (R ⧸ Ideal.span {c})] (P : AddSubgroup W) (hP : ∀ y ∈ Λ, c • y ∈ P) :
    P.relIndex Λ.toAddSubgroup ≠ 0 := by
  have h1 : Finite (Λ ⧸ (Ideal.span {c} • (⊤ : Submodule R Λ))) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top Λ).2 hΛ)
  have h2 : (Ideal.span {c} • (⊤ : Submodule R Λ)).toAddSubgroup.index ≠ 0 :=
    Nat.card_pos (α := Λ ⧸ (Ideal.span {c} • (⊤ : Submodule R Λ))) |>.ne'
  have h3 : (Ideal.span {c} • (⊤ : Submodule R Λ)).toAddSubgroup ≤ P.addSubgroupOf Λ.toAddSubgroup := by
    intro x hx
    rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hP y y.2
  intro h0
  exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.index_dvd_of_le h3))

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_addl (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a + b) y = hf L H a y + hf L H b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_addr (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a + b) = hf L H y a + hf L H y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smull (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H (c • a) y = c * hf L H a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smulr (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H y (c • a) = L.cj c * hf L H y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_cj (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (hH : IsHerm L H) (a y : Fin n → E) :
    L.cj (hf L H a y) = hf L H y a := by
  have h : ∀ i j, L.cj (H i j) = H j i := fun i j => congrFun (congrFun hH j) i
  simp only [hf, map_sum, map_mul, L.cj_cj, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [IsNonarchimedeanLocalField F]

theorem exists_pow_smul (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    (Λ : Submodule L.O (Fin n → E)) (hΛ : IsLat L Λ) (y : Fin n → E) :
    ∃ m : ℕ, algebraMap F E ((ϖ : F) ^ m) • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat
  | exact _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat
  | (apply _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat ..)

theorem exists_inv_one_add (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) :
    ∃ z ∈ L.O, z * (1 + algebraMap F E ϖ * x) = 1 := by
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_trace L hx
  obtain ⟨s, hs⟩ := GlobalTheory.UnramOrder.exists_norm L hx
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  have hu : IsUnit (1 + ϖ * (t + ϖ * s)) := by
    have : ϖ * (t + ϖ * s) ∈ IsLocalRing.maximalIdeal 𝒪[F] := Ideal.mul_mem_right _ _ hϖ.not_isUnit
    simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem this)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨algebraMap F E v * (1 + algebraMap F E ϖ * L.cj x), L.O.mul_mem (hint v)
    (L.O.add_mem L.O.one_mem (L.O.mul_mem (hint ϖ) (GlobalTheory.UnramOrder.cj_mem L hx))), ?_⟩
  have h2 := congrArg (fun a : 𝒪[F] => algebraMap F E a) hv
  push_cast at h2
  simp only [map_mul, map_add, map_one, ← ht, ← hs] at h2
  linear_combination h2

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem inZ_add {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {N : ℕ} (hN : S.a ≤ N) {u y : S.V}
    (hu : u ∈ Λ) (hy : y ∈ Λ) (hZ : S.InZ u) : S.InZ (u + algebraMap F E ((S.ϖ : F) ^ N) • y) := by
  obtain ⟨c, hc⟩ := hZ
  have h0 : (S.ϖ : F) ≠ 0 := fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (N : ℤ) = S.a + m := ⟨(N - S.a).toNat, by omega⟩
  have hpow : (S.ϖ : F) ^ N = (S.ϖ : F) ^ S.a * (S.ϖ : F) ^ m := by
    rw [← zpow_natCast, hm, zpow_add₀ h0, zpow_natCast]
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_trace L ((hΛ.2 y).2 hy u hu)
  obtain ⟨s, hs⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L ((hΛ.2 y).2 hy y hy) (hf_cj L _ S.herm.1 y y)
  rw [hf_cj L _ S.herm.1] at ht
  refine ⟨c + S.ϖ ^ m * (t + S.ϖ ^ N * s), ?_⟩
  unfold Frames.h at hc ⊢
  simp only [hf_addl, hf_addr, hf_smull, hf_smulr, AlgEquiv.commutes, hc, hs]
  push_cast
  have h2 := congrArg (algebraMap F E) hpow
  simp only [map_mul, map_add, map_pow, ← ht] at h2 ⊢
  linear_combination (hf L S.Hm u y + hf L S.Hm y u + algebraMap F E S.ϖ ^ N * algebraMap F E s) * h2

theorem noLeak_add {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {N : ℕ} (hN : 1 ≤ N) {u y : S.V}
    (hy : y ∈ Λ) (hZ : S.NoLeak Λ u) : S.NoLeak Λ (u + algebraMap F E ((S.ϖ : F) ^ N) • y) := by
  obtain ⟨x, hx, hxW, hux⟩ := hZ
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hp : algebraMap F E ((S.ϖ : F) ^ m) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 m)
  obtain ⟨z, hz, hz1⟩ := exists_inv_one_add L S.ϖ S.ϖ_irr (L.O.mul_mem hp ((hΛ.2 x).2 hx y hy))
  refine ⟨L.cj z • x, Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hz⟩ hx, S.W0.smul_mem _ hxW, ?_⟩
  unfold Frames.h at hux ⊢
  rw [hf_smulr, hf_addl, hf_smull, hux, L.cj_cj, pow_succ, map_mul]
  linear_combination hz1

def mulP (Λ : Submodule L.O S.V) (N : ℕ) : AddSubgroup S.V where
  carrier := {x | ∃ y ∈ Λ, x = algebraMap F E ((S.ϖ : F) ^ N) • y}
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Λ.add_mem ha hb, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, Λ.neg_mem ha, by simp⟩

theorem exists_reps_refU [CharZero F] {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) (J N : ℕ) :
    ∃ R : Finset S.V, (∀ w ∈ R, w ∈ S.refU J Λ) ∧ ∀ w ∈ S.refU J Λ, ∃! x, x ∈ R ∧ w - x ∈ mulP S Λ N := by
  have hp : algebraMap F E ((S.ϖ : F) ^ N) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 N)
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hset : {y : L.O | (y : E) = algebraMap F E ((S.ϖ : F) ^ N)} = {⟨_, hp⟩} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
  have h8 := h6 N
  rw [hset] at h8
  have : Finite (L.O ⧸ Ideal.span {(⟨_, hp⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [h8]; positivity)
  have h9 := relIndex_ne_zero Λ hΛ.1.1 ⟨_, hp⟩ (mulP S Λ N) fun y hy => ⟨y, hy, rfl⟩
  exact exists_reps _ _ fun h => h9 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)

end

theorem cint_eq_mean {W : Type} [AddCommGroup W] (A P : AddSubgroup W) (R : Finset W) (Q : W → Prop)
    (g : W → ℂ) (hR : ∀ w ∈ R, w ∈ A) (hR' : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ P)
    (hQ : ∀ w ∈ A, ∀ b ∈ P, Q w → Q (w + b)) (hg : ∀ w, ∀ b ∈ P, g (w + b) = g w) :
    cint A (fun u => ind (fun u => u ∈ A ∧ Q u) u * g u) = (∑ u ∈ R.filter Q, g u) / (R.card : ℂ) := by
  have := (GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives A (P ⊓ A) (fun u => ind (fun u => u ∈ A ∧ Q u) u * g u) R inf_le_right ?_ ?_ hR ?_).2.2
  · rw [this, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    simp [ind, hR u hu]
  · rintro w b ⟨hb, hb'⟩
    have : (w + b ∈ A ∧ Q (w + b)) ↔ (w ∈ A ∧ Q w) := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by simpa using A.sub_mem h1 hb', ?_⟩
        simpa using hQ _ h1 _ (P.neg_mem hb) h2
      · rintro ⟨h1, h2⟩
        exact ⟨A.add_mem h1 hb', hQ _ h1 _ hb h2⟩
    have h' : ind (fun u => u ∈ A ∧ Q u) (w + b) = ind (fun u => u ∈ A ∧ Q u) w := by
      unfold ind
      exact congrArg (fun p : Prop => @ite ℂ p (Classical.propDecidable p) 1 0) (propext this)
    simp only [h', hg w b hb]
  · intro w hw
    simp [ind, hw]
  · intro w hw
    obtain ⟨x, ⟨hx, hx'⟩, hu⟩ := hR' w hw
    exact ⟨x, ⟨hx, hx', A.sub_mem hw (hR x hx)⟩, fun y hy => hu y ⟨hy.1, hy.2.1⟩⟩

theorem shares : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → |(cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re * (S.q : ℝ) ^ S.a - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re * (S.q : ℝ) ^ S.a ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ∀ y : S.V, (∃ u ∈ S.refU J Λ, L.psi0 (S.h y u) ≠ 1) → ‖cint (S.refU J Λ) (fun u => ind (fun u => u ∈ S.refU J Λ ∧ S.InZ u) u * L.psi0 (S.h y u))‖ * (S.q : ℝ) ^ S.a ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk J d Λ hT
  have hΛ : IsSD L S.Hm Λ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  have hq : (0 : ℝ) < (S.q : ℝ) ^ S.a := by
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    have : 0 < S.q := lt_of_lt_of_le two_pos h7
    positivity
  have main : ∀ N : ℕ, S.a + 1 ≤ N → 1 ≤ N → ∃ R : Finset S.V, (0 : ℝ) < R.card ∧ (∀ w ∈ R, w ∈ S.refU J Λ) ∧
      (∀ w ∈ S.refU J Λ, ∃! x, x ∈ R ∧ w - x ∈ mulP S Λ N) := by
    intro N _ _
    obtain ⟨R, h1, h2⟩ := exists_reps_refU S hΛ J N
    obtain ⟨x, ⟨hx, -⟩, -⟩ := h2 0 (zero_mem _)
    exact ⟨R, by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩, h1, h2⟩
  have hZ : ∀ N : ℕ, S.a + 1 ≤ N → ∀ w ∈ S.refU J Λ, ∀ b ∈ mulP S Λ N, S.InZ w → S.InZ (w + b) := by
    rintro N hN w hw _ ⟨y, hy, rfl⟩ h
    exact inZ_add S hΛ (by omega) hw.1 hy h
  set ε : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with hε
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨R, h0, h1, h2⟩ := main (S.a.toNat + 1) (by omega) (by omega)
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (S.a.toNat + 1) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).1
    have h4 := cint_eq_mean _ _ R S.InZ (fun _ => 1) h1 h2 (hZ _ (by omega)) (fun _ _ _ => rfl)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re =
        ((R.filter S.InZ).card : ℝ) / R.card := by
      rw [show (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u) = fun u => (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u) u
        from rfl, h4, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
    rw [h5]
    have h6 : ((R.filter S.InZ).card : ℝ) / R.card * (S.q : ℝ) ^ S.a - 1 =
        (((R.filter S.InZ).card : ℝ) - R.card / (S.q : ℝ) ^ S.a) / (R.card / (S.q : ℝ) ^ S.a) := by
      field_simp
    rw [h6, abs_div, abs_of_pos (div_pos h0 hq), div_le_iff₀ (div_pos h0 hq)]
    exact h3
  · obtain ⟨R, h0, h1, h2⟩ := main (S.a.toNat + 1) (by omega) (by omega)
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (S.a.toNat + 1) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).2.1
    have h4 := cint_eq_mean _ _ R (fun u => S.InZ u ∧ ¬ S.NoLeak Λ u) (fun _ => 1) h1 h2
      (fun w hw b hb h => ⟨hZ _ (by omega) w hw b hb h.1, fun h' => h.2 (by
        obtain ⟨y, hy, hb'⟩ := (mulP S Λ _).neg_mem hb
        have := noLeak_add S hΛ (N := S.a.toNat + 1) (by omega) hy h'
        rwa [← hb', add_neg_cancel_right] at this)⟩) (fun _ _ _ => rfl)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re =
        ((R.filter fun u => S.InZ u ∧ ¬ S.NoLeak Λ u).card : ℝ) / R.card := by
      rw [show (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u) =
        fun u => (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u) u
        from rfl, h4, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
      congr
    rw [h5]
    have h6 : ∀ c : ℝ, c / R.card * (S.q : ℝ) ^ S.a = c / (R.card / (S.q : ℝ) ^ S.a) := by
      intro c
      field_simp
    rw [h6, div_le_iff₀ (div_pos h0 hq)]
    refine le_trans (le_of_eq ?_) h3
    congr 2
  · rintro y ⟨u, hu, hne⟩
    obtain ⟨m, hm⟩ := exists_pow_smul L S.ϖ S.ϖ_irr Λ hΛ.1 y
    obtain ⟨R, h0, h1, h2⟩ := main (m + (S.a.toNat + 1)) (by omega) (by omega)
    have hint : ∀ z ∈ Λ, algebraMap F E ((S.ϖ : F) ^ (m + (S.a.toNat + 1))) * S.h y z ∈ L.O := by
      intro z hz
      have := L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 (S.a.toNat + 1)))
        ((hΛ.2 z).2 hz _ hm)
      rw [hf_smull] at this
      convert this using 1
      rw [pow_add, map_mul, Frames.h]
      ring
    have hg : ∀ w, ∀ b ∈ mulP S Λ (m + (S.a.toNat + 1)), L.psi0 (S.h y (w + b)) = L.psi0 (S.h y w) := by
      rintro w _ ⟨z, hz, rfl⟩
      have := (L.additive_character_dual_ring _).2 (hint z hz) 1 L.O.one_mem
      rw [mul_one] at this
      unfold Frames.h at this ⊢
      rw [hf_addr, hf_smulr, AlgEquiv.commutes, AddChar.map_add_eq_mul, this, mul_one]
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (m + (S.a.toNat + 1)) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).2.2 y (fun u hu => hint u (h1 u hu).1) (by
        obtain ⟨x, ⟨hx, hx'⟩, -⟩ := h2 u hu
        refine ⟨x, hx, ?_⟩
        rwa [← hg x _ hx', add_sub_cancel])
    have h4 := cint_eq_mean _ _ R S.InZ (fun u => L.psi0 (S.h y u)) h1 h2 (hZ _ (by omega)) hg
    have h6 : ∀ c : ℝ, c / R.card * (S.q : ℝ) ^ S.a = c / (R.card / (S.q : ℝ) ^ S.a) := by
      intro c
      field_simp
    rw [h4, norm_div, Complex.norm_natCast, h6, div_le_iff₀ (div_pos h0 hq)]
    exact h3

end GlobalTheory.HL.FibU
