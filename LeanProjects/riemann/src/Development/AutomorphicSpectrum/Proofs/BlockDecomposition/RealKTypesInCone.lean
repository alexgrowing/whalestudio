import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.KTypeCone

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel KHighest)

section Generic

variable {n : ℕ} {Y X : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

theorem orth_stable {Kf : Fin n → Fin n → Module.End ℂ Y}
    (hK : ∀ a b (x y : Y), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) {S : Submodule ℂ Y}
    (hS : ∀ a b, ∀ w ∈ S, Kf a b w ∈ S) (a b : Fin n) {r : Y} (hr : r ∈ Sᗮ) : Kf a b r ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal] at hr ⊢
  intro u hu
  rw [← hK b a u r]
  exact hr _ (hS b a u hu)

theorem eq_zero_of_mem_orth {S : Submodule ℂ Y} {x : Y} (h : x ∈ S) (h' : x ∈ Sᗮ) : x = 0 :=
  inner_self_eq_zero (𝕜 := ℂ).1 ((Submodule.mem_orthogonal _ _).1 h' x h)

theorem proj_highest {Kf : Fin n → Fin n → Module.End ℂ Y}
    (hK : ∀ a b (x y : Y), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) {S : Submodule ℂ Y}
    (hS : ∀ a b, ∀ w ∈ S, Kf a b w ∈ S) {μ : Fin n → ℝ} {z p r : Y}
    (hz : KHighest (fun _ => true) Kf μ z) (hp : p ∈ S) (hr : r ∈ Sᗮ) (e : z = p + r) :
    KHighest (fun _ => true) Kf μ p := by
  subst e
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have h := hz.1 a
    rw [map_add, smul_add] at h
    have h1 : Kf a a p - (μ a : ℂ) • p ∈ S := S.sub_mem (hS a a p hp) (S.smul_mem _ hp)
    have h2 : Kf a a p - (μ a : ℂ) • p = -(Kf a a r - (μ a : ℂ) • r) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [sub_add_sub_comm, h, sub_self]
    have h3 : Kf a a p - (μ a : ℂ) • p ∈ Sᗮ := by
      rw [h2]
      exact Sᗮ.neg_mem (Sᗮ.sub_mem (orth_stable hK hS a a hr) (Sᗮ.smul_mem _ hr))
    exact sub_eq_zero.1 (eq_zero_of_mem_orth h1 h3)
  · have h := hz.2 a b hab he
    rw [map_add] at h
    have h2 : Kf a b p = -(Kf a b r) := eq_neg_of_add_eq_zero_left h
    refine eq_zero_of_mem_orth (hS a b p hp) ?_
    rw [h2]
    exact Sᗮ.neg_mem (orth_stable hK hS a b hr)

theorem lift_highest [AddCommGroup X] [Module ℂ X] {Kf : Fin n → Fin n → Module.End ℂ Y}
    (hK : ∀ a b (x y : Y), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) {S : Submodule ℂ Y} [FiniteDimensional ℂ S]
    (hS : ∀ a b, ∀ w ∈ S, Kf a b w ∈ S) (π : Y →ₗ[ℂ] X) (KX : Fin n → Fin n → Module.End ℂ X)
    (hπ : ∀ a b y, π (Kf a b y) = KX a b (π y)) {ν : Fin n → ℝ} {m : Y} (hm : m ∈ S)
    (hx : KHighest (fun _ => true) KX ν (π m)) :
    ∃ y ∈ S, π y = π m ∧ KHighest (fun _ => true) Kf ν y := by
  let T : Submodule ℂ Y := S ⊓ LinearMap.ker π
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace T := FiniteDimensional.complete ℂ T
  have hT : ∀ a b, ∀ w ∈ T, Kf a b w ∈ T := fun a b w hw =>
    ⟨hS a b w hw.1, by
      have h0 : π w = 0 := hw.2
      show π (Kf a b w) = 0
      rw [hπ, h0, map_zero]⟩
  obtain ⟨t, ht, c, hc, e⟩ := T.exists_add_mem_mem_orthogonal m
  have hcS : c ∈ S := by
    have : c = m - t := by rw [e]; abel
    rw [this]
    exact S.sub_mem hm ht.1
  have hπt : π t = 0 := ht.2
  have hπc : π c = π m := by rw [e, map_add, hπt, zero_add]
  refine ⟨c, hcS, hπc, fun a => ?_, fun a b hab he => ?_⟩
  · have h1 : Kf a a c - (ν a : ℂ) • c ∈ T := by
      refine ⟨S.sub_mem (hS a a c hcS) (S.smul_mem _ hcS), ?_⟩
      show π (Kf a a c - (ν a : ℂ) • c) = 0
      rw [map_sub, map_smul, hπ, hπc, hx.1 a, sub_self]
    have h2 : Kf a a c - (ν a : ℂ) • c ∈ Tᗮ := Tᗮ.sub_mem (orth_stable hK hT a a hc) (Tᗮ.smul_mem _ hc)
    exact sub_eq_zero.1 (eq_zero_of_mem_orth h1 h2)
  · have h1 : Kf a b c ∈ T := by
      refine ⟨hS a b c hcS, ?_⟩
      show π (Kf a b c) = 0
      rw [hπ, hπc, hx.2 a b hab he]
    exact eq_zero_of_mem_orth h1 (orth_stable hK hT a b hc)

end Generic

section Sum

variable {n : ℕ} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

local notation "𝐘" => WithLp 2 (V × W)

def dsum : (Module.End ℂ V × Module.End ℂ W) →ₐ[ℂ] Module.End ℂ (WithLp 2 (V × W)) :=
  ((WithLp.linearEquiv 2 ℂ (V × W)).symm.conjAlgEquiv ℂ).toAlgHom.comp (LinearMap.prodMapAlgHom ℂ V W)

@[simp] theorem dsum_fst (p : Module.End ℂ V × Module.End ℂ W) (y : 𝐘) : (dsum p y).ofLp.1 = p.1 y.ofLp.1 := rfl

@[simp] theorem dsum_snd (p : Module.End ℂ V × Module.End ℂ W) (y : 𝐘) : (dsum p y).ofLp.2 = p.2 y.ofLp.2 := rfl

theorem dsum_mk (p : Module.End ℂ V × Module.End ℂ W) (x : V) (w : W) :
    dsum p (WithLp.toLp 2 (x, w)) = WithLp.toLp 2 (p.1 x, p.2 w) := rfl

theorem y_ext {y z : 𝐘} (h1 : y.ofLp.1 = z.ofLp.1) (h2 : y.ofLp.2 = z.ofLp.2) : y = z :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

def sumF (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) :
    Fin n → Fin n → Module.End ℂ (WithLp 2 (V × W)) := fun a b => dsum (E a b, F a b)

theorem glRel_sumF {E : Fin n → Fin n → Module.End ℂ V} {F : Fin n → Fin n → Module.End ℂ W}
    (hE : GlRel E) (hF : GlRel F) : GlRel (sumF E F) := by
  intro a b c d
  have h1 := hE a b c d
  have h2 := hF a b c d
  have key : (E a b, F a b) * (E c d, F c d) - (E c d, F c d) * (E a b, F a b) =
      (if b = c then (E a d, F a d) else 0) - (if d = a then (E c b, F c b) else 0) := by
    split_ifs at h1 h2 ⊢ <;> exact Prod.ext (by simpa using h1) (by simpa using h2)
  have h3 := congrArg dsum key
  rw [map_sub, map_sub, map_mul, map_mul] at h3
  simp only [sumF]
  rw [h3]
  split_ifs <;> simp

theorem comm_sumF {E E' : Fin n → Fin n → Module.End ℂ V} {F F' : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b c d, E a b * E' c d = E' c d * E a b) (hF : ∀ a b c d, F a b * F' c d = F' c d * F a b)
    (a b c d : Fin n) : sumF E F a b * sumF E' F' c d = sumF E' F' c d * sumF E F a b := by
  simp only [sumF]
  rw [← map_mul, ← map_mul]
  exact congrArg dsum (Prod.ext (hE a b c d) (hF a b c d))

theorem kF_sumF (E1 E2 : Fin n → Fin n → Module.End ℂ V) (F1 F2 : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) :
    kF (sumF E1 F1) (sumF E2 F2) a b = dsum (kF E1 E2 a b, kF F1 F2 a b) := by
  simp only [kF, sumF]
  rw [← map_add]
  rfl

theorem epow_sumF (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) (m : ℕ) (a b : Fin n) :
    epow (sumF E F) m a b = dsum (epow E m a b, epow F m a b) := by
  induction m generalizing a b with
  | zero =>
    simp only [epow]
    split_ifs
    · exact (map_one dsum).symm
    · exact (map_zero dsum).symm
  | succ m ih =>
    simp only [epow, ih, sumF]
    simp only [← map_mul]
    rw [← map_sum]
    exact congrArg dsum (Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum]))

theorem gelA_sumF (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) (m : ℕ) :
    gelA (sumF E F) m = dsum (gelA E m, gelA F m) := by
  simp only [gelA, epow_sumF]
  rw [← map_sum]
  exact congrArg dsum (Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum]))

theorem barF_sumF (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) :
    barF (sumF E F) = sumF (barF E) (barF F) := by
  funext a b
  simp only [barF, sumF]
  rw [← map_neg]
  rfl

theorem hwSp_fst {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    {ν : Fin n → ℝ} {y : 𝐘} (h : y ∈ hwSp (sumF E1 F1) (sumF E2 F2) ν) : y.ofLp.1 ∈ hwSp E1 E2 ν := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have h' := h.1 a
    rw [kF_sumF] at h'
    exact congrArg (fun z : 𝐘 => z.ofLp.1) h'
  · have h' := h.2 a b hab he
    rw [kF_sumF] at h'
    exact congrArg (fun z : 𝐘 => z.ofLp.1) h'

theorem hwSp_snd {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    {ν : Fin n → ℝ} {y : 𝐘} (h : y ∈ hwSp (sumF E1 F1) (sumF E2 F2) ν) : y.ofLp.2 ∈ hwSp F1 F2 ν := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have h' := h.1 a
    rw [kF_sumF] at h'
    exact congrArg (fun z : 𝐘 => z.ofLp.2) h'
  · have h' := h.2 a b hab he
    rw [kF_sumF] at h'
    exact congrArg (fun z : 𝐘 => z.ofLp.2) h'

theorem hwSp_mk {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    {ν : Fin n → ℝ} {x : V} {w : W} (hx : x ∈ hwSp E1 E2 ν) (hw : w ∈ hwSp F1 F2 ν) :
    (WithLp.toLp 2 (x, w) : 𝐘) ∈ hwSp (sumF E1 F1) (sumF E2 F2) ν := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [kF_sumF]
    exact y_ext (hx.1 a) (hw.1 a)
  · rw [kF_sumF]
    exact y_ext (hx.2 a b hab he) (hw.2 a b hab he)

theorem unit_sumF {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ)
    (hF : ∀ a b (x y : W), ⟪kF F1 F2 a b x, y⟫_ℂ = ⟪x, kF F1 F2 b a y⟫_ℂ) (a b : Fin n) (x y : 𝐘) :
    ⟪kF (sumF E1 F1) (sumF E2 F2) a b x, y⟫_ℂ = ⟪x, kF (sumF E1 F1) (sumF E2 F2) b a y⟫_ℂ := by
  rw [kF_sumF, kF_sumF, WithLp.prod_inner_apply, WithLp.prod_inner_apply, dsum_fst, dsum_snd, dsum_fst, dsum_snd]
  exact congrArg₂ (· + ·) (hE a b _ _) (hF a b _ _)

theorem exists_prod_sub (S1 : Submodule ℂ V) (S2 : Submodule ℂ W) [FiniteDimensional ℂ S1] [FiniteDimensional ℂ S2] :
    ∃ S : Submodule ℂ 𝐘, FiniteDimensional ℂ S ∧ ∀ y : 𝐘, y ∈ S ↔ y.ofLp.1 ∈ S1 ∧ y.ofLp.2 ∈ S2 := by
  let f : (S1 × S2) →ₗ[ℂ] 𝐘 :=
    (WithLp.linearEquiv 2 ℂ (V × W)).symm.toLinearMap ∘ₗ (S1.subtype.prodMap S2.subtype)
  refine ⟨LinearMap.range f, inferInstance, fun y => ⟨?_, fun h => ⟨(⟨_, h.1⟩, ⟨_, h.2⟩), rfl⟩⟩⟩
  rintro ⟨⟨s1, s2⟩, rfl⟩
  exact ⟨s1.2, s2.2⟩

theorem locFin_sumF {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S)
    (hF : ∀ x : W, ∃ S : Submodule ℂ W, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) (y : 𝐘) :
    ∃ S : Submodule ℂ 𝐘, FiniteDimensional ℂ S ∧ y ∈ S ∧
      ∀ a b, ∀ w ∈ S, kF (sumF E1 F1) (sumF E2 F2) a b w ∈ S := by
  obtain ⟨S1, h1, m1, s1⟩ := hE y.ofLp.1
  obtain ⟨S2, h2, m2, s2⟩ := hF y.ofLp.2
  haveI := h1
  haveI := h2
  obtain ⟨S, hS, hm⟩ := exists_prod_sub S1 S2
  refine ⟨S, hS, (hm y).2 ⟨m1, m2⟩, fun a b w hw => ?_⟩
  have hw' := (hm w).1 hw
  rw [hm, kF_sumF]
  exact ⟨s1 a b _ hw'.1, s2 a b _ hw'.2⟩

theorem admissible_direct_sum_cone {lam : Fin n → ℤ} {lev : Fin n → ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hV : AdmFor lam lev E1 E2) (M : Model lam lev) (hN : ∀ ν, IsSecondTypeWeight lam lev ν → hwSp M.F1 M.F2 ν = ⊥) :
    AdmFor lam lev (sumF E1 M.F1) (sumF E2 M.F2) where
  gl1 := glRel_sumF hV.gl1 M.gl1
  gl2 := glRel_sumF hV.gl2 M.gl2
  comm := comm_sumF hV.comm M.comm
  unitK := unit_sumF hV.unitK M.unitK
  locFin := locFin_sumF hV.locFin M.locFin
  ch1 m x := by
    rw [gelA_sumF]
    exact y_ext (hV.ch1 m _) (M.ch1 m _)
  ch2 m x := by
    rw [barF_sumF, gelA_sumF]
    exact y_ext (hV.ch2 m _) (M.ch2 m _)
  no_second_type_weight ν hν := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h1 : y.ofLp.1 = 0 := by
      have := hwSp_fst hy
      rw [hV.no_second_type_weight ν hν] at this
      exact (Submodule.mem_bot ℂ).1 this
    have h2 : y.ofLp.2 = 0 := by
      have := hwSp_snd hy
      rw [hN ν hν] at this
      exact (Submodule.mem_bot ℂ).1 this
    exact y_ext h1 h2

def pairAlg (E1 E2 : Fin n → Fin n → Module.End ℂ V) (F1 F2 : Fin n → Fin n → Module.End ℂ W) :
    Subalgebra ℂ (Module.End ℂ V × Module.End ℂ W) :=
  Algebra.adjoin ℂ {x | ∃ a b, x = (E1 a b, F1 a b) ∨ x = (E2 a b, F2 a b)}

section PairAlg

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}

theorem first_generator_mem_pair_algebra (a b : Fin n) : (E1 a b, F1 a b) ∈ pairAlg E1 E2 F1 F2 :=
  Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩

theorem second_generator_mem_pair_algebra (a b : Fin n) : (E2 a b, F2 a b) ∈ pairAlg E1 E2 F1 F2 :=
  Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩

theorem kpair_mem (a b : Fin n) : (kF E1 E2 a b, kF F1 F2 a b) ∈ pairAlg E1 E2 F1 F2 :=
  add_mem (first_generator_mem_pair_algebra a b) (second_generator_mem_pair_algebra a b)

theorem exists_pair_of_mem_alg {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) :
    ∃ a2 : Module.End ℂ W, (a, a2) ∈ pairAlg E1 E2 F1 F2 := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl | rfl⟩ := hx
    · exact ⟨_, first_generator_mem_pair_algebra a b⟩
    · exact ⟨_, second_generator_mem_pair_algebra a b⟩
  | algebraMap r => exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨x2, hx⟩ := hx
    obtain ⟨y2, hy⟩ := hy
    exact ⟨x2 + y2, add_mem hx hy⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x2, hx⟩ := hx
    obtain ⟨y2, hy⟩ := hy
    exact ⟨x2 * y2, mul_mem hx hy⟩

theorem dsum_mem_alg {p : Module.End ℂ V × Module.End ℂ W} (hp : p ∈ pairAlg E1 E2 F1 F2) :
    dsum p ∈ alg (sumF E1 F1) (sumF E2 F2) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl | rfl⟩ := hx
    · exact Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩
    · exact Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

theorem adj_one (hp : IsPair E1 E2) (a b : Fin n) (x y : V) : ⟪E1 a b x, y⟫_ℂ = ⟪x, E2 b a y⟫_ℂ := by
  have h1 := hp.unitK a b x y
  have h2 := hp.unitP a b x y
  simp only [kF, pF, LinearMap.add_apply, LinearMap.sub_apply, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right] at h1 h2
  linear_combination (h1 + h2) / 2

theorem adj_two (hp : IsPair E1 E2) (a b : Fin n) (x y : V) : ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ := by
  have h1 := hp.unitK a b x y
  have h2 := hp.unitP a b x y
  simp only [kF, pF, LinearMap.add_apply, LinearMap.sub_apply, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right] at h1 h2
  linear_combination (h1 - h2) / 2

theorem exists_adj (hp : IsPair E1 E2) {p : Module.End ℂ V × Module.End ℂ W} (hpA : p ∈ pairAlg E1 E2 F1 F2) :
    ∃ q ∈ pairAlg E1 E2 F1 F2, ∀ x y : V, ⟪p.1 x, y⟫_ℂ = ⟪x, q.1 y⟫_ℂ := by
  induction hpA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl | rfl⟩ := hx
    · exact ⟨_, second_generator_mem_pair_algebra b a, adj_one hp a b⟩
    · exact ⟨_, first_generator_mem_pair_algebra b a, adj_two hp a b⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (starRingEnd ℂ r), Subalgebra.algebraMap_mem _ _, fun x y => ?_⟩
    show ⟪algebraMap ℂ (Module.End ℂ V) r x, y⟫_ℂ = ⟪x, algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ r) y⟫_ℂ
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, hq'⟩ := hx
    obtain ⟨q', hr, hr'⟩ := hy
    refine ⟨q + q', add_mem hq hr, fun u w => ?_⟩
    show ⟪(x.1 + y.1) u, w⟫_ℂ = ⟪u, (q.1 + q'.1) w⟫_ℂ
    rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right, hq', hr']
  | mul x y _ _ hx hy =>
    obtain ⟨q, hq, hq'⟩ := hx
    obtain ⟨q', hr, hr'⟩ := hy
    refine ⟨q' * q, mul_mem hr hq, fun u w => ?_⟩
    show ⟪x.1 (y.1 u), w⟫_ℂ = ⟪u, q'.1 (q.1 w)⟫_ℂ
    rw [hq', hr']

end PairAlg

def genN (A : Subalgebra ℂ (Module.End ℂ V × Module.End ℂ W)) (z : 𝐘) : Submodule ℂ 𝐘 where
  carrier := {y | ∃ p ∈ A, dsum p z = y}
  add_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p + q, add_mem hp hq, by rw [map_add, LinearMap.add_apply]⟩
  zero_mem' := ⟨0, zero_mem _, by rw [map_zero, LinearMap.zero_apply]⟩
  smul_mem' := by
    rintro c _ ⟨p, hp, rfl⟩
    exact ⟨c • p, A.smul_mem hp c, by rw [map_smul, LinearMap.smul_apply]⟩

theorem genN_stable {A : Subalgebra ℂ (Module.End ℂ V × Module.End ℂ W)} {z y : 𝐘}
    {q : Module.End ℂ V × Module.End ℂ W} (hq : q ∈ A) (hy : y ∈ genN A z) : dsum q y ∈ genN A z := by
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨q * p, mul_mem hq hp, by rw [map_mul]; rfl⟩

def sndL : 𝐘 →ₗ[ℂ] W := LinearMap.snd ℂ V W ∘ₗ (WithLp.linearEquiv 2 ℂ (V × W)).toLinearMap

def fstL : 𝐘 →ₗ[ℂ] V := LinearMap.fst ℂ V W ∘ₗ (WithLp.linearEquiv 2 ℂ (V × W)).toLinearMap

theorem first_summand_zero {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}
    (hp : IsPair E1 E2)
    (hunit : ∀ a b (x y : 𝐘), ⟪kF (sumF E1 F1) (sumF E2 F2) a b x, y⟫_ℂ = ⟪x, kF (sumF E1 F1) (sumF E2 F2) b a y⟫_ℂ)
    (hloc : ∀ y : 𝐘, ∃ S : Submodule ℂ 𝐘, FiniteDimensional ℂ S ∧ y ∈ S ∧
      ∀ a b, ∀ w ∈ S, kF (sumF E1 F1) (sumF E2 F2) a b w ∈ S)
    {μ : Fin n → ℝ} {v : V} {f : W} (hv : v ∈ hwSp E1 E2 μ) (hf : f ≠ 0)
    (hmult : ∀ w ∈ hwSp (sumF E1 F1) (sumF E2 F2) μ, w ∈ genN (pairAlg E1 E2 F1 F2) (WithLp.toLp 2 (v, f)) →
      ∃ c : ℂ, w = c • (WithLp.toLp 2 (v, f) : 𝐘))
    {u : V} (hu : (WithLp.toLp 2 (u, 0) : 𝐘) ∈ genN (pairAlg E1 E2 F1 F2) (WithLp.toLp 2 (v, f))) : u = 0 := by
  set N := genN (pairAlg E1 E2 F1 F2) (WithLp.toLp 2 (v, f) : 𝐘) with hN
  let N0 : Submodule ℂ 𝐘 := N ⊓ LinearMap.ker sndL
  have hK0 : ∀ a b, ∀ y ∈ N0, kF (sumF E1 F1) (sumF E2 F2) a b y ∈ N0 := by
    intro a b y hy
    rw [kF_sumF]
    refine ⟨genN_stable (kpair_mem a b) hy.1, ?_⟩
    have h0 : y.ofLp.2 = 0 := hy.2
    show (kF F1 F2 a b) y.ofLp.2 = 0
    rw [h0, map_zero]
  have key : ∀ u' : V, (WithLp.toLp 2 (u', 0) : 𝐘) ∈ N → ⟪u', v⟫_ℂ = 0 := by
    intro u' hu'
    obtain ⟨S', hfd, hmem, hst⟩ := hloc (WithLp.toLp 2 (u', 0))
    haveI := hfd
    let S : Submodule ℂ 𝐘 := S' ⊓ N0
    haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_inf_left S' N0
    haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
    have hSst : ∀ a b, ∀ w ∈ S, kF (sumF E1 F1) (sumF E2 F2) a b w ∈ S := fun a b w hw =>
      ⟨hst a b w hw.1, hK0 a b w hw.2⟩
    obtain ⟨p, hpS, r, hr, e⟩ := S.exists_add_mem_mem_orthogonal (WithLp.toLp 2 (v, 0) : 𝐘)
    have hph : p ∈ hwSp (sumF E1 F1) (sumF E2 F2) μ :=
      proj_highest hunit hSst (hwSp_mk hv (Submodule.zero_mem _)) hpS hr e
    obtain ⟨c, hc⟩ := hmult p hph hpS.2.1
    have hp0 : p.ofLp.2 = 0 := hpS.2.2
    have hcf : c • f = 0 := by
      rw [hc] at hp0
      exact hp0
    have hc0 : c = 0 := (smul_eq_zero.1 hcf).resolve_right hf
    have hpz : p = 0 := by rw [hc, hc0, zero_smul]
    have hre : r = WithLp.toLp 2 (v, 0) := by rw [e, hpz, zero_add]
    have h := (Submodule.mem_orthogonal _ _).1 hr (WithLp.toLp 2 (u', 0))
      ⟨hmem, hu', show (0 : W) = 0 from rfl⟩
    rw [hre, WithLp.prod_inner_apply] at h
    simpa using h
  obtain ⟨p, hpA, hpe⟩ := hu
  have hpv : p.1 v = u := congrArg (fun z : 𝐘 => z.ofLp.1) hpe
  obtain ⟨q, hq, hadj⟩ := exists_adj hp hpA
  have hqu : (WithLp.toLp 2 (q.1 u, 0) : 𝐘) ∈ N := by
    have h := genN_stable (z := (WithLp.toLp 2 (v, f) : 𝐘)) hq (show (WithLp.toLp 2 (u, 0) : 𝐘) ∈ N from ⟨p, hpA, hpe⟩)
    rw [dsum_mk, map_zero] at h
    exact h
  have h1 : ⟪u, u⟫_ℂ = 0 := by
    calc ⟪u, u⟫_ℂ = ⟪p.1 v, u⟫_ℂ := by rw [hpv]
      _ = ⟪v, q.1 u⟫_ℂ := hadj v u
      _ = 0 := by rw [← inner_conj_symm, key _ hqu, map_zero]
  exact inner_self_eq_zero (𝕜 := ℂ).1 h1

end Sum

theorem k_types_in_weight_cone : KTypeGenerationHighest := by
  intro hM n lam hlam lev hlev V _ _ E1 E2 hp hadm M hMn v hv hv0 ν x hx hx0 ⟨a, ha, hax⟩
  have hY := admissible_direct_sum_cone hadm M hMn
  set A := pairAlg E1 E2 M.F1 M.F2 with hA
  set vf : WithLp 2 (V × M.W) := WithLp.toLp 2 (v, M.f) with hvf
  have hvfh : vf ∈ hwSp (sumF E1 M.F1) (sumF E2 M.F2) (muQ lam lev) := hwSp_mk hv M.hw
  have hvf0 : vf ≠ 0 := fun h => hv0 (congrArg (fun z : WithLp 2 (V × M.W) => z.ofLp.1) h)
  have hmult : ∀ w ∈ hwSp (sumF E1 M.F1) (sumF E2 M.F2) (muQ lam lev), w ∈ genN A vf → ∃ c : ℂ, w = c • vf := by
    rintro w hw ⟨p, hpA, rfl⟩
    exact hM n lam hlam lev hlev _ _ _ hY vf _ hvfh hw hvf0 ⟨dsum p, dsum_mem_alg hpA, rfl⟩
  obtain ⟨a2, ha2⟩ := exists_pair_of_mem_alg (F1 := M.F1) (F2 := M.F2) ha
  have hm : dsum (a, a2) vf ∈ genN A vf := ⟨_, ha2, rfl⟩
  obtain ⟨S', hfd, hmem, hst⟩ := hY.locFin (dsum (a, a2) vf)
  haveI := hfd
  let S : Submodule ℂ (WithLp 2 (V × M.W)) := S' ⊓ genN A vf
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_inf_left S' _
  have hSst : ∀ i j, ∀ w ∈ S, kF (sumF E1 M.F1) (sumF E2 M.F2) i j w ∈ S := fun i j w hw =>
    ⟨hst i j w hw.1, by rw [kF_sumF]; exact genN_stable (kpair_mem i j) hw.2⟩
  have hπm : fstL (dsum (a, a2) vf) = x := hax
  obtain ⟨y, hyS, hyx, hyh⟩ := lift_highest hY.unitK hSst fstL (kF E1 E2)
    (fun i j y => by rw [kF_sumF]; rfl) (m := dsum (a, a2) vf) (ν := ν) ⟨hmem, hm⟩ (by rw [hπm]; exact hx)
  rw [hπm] at hyx
  have hyw : y.ofLp.2 ∈ hwSp M.F1 M.F2 ν := hwSp_snd (E1 := E1) (E2 := E2) hyh
  refine M.cone ν _ hyw fun h0 => hx0 ?_
  have hye : y = WithLp.toLp 2 (x, 0) := y_ext hyx h0
  exact first_summand_zero hp hY.unitK hY.locFin hv M.ne hmult (hye ▸ hyS.2)

end GlobalTheory.CompanionTheory.KTypeCone
