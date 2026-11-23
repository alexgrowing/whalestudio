import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL

noncomputable section

open scoped Classical

open ValuativeRel NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D) in

def QLocG : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ q, Agree δ M q) → ∀ (p : PlF D) (g : Loc.SplitG (M p).L), (M p).split = some g →
      ∀ k : ℕ, k ≤ D.R.rS → ∀ z : D.host.E,
        LocMem D p (qdPow D k) z ↔ ∃ o ∈ (D.s.atP p).O,
          cc δ p ^ k * (D.s.atP p).ιE z = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)
  (g : Loc.SplitG (M p).L) (hs : (M p).split = some g)

abbrev γp : (D.s.atP p).Fp := δ p * ((uP p : ℚ) : (D.s.atP p).Fp)

theorem cc_eq : cc δ p = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (γp δ p) := by
  have hE : (D.s.atP p).ιE (uP p : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp) := by
    rw [← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]
  rw [cc, hE, ← map_mul]

theorem e_alg (x : (D.s.atP p).Fp) : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep x) = (x, x) := by
  rw [AlgEquiv.commutes]; rfl

include hA in
theorem γp_ne : γp δ p ≠ 0 := by
  intro h0
  have hu := cc_unit δ M hA p
  rw [cc_eq, h0, map_zero] at hu
  exact not_isUnit_zero hu

include hA in
theorem e_frFac (a : Fin (D.R.rS + 1)) :
    g.e (frFac δ p a) = ((γp δ p ^ (D.R.rS - a.val))⁻¹, (γp δ p ^ (D.R.rS - a.val))⁻¹) := by
  have h := congrArg g.e (frFac_mul δ M hA p a)
  rw [map_mul, map_pow, cc_eq, e_alg, map_one] at h
  have hγ := pow_ne_zero (D.R.rS - a.val) (γp_ne δ M hA p)
  ext
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_one] at h1
    exact eq_inv_of_mul_eq_one_left h1
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_one] at h2
    exact eq_inv_of_mul_eq_one_left h2

theorem ratio {F : Type*} [Field F] {γ : F} (hγ : γ ≠ 0) {m n : ℕ} (h : m ≤ n) :
    (γ ^ m)⁻¹ / (γ ^ n)⁻¹ = γ ^ (n - m) := by
  rw [inv_div_inv, pow_sub₀ γ hγ h, div_eq_mul_inv]

include hA hs in

theorem e_conj (z : D.host.E) :
    g.e ((D.s.atP p).ιE (D.conjF z)) = (g.e ((D.s.atP p).ιE z)).swap := by
  rw [← (D.s.atP p).cj_ιE, ← (hA p).2.2.1]
  exact g.e_cj _

include hA in

theorem mem_O_split (w : (D.s.atP p).Ep) :
    w ∈ (D.s.atP p).O ↔ (g.e w).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e w).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  have hint : ∀ s : (D.s.atP p).Fp, IsIntegral 𝒪[(D.s.atP p).Fp] s ↔ s ∈ 𝒪[(D.s.atP p).Fp] := fun s =>
    ⟨fun h => (Valuation.integer.integers (valuation (D.s.atP p).Fp)).mem_of_integral h,
      fun h => by
        have := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Fp) (x := ⟨s, h⟩)
        exact this⟩
  rw [(D.s.atP p).O_def, ← isIntegral_algEquiv (g.e.restrictScalars 𝒪[(D.s.atP p).Fp]),
    IsIntegral.pair_iff, hint, hint]
  rfl

include hs in

theorem mem_R_split (w : (D.s.atP p).Ep) :
    w ∈ (M p).R ↔ (g.e w).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e w).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
      ∃ t ∈ 𝒪[(D.s.atP p).Fp], (g.e w).1 - (g.e w).2 = (g.q : (D.s.atP p).Fp) * t := by
  simp only [Loc.Model.R, hs, Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus, RingHom.comp_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have h1 : (g.e w).1 = (z.1 : (D.s.atP p).Fp) := by
      have := congrArg Prod.fst hze; simpa using this.symm
    have h2 : (g.e w).2 = (z.2 : (D.s.atP p).Fp) := by
      have := congrArg Prod.snd hze; simpa using this.symm
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hz
    obtain ⟨t, ht⟩ := hz
    refine ⟨by rw [h1]; exact z.1.2, by rw [h2]; exact z.2.2, t, t.2, ?_⟩
    rw [h1, h2, mul_comm]
    exact_mod_cast ht.symm
  · rintro ⟨h1, h2, t, ht, he⟩
    refine ⟨(⟨(g.e w).1, h1⟩, ⟨(g.e w).2, h2⟩), ?_, ?_⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      refine ⟨⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      simp only [RingHom.coe_fst, RingHom.coe_snd]
      push_cast
      rw [he]; ring
    · simp

include hA hs in
theorem e_lG_low (a b : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    g.e (StabShape.lG g.e (D.s.atP p).ιE (frFac δ p) a b i j) =
      (γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).1,
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).2) := by
  simp only [StabShape.lG, Matrix.of_apply, AlgEquiv.apply_symm_apply, e_frFac δ M hA p g, bt]
  have h1 : j.val < i.val := hji
  have h2 := i.isLt
  have hm : D.R.rS - i.val ≤ D.R.rS - j.val := by omega
  have hk : D.R.rS - j.val - (D.R.rS - i.val) = i.val - j.val := by omega
  rw [← hk, ← ratio (γp_ne δ M hA p) hm]
  ext <;> simp only <;> ring

include hA hs in
theorem e_ρG_up (a b : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    g.e (StabShape.ρG g.e (D.s.atP p).ιE (frFac δ p) a b j i) =
      (γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).1,
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).2) := by
  simp only [StabShape.ρG, Matrix.of_apply, AlgEquiv.apply_symm_apply, e_frFac δ M hA p g, bt]
  have h1 : j.val < i.val := hji
  have h2 := i.isLt
  have hm : D.R.rS - i.val ≤ D.R.rS - j.val := by omega
  have hk : D.R.rS - j.val - (D.R.rS - i.val) = i.val - j.val := by omega
  rw [← hk, ← ratio (γp_ne δ M hA p) hm]
  ext <;> simp only <;> ring

include hA hs in
theorem intLow_iff_G {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i →
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).1 ∈ 𝒪[(D.s.atP p).Fp] ∧
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
        ∃ t ∈ 𝒪[(D.s.atP p).Fp], γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).1 -
          γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).2 = (g.q : (D.s.atP p).Fp) * t := by
  have hl : StabShape.lOf δ M p a b = StabShape.lG g.e (D.s.atP p).ιE (frFac δ p) a b := by
    simp only [StabShape.lOf, hs]
  constructor
  · intro h i j hji
    have := (mem_R_split M p g hs _).1 (h.2.2 i j)
    rw [hl, e_lG_low δ M hA p g hs a b i j hji] at this
    exact this
  · intro h
    refine ⟨StabShape.lOf_diag δ M (hA p) a b ha hb, fun i j hij => ?_, fun i j => ?_⟩
    · rw [hl]; simp [StabShape.lG, (ha i j).1 hij, (hb j i).1 hij]
    · rcases lt_trichotomy j i with hji | rfl | hij
      · rw [mem_R_split M p g hs, hl, e_lG_low δ M hA p g hs a b i j hji]; exact h i j hji
      · rw [StabShape.lOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hl]; simp [StabShape.lG, (ha i j).1 hij, (hb j i).1 hij, ← Prod.zero_eq_mk]

include hA hs in
theorem intUp_iff_G {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i →
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).1 ∈ 𝒪[(D.s.atP p).Fp] ∧
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
        ∃ t ∈ 𝒪[(D.s.atP p).Fp], γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).1 -
          γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).2 = (g.q : (D.s.atP p).Fp) * t := by
  have hr : StabShape.ρOf δ M p a b = StabShape.ρG g.e (D.s.atP p).ιE (frFac δ p) a b := by
    simp only [StabShape.ρOf, hs]
  constructor
  · intro h i j hji
    have := (mem_R_split M p g hs _).1 (h.2.2 j i)
    rw [hr, e_ρG_up δ M hA p g hs a b i j hji] at this
    exact this
  · intro h
    refine ⟨StabShape.ρOf_diag δ M (hA p) a b ha hb, fun i j hji => ?_, fun i j => ?_⟩
    · rw [hr]; simp [StabShape.ρG, (hb i j).1 hji, (ha j i).1 hji]
    · rcases lt_trichotomy i j with hij | rfl | hji
      · rw [mem_R_split M p g hs, hr, e_ρG_up δ M hA p g hs a b j i hij]; exact h j i hij
      · rw [StabShape.ρOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hr]; simp [StabShape.ρG, (hb i j).1 hji, (ha j i).1 hji, ← Prod.zero_eq_mk]

include hA in
theorem e_cc_mul (k : ℕ) (w : (D.s.atP p).Ep) :
    g.e (cc δ p ^ k * w) = (γp δ p ^ k * (g.e w).1, γp δ p ^ k * (g.e w).2) := by
  rw [map_mul, map_pow, cc_eq, e_alg]
  ext <;> simp [Prod.pow_fst, Prod.pow_snd]

include hA in
theorem mem_qO (w : (D.s.atP p).Ep) :
    (∃ o ∈ (D.s.atP p).O, w = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) ↔
      (∃ t ∈ 𝒪[(D.s.atP p).Fp], (g.e w).1 = (g.q : (D.s.atP p).Fp) * t) ∧
        (∃ t ∈ 𝒪[(D.s.atP p).Fp], (g.e w).2 = (g.q : (D.s.atP p).Fp) * t) := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    rw [mem_O_split δ M hA p g] at ho
    rw [map_mul, e_alg]
    exact ⟨⟨_, ho.1, rfl⟩, ⟨_, ho.2, rfl⟩⟩
  · rintro ⟨⟨t1, h1, e1⟩, ⟨t2, h2, e2⟩⟩
    refine ⟨g.e.symm (t1, t2), ?_, ?_⟩
    · rw [mem_O_split δ M hA p g, AlgEquiv.apply_symm_apply]; exact ⟨h1, h2⟩
    · apply g.e.injective
      rw [map_mul, e_alg, AlgEquiv.apply_symm_apply]
      ext
      · simp [e1]
      · simp [e2]

include hA hs in
theorem locEntry_iff_G (hQ : QLocG D) (a b : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    (LocMem D p (ddPow D (i.val - j.val)) (a i j) ∧ LocMem D p (ddPow D (i.val - j.val)) (bt D b j i) ∧
      LocMem D p (qdPow D (i.val - j.val)) (a i j - D.conjF (bt D b j i))) ↔
    ((γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).1 ∈ 𝒪[(D.s.atP p).Fp] ∧
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (a i j))).2 ∈ 𝒪[(D.s.atP p).Fp]) ∧
      (γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).1 ∈ 𝒪[(D.s.atP p).Fp] ∧
        γp δ p ^ (i.val - j.val) * (g.e ((D.s.atP p).ιE (bt D b j i))).2 ∈ 𝒪[(D.s.atP p).Fp]) ∧
      (∃ t ∈ 𝒪[(D.s.atP p).Fp], γp δ p ^ (i.val - j.val) * ((g.e ((D.s.atP p).ιE (a i j))).1 -
        (g.e ((D.s.atP p).ιE (bt D b j i))).2) = (g.q : (D.s.atP p).Fp) * t) ∧
      (∃ t ∈ 𝒪[(D.s.atP p).Fp], γp δ p ^ (i.val - j.val) * ((g.e ((D.s.atP p).ιE (a i j))).2 -
        (g.e ((D.s.atP p).ιE (bt D b j i))).1) = (g.q : (D.s.atP p).Fp) * t)) := by
  have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
  rw [locMem_iff δ M hA p hk, locMem_iff δ M hA p hk, hQ δ M hA p g hs _ hk]
  have hq : ∀ w : (D.s.atP p).Ep, (∃ o ∈ (D.s.atP p).O,
      w = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) ↔ _ := mem_qO δ M hA p g
  rw [hq, mem_O_split δ M hA p g, mem_O_split δ M hA p g]
  simp only [e_cc_mul δ M hA p g, map_sub, Prod.fst_sub, Prod.snd_sub, e_conj δ M hA p g hs, Prod.fst_swap,
    Prod.snd_swap]

theorem locShapeG_of (hQ : QLocG D) : LocShapeG D := by
  intro δ M p hA hsome a b ha hb
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hsome
  rw [intLow_iff_G δ M hA p g hs ha hb, intUp_iff_G δ M hA p g hs ha hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hji
    obtain ⟨x1, v1, t1, ht1, e1⟩ := h1 i j hji
    obtain ⟨u2, y2, t2, ht2, e2⟩ := h2 i j hji
    refine (locEntry_iff_G δ M hA p g hs hQ a b i j hji).2
      ⟨⟨x1, y2⟩, ⟨u2, v1⟩, ⟨t1, ht1, by rw [mul_sub]; exact e1⟩, ⟨-t2, neg_mem ht2, ?_⟩⟩
    rw [mul_sub, mul_neg, ← e2]; ring
  · intro h
    refine ⟨fun i j hji => ?_, fun i j hji => ?_⟩
    · obtain ⟨⟨x1, -⟩, ⟨-, v1⟩, ⟨t1, ht1, e1⟩, -⟩ := (locEntry_iff_G δ M hA p g hs hQ a b i j hji).1 (h i j hji)
      exact ⟨x1, v1, t1, ht1, by rw [← mul_sub]; exact e1⟩
    · obtain ⟨⟨-, y1⟩, ⟨u1, -⟩, -, ⟨t2, ht2, e2⟩⟩ := (locEntry_iff_G δ M hA p g hs hQ a b i j hji).1 (h i j hji)
      refine ⟨u1, y1, -t2, neg_mem ht2, ?_⟩
      rw [mul_neg, ← e2]; ring

end Formalism.L2.SG.Pf.StabIntSh
