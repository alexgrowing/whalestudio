import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloPStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Ring

variable {O : Type} [CommRing O] {x : Sp O ⟶ X}

theorem base_eq (x : Sp O ⟶ X) (I : Ideal O) : spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x =
    spMap (algebraMap (O ⧸ I) (DualNumber (O ⧸ I))) ≫ spMap (Ideal.Quotient.mk I) ≫ x := by
  rw [← Category.assoc, Guard.sp_comp]

theorem red_ex (I : Ideal O) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v :=
  ⟨Over.homMk (spMap (dualMap (Ideal.Quotient.mk I)) ≫ v)
    ((GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv).1.trans (base_eq x I).symm), rfl⟩

theorem red_tors (I : Ideal O) {q : ℕ} (hq : (q : O) ∈ I) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G)
    (hw : w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v) : w ^ q = 1 := by
  have hv' := GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv
  have h0 := smT_zero_ovT hv'
  have key : ∀ n : ℕ, smT _ (n : O ⧸ I) (ovT hv') = ovT hv' ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero]; exact h0
    | succ n ih => rw [Nat.cast_succ, smT_add _ _ h0, ih, smT_unit, pow_succ]
  have hq0 : (q : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  have h1 : ovT hv' ^ q = 1 := by rw [← key, hq0, h0]
  let δ : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ tEpsG (spMap (Ideal.Quotient.mk I) ≫ x) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (base_eq x I).symm)
  have h2 : w = Formalism.L2.Pj.preHom δ (ovT hv') := Over.OverMorphism.ext (hw.trans (Category.id_comp _).symm)
  rw [h2, ← map_pow, h1, map_one]

def res {q q' : ℕ} (h : q ∣ q') (c : TorsChar t x q') : TorsChar t x q where
  χ := c.χ
  mul B _ _ _ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.mul B g g' (by rw [pow_mul, hg, one_pow]) (by rw [pow_mul, hg', one_pow])
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.nat B B' φ g g' (by rw [pow_mul, hg, one_pow]) hg'

theorem dlog_down {p k n : ℕ} (hk : k ≤ n) (c : TorsChar t x (p ^ n)) (c₁ : TorsChar t x (p ^ k))
    (hc : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
      (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G), w ^ (p ^ k) = 1 → c.χ B w = c₁.χ B w)
    {g : ℕ} {e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) {D : Fin g → O}
    (hD : DlogIs t p n c e D) : DlogIs t p k c₁ e D := by
  intro a v hav w hw
  have hv := Guard.comb_tan he hav
  obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : O) ^ n}) hv
  have hle : Ideal.span {(p : O) ^ n} ≤ Ideal.span {(p : O) ^ k} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hk)
  let φ : DualNumber (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] DualNumber (O ⧸ Ideal.span {(p : O) ^ k}) :=
    { dualMap (Ideal.Quotient.factor hle) with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }
  have h1 := c.nat _ _ φ w' w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w' hw') (by
    rw [hw, hw', ← Category.assoc, Guard.sp_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, φ])
  rw [← hc _ w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w hw), h1]
  have h2 := hD a v hav w' hw'
  have h3 : ∀ z, (φ z).snd = Ideal.Quotient.factor hle z.snd := fun z => by simp [φ, dualMap]
  rw [h3, h2, Ideal.Quotient.factor_mk]

end Ring

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp ↥(intO C) ⟶ X}

theorem coords {g : ℕ} {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) {a : Fin g → C}
    {w : Sp (DualNumber C) ⟶ t.G.left}
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w) (s : C)
    {vO : Sp (DualNumber ↥(intO C)) ⟶ t.G.left} (hv : IsTanAtG t x vO)
    (hs : spMap (dualMap (intO C).subtype) ≫ vO = spMap (epsMul s) ≫ w) :
    ∃ b : Fin g → ↥(intO C), IsCombAtG t x e b vO ∧ ∀ i, (b i : C) = s * a i := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 _ (RingHom.id ↥(intO C)) vO
  simp only [h1, h3, Category.id_comp] at h
  obtain ⟨b, hb, -⟩ := h hv
  have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
  have h4 := Guard.comb_smul heC hw s
  rw [← hs] at h4
  exact ⟨b, hb, congrFun ((he.2 C _ _ (GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hv)).unique
    (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hb) h4)⟩

theorem mem_latHT_iff : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [CompleteSpace C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (x : Sp ↥(intO C) ⟶ X), (∀ x' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x → x' = x) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)), IsTanBasis t x e → ∀ (n : ℕ) (h : Fin n → Fin g → ↥(intO C)), (∀ c : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c e (h j)) → (∀ j, ∃ c : TorsChar t x (p ^ 1), DlogIs t p 1 c e (h j)) → ∀ (a : Fin g → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO C).subtype ≫ x) ↔ (∀ j, ‖∑ i, (h j i : C) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : C) * a i‖ ≤ 1) := by
  intro hB E _ _ _ H X _ t p hp C _ _ _ _ _ hn x hx g e he n h hc hj a w hw
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  constructor
  · intro hL
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    have hpa : ∀ i, ‖(p : C) * a i‖ ≤ 1 := by
      obtain ⟨x', hx', vO, hv, hs⟩ := hB E H X t p C hn x hx w hL p (by
        rw [hn, ← Real.rpow_neg_one]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
        rw [div_le_one (by linarith)]
        linarith)
      obtain rfl := hx x' hx'
      obtain ⟨b, -, hb⟩ := coords he hw _ hv hs
      exact fun i => hb i ▸ (b i).2
    refine ⟨fun j => ?_, hpa⟩
    obtain ⟨x', hx', m, vO, hv, hs, hd⟩ := hL
    obtain rfl := hx x' hx'
    obtain ⟨b, hbv, hb⟩ := coords he hw _ hv hs
    show _ ∈ intO C
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h j i).2 ?_
      have := (b i).2
      rwa [hb, pow_zero, _root_.one_mul] at this
    obtain ⟨c, hcj⟩ := hj j
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t C x' (p ^ 1) (p ^ m) (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow _ hm) c
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p m c' g e he.1
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p 1 c g e he.1).2 D (h j) (dlog_down hm c' c hc' he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : ↥(intO C)) ^ m}) hv
    have h1 := hd m c' w' hw'
    have h2 : (p : ↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ m}) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [hD b vO hbv w' hw', h2, Ideal.span_singleton_zero, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    have h3 : ∑ i, (D i : C) * a i = r := by
      apply mul_right_cancel₀ (pow_ne_zero m hp0)
      have := congrArg (intO C).subtype hr
      simp only [map_mul, map_pow, map_natCast, map_sum, Subring.subtype_apply, hb] at this
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, (h j i : C) * a i = r - ∑ i, (δ i : C) * ((p : C) * a i) := by
      rw [← h3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (a i) * this
    rw [h4]
    exact Subring.sub_mem _ r.2 (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (δ i).2 (hpa i))
  · rintro ⟨h1, h2⟩
    let b : Fin g → ↥(intO C) := fun i => ⟨(p : C) * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
    refine ⟨x, rfl, 1, vO, hv, ?_, fun k c w' hw' => ?_⟩
    · rw [pow_one]
      exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hbv) (Guard.comb_smul heC hw p)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c g e he.1
    obtain ⟨j, hcj⟩ := hc (res (pow_dvd_pow p hk) c)
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 1 _ g e he.1).2 D (h j)
      (dlog_down hk c _ (fun _ _ _ _ _ _ => rfl) he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO C) := ⟨∑ i, (h j i : C) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO C)) ^ 1 := by
      apply (intO C).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : C) * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.HTLevel
