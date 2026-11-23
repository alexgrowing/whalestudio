import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open GlobalTheory.SW.Lev
open Formalism.L2.Pj
open scoped Classical

namespace GlobalTheory.Dict.TieModel

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_gen_one {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (A : Submodule (𝓞 E) E) (hA : A.FG) :
    ∃ p ∈ A, A ≤ Submodule.span (𝓞 E) {p} ⊔ 𝔪 • A := by
  by_cases hb : A = ⊥
  · exact ⟨0, zero_mem _, by simp [hb]⟩
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hA
  have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  let f : 𝓞 E →ₗ[𝓞 E] E := LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹
  have hf (a : 𝓞 E) : f a = (a : E) * (d : E)⁻¹ := rfl
  let I : Ideal (𝓞 E) := A.comap f
  have hI : Submodule.map f I = A := by
    refine Submodule.map_comap_eq_self fun x hx => ?_
    obtain ⟨a, ha⟩ := hint x hx
    refine ⟨a, ?_⟩
    have : (a : E) = (d : E) * x := ha
    rw [hf, this]; field_simp
  have hI0 : I ≠ ⊥ := fun h => hb (by rw [← hI, h, Submodule.map_bot])
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_sup_span_eq (I := 𝔪 * I) (J := I) Ideal.mul_le_right
    (mul_ne_zero h0 hI0)
  have hpI : p ∈ I := hp ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self p)
  refine ⟨f p, hpI, ?_⟩
  conv_lhs => rw [← hI, ← hp]
  rw [Submodule.map_sup, sup_comm]
  refine sup_le_sup ?_ ?_
  · rw [Ideal.span, Submodule.map_span, Set.image_singleton]
  · rw [← smul_eq_mul, Submodule.map_smul'', hI]

theorem exists_gens {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) : ∀ (r : ℕ) (L : Submodule (𝓞 E) (Fin r → E)), L.FG →
    ∃ β : Fin r → Fin r → E, (∀ i, β i ∈ L) ∧ L ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ 𝔪 • L := by
  intro r
  induction r with
  | zero => exact fun L _ => ⟨fun i => i.elim0, fun i => i.elim0, fun v _ => by
      rw [Subsingleton.elim v 0]; exact zero_mem _⟩
  | succ r ih =>
    intro L hL
    let π : (Fin (r + 1) → E) →ₗ[𝓞 E] E := LinearMap.proj 0
    let ι : (Fin r → E) →ₗ[𝓞 E] (Fin (r + 1) → E) := LinearMap.vecCons 0 LinearMap.id
    have hι : Function.Injective ι := fun a b h => by
      simpa [ι] using h
    obtain ⟨_, ⟨b, hb, rfl⟩, hgen⟩ := exists_gen_one h0 (L.map π) (hL.map π)
    have hfg : (L.comap ι).FG :=
      Submodule.fg_of_fg_map_injective ι hι (Submodule.FG.of_le hL (Submodule.map_comap_le _ _))
    obtain ⟨β, hβ, hsp⟩ := ih _ hfg
    refine ⟨Fin.cons b fun i => ι (β i), fun i => Fin.cases hb (fun i => hβ i) i, fun v hv => ?_⟩
    have h1 := hgen ⟨v, hv, rfl⟩
    rw [← Set.image_singleton, ← Submodule.map_span, ← Submodule.map_smul'', ← Submodule.map_sup] at h1
    obtain ⟨w, hw, e⟩ := h1
    have hwL : w ∈ L := (sup_le (Submodule.span_le.2 (by simpa using hb)) Submodule.smul_le_right :
      _ ≤ L) hw
    have e2 : v - w = ι (Fin.tail (v - w)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · have : w 0 = v 0 := e
        simp [ι, this]
      · simp [ι, Fin.tail]
    have h2 : Fin.tail (v - w) ∈ L.comap ι := by
      rw [Submodule.mem_comap, ← e2]; exact sub_mem hv hwL
    have h3 := Submodule.mem_map_of_mem (f := ι) (hsp h2)
    rw [← e2, Submodule.map_sup, Submodule.map_smul'', Submodule.map_span] at h3
    rw [← sub_add_cancel v w]
    refine add_mem (SetLike.le_def.1 (sup_le_sup (Submodule.span_mono ?_)
      (Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _))) h3)
      (SetLike.le_def.1 (sup_le_sup_right (Submodule.span_mono ?_) _) hw)
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.succ, rfl⟩
    · rintro _ rfl
      exact ⟨0, rfl⟩

theorem span_of_map {r : ℕ} {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [Module.Projective (𝓞 E) M] (hM : Module.finrank (𝓞 E) M = r) {𝔞 : Ideal (𝓞 E)}
    {L : Submodule (𝓞 E) (Fin r → E)} (hL : L.FG) (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤)
    {δ : M →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ 𝔞 • L)
    {S : Submodule (𝓞 E) M} (h : L ≤ loc 𝔞 (S.map δ ⊔ 𝔞 • L)) : S ⊔ 𝔞 • ⊤ = ⊤ := by
  by_cases ht : 𝔞 = ⊤
  · simp [ht]
  obtain ⟨s, hs, hN⟩ := nakayama hL hon
  have hs0 : (s : E) ≠ 0 := by simpa using cop_ne_zero ht hs
  have hinj : Function.Injective δ := by
    have h1 : Submodule.span E (LinearMap.range δ : Set (Fin r → E)) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      exact fun v hv => (Submodule.smul_mem_iff _ hs0).1 (Submodule.subset_span (hN v hv))
    have h2 : r ≤ Module.finrank (𝓞 E) (LinearMap.range δ) := by
      obtain ⟨b, hb, hs', hli⟩ := exists_linearIndependent E (LinearMap.range δ : Set (Fin r → E))
      have c : Cardinal.mk b = r := by
        rw [← rank_span_set hli, hs', h1, rank_top]; simp
      have li : LinearIndependent (𝓞 E) (fun x : b => (⟨x, hb x.2⟩ : LinearMap.range δ)) :=
        LinearIndependent.of_comp (LinearMap.range δ).subtype (hli.restrict_scalars' (𝓞 E))
      have := li.cardinal_le_rank
      rw [c, ← Module.finrank_eq_rank] at this
      exact_mod_cast this
    have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.ker δ)
    rw [δ.quotKerEquivRange.finrank_eq, hM] at h3
    have h4 : Module.finrank (𝓞 E) (LinearMap.ker δ) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 h4
  rw [eq_top_iff]
  intro a _
  obtain ⟨t, ht, h1⟩ := h (hδ a)
  refine mem_of_loc (L := ⊤) trivial le_sup_right ⟨s * t, cop_mul hs ht, ?_⟩
  have h2 : δ ((s * t) • a) ∈ (S ⊔ 𝔞 • ⊤).map δ := by
    obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 h1
    rw [map_smul, mul_smul, ← e, smul_add, Submodule.map_sup, Submodule.map_smul'', ← LinearMap.range_eq_map]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hu) (smul_map_mem LinearMap.id hN hw)
  obtain ⟨b, hb, e⟩ := h2
  exact hinj e ▸ hb

variable [IsCMField E] {r n : ℕ} {X : Data E r}

theorem cong_mono {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) {u v : Fin r → E} (H : Cong X 𝔞 u v) : Cong X 𝔟 u v := by
  obtain ⟨s, hs, H⟩ := H
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact ⟨s, cop_iff.2 ⟨a, m, h hm, e⟩, Submodule.smul_mono h le_rfl H⟩

theorem coeff_cong_factor (D : SW.Level X) {𝔞 𝔟 : Ideal (𝓞 E)} (hm : D.𝔪 = 𝔞 * 𝔟) (hc : IsCoprime 𝔞 𝔟)
    {c d : Fin r → 𝓞 E} (h : Cong X 𝔟 (∑ j, c j • D.β j) (∑ j, d j • D.β j)) (j) : c j - d j ∈ 𝔟 := by
  have hs (c : Fin r → 𝓞 E) : ∑ j, c j • D.β j ∈ X.Λ := X.Λ.sum_mem fun j _ => X.Λ.smul_mem _ (D.β_mem j)
  have h1 := mem_of_loc (sub_mem (hs c) (hs d)) le_rfl (cong_iff.1 h)
  obtain ⟨e, he, f, hf, hef⟩ := Ideal.isCoprime_iff_exists.1 hc
  have h2 : Cong X D.𝔪 (∑ j, (e * c j) • D.β j) (∑ j, (e * d j) • D.β j) := by
    rw [cong_iff]
    refine le_loc _ ?_
    simp only [mul_smul, ← Finset.smul_sum, ← smul_sub]
    rw [hm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul he h1
  have h3 : e * c j - e * d j ∈ 𝔟 := (hm.le.trans Ideal.mul_le_right) (coeff_cong D h2 j)
  have : c j - d j = (e * c j - e * d j) + (c j - d j) * f := by linear_combination -(c j - d j) * hef
  rw [this]; exact add_mem h3 (Ideal.mul_mem_left _ _ hf)

theorem exists_cong {𝔞 : Ideal (𝓞 E)} {N : Submodule (𝓞 E) (Fin r → E)} {v : Fin r → E} (hv : v ∈ loc 𝔞 X.Λ)
    (h : v ∈ loc 𝔞 (N ⊔ loc 𝔞 (𝔞 • X.Λ))) : ∃ u ∈ N, Cong X 𝔞 v u := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 h
  obtain ⟨a, m, hm, e'⟩ := cop_iff.1 hs
  refine ⟨a • u, N.smul_mem _ hu, ?_⟩
  have : v - a • u = m • v + a • w := by
    conv_lhs => rw [← one_smul (𝓞 E) v, ← e', add_smul, mul_smul, ← e, smul_add]
    abel
  rw [cong_iff, this]
  refine add_mem ?_ (Submodule.smul_mem _ _ hw)
  obtain ⟨t, ht, hv⟩ := hv
  exact ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hm hv⟩

theorem red_iff (D : SW.Level X) {𝔞 𝔟 : Ideal (𝓞 E)} (hm : D.𝔪 = 𝔞 * 𝔟) (hc : IsCoprime 𝔞 𝔟)
    {L : Lt E r} (hL : L ∈ D.lats) {y z : Fin r → Fin r → E} (hz : ∀ i, z i ∈ L)
    (h1 : ∀ i, Cong X 𝔟 (y i) (z i)) (h2 : ∀ i, Cong X 𝔞 (y i) (D.β i)) :
    (∃ k : GL (Fin r) (𝓞 E ⧸ D.𝔪), (∀ i j, ∃ a ∈ 𝔞,
      (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j =
        Ideal.Quotient.mk D.𝔪 a) ∧ D.Red y k) ↔
    L ≤ loc 𝔟 (Submodule.span (𝓞 E) (Set.range z) ⊔ 𝔟 • L) := by
  obtain ⟨-, s, hs, hLΛ, hΛL⟩ := hL
  have ha : D.𝔪 ≤ 𝔞 := hm.le.trans Ideal.mul_le_left
  have hb : D.𝔪 ≤ 𝔟 := hm.le.trans Ideal.mul_le_right
  have hsb : IsCoprime (Ideal.span {s}) 𝔟 := (hm ▸ hs.of_mul_right_left).of_mul_right_right
  have l1 : loc 𝔟 (𝔟 • X.Λ) ≤ loc 𝔟 (𝔟 • L) := fun v ⟨t, ht, hv⟩ =>
    loc_loc ht ⟨s, hsb, smul_map_mem LinearMap.id hΛL hv⟩
  have l2 : 𝔟 • L ≤ loc 𝔟 (𝔟 • X.Λ) := fun v hv => ⟨s, hsb, smul_map_mem LinearMap.id hLΛ hv⟩
  constructor
  · rintro ⟨k, -, hk⟩ v hv
    obtain ⟨b, hb'⟩ := exists_lift k⁻¹
    have h3 := red_comb hk hb'
    rw [mul_inv_cancel] at h3
    refine loc_loc hsb (SetLike.le_def.1 (D.β_span.trans (sup_le (Submodule.span_le.2 ?_) ?_)) (hLΛ v hv))
    · rintro _ ⟨i, rfl⟩
      have h4 := cong_trans (cong_mono hb (cong_of_red red_one h3 i)) (cong_sum h1 fun j => b j i)
      have := add_mem (loc_mono (le_sup_right (a := Submodule.span (𝓞 E) (Set.range z))) (l1 (cong_iff.1 h4)))
        (le_loc _ (Submodule.mem_sup_left (Submodule.sum_mem _ (t := Finset.univ) fun j _ =>
          Submodule.smul_mem _ (b j i) (Submodule.subset_span ⟨j, rfl⟩))))
      rwa [sub_add_cancel] at this
    · exact (Submodule.smul_mono hb le_rfl).trans ((le_loc _).trans (l1.trans (loc_mono le_sup_right)))
  · intro h
    have hy (i) : y i ∈ loc D.𝔪 X.Λ := by
      have a1 : y i ∈ loc 𝔞 X.Λ := by
        simpa using add_mem (loc_mono Submodule.smul_le_right (cong_iff.1 (h2 i))) (le_loc _ (D.β_mem i))
      have a2 : y i ∈ loc 𝔟 X.Λ := by
        simpa using add_mem (loc_mono Submodule.smul_le_right (cong_iff.1 (h1 i)))
          (show z i ∈ loc 𝔟 X.Λ from ⟨s, hsb, hLΛ _ (hz i)⟩)
      obtain ⟨t, ht, a1⟩ := a1
      obtain ⟨t', ht', a2⟩ := a2
      obtain ⟨p, q, hpq⟩ := cop_glue hc ht ht'
      refine ⟨_, hm ▸ hpq, ?_⟩
      rw [add_smul, mul_smul, mul_smul]
      exact add_mem (X.Λ.smul_mem _ a1) (X.Λ.smul_mem _ a2)
    have hk (i) : ∃ c : Fin r → 𝓞 E, Cong X D.𝔪 (y i) (∑ j, c j • D.β j) := by
      obtain ⟨u, hu, e⟩ := exists_cong (N := Submodule.span (𝓞 E) (Set.range D.β)) (hy i)
        (loc_mono (D.β_span.trans (sup_le_sup_left (le_loc _) _)) (hy i))
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hu
      exact ⟨c, e⟩
    have hb' (i) : ∃ c : Fin r → 𝓞 E, Cong X 𝔟 (D.β i) (∑ j, c j • z j) := by
      obtain ⟨u, hu, e⟩ := exists_cong (N := Submodule.span (𝓞 E) (Set.range z)) (le_loc _ (D.β_mem i))
        (loc_loc hsb (loc_mono (sup_le_sup_left l2 _) (h (hΛL _ (D.β_mem i)))))
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hu
      exact ⟨c, e⟩
    choose k hk using hk
    choose b hb' using hb'
    let K : Matrix (Fin r) (Fin r) (𝓞 E) := Matrix.of fun j i => k i j
    let B : Matrix (Fin r) (Fin r) (𝓞 E) := Matrix.of fun j i => b i j
    have one (i) : D.β i = ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i • D.β j := by simp [Matrix.one_apply]
    have e1 (j i) : K j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i ∈ 𝔞 :=
      coeff_cong_factor D (hm.trans (mul_comm _ _)) hc.symm (c := fun j => K j i) (d := fun j => (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i)
        (one i ▸ cong_trans (cong_symm (cong_mono ha (hk i))) (h2 i)) j
    have e2 (j i) : (K * B) j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i ∈ 𝔟 := by
      refine coeff_cong_factor D hm hc (c := fun j => (K * B) j i) (d := fun j => (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) ?_ j
      rw [← one i]
      have := cong_trans (hb' i) (cong_sum (fun j => cong_trans (cong_symm (h1 j)) (cong_mono hb (hk j))) (b i))
      convert cong_symm this using 1
      simp only [K, B, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm]
      exact Finset.sum_comm
    have dt {I : Ideal (𝓞 E)} {A : Matrix (Fin r) (Fin r) (𝓞 E)}
        (h : ∀ j i, A j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i ∈ I) : A.det - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, RingHom.map_det, map_one]
      have : (Ideal.Quotient.mk I).mapMatrix A = (Ideal.Quotient.mk I).mapMatrix 1 := by
        ext j i; exact Ideal.Quotient.eq.2 (h j i)
      rw [this, map_one, Matrix.det_one]
    have c1 : IsCoprime (Ideal.span {K.det}) 𝔞 := cop_of_sub_one (dt e1)
    have c2 : IsCoprime (Ideal.span {K.det}) 𝔟 := by
      have := cop_of_sub_one (dt e2)
      rw [Matrix.det_mul, ← Ideal.span_singleton_mul_span_singleton] at this
      exact this.of_mul_left_left
    obtain ⟨a, m, hm', e⟩ := cop_iff.1 (hm ▸ c1.mul_right c2 : IsCoprime _ D.𝔪)
    have hu : IsUnit (K.map (Ideal.Quotient.mk D.𝔪)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ a) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk D.𝔪), Ideal.Quotient.eq]
      have : K.det * a - 1 = -m := by linear_combination e
      rw [this]; exact neg_mem hm'
    refine ⟨Matrix.GeneralLinearGroup.mk'' _ hu, fun i j => ⟨_, e1 i j, ?_⟩, K, rfl, hk⟩
    rw [map_sub]
    congr 1
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

variable {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hbar_eq (a : 𝓞 E) : H.bar a = bar a :=
  RingOfIntegers.ext ((H.bar_eq a).trans (coe_bar a).symm)

theorem conjI_mfr (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  ext a
  rw [mem_conjI, ← hbar_eq (H := H), Mfr]
  exact Ideal.apply_mem_of_equiv_iff (f := H.bar)

theorem m_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l :=
  (l.prod.ge.trans Ideal.mul_le_right) (Ideal.mem_span_singleton_self _)

theorem mfr_ne_top (l : Geo.Tor.Level H) : Mfr l ≠ ⊤ := by
  intro h
  have h1 : l.Mb = ⊤ := by
    rw [← conjI_mfr, h, eq_top_iff]; exact fun a _ => mem_conjI.2 trivial
  have h2 := l.prod
  rw [h1, Ideal.map_top, Ideal.mul_top, eq_comm, Ideal.span_singleton_eq_top] at h2
  have h3 := h2.map (Algebra.norm ℤ)
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
    Int.isUnit_iff] at h3
  have := l.three_le
  omega

def congGrp (r : ℕ) {𝔪 𝔞 : Ideal (𝓞 E)} (h : 𝔪 ≤ 𝔞) : Subgroup (GL (Fin r) (𝓞 E ⧸ 𝔪)) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h)).ker

omit [NumberField E] [IsCMField E] in
theorem mem_congGrp {𝔪 𝔞 : Ideal (𝓞 E)} (h : 𝔪 ≤ 𝔞) (k : GL (Fin r) (𝓞 E ⧸ 𝔪)) :
    k ∈ congGrp r h ↔ ∀ i j, ∃ a ∈ 𝔞,
      (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ 𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ 𝔪)) i j =
        Ideal.Quotient.mk 𝔪 a := by
  have key (x : 𝓞 E ⧸ 𝔪) : Ideal.Quotient.factor h x = 0 ↔ ∃ a ∈ 𝔞, x = Ideal.Quotient.mk 𝔪 a := by
    constructor
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact fun e => ⟨a, Ideal.Quotient.eq_zero_iff_mem.1 e, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [← key, map_sub, sub_eq_zero]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

def mkLevel (X : Data E r) (l₂ : Geo.Tor.Level H) {𝔞 : Ideal (𝓞 E)} (h : Mfr l₂ ≤ 𝔞) (β : Fin r → Fin r → E)
    (h1 : ∀ i, β i ∈ X.Λ) (h2 : X.Λ ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ Mfr l₂ • X.Λ) : SW.Level X where
  𝔪 := Mfr l₂
  proper := mfr_ne_top l₂
  ne_bot := fun e => by
    have := m_mem l₂
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at this
    have := l₂.three_le
    omega
  cop := by
    rw [conjI_mfr, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact l₂.coprime
  odd := by
    obtain ⟨k, hk⟩ := l₂.odd
    refine (cop_iff.2 ⟨-(k : 𝓞 E), _, m_mem l₂, ?_⟩).symm
    rw [hk]; push_cast; ring
  β := β
  β_mem := h1
  β_span := h2
  J := congGrp r h
  lam := 1
  w := (H.w0 : E)
  w_int := H.w0.2
  w_tr := by
    have e1 : 2 * (H.w0 : E) = 1 + H.rt := by simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have e2 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
    have e3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
      simpa [cc, map_ofNat] using congrArg cc e1
    have e4 : cc (H.rt : E) ^ 2 = -(H.d : E) := by simpa [cc] using congrArg cc e2
    have e5 : cc (H.rt : E) = -(H.rt : E) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (e4.trans e2.symm) with e | e
      · exfalso
        obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        have a1 : (starRingEnd ℂ) (τ H.rt) = τ H.rt := by
          rw [← IsCMField.complexEmbedding_complexConj]; exact congrArg τ e
        have a2 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ e2
        obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 a1
        rw [hx] at a2
        have a3 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast a2
        have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
        nlinarith [sq_nonneg x]
      · exact e
    linear_combination e1 / 2 + e3 / 2 + e5 / 2

def spanInd (d : DeltaDat Xo c n) (x : Fin n → LaJ Xo c d) : c.F :=
  if Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤ then 1 else 0

omit [IsCMField E] in
theorem image_upper {α : Type} (hn : r ≤ n) (x : Fin n → α) :
    x '' {b | b.val < r} = Set.range fun i => x (Fin.castLE hn i) := by
  ext a
  exact ⟨fun ⟨b, hb, e⟩ => ⟨⟨b, hb⟩, e⟩, fun ⟨i, e⟩ => ⟨_, i.2, e⟩⟩

theorem exists_levTie (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (hI : d.l₂.Mb = l.Mb * d.I)
    (hc : IsCoprime (Mfr l) (Jd d)) (X : Data E (Dw.p + Dw.q)) (hn : Dw.p + Dw.q ≤ n) :
    ∃ D : SW.Level X, LevTie d σ (spanInd d) D hn := by
  have := Dw.fin
  have := Dw.proj
  have hp : Mfr d.l₂ = Mfr l * Jd d := by rw [Mfr, hI, Ideal.map_mul]; rfl
  have hle : Mfr d.l₂ ≤ Mfr l := hp.le.trans Ideal.mul_le_left
  have h0 : Mfr d.l₂ ≠ ⊥ := fun e => by
    have := m_mem d.l₂
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at this
    have := d.l₂.three_le
    omega
  obtain ⟨β, h1, h2⟩ := exists_gens h0 _ X.Λ X.Λ_fg
  refine ⟨mkLevel X d.l₂ hle β h1 h2, rfl, hp, hc, rfl, mem_congGrp hle, fun _ _ => rfl, ?_⟩
  intro L hL δ hδ hon
  refine ⟨1, norm_one, fun xs y hup hlow => ?_⟩
  have key := red_iff (mkLevel X d.l₂ hle β h1 h2) hp hc hL (fun i => hδ _) (fun i => (hup i).1)
    (fun i => (hup i).2)
  set S := Submodule.span (𝓞 E) (Set.range fun i => xs (Fin.castLE hn i)) with hS
  have e1 : Submodule.span (𝓞 E) (Set.range fun i => δ (xs (Fin.castLE hn i))) = S.map δ := by
    rw [hS, Submodule.map_span, ← Set.range_comp]; rfl
  have e2 : Submodule.span (𝓞 E) ((fun b => (Submodule.Quotient.mk (xs b) : LaJ Xo c d)) ''
      {b | b.val < Dw.p + Dw.q}) = ⊤ ↔ S ⊔ Jd d • ⊤ = ⊤ := by
    rw [image_upper hn, sup_comm, ← Submodule.map_mkQ_eq_top, hS, Submodule.map_span, ← Set.range_comp]
    rfl
  have e3 : S ⊔ Jd d • ⊤ = ⊤ ↔ L ≤ loc (Jd d) (S.map δ ⊔ Jd d • L) := by
    refine ⟨fun h => le_trans ?_ (le_loc _), span_of_map Dw.rank hL.1.1 (span_lats hL) hδ hon⟩
    refine hon.trans (sup_le ?_ le_sup_right)
    rw [LinearMap.range_eq_map, ← h, Submodule.map_sup, Submodule.map_smul'']
    exact sup_le_sup_left (Submodule.smul_mono le_rfl (by rintro _ ⟨a, -, rfl⟩; exact hδ a)) _
  rw [e1, ← e3, ← e2] at key
  rw [one_mul, spanInd, datF]
  split_ifs with a b b
  · rw [map_one]; rfl
  · obtain ⟨k, hk, hk'⟩ := key.2 a
    exact (b ⟨⟨⟨k, (mem_congGrp hle k).2 hk⟩, hk'⟩, hlow⟩).elim
  · obtain ⟨k, hk⟩ := b.1
    exact (a (key.1 ⟨k.1, (mem_congGrp hle k.1).1 k.2, hk⟩)).elim
  · simp

theorem exists_x0Tie (d : DeltaDat Xo c n) (hpd : Nat.Coprime d.pd l.M) {X : Data E (Dw.p + Dw.q)}
    (D : SW.Level X) (hm : D.𝔪 ≤ Mfr l) (hn : Dw.p + Dw.q ≤ n) {L : Lt E (Dw.p + Dw.q)} (hL : L ∈ D.lats)
    {δ : Dw.La →ₗ[𝓞 E] (Fin (Dw.p + Dw.q) → E)} (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ Mfr l • L)
    (rk : Bool) : ∃ x0, IsBaseClassLevelAdapted d D hn x0 δ ∧ AdmX (l := l) rk x0 := by
  have := Dw.fin
  have := Dw.proj
  obtain ⟨s, hs, hLΛ, hΛL⟩ := hL.2
  have mono {t : 𝓞 E} (ht : IsCoprime (Ideal.span {t}) D.𝔪) : IsCoprime (Ideal.span {t}) (Mfr l) := by
    obtain ⟨a, m, hm', e⟩ := cop_iff.1 ht
    exact cop_iff.2 ⟨a, m, hm hm', e⟩
  have hsb := mono hs.of_mul_right_left
  have hp : IsCoprime (Ideal.span {(d.pd : 𝓞 E)}) (Mfr l) := by
    obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hpd).map (Int.castRingHom (𝓞 E))
    exact cop_iff.2 ⟨a, _, Ideal.mul_mem_left _ b (m_mem l), by simpa using e⟩
  have l1 : loc (Mfr l) (Mfr l • X.Λ) ≤ loc (Mfr l) (Mfr l • L) := fun v ⟨t, ht, hv⟩ =>
    loc_loc ht ⟨s, hsb, smul_map_mem LinearMap.id hΛL hv⟩
  have l2 : Mfr l • L ≤ loc (Mfr l) (Mfr l • X.Λ) := fun v hv => ⟨s, hsb, smul_map_mem LinearMap.id hLΛ hv⟩
  have hx (i) : ∃ a : Dw.La, Cong X (Mfr l) (d.pd • δ a) (D.β i) := by
    obtain ⟨u, hu, e⟩ := exists_cong (N := LinearMap.range ((d.pd : 𝓞 E) • δ)) (le_loc _ (D.β_mem i))
      (loc_loc (cop_mul hp hsb) (le_loc _ (by
        obtain ⟨_, ⟨a, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (hon (hΛL _ (D.β_mem i)))
        rw [mul_smul, ← e, smul_add]
        exact Submodule.add_mem_sup ⟨a, rfl⟩ (Submodule.smul_mem _ _ (l2 hw)))))
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Nat.cast_smul_eq_nsmul] using cong_symm e⟩
  choose a ha using hx
  refine ⟨fun k => if h : (k : ℕ) < Dw.p + Dw.q then a ⟨k, h⟩ else 0, ⟨fun i => by simpa using ha i,
    fun k hk => by simp [not_lt.2 hk]⟩, ?_⟩
  refine span_of_map Dw.rank hL.1.1 (span_lats hL) hδ hon fun v hv => ?_
  refine loc_loc hsb (SetLike.le_def.1 (D.β_span.trans (sup_le (Submodule.span_le.2 ?_) ?_)) (hLΛ v hv))
  · rintro _ ⟨i, rfl⟩
    rw [← sub_add_cancel (D.β i) (d.pd • δ (a i))]
    refine add_mem (loc_mono le_sup_right (l1 (cong_iff.1 (cong_symm (ha i)))))
      (le_loc _ (Submodule.mem_sup_left (nsmul_mem (Submodule.mem_map_of_mem (Submodule.subset_span ?_)) _)))
    exact ⟨Fin.castLE hn i, Or.inr i.2, by simp⟩
  · exact (Submodule.smul_mono hm le_rfl).trans ((le_loc _).trans (l1.trans (loc_mono le_sup_right)))

theorem LevTie.norm_eq_one {d : DeltaDat Xo c n} {σ : c.F →+* ℂ} {ph : (Fin n → LaJ Xo c d) → c.F}
    {D : SW.Level X} {hn : r ≤ n} (T : LevTie d σ ph D hn) {L : Lt E r} (hL : L ∈ D.lats)
    {δ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ Jd d • L)
    (xs : Fin n → Dw.La) (hx : ∀ i, Cong X (Jd d) (D.β i) (δ (xs (Fin.castLE hn i)))) :
    ‖σ (ph fun b => Submodule.Quotient.mk (xs b))‖ = 1 := by
  obtain ⟨t, ht, h⟩ := T.tie L hL δ hδ hon
  let y : Matrix (Fin n) (Fin r) E := Matrix.of fun k => if h : (k : ℕ) < r then D.β ⟨k, h⟩ else 0
  have e (i : Fin r) : y (Fin.castLE hn i) = D.β i := by
    change (if h : _ then _ else _) = _
    simp
  have e0 (k : Fin n) (hk : r ≤ (k : ℕ)) : Cong X (Mfr l) (y k) 0 := by
    have : y k = 0 := dif_neg (not_lt.2 hk)
    rw [this]; exact cong_refl _
  rw [h xs y (fun i => by rw [e]; exact ⟨hx i, cong_refl _⟩) e0, datF,
    dif_pos ⟨⟨1, by simp only [e]; exact red_one⟩, e0⟩, norm_mul, ht, norm_lam, one_mul]

theorem spanInd_laws (d : DeltaDat Xo c n) :
    (∀ x x' : Fin n → LaJ Xo c d, (∀ b : Fin n, b.val < Dw.p + Dw.q → x b = x' b) → spanInd d x = spanInd d x') ∧
    (∀ x, spanInd d x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤) ∧
    ∀ (k : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) x, spanInd d (fun b => k (x b)) = spanInd d x := by
  refine ⟨fun x x' h => ?_, fun x h => ?_, fun k x => ?_⟩
  · rw [spanInd, spanInd, Set.image_congr (s := {b : Fin n | b.val < Dw.p + Dw.q}) (g := x') h]
  · by_contra e; exact h (if_neg e)
  · have : Submodule.span (𝓞 E) ((fun b => k (x b)) '' {b | b.val < Dw.p + Dw.q}) =
        (Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q})).map (k : LaJ Xo c d →ₗ[𝓞 E] LaJ Xo c d) := by
      rw [Submodule.map_span, Set.image_image]; rfl
    simp only [spanInd, this, Submodule.map_eq_top_iff]

end

end GlobalTheory.Dict.TieModel
