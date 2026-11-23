import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeanSquareEvenThetaTwelfthRootInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasRationalTorsionIffMemRange
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI

noncomputable section

namespace GlobalTheory.Mem.PeriodTie

section Lattice

open PeriodPair GlobalTheory.ConjPoint

theorem exists_action (L : PeriodPair) (σ : ℂ ≃+* ℂ) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3) (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) :
    ∃ η : ℂ, σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ ∧ ∀ t, ∃ t', ∀ c : ℂ, σ c = c →
      (∀ l ∈ L.lattice, c * l ∈ L.lattice) → (c * t ∈ L.lattice ↔ c * t' ∈ L.lattice) ∧
        (c * t ∉ L.lattice → σ (℘[L] (c * t)) = η * ℘[L] (c * t')) := by
  rw [map_pow] at h2 h3
  obtain ⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ σ L.g₂ = u * L.g₂ := by
    by_cases h0 : L.g₂ = 0
    · exact ⟨1, one_pow _, by simp [h0]⟩
    · exact ⟨σ L.g₂ / L.g₂, by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩
  obtain ⟨η, hη, e2, e3⟩ : ∃ η : ℂ, η ≠ 0 ∧ σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e
    · exact ⟨u ^ 2, pow_ne_zero _ hu0, by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination -(u ^ 3 + 1) * L.g₃ * hu⟩
    · exact ⟨-u ^ 2, neg_ne_zero.2 (pow_ne_zero _ hu0), by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination (u ^ 3 + 1) * L.g₃ * hu⟩
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq η⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hη (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = η := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  generalize scalePeriods L m hm0 = L' at H
  have f2 : L'.g₂ = σ L.g₂ := by rw [H.g₂_eq, e2, ← hmu]; ring
  have f3 : L'.g₃ = σ L.g₃ := by rw [H.g₃_eq, e3, ← hmu]; ring
  refine ⟨η, e2, e3, fun t => ?_⟩
  obtain ⟨s, -, hc⟩ := exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L t))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  refine ⟨t', fun c hσ hc' => ?_⟩
  have := IsConj.mul f2 f3 hc' ((hc _ _).2 hw.symm)
  rw [hσ, mul_left_comm] at this
  rcases this with ⟨a, b⟩ | ⟨a, b, e, -⟩
  · exact ⟨iff_of_true a ((H _).1 b), fun h => absurd a h⟩
  · exact ⟨iff_of_false a fun h => b ((H _).2 h), fun _ => by rw [← e, H.weierstrassP_mul, hmu]⟩

theorem cubic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : t + t ∈ L.lattice) :
    4 * ℘[L] t ^ 3 - L.g₂ * ℘[L] t - L.g₃ = 0 := by
  rw [← L.derivWeierstrassP_sq t ht, (derivWeierstrassP_eq_zero_iff L ht).2 h]; simp

theorem quartic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : 3 * t ∈ L.lattice) :
    3 * ℘[L] t ^ 4 - 3 / 2 * L.g₂ * ℘[L] t ^ 2 - 3 * L.g₃ * ℘[L] t - L.g₂ ^ 2 / 16 = 0 := by
  have h0 : 3 • latticePoint L t = 0 := by
    rw [← latticePointHom_apply, ← map_nsmul, latticePointHom_apply, latticePoint_eq_zero_iff]
    simpa using h
  rw [latticePoint_of_notMem L ht, three_nsmul_eq_zero_iff] at h0
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, latticeCurve, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] at h0
  linear_combination h0

theorem cubic_discr {G T x y : ℂ} (hx : 4 * x ^ 3 - G * x - T = 0) (hy : 4 * y ^ 3 - G * y - T = 0) (hxy : x ≠ y) :
    (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) ^ 2 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : G = 4 * (x ^ 2 + x * y + y ^ 2) :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination hy - hx)
  have h2 : T = 4 * x ^ 3 - G * x := by linear_combination -hx
  rw [h2, h1]; ring

theorem quartic_discr {G T x y : ℂ} (hx : 3 * x ^ 4 - 3 / 2 * G * x ^ 2 - 3 * T * x - G ^ 2 / 16 = 0)
    (hy : 3 * y ^ 4 - 3 / 2 * G * y ^ 2 - 3 * T * y - G ^ 2 / 16 = 0) (hxy : x ≠ y) :
    (G - 3 * (x + y) ^ 2) ^ 3 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : T = (x + y) * (x ^ 2 + y ^ 2) - G * (x + y) / 2 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination (hy - hx) / 3)
  have h2 : -3 * (x * y) * ((x + y) ^ 2 - x * y) + 3 / 2 * G * (x * y) - G ^ 2 / 16 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination x * hy - y * hx)
  rw [h1]
  linear_combination 36 * (x + y) ^ 2 * h2

theorem quartic_sum {A B C x y z w : ℂ} (hx : 3 * x ^ 4 - A * x ^ 2 - B * x - C = 0)
    (hy : 3 * y ^ 4 - A * y ^ 2 - B * y - C = 0) (hz : 3 * z ^ 4 - A * z ^ 2 - B * z - C = 0)
    (hw : 3 * w ^ 4 - A * w ^ 2 - B * w - C = 0) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : z + w = -(x + y) := by
  have k : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u →
      3 * (x ^ 3 + x ^ 2 * u + x * u ^ 2 + u ^ 3) - A * (x + u) - B = 0 := fun u hu h =>
    mul_left_cancel₀ (sub_ne_zero.2 h) (by linear_combination hx - hu)
  have k' : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u → y ≠ u →
      3 * (x ^ 2 + x * (y + u) + (y ^ 2 + y * u + u ^ 2)) - A = 0 := fun u hu h h' =>
    mul_left_cancel₀ (sub_ne_zero.2 h') (by linear_combination k y hy hxy - k u hu h)
  exact mul_left_cancel₀ (sub_ne_zero.2 hzw) (by linear_combination (k' z hz hxz hyz - k' w hw hxw hyw) / 3)

theorem exists_order_three (L : PeriodPair) {β : ℂ} {d : ℕ} (hd : 0 < d) (hβ : β ^ 2 = -d)
    (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ t, 3 * t ∈ L.lattice ∧ (β - 1) * t ∉ L.lattice ∧ (β + 1) * t ∉ L.lattice := by
  have uniq : ∀ a b : ℤ, (a : ℂ) * L.ω₁ + b * L.ω₂ = 0 → a = 0 ∧ b = 0 := fun a b h => by
    have := LinearIndependent.pair_iff.1 L.indep (a : ℝ) (b : ℝ) (by simpa using h)
    exact_mod_cast this
  obtain ⟨a, b, h1⟩ := mem_lattice.1 (hL _ L.ω₁_mem_lattice)
  obtain ⟨c, e, h2⟩ := mem_lattice.1 (hL _ L.ω₂_mem_lattice)
  obtain ⟨q1, q2⟩ := uniq (a ^ 2 + b * c + d) (b * (a + e)) (by
    push_cast
    linear_combination (a + β) * h1 + b * h2 + L.ω₁ * hβ)
  have hb : b ≠ 0 := by rintro rfl; nlinarith [sq_nonneg a]
  obtain rfl : e = -a := by have := (mul_eq_zero.1 q2).resolve_left hb; omega
  have key : ∀ x y ε : ℤ, (β - ε) * ((x * L.ω₁ + y * L.ω₂) / 3) ∈ L.lattice →
      (x * a + y * c - ε * x) % 3 = 0 ∧ (x * b - y * a - ε * y) % 3 = 0 := fun x y ε h => by
    obtain ⟨m, n, h⟩ := mem_lattice.1 h
    obtain ⟨r1, r2⟩ := uniq (x * a + y * c - ε * x - 3 * m) (x * b - y * a - ε * y - 3 * n) (by
      push_cast at h2 ⊢
      linear_combination x * h1 + y * h2 - 3 * h)
    omega
  by_contra hcon
  have k : ∀ x y : ℤ, ((x * a + y * c - 1 * x) % 3 = 0 ∧ (x * b - y * a - 1 * y) % 3 = 0) ∨
      ((x * a + y * c - (-1) * x) % 3 = 0 ∧ (x * b - y * a - (-1) * y) % 3 = 0) := fun x y => by
    by_contra h
    rw [not_or] at h
    refine hcon ⟨(x * L.ω₁ + y * L.ω₂) / 3, mem_lattice.2 ⟨x, y, by ring⟩, fun h' => h.1 (key x y 1 ?_),
      fun h' => h.2 (key x y (-1) ?_)⟩
    · simpa using h'
    · simpa using h'
  have k1 := k 1 0
  have k2 := k 0 1
  have k3 := k 1 1
  omega

theorem map_g₃ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {w : ℂ} {k : ℤ} (hw : w * (1 - w) = 2 * k)
    (hs : ∀ l ∈ L.lattice, w * l ∈ L.lattice) {t : ℂ} (t2 : 2 * t ∈ L.lattice) (ta : w * t ∉ L.lattice)
    (tb : (1 - w) * t ∉ L.lattice) (σ : ℂ ≃+* ℂ) (hσ : σ w = w) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3)
    (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) : σ L.g₃ = L.g₃ := by
  obtain ⟨η, -, e3, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have hs' : ∀ l ∈ L.lattice, (1 - w) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hs l hl)
  obtain ⟨a1, a2⟩ := h w hσ hs
  obtain ⟨b1, b2⟩ := h (1 - w) (by rw [map_sub, map_one, hσ]) hs'
  obtain ⟨c1, -⟩ := h 2 (map_ofNat σ 2) fun l hl => by rw [two_mul]; exact add_mem hl hl
  have hlat : GlobalTheory.ThetaConj.IsLat L.lattice.toAddSubgroup := by
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [AddSubgroup.mem_closure_pair, Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice]
    simp only [zsmul_eq_mul]
  have hu : t - t' ∈ L.lattice := GlobalTheory.ThetaConj.two_torsion_unique hlat w k hw t2 ta tb (c1.1 t2)
    (mt a1.2 ta) (mt b1.2 tb) hs
  have ea : ℘[L] (w * t) = ℘[L] (w * t') :=
    (weierstrassP_eq_iff L ta (mt a1.2 ta)).2 (.inl (by rw [← mul_sub]; exact hs _ hu))
  have eb : ℘[L] ((1 - w) * t) = ℘[L] ((1 - w) * t') :=
    (weierstrassP_eq_iff L tb (mt b1.2 tb)).2 (.inl (by rw [← mul_sub]; exact hs' _ hu))
  have fa := a2 ta
  have fb := b2 tb
  rw [← ea] at fa
  rw [← eb] at fb
  have ha2 : w * t + w * t ∈ L.lattice := by convert hs _ t2 using 1; ring
  have hb2 : (1 - w) * t + (1 - w) * t ∈ L.lattice := by convert hs' _ t2 using 1; ring
  have hne : ℘[L] (w * t) ≠ ℘[L] ((1 - w) * t) := fun e => by
    have ht : t ∈ L.lattice := by
      rcases (weierstrassP_eq_iff L ta tb).1 e with e | e
      · convert add_mem e hb2 using 1; ring
      · convert e using 1; ring
    exact ta (hs _ ht)
  have hd := cubic_discr (cubic_eq_zero L ta ha2) (cubic_eq_zero L tb hb2) hne
  rw [hΔ] at hd
  generalize ℘[L] (w * t) = x at *
  generalize ℘[L] ((1 - w) * t) = y at *
  have hP : σ (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) = η ^ 3 * (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) := by
    simp only [map_mul, map_add, map_sub, map_ofNat, fa, fb]; ring
  have : η ^ 3 = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hd.trans (one_pow 2).symm) with e | e <;> rw [e] at hP
    · simpa using hP.symm
    · simpa using hP.symm
  rw [e3, this, one_mul]

theorem exists_map_g₂ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {β : ℂ} {d : ℕ} (hd : d % 3 ≠ 0)
    (hβ : β ^ 2 = -d) (hs : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ u : ℂ, u ^ 3 = 1 ∧ ∀ σ : ℂ ≃+* ℂ, σ β = β → σ (L.g₂ ^ 3) = L.g₂ ^ 3 → σ (L.g₃ ^ 2) = L.g₃ ^ 2 →
      σ (u * L.g₂) = u * L.g₂ := by
  have hββ : ∀ t, 3 * t ∈ L.lattice → β * (β * t) - t ∈ L.lattice ∨ β * (β * t) + t ∈ L.lattice := fun t ht => by
    obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, d + 1 = 3 * n ∨ d = 3 * n + 1 := by
      rcases (show d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h
      · exact ⟨d / 3, .inr (by omega)⟩
      · exact ⟨d / 3 + 1, .inl (by omega)⟩
    · have hn' : (d : ℂ) + 1 = 3 * n := by exact_mod_cast hn
      left
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
    · have hn' : (d : ℂ) = 3 * n + 1 := by exact_mod_cast hn
      right
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
  have h3β : ∀ t, 3 * t ∈ L.lattice → 3 * (β * t) ∈ L.lattice := fun t ht => by
    rw [mul_left_comm]; exact hs _ ht
  have hnβ : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → β * t ∉ L.lattice := fun t ht hn h => hn <| by
    rcases hββ t ht with e | e
    · simpa using sub_mem (hs _ h) e
    · simpa using sub_mem e (hs _ h)
  have hA : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] (β * (β * t)) = ℘[L] t := fun t ht hn =>
    (weierstrassP_eq_iff L (hnβ _ (h3β t ht) (hnβ t ht hn)) hn).2 (hββ t ht)
  have hB : ∀ s t, 3 * s ∈ L.lattice → s ∉ L.lattice → 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] s = ℘[L] t →
      ℘[L] (β * s) = ℘[L] (β * t) := fun s t s3 sn t3 tn e => by
    rw [weierstrassP_eq_iff L (hnβ s s3 sn) (hnβ t t3 tn), ← mul_sub, ← mul_add]
    exact ((weierstrassP_eq_iff L sn tn).1 e).imp (hs _) (hs _)
  have hs1 : ∀ l ∈ L.lattice, (β - 1) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem (hs l hl) hl
  have hs2 : ∀ l ∈ L.lattice, (β + 1) * l ∈ L.lattice := fun l hl => by
    rw [add_mul, one_mul]; exact add_mem (hs l hl) hl
  have hne : ∀ t, 3 * t ∈ L.lattice → (β - 1) * t ∉ L.lattice → (β + 1) * t ∉ L.lattice →
      ℘[L] t ≠ ℘[L] (β * t) := fun t ht a b e => by
    have tn : t ∉ L.lattice := fun h => a (hs1 _ h)
    rcases (weierstrassP_eq_iff L (hnβ t ht tn) tn).1 e.symm with e | e
    · exact a (by convert e using 1; ring)
    · exact b (by convert e using 1; ring)
  obtain ⟨t, t3, ta, tb⟩ := exists_order_three L (Nat.pos_of_ne_zero (by rintro rfl; simp at hd)) hβ hs
  have tn : t ∉ L.lattice := fun h => ta (hs1 _ h)
  have hx := quartic_eq_zero L tn t3
  have hy := quartic_eq_zero L (hnβ t t3 tn) (h3β t t3)
  have hv := quartic_discr hx hy (hne t t3 ta tb)
  rw [hΔ] at hv
  refine ⟨(L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2)⁻¹, by rw [inv_pow, hv, inv_one], fun σ hσ h2 h3 => ?_⟩
  obtain ⟨η, e2, -, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have t3' := (h 3 (map_ofNat σ 3) fun l hl => by simpa using nsmul_mem hl 3).1.1 t3
  have ta' := mt (h (β - 1) (by rw [map_sub, map_one, hσ]) hs1).1.2 ta
  have tb' := mt (h (β + 1) (by rw [map_add, map_one, hσ]) hs2).1.2 tb
  have tn' : t' ∉ L.lattice := fun h => ta' (hs1 _ h)
  have fx := (h 1 (map_one σ) fun l hl => by simpa using hl).2 (by simpa using tn)
  rw [one_mul, one_mul] at fx
  have fy := (h β hσ hs).2 (hnβ t t3 tn)
  have hsq : (℘[L] t' + ℘[L] (β * t')) ^ 2 = (℘[L] t + ℘[L] (β * t)) ^ 2 := by
    by_cases c1 : ℘[L] t = ℘[L] t'
    · rw [hB _ _ t3 tn t3' tn' c1, c1]
    by_cases c2 : ℘[L] t = ℘[L] (β * t')
    · rw [hB _ _ t3 tn (h3β _ t3') (hnβ _ t3' tn') c2, hA _ t3' tn', c2, add_comm]
    have c3 : ℘[L] (β * t) ≠ ℘[L] t' := fun e => c2 (by
      rw [← hB _ _ (h3β _ t3) (hnβ _ t3 tn) t3' tn' e, hA _ t3 tn])
    have c4 : ℘[L] (β * t) ≠ ℘[L] (β * t') := fun e => c1 (by
      rw [← hA _ t3 tn, hB _ _ (h3β _ t3) (hnβ _ t3 tn) (h3β _ t3') (hnβ _ t3' tn') e, hA _ t3' tn'])
    rw [quartic_sum hx hy (quartic_eq_zero L tn' t3') (quartic_eq_zero L (hnβ _ t3' tn') (h3β _ t3'))
      (hne t t3 ta tb) c1 c2 c3 c4 (hne t' t3' ta' tb'), neg_sq]
  have hσv : σ (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) = η ^ 2 * (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) := by
    rw [map_sub, map_mul, map_pow, map_add, map_ofNat, fx, fy, e2, ← hsq]; ring
  generalize L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2 = v at hv hσv
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hη : η ^ 2 ≠ 0 := left_ne_zero_of_mul (hσv ▸ (map_ne_zero σ).2 hv0)
  rw [map_mul, map_inv₀, hσv, e2, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hη, one_mul]

end Lattice

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods

theorem exists_delta_data (D : D7) (hF : FieldOK D.host D.what₂.embLL D.embE) :
    ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ g2 (lamOf D D.host.ccK δ) ∈ coefM D ∧ g3 (lamOf D D.host.ccK δ) ∈ coefM D := by
  obtain ⟨δ, h⟩ := exists_discriminantTwelfthRoot_of_ideal D
  have hc : Crv D D.host.ccK δ := ⟨isCurveIdeal_ccK D, h⟩
  obtain ⟨-, m2, m3⟩ := data_of_fieldOK (M := coefM D) hF h fun x => ⟨x, rfl⟩
  obtain ⟨hlat, -, hΔ, -, hO⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 _ δ hc
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaConj.IsLat.exists_periodPair hlat
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  rw [TaylorLogMetric.discr, e2, e3] at hΔ
  rw [e2] at m2
  rw [e3] at m3
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have mw : w0 D ∈ coefM D := ⟨D.embE _, by rw [← ha, ← D.embE_φ₀]; rfl⟩
  have hs : ∀ l ∈ L.lattice, w0 D * l ∈ L.lattice := fun l hl => (hL _).1 (ha ▸ hO a l ((hL l).2 hl))
  have key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ coefM D, σ y = y) → σ x = x) → x ∈ coefM D := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := coefM D) x
      fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩
    exact y.2
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  obtain ⟨t, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ δ hc).1
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff, hL, hL, hL] at ht
  have n3 : L.g₃ ∈ coefM D := key _ fun σ hσ =>
    map_g₃ L hΔ hk hs ht.1 ht.2.1 ht.2.2 σ (hσ _ mw) (hσ _ m2) (hσ _ m3)
  have hd : D.host.d % 3 ≠ 0 := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three D.host.hyp.2.1).1 (Nat.dvd_of_mod_eq_zero h3)
    have := D.host.hyp.2.2.2.1
    omega
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  obtain ⟨u, hu, hσu⟩ := exists_map_g₂ L hΔ (β := 2 * w0 D - 1) hd
    (by unfold w0; linear_combination ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hsq)
    fun l hl => by
      convert sub_mem (add_mem (hs l hl) (hs l hl)) hl using 1; ring
  have n2 : u * L.g₂ ∈ coefM D := key _ fun σ hσ =>
    hσu σ (by rw [map_sub, map_mul, map_ofNat, map_one, hσ _ mw]) (hσ _ m2) (hσ _ m3)
  have hu0 : u ^ 2 ≠ 0 := by
    refine pow_ne_zero _ ?_
    rintro rfl; simp at hu
  have hmap : lamOf D D.host.ccK (u ^ 2 * δ) = (lamOf D D.host.ccK δ).map (AddMonoidHom.mulLeft (u ^ 2)) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [mul_assoc]
  refine ⟨u ^ 2 * δ, ?_, ?_, ?_⟩
  · unfold IsDiscriminantTwelfthRootOfIdealLattice at h ⊢
    rw [mul_pow, h, show (u ^ 2) ^ 12 = (u ^ 3) ^ 8 by ring, hu, one_pow, one_mul]
  · rw [← e2] at n2
    convert n2 using 1
    unfold g2
    rw [hmap, Model.eisG_map _ _ hu0, inv_eq_of_mul_eq_one_right (b := u)
      (by rw [show (u ^ 2) ^ (2 * 2) * u = (u ^ 3) ^ 3 by ring, hu, one_pow])]
    ring
  · rw [← e3] at n3
    convert n3 using 1
    unfold g3
    rw [hmap, Model.eisG_map _ _ hu0, show (u ^ 2) ^ (2 * 3) = (u ^ 3) ^ 4 by ring, hu]
    simp

theorem isTheta0_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} (h : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) : GL3Theta.IsTheta0 D.host.d (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HalfPeriodTheta.theta_signed_translation D (GlobalTheory.InducedType.induced_type D).1 cc δ h t ht
  refine ⟨h1, fun x hx z => ?_, div_self fun h0 => ?_⟩
  · obtain ⟨m, hm, e⟩ := h2 x hx
    have : Real.sqrt D.host.d / 2 * (GL3Theta.hf1 (lamOf D cc δ) x x).re = m := by
      rw [← hm, q1, GL3Theta.hf1, Complex.mul_conj, Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [GL3Theta.al1, this, round_intCast, e]
  · apply GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t h ht
    unfold GL3Theta.th0
    rw [h0]
    simp [nrm1Sq]

theorem isTheta0_conj {d : ℕ} {Λ : AddSubgroup ℂ} {G : ℂ → ℂ} (h : GL3Theta.IsTheta0 d Λ G) :
    GL3Theta.IsTheta0 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) := by
  refine ⟨fun z => differentiableAt_conj_conj_iff.mpr (h.1 _), ?_, by simp [h.2.2]⟩
  rintro _ ⟨x, hx, rfl⟩ z
  have e : (starRingEnd ℂ).toAddMonoidHom x = starRingEnd ℂ x := rfl
  have e' : GL3Theta.al1 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ x) =
      starRingEnd ℂ (GL3Theta.al1 d Λ x) := by
    unfold GL3Theta.al1 GL3Theta.hf1
    rw [GlobalTheory.ThetaConj.area_conj, Complex.conj_conj, mul_comm ((starRingEnd ℂ) x) x, map_zpow₀, map_neg, map_one]
  rw [e, e', GlobalTheory.ThetaConj.thetaTranslate_conjugateLattice]
  simp only [Function.comp]
  rw [← map_mul, h.2.1 x hx]

theorem isTheta0_lamConj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} {M : IntermediateField ℚ ℂ} (h : Crv D cc δ)
    (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ⊢; exact isTheta0_lamOf h' ht
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    rw [e] at h1
    have h2 := isTheta0_conj (isTheta0_lamOf h' h1)
    rw [← GlobalTheory.ThetaConj.evenTheta_conjugateLattice (GlobalTheory.ThetaConj.isLat_lamOf h'), ← e, GlobalTheory.ThetaConj.conj_conj_lat,
      Complex.conj_conj] at h2
    exact h2

open Formalism.L2.GlobalTheoryTheory in

theorem ties_of_data {D : D7} {δ : ℂ} (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (h2 : g2 (lamOf D D.host.ccK δ) ∈ coefM D) (h3 : g3 (lamOf D D.host.ccK δ) ∈ coefM D) :
    OmegaCompatible (retie D) δ ∧ DataIn D (tor0 D D.host.ccK δ) (coefM D) ∧ ∀ s : D.what₂.LL →+* ℂ,
      ∃ G, IsTheta0 D.host.d (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G ∧
        (retie D).gx.thOne s ^ 2 = normSq1 (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G := by
  obtain ⟨hc, hM, -, hth⟩ := perTie_retie hF h h2 h3
  refine ⟨⟨coefM D, inferInstance, (imEquiv D.what₂.embLL).toRingEquiv, fun _ => rfl, hM, fun τ => ?_⟩, hM,
    fun s => ?_⟩
  · have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
    refine ⟨_, (span_gen hF hL τ).symm, fun s : D.what₂.LL →+* ℂ => ?_⟩
    have hs : ∀ x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x) := fun x =>
      (rhoOf_imEquiv D.what₂.embLL s x).symm
    obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM _ s hs
    have h1 : (retie D).gx.Om τ s = _ := Model.om_eq D.host hF D.eTau τ s
    rw [e, area_map_unit _ (norm_eq_one_of_pow hζ), hs] at h1
    rw [h1, inv_div]
    rfl
  · obtain ⟨t, ht⟩ := exists_isThetaZero hc hM (rhoOf D.what₂.embLL s)
    exact ⟨_, (is_theta_zero_iff _ _ _).1 (isTheta0_lamConj hc hM _ ht), hth s t ht⟩

end GlobalTheory.Mem.PeriodTie
