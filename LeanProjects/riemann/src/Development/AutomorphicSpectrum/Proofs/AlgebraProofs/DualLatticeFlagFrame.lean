import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagDual

section Linear

variable {O Ω : Type*} [CommRing O] [Field Ω] [Algebra O Ω]
variable {V V₁ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁] {N : ℕ}

theorem form_eq_sum {W : Type*} [AddCommGroup W] [Module Ω W] (w : Module.Basis (Fin N) Ω W)
    (φ : W →ₗ[Ω] Ω) (v : W) : φ v = ∑ j, w.repr v j * φ (w j) := by
  conv_lhs => rw [← w.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem exists_coeffs (R : Subalgebra O Ω) (L : AddSubgroup V)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (e : Fin N → V) (heL : ∀ i, e i ∈ L) (hez : ∀ i j, i < j → w.repr (e i) j = 0)
    (hed : ∀ i, w.repr (e i) i = m i) (k : ℕ) :
    ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → w.repr v j = 0) →
      ∃ c : Fin N → Ω, (∀ i, c i ∈ R) ∧ v = ∑ i, c i • e i := by
  induction k with
  | zero =>
    intro v _ hv
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    have : v = 0 := by
      apply w.repr.injective
      ext j
      simpa using hv j (Nat.zero_le _)
    simp [this]
  | succ k ih =>
    intro v hvL hv
    by_cases hk : k < N
    · set i : Fin N := ⟨k, hk⟩ with hi
      obtain ⟨a, haR, ha⟩ := (hg i (w.repr v i)).1
        ⟨v, hvL, fun j hj => hv j (by
          have : i.val < j.val := hj
          simpa [hi] using this), rfl⟩
      have hv' : v - a • e i ∈ L := sub_mem hvL (hst a haR _ (heL i))
      obtain ⟨c, hcR, hc⟩ := ih _ hv' (fun j hj => by
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · have hij : i < j := by
            show i.val < j.val
            simpa [hi] using hlt
          have h1 : w.repr v j = 0 := hv j hlt
          simp [h1, hez i j hij]
        · have hij : j = i := Fin.ext (by simp [hi, heq])
          subst hij
          simp [hed, ha])
      refine ⟨fun l => c l + (if l = i then a else 0), fun l => ?_, ?_⟩
      · refine add_mem (hcR l) ?_
        split_ifs
        · exact haR
        · exact zero_mem _
      · have : v = (v - a • e i) + a • e i := by abel
        rw [this, hc]
        simp [add_smul, Finset.sum_add_distrib, ite_smul]
    · exact ih v hvL (fun j _ => hv j (by have := j.isLt; omega))

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (e : Fin N → V) (hez : ∀ i j, i < j → w.repr (e i) j = 0) (hed : ∀ i, w.repr (e i) i = m i) :
    ∃ e' : Module.Basis (Fin N) Ω V, ∀ i, e' i = e i := by
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, isUnit_iff_ne_zero,
      Matrix.det_of_upperTriangular (M := w.toMatrix e)]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simpa [Module.Basis.toMatrix_apply, hed] using hm i
    · intro i j hij
      simpa [Module.Basis.toMatrix_apply] using hez j i hij
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det w).2 hdet
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simp⟩

theorem coord_w (w e' : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (hez : ∀ i j, i < j → w.repr (e' i) j = 0) (hed : ∀ i, w.repr (e' i) i = m i) (r : Fin N) :
    (∀ l, l < r → e'.repr (w l) r = 0) ∧ e'.repr (w r) r = (m r)⁻¹ := by
  have hexp : ∀ l, (∀ j, j < l → e'.repr (w j) r = 0) →
      e'.repr (e' l) r = m l * e'.repr (w l) r := by
    intro l hl
    have h0 : e'.repr (e' l) r = ∑ j, w.repr (e' l) j * e'.repr (w j) r :=
      form_eq_sum w (e'.coord r) (e' l)
    rw [h0, Finset.sum_eq_single l]
    · rw [hed]
    · intro j _ hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · simp [hl j h]
      · simp [hez l j h]
    · simp
  have hlow : ∀ n : ℕ, ∀ l : Fin N, l.val = n → l < r → e'.repr (w l) r = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hln hlr
      have h1 := hexp l (fun j hj => ih j.val (by rw [← hln]; exact hj) j rfl (hj.trans hlr))
      have h2 : e'.repr (e' l) r = 0 := by
        simp [Module.Basis.repr_self, Finsupp.single_apply, hlr.ne]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (hm l)
  have hlow' : ∀ l, l < r → e'.repr (w l) r = 0 := fun l hl => hlow _ l rfl hl
  refine ⟨hlow', ?_⟩
  have h1 := hexp r hlow'
  have h2 : e'.repr (e' r) r = 1 := by simp
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem dual_graded (R : Subalgebra O Ω) (L : AddSubgroup V) (L₁ : AddSubgroup V₁)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hm : ∀ i, m i ≠ 0)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Surjective β.flip)
    (hL₁ : ∀ u, u ∈ L₁ ↔ ∀ v ∈ L, β v u ∈ R) (w₁ : Module.Basis (Fin N) Ω V₁)
    (hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (j : Fin N) (s : Ω) :
    (∃ u ∈ L₁, (∀ l, j < l → w₁.repr u l = 0) ∧ w₁.repr u j = s) ↔
      ∃ a ∈ R, s = a * (m j.rev)⁻¹ := by
  have hcoord : ∀ u l, w₁.repr u l = β (w l.rev) u := by
    intro u l
    rw [form_eq_sum w₁ (β (w l.rev)) u]
    simp [hw, Fin.rev_inj]
  have hex : ∀ i, ∃ v, v ∈ L ∧ (∀ l, i < l → w.repr v l = 0) ∧ w.repr v i = m i := by
    intro i
    obtain ⟨v, hv, h1, h2⟩ := (hg i (m i)).2 ⟨1, one_mem _, by simp⟩
    exact ⟨v, hv, h1, h2⟩
  choose e heL hez hed using hex
  obtain ⟨e', he'⟩ := exists_basis w m hm e hez hed
  have hez' : ∀ i l, i < l → w.repr (e' i) l = 0 := fun i l h => by rw [he']; exact hez i l h
  have hed' : ∀ i, w.repr (e' i) i = m i := fun i => by rw [he']; exact hed i
  set r := j.rev with hr
  obtain ⟨hlow, htop⟩ := coord_w w e' m hm hez' hed' r
  constructor
  · rintro ⟨u, hu, hz, rfl⟩
    refine ⟨m r * w₁.repr u j, ?_, ?_⟩
    · have hmem := (hL₁ u).1 hu _ (heL r)
      have hsum : β (e r) u = m r * w₁.repr u j := by
        have h0 : β (e r) u = ∑ l, w.repr (e r) l * β (w l) u :=
          form_eq_sum w (β.flip u) (e r)
        rw [h0, Finset.sum_eq_single r]
        · rw [hed, hcoord u j]
        · intro l _ hlr
          rcases lt_or_gt_of_ne hlr with h | h
          · have hl : j < l.rev := by
              rw [hr] at h
              have := Fin.rev_lt_rev.2 h
              simpa using this
            have h2 := hcoord u l.rev
            rw [Fin.rev_rev] at h2
            rw [← h2, hz _ hl, mul_zero]
          · simp [hez r l h]
        · simp
      rwa [hsum] at hmem
    · field_simp [hm r]
  · rintro ⟨a, haR, rfl⟩
    obtain ⟨u, hu⟩ := hβ (a • e'.coord r)
    have hβu : ∀ v, β v u = a * e'.repr v r := fun v => by
      have := LinearMap.congr_fun hu v
      simpa using this
    refine ⟨u, (hL₁ u).2 fun v hv => ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨c, hcR, hc⟩ := exists_coeffs R L hst w m hg e heL hez hed N v hv
        (fun l hl => by have := l.isLt; omega)
      have hcoef : e'.repr v r = c r := by
        have : v = ∑ i, c i • e' i := by simpa [he'] using hc
        rw [this]
        simp [map_sum, Finsupp.finset_sum_apply, Finsupp.single_apply]
      rw [hβu, hcoef]
      exact mul_mem haR (hcR r)
    · rw [hcoord, hβu, hlow _ (by simpa [hr] using Fin.rev_lt_rev.2 hl), mul_zero]
    · rw [hcoord, hβu, ← hr, htop]

end Linear

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hdual w b hE w₁ hw
  refine ⟨fun c hc i => ?_⟩
  have hc' : mseg x c ≠ 0 := hc
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hm : ∀ l, (∏ k, x ⟨k, c k⟩ ^ b l k) ≠ 0 := fun l =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  ext s
  have key := dual_graded (chartRing O (mseg x) c) (E.lat c) (F.lat c)
    (fun a ha v hv => E.stable c a ha v hv) w (fun l => ∏ k, x ⟨k, c k⟩ ^ b l k) hm
    (fun l s => by
      have := Set.ext_iff.1 (hE.graded c hc l) s
      exact this)
    β hdual.1.2 (hdual.2 c hc') w₁ hw i s
  have hinv : (∏ k, x ⟨k, c k⟩ ^ b i.rev k)⁻¹ = ∏ k, x ⟨k, c k⟩ ^ (-b i.rev) k := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by simp [zpow_neg]
  rw [hinv] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num.FlagDual
