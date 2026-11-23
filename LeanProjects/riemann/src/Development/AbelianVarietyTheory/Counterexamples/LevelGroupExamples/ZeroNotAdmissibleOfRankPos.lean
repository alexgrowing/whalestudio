import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelPairing

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  have h2 := H.bar_eq a
  change ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [h1, h2, IsCMField.complexConj_apply_apply]

theorem cSep_spec (l : Level H) : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cSep
  rw [dif_pos h]
  exact h.choose_spec

theorem dvd_EF_of_mem (x y : Dw.La) {a : 𝓞 E} (ha : a ∈ Ideal.span {(l.M : 𝓞 E)}) :
    (l.M : ℤ) ∣ Dw.EF x (a • y) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : (b * (l.M : 𝓞 E)) • y = (l.M : ℤ) • (b • y) := by
    rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this, map_zsmul]
  exact Dvd.intro _ rfl

theorem mul_mem_M {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ Mfr l) : a * b ∈ Ideal.span {(l.M : 𝓞 E)} :=
  l.prod ▸ Ideal.mul_mem_mul ha hb

theorem bar_mem_Mb {a : 𝓞 E} (ha : a ∈ Mfr l) : H.bar a ∈ l.Mb := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := bar_bar H b
  rwa [this]

theorem dvd_right (x : Dw.La) {y : Dw.La} (hy : y ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)
  · rw [← mul_smul, mul_comm]; exact dvd_EF_of_mem _ _ (mul_mem_M ha (cSep_spec l).1)
  · rw [smul_add, map_add]; exact dvd_add hu hv

theorem dvd_left {x : Dw.La} (y : Dw.La) (hx : x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
  · rw [Dw.adj, ← mul_smul]; exact dvd_EF_of_mem _ _ (mul_mem_M (bar_mem_Mb ha) (cSep_spec l).1)
  · rw [map_add, LinearMap.add_apply]; exact dvd_add hu hv

theorem pairL_congr {n : ℕ} (x0 x0' x x' : Fin n → Dw.La)
    (h0 : ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h1 : ∀ b, x b - x' b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ pairL (l := l) x0 x - pairL (l := l) x0' x' := by
  unfold pairL
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun b _ => ?_
  have : Dw.EF (x0 b) (cSep l • x b) - Dw.EF (x0' b) (cSep l • x' b) =
      Dw.EF (x0 b - x0' b) (cSep l • x b) + Dw.EF (x0' b) (cSep l • (x b - x' b)) := by
    simp [smul_sub]
  rw [this]
  exact dvd_add (dvd_left _ (h0 b)) (dvd_right _ (h1 b))

theorem zetaM_coe (c : Coeff l) : ((zetaM c : c.F) : ℂ) = zeta l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hA : l.A ≠ 0 := l.A_pos.ne'
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM hA
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hM'
  have hdiv : l.M' / l.M = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)
  unfold zetaM
  rw [hdiv]
  change (zeta l.M') ^ k = _
  unfold zeta
  rw [← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have : (l.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp

theorem zetaM_prim (c : Coeff l) : IsPrimitiveRoot (zetaM c) l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  refine IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) ?_ Subtype.val_injective
  have := zetaM_coe c
  change IsPrimitiveRoot ((zetaM c : c.F) : ℂ) l.M
  rw [this]
  exact Complex.isPrimitiveRoot_exp l.M hM

theorem levRep_mk (x : Dw.La) :
    levRep (Submodule.Quotient.mk x : LevQ Dw l) - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
  (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk x : LevQ Dw l)))

theorem zpow_congr (c : Coeff l) {a b : ℤ} (h : (l.M : ℤ) ∣ a - b) : zetaM c ^ a = zetaM c ^ b := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
  have := ((zetaM_prim c).zpow_eq_one_iff_dvd (a - b)).2 h
  rw [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  exact this

theorem levelFourierDatum_mk (c : Coeff l) {n : ℕ} (x0 x : Fin n → Dw.La) :
    x0Dat c x0 (fun b => (Submodule.Quotient.mk (x b) : LevQ Dw l)) = zetaM c ^ pairL (l := l) x0 x :=
  zpow_congr c (pairL_congr _ _ _ _ (fun b => by simp) (fun b => levRep_mk (x b)))

theorem exists_eq_smul_of_dvd (x : Dw.La) (m : ℕ) (hm : m ≠ 0) (h : ∀ y, (m : ℤ) ∣ Dw.EF x y) :
    ∃ z, x = (m : ℤ) • z := by
  let f : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF x y / m
      map_add' := fun a b => by rw [map_add, Int.add_ediv_of_dvd_left (h a)]
      map_smul' := fun k a => by
        rw [map_zsmul]; simp only [smul_eq_mul, RingHom.id_apply]; exact Int.mul_ediv_assoc _ (h a) }
  obtain ⟨z, hz⟩ := Dw.unimod.2 f
  refine ⟨z, Dw.unimod.1 ?_⟩
  ext y
  rw [map_zsmul, hz]
  simp only [LinearMap.smul_apply, smul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Int.mul_ediv_cancel' (h y)).symm

theorem mem_of_dvd {x : Dw.La} (h : ∀ y, (l.M : ℤ) ∣ Dw.EF x (cSep l • y)) :
    x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨z, hz⟩ := exists_eq_smul_of_dvd (H.bar (cSep l) • x) l.M hM (fun y => by
    rw [Dw.adj, bar_bar]; exact h y)
  have h1 : H.bar (cSep l - 1) ∈ Mfr l := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (cSep_spec l).2
  have hMm : (l.M : 𝓞 E) ∈ Mfr l := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  have : x = (l.M : 𝓞 E) • z - H.bar (cSep l - 1) • x := by
    rw [map_sub, map_one, sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this]
  exact sub_mem (Submodule.smul_mem_smul hMm trivial) (Submodule.smul_mem_smul h1 trivial)

theorem levelFourierDatum_eq_iff (c : Coeff l) {n : ℕ} (x0 x0' : Fin n → Dw.La) :
    x0Dat c x0 = x0Dat c x0' ↔ ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  constructor
  · intro h b
    refine mem_of_dvd fun y => ?_
    have h1 := congrFun h (fun i => (Submodule.Quotient.mk ((Pi.single b y : Fin n → Dw.La) i) : LevQ Dw l))
    rw [levelFourierDatum_mk, levelFourierDatum_mk] at h1
    have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
    have h2 : (l.M : ℤ) ∣ pairL (l := l) x0 (Pi.single b y) - pairL (l := l) x0' (Pi.single b y) := by
      rw [← (zetaM_prim c).zpow_eq_one_iff_dvd, zpow_sub₀ h0, h1, div_self (zpow_ne_zero _ h0)]
    have h3 : ∀ u : Fin n → Dw.La, pairL (l := l) u (Pi.single b y) = Dw.EF (u b) (cSep l • y) := by
      intro u
      unfold pairL
      rw [Finset.sum_eq_single b]
      · simp
      · intro i _ hi; simp [Pi.single_eq_of_ne hi]
      · simp
    rw [h3, h3] at h2
    simpa using h2
  · intro h
    funext q
    exact zpow_congr c (pairL_congr _ _ _ _ h (fun b => by simp))

theorem finite_LevQ : Finite (LevQ Dw l) := by
  haveI := Dw.fin
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hb : l.Mb ≠ ⊥ := by
    intro h
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    have := this (Ideal.subset_span rfl)
    rw [h, Ideal.mem_bot] at this
    exact hM (by exact_mod_cast this)
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  haveI : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem Mfr_ne_top (l : Level H) : Mfr l ≠ ⊤ := by
  intro h
  have h1 : (1 : 𝓞 E) ∈ l.Mb := by simpa using bar_mem_Mb (l := l) (a := 1) (h ▸ Submodule.mem_top)
  have h2 := mul_mem_M h1 (show (1 : 𝓞 E) ∈ Mfr l from h ▸ Submodule.mem_top)
  rw [one_mul, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h2
  have h3 : IsUnit (l.M : ℤ) := by
    have : IsUnit (algebraMap ℤ (𝓞 E) (l.M : ℤ)) := by simpa using h2
    exact (isUnit_map_iff (algebraMap ℤ (𝓞 E)) _).1 this
  have := l.three_le
  rcases Int.isUnit_iff.1 h3 with h | h <;> omega

end GlobalTheory.LevelPairing
