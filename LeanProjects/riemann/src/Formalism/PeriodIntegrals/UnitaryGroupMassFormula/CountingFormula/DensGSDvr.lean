import Mathlib

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Classical ValuativeRel

section Dvr

variable (F : Type) [Field F] [ValuativeRel F]

def resF (x : F) : 𝓀[F] := if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

def liftF (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])

theorem resF_coe (o : 𝒪[F]) : resF F (o : F) = IsLocalRing.residue 𝒪[F] o := by
  rw [resF, dif_pos o.2]

theorem liftF_mem (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] :=
  (IsLocalRing.residue_surjective c).choose.2

theorem resF_liftF (c : 𝓀[F]) : resF F (liftF F c) = c := by
  rw [liftF, resF_coe]
  exact (IsLocalRing.residue_surjective c).choose_spec

theorem resF_one : resF F 1 = 1 := by
  simpa using resF_coe F 1

theorem resF_mul {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : resF F (x * y) = resF F x * resF F y := by
  have h := resF_coe F (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [map_mul, ← resF_coe F ⟨x, hx⟩, ← resF_coe F ⟨y, hy⟩] at h
  exact h

theorem resF_sum_mul {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by
  have hs : ((∑ i, (⟨c i, hc i⟩ : 𝒪[F]) * ⟨x i, hx i⟩ : 𝒪[F]) : F) = ∑ i, c i * x i := by
    simp
  rw [← hs, resF_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← resF_coe F ⟨c i, hc i⟩, ← resF_coe F ⟨x i, hx i⟩]

theorem resF_eq_zero_of_lt {x : F} (hx : valuation F x < 1) : resF F x = 0 := by
  have hx1 : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hx.le
  rw [show x = ((⟨x, hx1⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact hx.ne

theorem dvd_of_resF_eq_zero [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F}
    (hx : x ∈ 𝒪[F]) (h0 : resF F x = 0) : ∃ o : 𝒪[F], x = (ϖ : F) * o := by
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  refine ⟨a, ?_⟩
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, ← ha]
  push_cast
  ring

theorem resF_irr {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resF F (ϖ : F) = 0 := by
  rw [resF_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit

def SatF {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) : Prop :=
  ∀ u : Fin n → F, (∀ k, u k ∈ 𝒪[F]) → (∃ c : ι → F, ∑ i, c i • X i = u) →
    ∃ c : ι → F, (∀ i, c i ∈ 𝒪[F]) ∧ ∑ i, c i • X i = u

def redM {ι : Type} {n : ℕ} (X : ι → Fin n → F) : ι → Fin n → 𝓀[F] := fun i k => resF F (X i k)

variable {F}

theorem key_norm {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) (c : ι → F) (u : Fin n → F) (hu : ∑ i, c i • X i = u)
    (j : ι) (hj : ∀ i, valuation F (c i) ≤ valuation F (c j)) (hcj : c j ≠ 0)
    (hlt : ∀ k, valuation F (u k) < valuation F (c j)) : False := by
  have hvj : 0 < valuation F (c j) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
  have hd : ∀ i, c i / c j ∈ 𝒪[F] := fun i =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_div₀]; exact (div_le_one₀ hvj).2 (hj i))
  have hz : ∑ i, resF F (c i / c j) • redM F X i = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, redM, Pi.zero_apply]
    have h := resF_sum_mul F (fun i => c i / c j) (fun i => X i k) hd (fun i => hX i k)
    rw [← h]
    apply resF_eq_zero_of_lt F
    have hs : ∑ i, c i / c j * X i k = u k / c j := by
      rw [← hu, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, map_div₀]
    exact (div_lt_one₀ hvj).2 (hlt k)
  have h1 := (Fintype.linearIndependent_iff.1 hred) _ hz j
  rw [div_self hcj, resF_one] at h1
  exact one_ne_zero h1

theorem indep_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : LinearIndependent F X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hcj : g j ≠ 0 := by
    intro h
    have h2 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h2
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h2 zero_le'))
  refine key_norm X hX hred g 0 hg j (fun i => hj i (Finset.mem_univ _)) hcj (fun k => ?_)
  rw [Pi.zero_apply, map_zero]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)

theorem sat_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : SatF F X := by
  intro u hu hex
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun i => ?_, hc⟩
  by_contra hci
  rw [Valuation.mem_integer_iff, not_le] at hci
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (c i))
    ⟨i, Finset.mem_univ _⟩
  have hj1 : 1 < valuation F (c j) := lt_of_lt_of_le hci (hj i (Finset.mem_univ _))
  have hcj : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj1
    exact not_lt.2 zero_le' hj1
  exact key_norm X hX hred c u hc j (fun i => hj i (Finset.mem_univ _)) hcj
    (fun k => lt_of_le_of_lt ((Valuation.mem_integer_iff _ _).1 (hu k)) hj1)

theorem red_of_indep_sat [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hind : LinearIndependent F X) (hsat : SatF F X) : LinearIndependent 𝓀[F] (redM F X) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨d, hdm, hres⟩ : ∃ d : ι → F, (∀ i, d i ∈ 𝒪[F]) ∧ ∀ i, resF F (d i) = a i :=
    ⟨fun i => liftF F (a i), fun i => liftF_mem F _, fun i => resF_liftF F _⟩
  have hcomp : ∀ k, (∑ i, d i • X i) k = ∑ i, d i * X i k := fun k => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ k, (∑ i, d i • X i) k ∈ 𝒪[F] := fun k => by
    rw [hcomp]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hdm i) (hX i k)
  have hr0 : ∀ k, resF F ((∑ i, d i • X i) k) = 0 := fun k => by
    have h := resF_sum_mul F d (fun i => X i k) hdm (fun i => hX i k)
    rw [hcomp, h]
    simp only [hres]
    have h2 := congrFun ha k
    simpa [Finset.sum_apply, redM] using h2
  choose w hw using fun k => dvd_of_resF_eq_zero F hϖ (hmem k) (hr0 k)
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  obtain ⟨c', hc'm, hc'⟩ := hsat (fun k => (w k : F)) (fun k => (w k).2)
    ⟨fun i => d i / ϖ, by
      funext k
      have e := hw k
      rw [hcomp] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, e]
      field_simp⟩
  have hzero : ∑ i, (d i - ϖ * c' i) • X i = 0 := by
    funext k
    have e1 := congrFun hc' k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
    have e2 := hw k
    rw [hcomp] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, e1, e2, sub_self]
  have hdi := (Fintype.linearIndependent_iff.1 hind) _ hzero i
  rw [← hres i, sub_eq_zero.1 hdi, resF_mul F ϖ.2 (hc'm i), resF_irr F hϖ, zero_mul]

theorem dvr_prim_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) :=
  ⟨fun h => red_of_indep_sat hϖ X hX h.1 h.2, fun h => ⟨indep_of_red X hX h, sat_of_red X hX h⟩⟩

end Dvr

end PI.UnitaryGroupMassFormula.CntFormula
