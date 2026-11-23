import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlgebraMapMemO
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SameTrace

open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

theorem hf_zero_r (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

theorem exists_mul_mem [IsNonarchimedeanLocalField F] (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t * c ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have h1 : IsAlgebraic F c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic 𝒪[F] c := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨t, ht, h⟩ := h2.exists_integral_multiple
  refine ⟨t, ht, (L.O_def _).2 ?_⟩
  convert h using 1
  rw [Algebra.smul_def]; rfl

theorem exists_smul_mem [IsNonarchimedeanLocalField F] {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsLat L Λ) (x : Fin n → E) : ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.CommonDenominator.main
  | exact _root_.GlobalTheory.CommonDenominator.main
  | (apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominator.main ..)

noncomputable def shear {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := v + ∑ j, hf L Hm v (b j) • d j
  map_add' v w := by simp only [hf_add_l, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [hf_smul_l, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul]
  invFun v := v - ∑ j, hf L Hm v (b j) • d j
  left_inv v := by simp [hf_add_l, hf_sum_l, hf_smul_l, hdb]
  right_inv v := by simp [hf_sub_l, hf_sum_l, hf_smul_l, hdb]

theorem shear_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : shear L Hm b d hdb v = v + ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_symm_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : (shear L Hm b d hdb).symm v = v - ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_mem_isomG {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by
  intro v w
  have hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j) := by
    intro k
    rw [← hf_cj L h, hv, map_sum]
    simp only [map_mul, hf_cj L h]
  simp only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [hw]
  simp only [hv v, Finset.mul_sum]
  have key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k))
      + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k
  linear_combination key

end

theorem exists_isometry_of_same_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ La Lb, IsSD L Hm La → IsSD L Hm Lb → ∀ (m : ℕ) (e : Fin m → Fin n → E), LinearIndependent E e → (∀ i j, hf L Hm (e i) (e j) = 0) → (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), x ∈ La ↔ x ∈ Lb) → ∃ g ∈ isomG L Hm, (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), g x = x) ∧ g • La = Lb := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH La Lb hLa hLb m e he hee hab
  obtain ⟨-, hA, -, b, c, hb, hc, hbc⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH La hLa m e he
  obtain ⟨-, hB, -, -⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH Lb hLb m e he
  set X := Submodule.span E (Set.range e) with hX
  have hcj := hf_cj L hH.1

  have hXp : ∀ x ∈ X, x ∈ perp L Hm X := by
    have h1 : ∀ i, e i ∈ perp L Hm X := by
      intro i y hy
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      simp [hf_sum_r, hf_smul_r, hee]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 h1)
  have hbm : ∀ j, b j ∈ La ∧ b j ∈ X := fun j => by
    have : b j ∈ La ⊓ X.restrictScalars L.O := by
      rw [hb]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hbLb : ∀ j, b j ∈ Lb := fun j => (hab _ (hXp _ (hbm j).2)).1 (hbm j).1
  have hcb : ∀ i j, hf L Hm (c i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [← hcj, hbc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hperp : ∀ v, (∀ j, hf L Hm v (b j) = 0) → v ∈ perp L Hm X := by
    intro v hv x hx
    obtain ⟨t, ht, htx⟩ := exists_smul_mem L hLa.1 x
    have h1 : algebraMap F E t • x ∈ Submodule.span L.O (Set.range b) := by
      rw [← hb]; exact ⟨htx, X.smul_mem _ hx⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : hf L Hm v (algebraMap F E t • x) = 0 := by
      rw [← ha]
      simp [hf_sum_r, Subring.smul_def, hf_smul_r, hv]
    rw [hf_smul_r, AlgEquiv.commutes] at h2
    have ht' : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
    exact ((IsUnit.mk0 _ ht').map (algebraMap F E)).mul_right_eq_zero.1 h2
  have hint : ∀ {Λ}, IsSD L Hm Λ → ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O :=
    fun hΛ x hx y hy => (hΛ.2 y).2 hy x hx

  have hc' : ∀ j, ∃ a ∈ Lb, c j - a ∈ X := fun j =>
    (hB (c j)).1 fun x hx hxp => hint hLa x ((hab x hxp).2 hx) _ (hc j)
  choose c' hc'b hc'X using hc'
  obtain ⟨ω, hω, ε, hε, hωε⟩ := exists_sub_cj_mul_eq_one L
  have hε' : (L.cj ω - ω) * L.cj ε = 1 := by simpa [L.cj_cj] using congrArg L.cj hωε
  have hcε : L.cj ε = -ε := by linear_combination (-ε) * hε' - (L.cj ε) * hωε
  obtain ⟨τ, hτO, hτ⟩ : ∃ τ ∈ L.O, τ + L.cj τ = 1 :=
    ⟨ω * ε, L.O.mul_mem hω hε, by rw [map_mul, hcε]; linear_combination hωε⟩
  let d₀ : Fin m → Fin n → E := fun j => c' j - c j
  have hd₀ : ∀ j, d₀ j ∈ X := fun j => by
    have := X.neg_mem (hc'X j)
    rwa [neg_sub] at this
  let H : Fin m → Fin m → E := fun j k => hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)
  have hHO : ∀ j k, H j k ∈ L.O := fun j k => by
    have h0 : hf L Hm (d₀ j) (d₀ k) = 0 := hXp _ (hd₀ j) _ (hd₀ k)
    have h1 : H j k = hf L Hm (c' j) (c' k) - hf L Hm (c j) (c k) := by
      simp only [H, d₀, hf_sub_l, hf_sub_r] at h0 ⊢
      linear_combination -h0
    rw [h1]
    exact L.O.sub_mem (hint hLb _ (hc'b j) _ (hc'b k)) (hint hLa _ (hc j) _ (hc k))
  have hHc : ∀ j k, L.cj (H k j) = H j k := fun j k => by
    simp only [H, map_add, hcj]; ring
  let d : Fin m → Fin n → E := fun j => d₀ j - ∑ l, (τ * H j l) • b l
  have hd : ∀ j, d j ∈ X := fun j =>
    X.sub_mem (hd₀ j) (X.sum_mem fun l _ => X.smul_mem _ (hbm l).2)
  have hcdb : ∀ j, c j + d j ∈ Lb := fun j => by
    have h1 : c j + d j = c' j - ∑ l, (τ * H j l) • b l := by
      simp only [d, d₀]; abel
    rw [h1]
    exact Lb.sub_mem (hc'b j) (Lb.sum_mem fun l _ =>
      Lb.smul_mem ⟨_, L.O.mul_mem hτO (hHO j l)⟩ (hbLb l))
  have hdb : ∀ i j, hf L Hm (d i) (b j) = 0 := fun i j => hXp _ (hd i) _ (hbm j).2
  have hdd : ∀ i j, hf L Hm (d i) (d j) = 0 := fun i j => hXp _ (hd i) _ (hd j)
  have hv0 : ∀ v, v - ∑ j, hf L Hm v (b j) • c j ∈ perp L Hm X := fun v =>
    hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hcb]
  have hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k) := fun v k => by
    have h1 := hv0 v _ (hd k)
    simp only [hf_sub_l, hf_sum_l, hf_smul_l] at h1
    exact sub_eq_zero.1 h1
  have hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0 := fun j k => by
    have h1 : hf L Hm (c j) (d k) = hf L Hm (c j) (d₀ k) - L.cj τ * H j k := by
      simp [d, hf_sub_r, hf_sum_r, hf_smul_r, hcb, hHc]
    have h2 : hf L Hm (d j) (c k) = hf L Hm (d₀ j) (c k) - τ * H j k := by
      simp [d, hf_sub_l, hf_sum_l, hf_smul_l, hbc]
    have h3 : H j k = hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k) := rfl
    rw [h1, h2]
    linear_combination -h3 - H j k * hτ
  refine ⟨shear L Hm b d hdb, shear_mem_isomG L hH.1 b c d hdb hdd hv hcd, fun x hx => ?_, ?_⟩
  · have h1 : ∀ j, hf L Hm x (b j) = 0 := fun j => hx _ (hbm j).2
    simp [shear_apply, h1]
  · apply le_antisymm
    · rintro _ ⟨v, hva, rfl⟩
      show shear L Hm b d hdb v ∈ Lb
      have hβ : ∀ j, hf L Hm v (b j) ∈ L.O := fun j => hint hLa _ hva _ (hbm j).1
      have h1 : shear L Hm b d hdb v = (v - ∑ j, hf L Hm v (b j) • c j)
          + ∑ j, hf L Hm v (b j) • (c j + d j) := by
        simp only [shear_apply, smul_add, Finset.sum_add_distrib]; abel
      rw [h1]
      refine Lb.add_mem ((hab _ (hv0 v)).1 (La.sub_mem hva (La.sum_mem fun j _ =>
        La.smul_mem ⟨_, hβ j⟩ (hc j)))) (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j))
    · intro w hw
      refine ⟨(shear L Hm b d hdb).symm w, ?_, (shear L Hm b d hdb).apply_symm_apply w⟩
      have hβ : ∀ j, hf L Hm w (b j) ∈ L.O := fun j => hint hLb _ hw _ (hbLb j)
      have h1 : (shear L Hm b d hdb).symm w = (w - ∑ j, hf L Hm w (b j) • (c j + d j))
          + ∑ j, hf L Hm w (b j) • c j := by
        simp only [shear_symm_apply, smul_add, Finset.sum_add_distrib]; abel
      have h2 : w - ∑ j, hf L Hm w (b j) • (c j + d j) ∈ perp L Hm X :=
        hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hf_add_l, hcb, hdb]
      show (shear L Hm b d hdb).symm w ∈ La
      rw [h1]
      refine La.add_mem ((hab _ h2).2 (Lb.sub_mem hw (Lb.sum_mem fun j _ =>
        Lb.smul_mem ⟨_, hβ j⟩ (hcdb j)))) (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j))

end GlobalTheory.HL.SameTrace
