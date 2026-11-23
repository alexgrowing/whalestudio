import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicGeneratorsSeparableMinStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open Polynomial in

theorem GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n e N : ℕ) (t T : Matrix (Fin n) (Fin n) k) (h : Polynomial k), 0 < e → h.Monic → h.Separable → t * T = T * t → t ^ e = 0 → (∀ x, t *ᵥ x = 0 → ∃ y, x = t ^ (e - 1) *ᵥ y) → (∀ x, ∃ y, Polynomial.aeval T h *ᵥ x = t *ᵥ y) → T.charpoly = h ^ (e * N) → ∃ x : Fin N → Fin n → k, ∀ U : Submodule k (Fin n → k), (∀ i, x i ∈ U) → (∀ z ∈ U, t *ᵥ z ∈ U) → (∀ z ∈ U, T *ᵥ z ∈ U) → U = ⊤ := by
  intro k _ _ n e N t T h he hmon hsep htT hte hker himg hchar
  obtain ⟨t', ht'⟩ : ∃ t' : Module.End k (Fin n → k), t' = Matrix.toLin' t := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Module.End k (Fin n → k), T' = Matrix.toLin' T := ⟨_, rfl⟩
  have htz : ∀ z, t' z = t *ᵥ z := fun z => by rw [ht', Matrix.toLin'_apply]
  have hTz : ∀ z, T' z = T *ᵥ z := fun z => by rw [hT', Matrix.toLin'_apply]
  have hcz : ∀ z, t' (T' z) = T' (t' z) := fun z => by
    simp only [htz, hTz, Matrix.mulVec_mulVec, htT]
  have hcomm : Commute t' T' := LinearMap.ext fun z => hcz z
  have hpow : ∀ (m : ℕ) z, (t' ^ m) z = t ^ m *ᵥ z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, htz, Matrix.mulVec_mulVec]
  have hte' : t' ^ e = 0 := LinearMap.ext fun z => by rw [hpow, hte]; simp
  have hker' : ∀ x, t' x = 0 → x ∈ LinearMap.range (t' ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, hy⟩ := hker x (by rw [← htz]; exact hx)
    exact ⟨y, by rw [hpow, hy]⟩
  have hTW : LinearMap.range t' ≤ (LinearMap.range t').comap T' := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T' y, hcz y⟩
  have hc := GlobalTheory.T.charpoly_eq_quotient_charpoly_pow k (Fin n → k) t' T' hcomm e he hte' hker' hTW
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Module.End k ((Fin n → k) ⧸ LinearMap.range t'),
      Tb = (LinearMap.range t').mapQ (LinearMap.range t') T' hTW := ⟨_, rfl⟩
  rw [← hTb] at hc
  have hcT : LinearMap.charpoly T' = T.charpoly := by rw [hT', Matrix.charpoly_toLin']
  have hroot : (LinearMap.charpoly Tb) ^ e = (h ^ N) ^ e := by
    rw [← hc, hcT, hchar, mul_comm, pow_mul]
  have hchb : LinearMap.charpoly Tb = h ^ N :=
    Polynomial.eq_of_monic_of_associated (LinearMap.charpoly_monic Tb) (hmon.pow N)
      (associated_of_dvd_dvd
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.dvd)
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.symm.dvd))
  have hb1 : ∀ x, Tb ((LinearMap.range t').mkQ x) = (LinearMap.range t').mkQ (T' x) := by
    intro x
    rw [hTb]
    rfl
  have hbm : ∀ (m : ℕ) x, (Tb ^ m) ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ ((T' ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hb1, ih]
  have hmk : ∀ (p : k[X]) x, aeval Tb p ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ (aeval T' p x) := by
    intro p x
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial m c =>
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, hbm, map_smul]
  have hA : ∀ x, aeval T' h x = aeval T h *ᵥ x := by
    intro x
    have h1 : T' = Matrix.toLinAlgEquiv' T := hT'
    rw [h1, Polynomial.aeval_algHom_apply]
    exact Matrix.toLin'_apply _ _
  have hTbh : aeval Tb h = 0 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (LinearMap.range t').mkQ_surjective v
    rw [hmk, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hA]
    obtain ⟨y, hy⟩ := himg x
    exact ⟨y, by rw [htz, hy]⟩
  obtain ⟨xb, hgen⟩ := GlobalTheory.T.exists_cyclic_generators_separable_min k _ Tb h hmon hsep hTbh N hchb
  choose xs hxs using fun j => (LinearMap.range t').mkQ_surjective (xb j)
  refine ⟨xs, fun U hU htU hTU => ?_⟩
  have hstab : ∀ f : Module.End k (Fin n → k), (∀ z ∈ U, f z ∈ U) →
      ∀ (m : ℕ), ∀ z ∈ U, (f ^ m) z ∈ U := by
    intro f hf m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hf z hz)
  have htm := hstab t' fun z hz => by rw [htz]; exact htU z hz
  have hTm := hstab T' fun z hz => by rw [hTz]; exact hTU z hz
  have hUa : ∀ (p : k[X]), ∀ z ∈ U, aeval T' p z ∈ U := by
    intro p z hz
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, LinearMap.add_apply]
      exact U.add_mem hp hq
    | monomial m c =>
      rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      exact U.smul_mem c (hTm m z hz)
  have step : ∀ v, ∃ u ∈ U, ∃ w, v = u + t' w := by
    intro v
    obtain ⟨p, hp⟩ := hgen ((LinearMap.range t').mkQ v)
    refine ⟨∑ j, aeval T' (p j) (xs j), U.sum_mem fun j _ => hUa _ _ (hU j), ?_⟩
    have h0 : (LinearMap.range t').mkQ (v - ∑ j, aeval T' (p j) (xs j)) = 0 := by
      rw [map_sub, map_sum, hp, sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [← hmk, hxs]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by rw [hw]; abel⟩
  have iter : ∀ (m : ℕ) v, ∃ u ∈ U, ∃ w, v = u + (t' ^ m) w := by
    intro m
    induction m with
    | zero => intro v; exact ⟨0, U.zero_mem, v, by simp⟩
    | succ m ih =>
      intro v
      obtain ⟨u, hu, w, rfl⟩ := ih v
      obtain ⟨u', hu', w', rfl⟩ := step w
      refine ⟨u + (t' ^ m) u', U.add_mem hu (htm m u' hu'), w', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨u, hu, w, rfl⟩ := iter e v
  rw [hte']
  simpa using hu
