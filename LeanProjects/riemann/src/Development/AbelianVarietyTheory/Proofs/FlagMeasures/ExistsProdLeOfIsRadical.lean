import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.SqfCrt

theorem mem_mul_smul_of_coprime {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    {A B : Ideal S} (h : IsCoprime A B) {y : M} (hA : y ∈ A • N) (hB : y ∈ B • N) : y ∈ (A * B) • N := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have hsplit : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hB
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hb hA

theorem mem_prod_smul_of_coprime {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by
  induction T using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top, Submodule.top_smul] using hy
  | @insert a T haT ih =>
    rw [Finset.prod_insert haT]
    refine mem_mul_smul_of_coprime N ?_ (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact IsCoprime.prod_right fun i hi => hJ a i fun hai => haT (hai ▸ hi)

theorem exists_prod_le_of_isRadical {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) : ∃ T : Finset (HeightOneSpectrum R), (∀ u ∈ T, 𝔞 ≤ u.asIdeal) ∧
      ∏ u ∈ T, u.asIdeal ≤ 𝔞 := by
  have hfin := Ideal.finite_factors h0
  refine ⟨hfin.toFinset, fun u hu => Ideal.le_of_dvd ((Set.Finite.mem_toFinset hfin).1 hu), ?_⟩
  intro x hx
  apply hr
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  have hP0 : P ≠ ⊥ := fun hb => h0 (le_bot_iff.1 (hb ▸ hle))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hv : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 (Ideal.dvd_iff_le.2 hle)
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hv)) hx

theorem extId_eq_image (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId
  rw [Ideal.map]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, Subtype.ext hz.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

private theorem isCoprime_map_of_ne {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) {u v : HeightOneSpectrum R} (huv : u ≠ v) :
    IsCoprime (u.asIdeal.map f) (v.asIdeal.map f) := by
  have hmax : u.asIdeal ⊔ v.asIdeal = ⊤ :=
    u.isMaximal.coprime_of_ne v.isMaximal fun e => huv (HeightOneSpectrum.ext e)
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hmax, Ideal.map_top]

private theorem prod_map_le_map_of_prod_le {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Finset (HeightOneSpectrum R)) {𝔞 : Ideal R} (hle : ∏ u ∈ T, u.asIdeal ≤ 𝔞) :
    ∏ u ∈ T, u.asIdeal.map f ≤ 𝔞.map f := by
  have hprod : ∀ T' : Finset (HeightOneSpectrum R),
      ∏ u ∈ T', u.asIdeal.map f = (∏ u ∈ T', u.asIdeal).map f := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
    | @insert a T' haT ih => rw [Finset.prod_insert haT, Finset.prod_insert haT, Ideal.map_mul, ih]
  rw [hprod]
  exact Ideal.map_mono hle

private theorem mem_map_smul_of_forall_mem_map_smul {R S M : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (N : Submodule S M) {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) {y : M} (hy : y ∈ N)
    (h : ∀ u : HeightOneSpectrum R, 𝔞 ≤ u.asIdeal → y ∈ u.asIdeal.map f • N) : y ∈ 𝔞.map f • N := by
  obtain ⟨T, hT, hle⟩ := exists_prod_le_of_isRadical h0 hr
  have hmem : y ∈ (∏ u ∈ T, u.asIdeal.map f) • N :=
    mem_prod_smul_of_coprime (ι := HeightOneSpectrum R) N (fun u => u.asIdeal.map f)
      (fun _ _ huv => isCoprime_map_of_ne f huv) hy T fun u hu => h u (hT u hu)
  exact Submodule.smul_mono_left (prod_map_le_map_of_prod_le f T hle) hmem

theorem mem_extId_smul_forall_iff : ∀ (I : AutInst) (m : ℕ), 1 ≤ m → (Ideal.span {(m : 𝓞 I.E)}).IsRadical →
    ∀ y ∈ I.Lf, (∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal → y ∈ extId I u.asIdeal • I.Lf) ↔
      ∃ z ∈ I.Lf, y = (m : (I.E ⊗[I.F] Af I.F)) • z := by
  intro I m hm hrad y hy
  constructor
  · intro h
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have key : y ∈ (Ideal.span {(m : 𝓞 I.E)}).map (Inhab.psi I.F I.E) • I.Lf :=
      mem_map_smul_of_forall_mem_map_smul (Inhab.psi I.F I.E) I.Lf h0 hrad hy fun u hu => by
        rw [← extId_eq_image I]
        exact h u (hu (Ideal.mem_span_singleton_self _))
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨z, hz, hzy⟩ := key
    refine ⟨z, hz, ?_⟩
    rw [← hzy, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨z, hz, rfl⟩ u hu
    have hm' : (m : IntAf I.F I.E) ∈ extId I u.asIdeal := by
      rw [extId_eq_image, ← map_natCast (Inhab.psi I.F I.E)]
      exact Ideal.mem_map_of_mem _ hu
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (IntAf I.F I.E)]
    exact Submodule.smul_mem_smul hm' hz

end GlobalTheory.RowLev.SqfCrt
