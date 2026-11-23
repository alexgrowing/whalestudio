import Mathlib
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors

namespace Formalism.L2.DIV

theorem degree_one_places : DegOnePlc := by
  intro F _ _ v hv
  have hp := hv.1
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.absNorm_mem v.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at this
    exact this
  have hd : plc v ∣ Ideal.absNorm v.asIdeal := ringChar.dvd h0
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact absurd h (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
  · exact h.symm

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensor_conjugation_tmul (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) (r : R) :
    sigR σ R (e ⊗ₜ[F] r) = σ e ⊗ₜ[F] r := by
  rfl

theorem conjugation_involutive (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    sigR σ R (sigR σ R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => rw [tensor_conjugation_tmul, tensor_conjugation_tmul, hσ.2.1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem add_conjugation_mem_range (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    z + sigR σ R z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e r =>
    obtain ⟨a, ha⟩ := hσ.2.2 (e + σ e) (by rw [map_add, hσ.2.1, add_comm])
    refine ⟨a • r, ?_⟩
    show (1 : E) ⊗ₜ[F] (a • r) = e ⊗ₜ[F] r + sigR σ R (e ⊗ₜ[F] r)
    rw [tensor_conjugation_tmul, ← TensorProduct.add_tmul, ← ha, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    have : x + y + sigR σ R (x + y) = (x + sigR σ R x) + (y + sigR σ R y) := by rw [map_add]; ring
    rw [this]; exact add_mem hx hy

theorem conjugation_fixed_mem_range [CharZero F] (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R]
    (z : E ⊗[F] R) (hz : sigR σ R z = z) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  have h := add_conjugation_mem_range σ hσ R z
  rw [hz] at h
  have h2 : z = (2⁻¹ : F) • (z + z) := by
    rw [← two_smul F z, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [h2]; exact Subalgebra.smul_mem _ h _

theorem include_right_injective_of_field (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective

theorem exists_conjugation_negated (σ : E →ₐ[F] E) (hσ : IsConjOf σ) : ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ := by
  have : ∃ e, σ e ≠ e := by
    by_contra h
    exact hσ.1 (AlgHom.ext fun e => by_contra fun he => h ⟨e, he⟩)
  obtain ⟨e, he⟩ := this
  exact ⟨e - σ e, sub_ne_zero.mpr (Ne.symm he), by rw [map_sub, hσ.2.1]; ring⟩

theorem hilbert90_quadratic_field (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (d : E) (hd : σ d * d = 1) :
    ∃ x : E, x ≠ 0 ∧ x = d * σ x := by
  by_cases h : 1 + d = 0
  · obtain ⟨θ, h0, hθ⟩ := exists_conjugation_negated σ hσ
    refine ⟨θ, h0, ?_⟩
    have : d = -1 := by linear_combination h
    rw [hθ, this]; ring
  · refine ⟨1 + d, h, ?_⟩
    rw [map_add, map_one]
    linear_combination -hd

end Gen

theorem unitary_det_norm_one {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (g : GL (Fin n) A) (hg : g ∈ UJ σ J) : σ (g : Matrix (Fin n) (Fin n) A).det * (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h2
  have h3 : ((g : Matrix (Fin n) (Fin n) A).map σ).det = σ (g : Matrix (Fin n) (Fin n) A).det := by
    rw [RingHom.map_det]; rfl
  rw [h3] at h2
  apply hJ.mul_left_cancel
  linear_combination h2

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conjugation_units_val (σ : E →ₐ[F] E) (x : (AfE F E)ˣ) :
    ((conjId σ x : (AfE F E)ˣ) : AfE F E) = sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) := rfl

theorem idele_conjugation_involutive (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (x : (AfE F E)ˣ) : conjId σ (conjId σ x) = x := by
  apply Units.ext
  rw [conjugation_units_val, conjugation_units_val, conjugation_involutive σ hσ]

theorem mem_ker_norm_quotient_iff (σ : E →ₐ[F] E) (x : (AfE F E)ˣ) : x ∈ (h90 σ).ker ↔ conjId σ x = x := by
  rw [MonoidHom.mem_ker, h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_one, eq_comm]

theorem norm_quotient_eq_iff (σ : E →ₐ[F] E) (x y : (AfE F E)ˣ) : h90 σ x = y ↔ x = y * conjId σ x := by
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]

end Main

theorem fixed_field_is_base : FixedIsIdF := by
  intro F E _ _ _ _ _ σ hσ
  ext x
  rw [mem_ker_norm_quotient_iff]
  constructor
  · intro hx
    have h1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = x := by
      rw [← conjugation_units_val, hx]
    have h2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((x⁻¹ : (AfE F E)ˣ) : AfE F E) = ((x⁻¹ : (AfE F E)ˣ) : AfE F E) := by
      rw [← conjugation_units_val, map_inv, hx]
    obtain ⟨r, hr⟩ := conjugation_fixed_mem_range σ hσ _ _ h1
    obtain ⟨s, hs⟩ := conjugation_fixed_mem_range σ hσ _ _ h2
    have hrs : r * s = 1 := by
      apply include_right_injective_of_field (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      rw [map_mul, map_one]
      erw [hr, hs]
      exact x.mul_inv
    refine ⟨⟨r, s, hrs, by rw [mul_comm]; exact hrs⟩, ?_⟩
    apply Units.ext
    exact hr
  · rintro ⟨r, rfl⟩
    apply Units.ext
    rw [conjugation_units_val]
    show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)
    rw [tensor_conjugation_tmul, map_one]

theorem conjugation_invariant_measure : ConjInv := by
  intro F E _ _ _ _ _ L _ σ ξ hσ hξ
  ext1 x
  rw [MonoidHom.comp_apply, MonoidHom.inv_apply, eq_inv_iff_mul_eq_one, ← map_mul]
  have : conjId σ x * x ∈ (h90 σ).ker := by
    rw [mem_ker_norm_quotient_iff, map_mul, idele_conjugation_involutive σ hσ, mul_comm]
  rw [fixed_field_is_base F E σ hσ] at this
  exact hξ this

theorem det_in_unitary_one : DetInUnitaryOne := by
  intro F E _ _ _ _ _ σ n J hJ g hg
  have hJ' : IsUnit (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det := by
    have : (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hJ.map _
  have h := unitary_det_norm_one _ _ hJ' g hg
  rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
  apply Units.ext
  rw [Units.val_mul, conjugation_units_val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact h

theorem norm_quotient_ker_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L) (hσ : IsConjOf σ) (hξ : (idF F E).range ≤ ξ.ker) : (h90 σ).ker ≤ ξ.ker := by
  rw [fixed_field_is_base F E σ hσ]; exact hξ

theorem detTwMul_of (H : Hilbert90FiniteIdeles) : DetTwMul := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ g hg g' hg'
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  have h1 := det_in_unitary_one F E σ n J hJ g hg
  have h2 := det_in_unitary_one F E σ n J hJ g' hg'
  rw [H F E σ hσ] at h1 h2
  obtain ⟨x, hx⟩ := h1
  obtain ⟨x', hx'⟩ := h2
  rw [detTw_of_det σ ξ hk g x hx, detTw_of_det σ ξ hk g' x' hx',
    detTw_of_det σ ξ hk (g * g') (x * x') (by rw [map_mul, map_mul, hx, hx']), map_mul]

theorem detTwSq_of (H : Hilbert90FiniteIdeles) : DetTwSq := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ g hg
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  have h1 := det_in_unitary_one F E σ n J hJ g hg
  rw [H F E σ hσ] at h1
  obtain ⟨x, hx⟩ := h1
  rw [detTw_of_det σ ξ hk g x hx, ← hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, map_div]
  have := congrArg (fun η : Chr F E L => η x) (conjugation_invariant_measure F E L σ ξ hσ hξ)
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply] at this
  rw [this, div_inv_eq_mul, sq]

theorem det_twist_rational : DetTwRat := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ hrat g hg
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  obtain ⟨g0, hg0, rfl⟩ := hg
  have hd := unitary_det_norm_one (σ : E →+* E) J hJ g0 hg0
  obtain ⟨x, hx0, hx⟩ := hilbert90_quadratic_field σ hσ _ hd
  have key : h90 σ (ratId F E (Units.mk0 x hx0)) =
      Matrix.GeneralLinearGroup.det (bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) g0) := by
    rw [norm_quotient_eq_iff]
    apply Units.ext
    rw [Units.val_mul, conjugation_units_val, Matrix.GeneralLinearGroup.val_det_apply]
    have e1 : ((ratId F E (Units.mk0 x hx0) : (AfE F E)ˣ) : AfE F E) =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) x := rfl
    have e2 : ((bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) g0 : GL (Fin n) (AfE F E)) :
        Matrix (Fin n) (Fin n) (AfE F E)).det =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (g0 : Matrix (Fin n) (Fin n) E).det := by
      rw [RingHom.map_det]; rfl
    have e3 : sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) x) =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (σ x) := tensor_conjugation_tmul σ _ x 1
    rw [e1, e2, e3, ← map_mul]
    exact congrArg _ hx
  rw [detTw_of_det σ ξ hk _ _ key]
  exact hrat ⟨_, rfl⟩

section A2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem conjugation_tmul (σ : E →ₐ[F] E) (e : E) (a : 𝔸) : sigR σ 𝔸 (e ⊗ₜ[F] a) = σ e ⊗ₜ[F] a := rfl

theorem adele_conjugation_involutive (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (z : AfE F E) :
    sigR σ 𝔸 (sigR σ 𝔸 z) = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp only [map_zero]
  · intro e a
    rw [conjugation_tmul, conjugation_tmul, h]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

theorem adele_trace_from_base (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (z : AfE F E) :
    ∃ t : 𝔸, (1 : E) ⊗ₜ[F] t = z + sigR σ 𝔸 z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e a =>
    obtain ⟨c, hc⟩ := hf (e + σ e) (by rw [map_add, h, add_comm])
    refine ⟨c • a, ?_⟩
    rw [conjugation_tmul, ← TensorProduct.add_tmul, ← hc, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [TensorProduct.tmul_add, hs, ht, map_add]; ring⟩

theorem finite_adele_is_unit (a : 𝔸) (h0 : ∀ v, a v ≠ 0)
    (h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (a v) = 1) : IsUnit a := by
  let b : 𝔸 := ⟨fun v => (a v)⁻¹, by
    filter_upwards [h1] with v hv
    show (a v)⁻¹ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]⟩
  refine IsUnit.of_mul_eq_one b ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  show a v * (a v)⁻¹ = 1
  exact mul_inv_cancel₀ (h0 v)

theorem valuation_eq_one_eventually (k : F) (hk : k ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (algebraMap F (v.adicCompletion F) k) = 1 := by
  have h1 := (algebraMap F 𝔸 k).2
  have h2 := (algebraMap F 𝔸 k⁻¹).2
  filter_upwards [h1, h2] with v a b
  have a' : Valued.v (algebraMap F (v.adicCompletion F) k) ≤ 1 := a
  have b' : Valued.v (algebraMap F (v.adicCompletion F) k⁻¹) ≤ 1 := b
  rw [map_inv₀, map_inv₀] at b'
  have hpos : 0 < Valued.v (algebraMap F (v.adicCompletion F) k) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hk))
  exact le_antisymm a' ((inv_le_one₀ hpos).mp b')

theorem unitary_one_mem_range_norm_quotient (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (y : (AfE F E)ˣ) (hy : y ∈ U1 σ) :
    y ∈ (h90 σ).range := by
  classical
  obtain ⟨hne, hinv, hfix⟩ := hσ
  have hex : ∃ e, σ e ≠ e := by
    by_contra hcon
    exact hne (AlgHom.ext fun e => by
      by_contra h
      exact hcon ⟨e, h⟩)
  obtain ⟨e0, he0⟩ := hex
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = e0 - σ e0 := ⟨_, rfl⟩
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact sub_ne_zero.mpr (Ne.symm he0)
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hinv]; ring
  obtain ⟨D, hD⟩ := hfix (θ * θ) (by rw [map_mul, hσθ]; ring)
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hθ0 (mul_self_eq_zero.mp hD.symm)
  obtain ⟨Y, hY⟩ : ∃ Y : AfE F E, Y = (y : AfE F E) := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : AfE F E, Y' = ((y⁻¹ : (AfE F E)ˣ) : AfE F E) := ⟨_, rfl⟩
  have hYY : Y * Y' = 1 := by rw [hY, hY']; exact y.mul_inv
  have hsY : sigR σ 𝔸 Y = Y' := by
    have h1 : y * conjId σ y = 1 := hy
    have h2 : conjId σ y = y⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hY, hY', ← h2]
    rfl
  obtain ⟨T, hT⟩ := adele_trace_from_base σ hinv hfix Y
  rw [hsY] at hT
  let iR : 𝔸 →ₐ[F] AfE F E := Algebra.TensorProduct.includeRight
  have hT' : iR T = Y + Y' := hT
  let Sp : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)}
  let ep : 𝔸 := ⟨fun v => if v ∈ Sp then 1 else 0, Filter.Eventually.of_forall (fun v => by
    show (if v ∈ Sp then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _)⟩
  have hep : ∀ v, ep v = if v ∈ Sp then 1 else 0 := fun v => rfl
  have hpp : ep * ep = ep := by
    refine FiniteAdeleRing.ext _ fun v => ?_
    show ep v * ep v = ep v
    rw [hep]
    split_ifs <;> simp
  obtain ⟨m, hmdef⟩ : ∃ m : 𝔸, m = ep * (2 + T) + (1 - ep) * (algebraMap F 𝔸 (-D) * (2 - T)) := ⟨_, rfl⟩
  have hm : ∀ v, m v = if v ∈ Sp then 2 + T v
      else algebraMap F (v.adicCompletion F) (-D) * (2 - T v) := by
    intro v
    have h1 : m v = ep v * (2 + T v) +
        (1 - ep v) * (algebraMap F (v.adicCompletion F) (-D) * (2 - T v)) := by
      show evalV F v m = evalV F v ep * (2 + evalV F v T) +
        (1 - evalV F v ep) * (algebraMap F (v.adicCompletion F) (-D) * (2 - evalV F v T))
      rw [hmdef]
      simp only [map_add, map_mul, map_sub, map_one, map_ofNat, AlgHom.commutes]
    rw [h1, hep]
    split_ifs <;> simp
  have h4 : ∀ v : HeightOneSpectrum (𝓞 F), (4 : v.adicCompletion F) ≠ 0 := by
    intro v
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
    exact (map_ne_zero _).mpr (by norm_num)
  have hmU : IsUnit m := by
    apply finite_adele_is_unit
    · intro v
      rw [hm]
      split_ifs with hv
      · rcases hv with hv | hv
        · intro h
          rw [h, map_zero] at hv
          exact zero_ne_one hv
        · exact hv.2
      · have hv' : ¬ (Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)) := hv
        rw [not_or, not_and_or, not_not, not_not] at hv'
        refine mul_ne_zero ((map_ne_zero _).mpr (neg_ne_zero.mpr hD0)) ?_
        rcases hv'.2 with h | h
        · intro h'
          rw [h', map_zero] at h
          exact zero_ne_one h
        · have : 2 - T v = 4 := by linear_combination -h
          rw [this]
          exact h4 v
    · filter_upwards [T.2, valuation_eq_one_eventually (F := F) 2 (by norm_num), valuation_eq_one_eventually (F := F) 4 (by norm_num),
        valuation_eq_one_eventually D hD0] with v hTv h2v h4v hDv
      have hTv' : Valued.v (T v) ≤ 1 := hTv
      rw [map_ofNat] at h2v h4v
      have hle1 : Valued.v (2 + T v) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le h2v.le hTv')
      have hle2 : Valued.v (2 - T v) ≤ 1 := (Valuation.map_sub _ _ _).trans (max_le h2v.le hTv')
      have hor : Valued.v (2 + T v) = 1 ∨ Valued.v (2 - T v) = 1 := by
        by_contra hcon
        rw [not_or] at hcon
        have := Valuation.map_add_lt (Valued.v) (lt_of_le_of_ne hle1 hcon.1) (lt_of_le_of_ne hle2 hcon.2)
        rw [show (2 + T v) + (2 - T v) = 4 by ring, h4v] at this
        exact lt_irrefl _ this
      rw [hm]
      split_ifs with hv
      · rcases hv with hv | hv
        · exact hv
        · exact hor.resolve_right hv.1
      · have hv' : ¬ (Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)) := hv
        rw [not_or] at hv'
        rw [map_mul, map_neg, Valuation.map_neg, hDv, one_mul]
        exact hor.resolve_left hv'.1
  obtain ⟨p, hpdef⟩ : ∃ p : AfE F E, p = iR ep := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : AfE F E, t = θ ⊗ₜ[F] (1 : 𝔸) := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : AfE F E, d = iR (algebraMap F 𝔸 D) := ⟨_, rfl⟩
  have hp : p * p = p := by rw [hpdef, ← map_mul, hpp]
  have hsp : sigR σ 𝔸 p = p := by
    rw [hpdef]
    show sigR σ 𝔸 ((1 : E) ⊗ₜ[F] ep) = (1 : E) ⊗ₜ[F] ep
    rw [conjugation_tmul, map_one]
  have hst : sigR σ 𝔸 t = -t := by rw [htdef, conjugation_tmul, hσθ, TensorProduct.neg_tmul]
  have htt : t * t = d := by
    rw [htdef, hddef, Algebra.TensorProduct.tmul_mul_tmul, ← hD, mul_one]
    show algebraMap F E D ⊗ₜ[F] (1 : 𝔸) = (1 : E) ⊗ₜ[F] algebraMap F 𝔸 D
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨X, hX⟩ : ∃ X : AfE F E, X = p * (1 + Y) + (1 - p) * t * (1 - Y) := ⟨_, rfl⟩
  have hsX : sigR σ 𝔸 X = p * (1 + Y') - (1 - p) * t * (1 - Y') := by
    rw [hX]
    simp only [map_add, map_mul, map_sub, map_one, hsp, hst, hsY]
    ring
  have hYX : Y * sigR σ 𝔸 X = X := by
    rw [hsX, hX]
    linear_combination (p + (1 - p) * t) * hYY
  have him : iR m = p * (2 + (Y + Y')) + (1 - p) * (-d * (2 - (Y + Y'))) := by
    rw [hmdef, hpdef, hddef, ← hT']
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, map_neg]
  have hXX : X * sigR σ 𝔸 X = iR m := by
    rw [him, hsX, hX]
    linear_combination ((1 + Y) * (1 + Y') - (-t * (1 + Y) * (1 - Y') + t * (1 - Y) * (1 + Y'))
      - t * t * ((1 - Y) * (1 - Y'))) * hp - (1 - p) * ((1 - Y) * (1 - Y')) * htt
      + (p - (1 - p) * d) * hYY
  have hXU : IsUnit X := by
    apply isUnit_of_mul_isUnit_left (y := sigR σ 𝔸 X)
    rw [hXX]
    exact hmU.map iR
  obtain ⟨Xu, hXu⟩ := hXU
  refine ⟨Xu, ?_⟩
  show Xu / conjId σ Xu = y
  rw [div_eq_iff_eq_mul]
  apply Units.ext
  show (Xu : AfE F E) = (y : AfE F E) * sigR σ 𝔸 (Xu : AfE F E)
  rw [hXu, ← hY, hYX]

end A2

theorem hilbert90_finite_ideles : Hilbert90FiniteIdeles := by
  intro F E _ _ _ _ _ σ hσ
  apply le_antisymm
  · intro y hy
    exact unitary_one_mem_range_norm_quotient σ hσ y hy
  · rintro _ ⟨x, rfl⟩
    have hcc : conjId σ (conjId σ x) = x := Units.ext (adele_conjugation_involutive σ hσ.2.1 _)
    show h90 σ x * conjId σ (h90 σ x) = 1
    have h1 : h90 σ x = x / conjId σ x := rfl
    rw [h1, map_div, hcc, div_mul_div_cancel, div_self']

theorem det_twist_mul : DetTwMul := detTwMul_of hilbert90_finite_ideles

theorem det_twist_square : DetTwSq := detTwSq_of hilbert90_finite_ideles

section C

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def c_lat (x : (AfE F E)ˣ) : Submodule (𝓞 E) E where
  carrier := {e | ((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE e ∈ RInt F E}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul, mul_left_comm]
    exact mul_mem (Formalism.UG.CS.incl_int c) ha

theorem c_mem_lat (x : (AfE F E)ˣ) (e : E) :
    e ∈ c_lat x ↔ ((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE e ∈ RInt F E := Iff.rfl

theorem c_lat_frac (x : (AfE F E)ˣ) : IsFractional (𝓞 E)⁰ (c_lat x) := by
  obtain ⟨d, hd, hdx⟩ := levelaf_denom (E := E) (x : AfE F E)
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    apply adelstab_algebraMap_ne_zero (E := E) d hd
    rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero]
  · intro b hb
    have h1 : ιE (algebraMap (𝓞 F) (𝓞 E) d • b) ∈ RInt F E := by
      have : ιE (algebraMap (𝓞 F) (𝓞 E) d • b) =
          (levelafC E d * (x : AfE F E)) * (((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, adelstab_incl_C]
        have := x.mul_inv
        linear_combination (-(levelafC E d * ιE b)) * this
      rw [this]; exact mul_mem hdx hb
    have h2 := csGlob_int _ h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h2, IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem c_decomp (x : (AfE F E)ˣ) : ∃ e₁ ∈ c_lat x, ∃ e₂ ∈ c_lat x, e₂ ≠ 0 ∧ ∃ t ∈ RInt F E,
    (x : AfE F E) = ιE e₁ + ιE e₂ * t := by
  obtain ⟨d₁, hd₁, hx₁⟩ := levelaf_denom (E := E) (x : AfE F E)
  obtain ⟨d₂, hd₂, hx₂⟩ := levelaf_denom (E := E) ((x⁻¹ : (AfE F E)ˣ) : AfE F E)
  obtain ⟨b, t, ht, hbt⟩ := csGlob_approx csGlob_intAdApprox (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hx₁
  have hne₁ := adelstab_algebraMap_ne_zero (E := E) d₁ hd₁
  have hne₂ := adelstab_algebraMap_ne_zero (E := E) d₂ hd₂
  have h2 : algebraMap (𝓞 F) E d₂ ∈ c_lat x := by
    rw [c_mem_lat, adelstab_incl_C, mul_comm]; exact hx₂
  have hinv : ιE (algebraMap (𝓞 F) E d₁)⁻¹ * levelafC E d₁ = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ hne₁, map_one]
  have hx : (x : AfE F E) = ιE ((algebraMap (𝓞 F) E d₁)⁻¹ * algebraMap (𝓞 E) E b) +
      ιE (algebraMap (𝓞 F) E d₂) * t := by
    rw [levelafC_mul] at hbt
    rw [map_mul, adelstab_incl_C]
    linear_combination (ιE (algebraMap (𝓞 F) E d₁)⁻¹) * hbt + ((levelafC E d₂) * t - (x : AfE F E)) * hinv
  refine ⟨_, ?_, _, h2, hne₂, t, ht, hx⟩
  rw [c_mem_lat]
  have h3 : ιE ((algebraMap (𝓞 F) E d₁)⁻¹ * algebraMap (𝓞 E) E b) =
      (x : AfE F E) - ιE (algebraMap (𝓞 F) E d₂) * t := by rw [hx]; ring
  rw [h3, mul_sub, x.inv_mul, ← mul_assoc]
  exact sub_mem (one_mem _) (mul_mem h2 ht)

def integralAdeleSpan (N : Submodule (𝓞 E) E) : Submodule (RInt F E) (AfE F E) :=
  Submodule.span (RInt F E) (ιE '' (N : Set E))

theorem c_T_mul (N N' : Submodule (𝓞 E) E) {z z' : AfE F E} (hz : z ∈ integralAdeleSpan (F := F) N)
    (hz' : z' ∈ integralAdeleSpan (F := F) N') : z * z' ∈ integralAdeleSpan (F := F) (N * N') := by
  have h := Submodule.mul_mem_mul hz hz'
  rw [integralAdeleSpan, integralAdeleSpan, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨n, hn, rfl⟩, _, ⟨n', hn', rfl⟩, rfl⟩
  exact ⟨n * n', Submodule.mul_mem_mul hn hn', map_mul _ _ _⟩

theorem pow_mem_integral_span (x : (AfE F E)ˣ) (k : ℕ) : (x : AfE F E) ^ k ∈ integralAdeleSpan (F := F) ((c_lat x) ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Submodule.subset_span ⟨1, Submodule.mem_one.mpr ⟨1, map_one _⟩, map_one _⟩
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine c_T_mul _ _ ih ?_
    obtain ⟨e₁, h₁, e₂, h₂, _, t, ht, hx⟩ := c_decomp x
    rw [hx]
    refine add_mem (Submodule.subset_span ⟨e₁, h₁, rfl⟩) ?_
    have : ιE e₂ * t = (⟨t, ht⟩ : RInt F E) • ιE e₂ := by
      rw [Subring.smul_def, smul_eq_mul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e₂, h₂, rfl⟩)

theorem c_inv_pow_mem (x : (AfE F E)ˣ) (k : ℕ) : ∀ y ∈ (c_lat x) ^ k,
    ((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ k * ιE y ∈ RInt F E := by
  induction k with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hy
    rw [pow_zero, one_mul]; exact Formalism.UG.CS.incl_int b
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn
      have : ((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ (k + 1) * ιE (m * n) =
          (((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ k * ιE m) * (((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE n) := by
        rw [map_mul]; ring
      rw [this]; exact mul_mem (ih m hm) hn
    · intro a b ha hb
      rw [map_add, mul_add]; exact add_mem ha hb

theorem c_class (x : (AfE F E)ˣ) :
    ∃ e : Eˣ, x ^ Fintype.card (ClassGroup (𝓞 E)) * (ratId F E e)⁻¹ ∈ intU F E := by
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  obtain ⟨_, _, e₂, h₂, hne, _⟩ := c_decomp x
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨c_lat x, c_lat_frac x⟩
  have hI : I ≠ 0 := by
    intro h0
    have : e₂ ∈ I := h₂
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    exact hne this
  let U : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 I hI
  have h1 : ClassGroup.mk E (U ^ h) = 1 := by rw [map_pow, hh, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨⟨g, hg⟩⟩ := h1
  have hc : (((U ^ h : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) =
      (c_lat x) ^ h := by
    rw [Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]; rfl
  rw [hc] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h3 : e₂ ^ h ∈ (c_lat x) ^ h := Submodule.pow_mem_pow _ h₂ h
    rw [hg, Submodule.mem_span_singleton] at h3
    obtain ⟨b, hb⟩ := h3
    rw [smul_zero] at hb
    exact pow_ne_zero h hne hb.symm
  have hgm : g ∈ (c_lat x) ^ h := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hA := c_inv_pow_mem x h g hgm
  have hB : ∃ s ∈ RInt F E, (x : AfE F E) ^ h = ιE g * s := by
    have h4 := pow_mem_integral_span x h
    rw [hg] at h4
    refine Submodule.span_induction (p := fun z _ => ∃ s ∈ RInt F E, z = ιE g * s) ?_ ?_ ?_ ?_ h4
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨ιE (algebraMap _ _ b), Formalism.UG.CS.incl_int b, by rw [Algebra.smul_def, map_mul, mul_comm]⟩
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro a b _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
      exact ⟨s + s', add_mem hs hs', by ring⟩
    · rintro r a _ ⟨s, hs, rfl⟩
      exact ⟨r * s, mul_mem r.2 hs, by rw [Subring.smul_def, smul_eq_mul]; ring⟩
  obtain ⟨s, hs, hxs⟩ := hB
  have hv2 : ((ratId F E (Units.mk0 g hg0) : (AfE F E)ˣ) : AfE F E) = ιE g := rfl
  have hv1 : (((ratId F E (Units.mk0 g hg0))⁻¹ : (AfE F E)ˣ) : AfE F E) = ιE g⁻¹ := by
    rw [← map_inv]
    show ιE (((Units.mk0 g hg0)⁻¹ : Eˣ) : E) = ιE g⁻¹
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  refine ⟨Units.mk0 g hg0, ?_⟩
  rw [intU, Submonoid.mem_units_iff]
  constructor
  · rw [Units.val_mul, Units.val_pow_eq_pow_val, hv1, hxs]
    have : ιE g * s * ιE g⁻¹ = s := by
      have h5 : ιE g * ιE g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hg0, map_one]
      linear_combination s * h5
    rw [this]; exact hs
  · rw [mul_inv, inv_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, hv2]
    exact hA

theorem c_unit_pow (N : ℕ) (hN : 0 < N) : ∃ m : ℕ, 0 < m ∧ ∀ u ∈ intU F E, u ^ m ∈ congN F E N := by
  have hfin : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
    apply levelaf_finite_quot (N : 𝓞 F) (by exact_mod_cast hN.ne')
    rw [levelafC, map_natCast]
    show ((N : RInt F E) : AfE F E) =
      (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E) (N : FiniteAdeleRing (𝓞 F) F)
    rw [map_natCast]
    simp
  refine ⟨Nat.card (RInt F E ⧸ Ideal.span {(N : RInt F E)})ˣ, Nat.card_pos, ?_⟩
  intro u hu
  rw [intU, Submonoid.mem_units_iff] at hu
  let u' : (RInt F E)ˣ := ⟨⟨u, hu.1⟩, ⟨((u⁻¹ : (AfE F E)ˣ) : AfE F E), hu.2⟩,
    Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  refine ⟨u' ^ Nat.card (RInt F E ⧸ Ideal.span {(N : RInt F E)})ˣ, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, pow_card_eq_one']
  · rw [map_pow]
    congr 1

end C

theorem finite_order_automorphism : FinOrdAuto := by
  intro F E _ _ _ _ _ L _ ξ hξ
  obtain ⟨h1, N, hN, h2⟩ := Subgroup.mem_inf.mp hξ
  rw [mem_kills] at h1
  obtain ⟨m, hm, hu⟩ := c_unit_pow (F := F) (E := E) N hN
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨Fintype.card (ClassGroup (𝓞 E)) * m, Nat.mul_pos Fintype.card_pos hm, ?_⟩
  ext x
  obtain ⟨e, he⟩ := c_class x
  have h3 : ξ (ratId F E e) = 1 := h1 ⟨e, rfl⟩
  have h4 : ξ ((x ^ Fintype.card (ClassGroup (𝓞 E)) * (ratId F E e)⁻¹) ^ m) = 1 := h2 (hu _ he)
  rw [map_pow, map_mul, map_inv, h3, inv_one, mul_one, map_pow, ← pow_mul] at h4
  rw [MonoidHom.pow_apply, h4, MonoidHom.one_apply]

theorem base_tuple_quotient : Mu0Quot := by
  intro F E _ _ _ _ _ L _ σ Ψ e G μ μ' h h'
  have h1 : μ * μ'⁻¹ ∈ kills Lˣ (ratId F E).range ⊓ openChr F E L := by
    refine Subgroup.mem_inf.mpr ⟨?_, (openChr F E L).mul_mem h.isOpen ((openChr F E L).inv_mem h'.isOpen)⟩
    rw [mem_kills]
    rintro _ ⟨a, rfl⟩
    have h2 : μ (ratId F E a) = μ' (ratId F E a) := Units.ext (by rw [h.rat, h'.rat])
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, h2, mul_inv_cancel]
  exact Subgroup.mem_inf.mpr ⟨h1, finite_order_automorphism F E L h1⟩

section B

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bEps (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : RInt F E :=
  ⟨afsplitEps E v, afsplit_eps_int v⟩

theorem b_eps_idem (v : HeightOneSpectrum (𝓞 F)) : bEps E v * bEps E v = bEps E v :=
  Subtype.ext (afsplit_eps_idem v)

theorem b_toRInt_val (b : 𝓞 E) :
    ((toRInt F E b : RInt F E) : AfE F E) = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E b) := rfl

theorem b_toRInt_alg (d : 𝓞 F) :
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) d) : RInt F E) : AfE F E) =
      (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d := by
  rw [b_toRInt_val, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, adelstab_incl_C]
  rfl

theorem b_eps_val (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F) := by
  rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]

theorem b_mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) :
    x ∈ suppAt E v ↔ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' (x : AfE F E) = 1 := by
  simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem b_eps_mul (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E)
    (hz : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' z = 0) : afsplitEps E v * z = z := by
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  by_cases h : w = v
  · subst h
    rw [map_sub, map_mul, afsplit_prV_eps, one_mul, sub_self]
  · rw [map_sub, map_mul, hz w h, mul_zero, sub_self]

theorem b_eps_mul_unit (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    bEps E v * ((u : RInt F E) - 1) = (u : RInt F E) - 1 := by
  apply Subtype.ext
  apply b_eps_mul v
  intro v' hv'
  have := (b_mem_suppAt v _).mp hu v' hv'
  show prV (E := E) v' (((u : RInt F E) : AfE F E) - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]
  exact this

theorem b_val_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact hr

theorem b_inv_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, b_val_one v r hr, inv_one]

theorem b_alg_ne_zero (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := by
  intro h
  have := b_val_one v r hr
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem b_loc_inv (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = bEps E v := by
  refine ⟨⟨(1 : E) ⊗ₜ[F] afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 (afsplitI_mem_intAd v _ (b_inv_int v r hr))
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    by_cases h : w = v
    · subst h
      rw [afsplit_mul_apply, afsplitI_self, afsplitI_self]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r hr)
    · rw [afsplit_mul_apply, afsplitI_ne v w h, afsplitI_ne v w h, mul_zero]

theorem b_off_inv (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F)
    (hr : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → r ∉ v'.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = 1 - bEps E v := by
  classical
  have hint : ∀ w : HeightOneSpectrum (𝓞 F),
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) ∈
        w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · exact b_inv_int w r (hr w h)
  let a : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun w => if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹,
      Filter.Eventually.of_forall hint⟩
  have ha : a ∈ intAd F := hint
  refine ⟨⟨(1 : E) ⊗ₜ[F] a, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 ha
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = 1 - afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val, Algebra.TensorProduct.one_def,
      ← TensorProduct.tmul_sub]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    rw [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply]
    show algebraMap (𝓞 F) (w.adicCompletion F) r *
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) = _
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, afsplitI_self, mul_zero, sub_self]
    · rw [if_neg h, afsplitI_ne v w h, sub_zero]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r (hr w h))

theorem b_pi (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ∈ v.asIdeal ∧ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → π ∉ v'.asIdeal := by
  classical
  have hv0 : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have h1 : ClassGroup.mk0 (⟨v.asIdeal, hv0⟩ ^ h) = 1 := by
    rw [map_pow, hh, pow_card_eq_one]
  have h2 : (v.asIdeal ^ h).IsPrincipal := by
    have h3 : v.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv0 h
    rw [← ClassGroup.mk0_eq_one_iff h3, ← h1]
    rfl
  obtain ⟨π, hπ⟩ := h2
  have hπ' : v.asIdeal ^ h = Ideal.span {π} := hπ
  have hmem : π ∈ v.asIdeal ^ h := by rw [hπ']; exact Ideal.mem_span_singleton_self π
  refine ⟨π, Ideal.pow_le_self hpos.ne' hmem, fun v' hv' hc => hv' ?_⟩
  have hle : v.asIdeal ^ h ≤ v'.asIdeal := by
    rw [hπ', Ideal.span_singleton_le_iff_mem]; exact hc
  have hle' : v.asIdeal ≤ v'.asIdeal := v'.isPrime.le_of_pow_le hle
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle').symm

theorem b_mul_mem_map (P : Ideal (𝓞 E)) (c : 𝓞 E) (hc : c ∈ P) (t : RInt F E) :
    toRInt F E c * t ∈ P.map (toRInt F E) := by
  have h1 : toRInt F E c ∈ P.map (toRInt F E) := Ideal.mem_map_of_mem _ hc
  first
  | exact Ideal.mul_mem_right _ _ h1
  | exact Ideal.mul_mem_right t _ h1
  | exact Ideal.mul_mem_right t h1
  | exact (P.map (toRInt F E)).mul_mem_right t h1

theorem b_eps_mem (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) : bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  have hmax : (P.asIdeal.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hnle : ¬ P.asIdeal.under (𝓞 F) ≤ v.asIdeal := fun hle =>
    hP (hmax.eq_of_le v.isPrime.ne_top hle)
  obtain ⟨π, hπ, hπv⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v π hπv
  rw [← hρ]
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ

theorem b_one_sub_eps_mem (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : 1 - bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨π, hπ, hπv⟩ := b_pi v
  obtain ⟨ρ, hρ⟩ := b_off_inv (E := E) v π hπv
  rw [← hρ]
  rw [← hP] at hπ
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ

theorem tpOff_proof' (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E) := by
  rw [← b_eps_mul_unit v u hu]
  exact Ideal.mul_mem_right _ _ (b_eps_mem v P hP)

end B

section B2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem b_approx (D : 𝓞 F) (hD : D ≠ 0) (s : RInt F E) :
    ∃ (b : 𝓞 E) (t : RInt F E), s = toRInt F E b + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  obtain ⟨b, t, ht, h⟩ := csGlob_approx csGlob_intAdApprox D hD (s : AfE F E) s.2
  refine ⟨b, ⟨t, ht⟩, Subtype.ext ?_⟩
  rw [h]
  show _ = ((toRInt F E b : RInt F E) : AfE F E) +
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) : RInt F E) : AfE F E) * t
  rw [b_toRInt_alg, b_toRInt_val]
  rfl

theorem b_under_elt (P : HeightOneSpectrum (𝓞 E)) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 E) D ∈ P.asIdeal := by
  have hne : P.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨D, hD0, hD⟩

theorem tpApprox_proof' (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E) :
    ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
  obtain ⟨b, t, h⟩ := b_approx D hD0 s
  refine ⟨b, ?_⟩
  rw [h, add_sub_cancel_left]
  exact b_mul_mem_map _ _ hD t

theorem b_map_shape (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0)
    (s : RInt F E) (hs : s ∈ I.map (toRInt F E)) :
    ∃ c ∈ I, ∃ t : RInt F E, s = toRInt F E c + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  unfold Ideal.map at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, hc, 0, by rw [mul_zero, add_zero]⟩
  | zero => exact ⟨0, I.zero_mem, 0, by rw [mul_zero, add_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨c', hc', t', rfl⟩ := hy
    exact ⟨c + c', I.add_mem hc hc', t + t', by rw [map_add]; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨b, t', rfl⟩ := b_approx D hD0 a
    refine ⟨b * c, I.mul_mem_left b hc, toRInt F E b * t + t' * toRInt F E c +
      toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t' * t, ?_⟩
    rw [smul_eq_mul, map_mul]; ring

theorem b_comap (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0) (hD : algebraMap (𝓞 F) (𝓞 E) D ∈ I)
    (c : 𝓞 E) (hc : toRInt F E c ∈ I.map (toRInt F E)) : c ∈ I := by
  obtain ⟨c', hc', t, h⟩ := b_map_shape I D hD0 _ hc
  have hDE : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E]
    exact adelstab_algebraMap_ne_zero D hD0
  set d : E := algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) with hd
  have h1 : ((t : RInt F E) : AfE F E) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    have h2 := congrArg (fun z : RInt F E => (z : AfE F E)) h
    simp only [Subring.coe_add, Subring.coe_mul, b_toRInt_val] at h2
    have h3 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d * (t : AfE F E) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d *
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
      rw [← map_mul, mul_div_cancel₀ _ hDE, map_sub, h2]
      ring
    have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d) := (IsUnit.mk0 d hDE).map _
    exact hu.mul_left_cancel h3
  have hint : IsIntegral ℤ ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    apply csGlob_int (F := F)
    rw [← h1]
    exact t.2
  let m : 𝓞 E := ⟨_, hint⟩
  have hm : c - c' = algebraMap (𝓞 F) (𝓞 E) D * m := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (c - c') = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D * m)
    rw [map_sub, map_mul]
    show _ = d * ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d)
    rw [mul_div_cancel₀ _ hDE]
  have : c = c' + algebraMap (𝓞 F) (𝓞 E) D * m := by rw [← hm]; ring
  rw [this]
  exact I.add_mem hc' (I.mul_mem_right _ hD)

theorem tpComap_proof' (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E)
    (hc : toRInt F E c ∈ P.asIdeal.map (toRInt F E)) : c ∈ P.asIdeal := by
  obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
  exact b_comap P.asIdeal D hD0 hD c hc

theorem b_pow_mem (z : RInt F E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), z ∈ P.asIdeal.map (toRInt F E))
    (I : Ideal (𝓞 E)) : I ≠ 0 → ∃ k : ℕ, z ^ k ∈ I.map (toRInt F E) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff] at hx
    exact ⟨0, by rw [hx, Ideal.map_top]; trivial⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨k, hk⟩ := ih ha
    refine ⟨k + 1, ?_⟩
    rw [Ideal.map_mul, pow_succ']
    exact Ideal.mul_mem_mul (hz ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩) hk

theorem b_plc_ne_zero (v : HeightOneSpectrum (𝓞 F)) : plc v ≠ 0 := by
  have := ringChar.charP (𝓞 F ⧸ v.asIdeal)
  exact CharP.char_ne_zero_of_finite (𝓞 F ⧸ v.asIdeal) (plc v)

theorem tpWild_proof' (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v := by
  refine ⟨⟨u, ?_, rfl⟩, hu⟩
  rw [SetLike.mem_coe, mem_kerRed]
  have hne : Ideal.span {((plc v : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact b_plc_ne_zero v
  obtain ⟨k, hk⟩ := b_pow_mem _ h _ hne
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at hk
  exact ⟨k, hk⟩

end B2

section B3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem b_intU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) :
    ∃ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u = x := by
  rw [intU, Submonoid.mem_units_iff] at hx
  refine ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩

theorem b_mkU (v : HeightOneSpectrum (𝓞 F)) (b c : 𝓞 E) (r : 𝓞 F) (hr : r ∉ v.asIdeal)
    (hbc : b * c = algebraMap (𝓞 F) (𝓞 E) r) :
    ∃ u : (RInt F E)ˣ, (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v) := by
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v r hr
  have hi := b_eps_idem (E := E) v
  rw [← hbc, map_mul] at hρ
  refine ⟨⟨toRInt F E b * bEps E v + (1 - bEps E v), toRInt F E c * ρ * bEps E v + (1 - bEps E v), ?_, ?_⟩, rfl⟩
  · have : (toRInt F E b * bEps E v + (1 - bEps E v)) * (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring
  · have : (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) * (toRInt F E b * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring

theorem b_mkU_supp (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v := by
  rw [b_mem_suppAt]
  intro v' hv'
  show prV (E := E) v' ((u : RInt F E) : AfE F E) = 1
  rw [hu]
  show prV (E := E) v' (((toRInt F E b : RInt F E) : AfE F E) * afsplitEps E v + (1 - afsplitEps E v)) = 1
  rw [map_add, map_mul, map_sub, afsplit_prV_eps_ne v v' hv', mul_zero, map_one, sub_zero, zero_add]

theorem b_exists_mul (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hb : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → b ∉ P.asIdeal) :
    ∃ (c : 𝓞 E) (r : 𝓞 F), r ∉ v.asIdeal ∧ b * c = algebraMap (𝓞 F) (𝓞 E) r := by
  by_contra hcon
  push Not at hcon
  have hle : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {b}) ≤ v.asIdeal := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
    obtain ⟨c, hc⟩ := hr
    by_contra hrv
    exact hcon c r hrv hc.symm
  have := v.isPrime
  obtain ⟨Q, hQ, hQp, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (Ideal.span {b}) hle
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  exact hb ⟨Q, hQp, hQ0⟩ hQv (hQ (Ideal.mem_span_singleton_self b))

theorem tpExU_proof' (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) (a : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  classical
  obtain ⟨b0, hb0⟩ := Ideal.Quotient.mk_surjective (a : 𝓞 E ⧸ P.asIdeal)
  have hb0P : b0 ∉ P.asIdeal := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, hb0] at h
    have : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    exact a.ne_zero h
  have hmap0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact v.ne_bot
  have hfin := Ideal.finite_factors hmap0
  have hmemT : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.under (𝓞 F) = v.asIdeal → P' ∈ hfin.toFinset := by
    intro P' hP'
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP']
  obtain ⟨b', hb'⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun Q => if (Q : HeightOneSpectrum (𝓞 E)) = P then b0 else 1)
  have hbP : b' - b0 ∈ P.asIdeal := by
    have := hb' P (hmemT P hPv)
    rwa [if_pos rfl, pow_one] at this
  have hbP' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal →
      b' - 1 ∈ P'.asIdeal := by
    intro P' hne hP'
    have := hb' P' (hmemT P' hP')
    rwa [if_neg hne, pow_one] at this
  have hnot : ∀ Q : HeightOneSpectrum (𝓞 E), Q.asIdeal.under (𝓞 F) = v.asIdeal → b' ∉ Q.asIdeal := by
    intro Q hQ hmem
    by_cases h : Q = P
    · subst h
      apply hb0P
      have := Q.asIdeal.sub_mem hmem hbP
      rwa [sub_sub_cancel] at this
    · apply Q.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := Q.asIdeal.sub_mem hmem (hbP' Q h hQ)
      rwa [sub_sub_cancel] at this
  obtain ⟨c, r, hr, hbc⟩ := b_exists_mul v b' hnot
  obtain ⟨u, hu⟩ := b_mkU v b' c r hr hbc
  refine ⟨u, b0, hb0, b_mkU_supp v b' u hu, ?_, ?_⟩
  · have : (u : RInt F E) - toRInt F E b0 =
        toRInt F E (b' - b0) * bEps E v + (1 - toRInt F E b0) * (1 - bEps E v) := by
      rw [hu, map_sub]; ring
    rw [this]
    exact Ideal.add_mem _ (b_mul_mem_map _ _ hbP _) (Ideal.mul_mem_left _ _ (b_one_sub_eps_mem v P hPv))
  · intro P' hne
    have : (u : RInt F E) - 1 = toRInt F E (b' - 1) * bEps E v := by
      rw [hu, map_sub, map_one]; ring
    rw [this]
    by_cases hP' : P'.asIdeal.under (𝓞 F) = v.asIdeal
    · exact b_mul_mem_map _ _ (hbP' P' hne hP') _
    · exact Ideal.mul_mem_left _ _ (b_eps_mem v P' hP')

def bUnder (F : Type) [Field F] [NumberField F] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 F) :=
  ⟨P.asIdeal.under (𝓞 F), have := P.isPrime; inferInstance, Ideal.under_ne_bot (𝓞 F) P.ne_bot⟩

variable {L : Type} [Field L]

theorem b_same (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (u u' : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (hu' : Units.map (RInt F E).subtype.toMonoidHom u' ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u' ∈ P.asIdeal.map (toRInt F E)) :
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom u') := by
  have hw : Units.map (RInt F E).subtype.toMonoidHom (u * u'⁻¹) ∈ wildAt E v := by
    apply tpWild_proof'
    · rw [map_mul, map_inv]
      exact mul_mem hu (inv_mem hu')
    · intro P
      have : ((u * u'⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 = ((u : RInt F E) - u') * ((u'⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.mul_inv, Units.val_mul]
      rw [this]
      exact Ideal.mul_mem_right _ _ (h P)
  have h1 := hξ v hw
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem residue_character_exists : ResCharEx := by
  intro F E _ _ _ _ _ L _ ξ hξ P
  classical
  set v := bUnder F P with hv
  have hPv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  choose U B hB hU hUP hUP' using tpExU_proof' P v hPv
  have key : ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
      ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom (U a)) := by
    intro u a b hb hu huP huP'
    apply b_same ξ hξ v u (U a) hu (hU a)
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      have hbb : b - B a ∈ Q.asIdeal := by
        rw [← Ideal.Quotient.eq, hb, hB]
      have : (u : RInt F E) - U a = ((u : RInt F E) - toRInt F E b) - ((U a : RInt F E) - toRInt F E (B a)) +
          toRInt F E (b - B a) := by rw [map_sub]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.sub_mem _ huP (hUP a)) (Ideal.mem_map_of_mem _ hbb)
    · have : (u : RInt F E) - U a = ((u : RInt F E) - 1) - ((U a : RInt F E) - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (huP' Q hQ) (hUP' a Q hQ)
  let χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ := MonoidHom.mk' (fun a => ξ (Units.map (RInt F E).subtype.toMonoidHom (U a))) (by
    intro a a'
    rw [← map_mul, ← map_mul]
    symm
    apply key (U a * U a') (a * a') (B a * B a')
    · rw [map_mul, hB, hB, Units.val_mul]
    · rw [map_mul]; exact mul_mem (hU a) (hU a')
    · have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - toRInt F E (B a * B a') =
          ((U a : RInt F E) - toRInt F E (B a)) * (U a' : RInt F E) +
            toRInt F E (B a) * ((U a' : RInt F E) - toRInt F E (B a')) := by
        rw [map_mul, Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP a)) (Ideal.mul_mem_left _ _ (hUP a'))
    · intro P' hP'
      have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - 1 =
          ((U a : RInt F E) - 1) * (U a' : RInt F E) + ((U a' : RInt F E) - 1) := by
        rw [Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP' a P' hP')) (hUP' a' P' hP'))
  refine ⟨χ, ?_, ?_⟩
  · intro v' hv' u a b hb hu huP huP'
    have : v' = v := HeightOneSpectrum.ext (hv'.symm.trans hPv)
    subst this
    exact key u a b hb hu huP huP'
  · intro χ' hχ'
    ext a
    rw [← hχ' v hPv (U a) a (B a) (hB a) (hU a) (hUP a) (hUP' a)]
    rfl

theorem b_resChar_spec (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : IsResChar ξ P (resChar ξ P) := by
  have h : ∃ χ, IsResChar ξ P χ := (residue_character_exists F E L ξ hξ P).exists
  rw [resChar, dif_pos h]
  exact h.choose_spec

theorem residue_character_mul : ResCharMul := by
  intro F E _ _ _ _ _ L _ ξ η hξ hη P
  have hξη : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (ξ * η).ker := fun v =>
    (kills Lˣ (wildAt E v)).mul_mem (hξ v) (hη v)
  apply (residue_character_exists F E L (ξ * η) hξη P).unique (b_resChar_spec _ hξη P)
  intro v hv u a b hb hu huP huP'
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, b_resChar_spec ξ hξ P v hv u a b hb hu huP huP',
    b_resChar_spec η hη P v hv u a b hb hu huP huP']

end B3

section B4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem auxiliary_primes_finite : QprimeFinite := by
  intro F E _ _ _ _ _ L _ ξ hξ
  obtain ⟨N, hN, hker⟩ := hξ
  have hN0 : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hN.ne'
  apply (Ideal.finite_factors hN0).subset
  intro v hv
  rw [Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hNv
  apply hv
  refine le_trans ?_ hker
  rintro x ⟨hx1, hx2⟩
  obtain ⟨u, rfl⟩ := b_intU x hx1
  refine ⟨u, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_kerRed, ← b_eps_mul_unit v u hx2]
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v _ hNv
  rw [← hρ, map_natCast, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem under_eq_of_le_lemma {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal) : P.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : v.asIdeal ≤ P.asIdeal.under (𝓞 F) := Ideal.map_le_iff_le_comap.mp h
  exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h1).symm

theorem b_under_of_split (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ P'.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_right
    | exact le_trans Ideal.mul_le_inf inf_le_left
    | exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right _ _ hr)
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P'.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_left
    | exact le_trans Ideal.mul_le_inf inf_le_right
    | exact Ideal.mul_le.mpr (fun r _ s hs => Ideal.mul_mem_left _ _ hs)
  exact ⟨under_eq_of_le_lemma h1, under_eq_of_le_lemma h2⟩

private theorem hs_eq_lemma_2 {P Q : HeightOneSpectrum (𝓞 E)} (h : P.asIdeal = Q.asIdeal) : P = Q := by
  first
  | exact HeightOneSpectrum.ext h
  | (cases P; cases Q; cases h; rfl)

theorem b_other_of_split (v : HeightOneSpectrum (𝓞 F)) (P P' Q : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (hQ : Q ≠ P) (hQ' : Q ≠ P') :
    Q.asIdeal.under (𝓞 F) ≠ v.asIdeal := by
  intro hQv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hQv.symm)
  rw [h] at hle
  rcases (Ideal.IsPrime.mul_le Q.isPrime).mp hle with h1 | h1
  · exact hQ (hs_eq_lemma_2 (P.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)
  · exact hQ' (hs_eq_lemma_2 (P'.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)

theorem b_mkU_idF (v : HeightOneSpectrum (𝓞 F)) (n : 𝓞 F) (hn : n ∉ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ (idF F E).range := by
  set nv := algebraMap (𝓞 F) (v.adicCompletion F) n with hnv
  have hn0 : nv ≠ 0 := b_alg_ne_zero v n hn
  have hmul : (afsplitI v nv + (1 - afsplitI v 1)) * (afsplitI v nv⁻¹ + (1 - afsplitI v 1)) = 1 := by
    refine FiniteAdeleRing.ext _ fun w => ?_
    by_cases h : w = v
    · subst h
      simp only [afsplit_mul_apply, afsplit_add_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_self, sub_self,
        add_zero]
      exact mul_inv_cancel₀ hn0
    · simp only [afsplit_mul_apply, afsplit_add_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_ne v w h,
        sub_zero, zero_add, mul_one]
  refine ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, ?_⟩
  apply Units.ext
  show (1 : E) ⊗ₜ[F] (afsplitI v nv + (1 - afsplitI v 1)) = ((u : RInt F E) : AfE F E)
  rw [hu]
  show _ = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) : RInt F E) : AfE F E) * afsplitEps E v + (1 - afsplitEps E v)
  rw [b_toRInt_alg, b_eps_val, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.one_def,
    ← TensorProduct.tmul_sub, ← TensorProduct.tmul_add]
  congr 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplit_mul_apply, afsplitI_self, afsplitI_self, mul_one]
    rfl
  · rw [afsplit_mul_apply, afsplitI_ne v w h, afsplitI_ne v w h, mul_zero]

theorem residue_character_conj : ResCharConj := by
  intro F E _ _ _ _ _ L _ ξ hξ hF v P P' hne hsplit n a a' ha ha'
  obtain ⟨hPv, hP'v⟩ := b_under_of_split v P P' hsplit
  have hn : n ∉ v.asIdeal := by
    intro h
    rw [← hPv] at h
    have h0 : (a : 𝓞 E ⧸ P.asIdeal) = 0 := by
      rw [ha, Ideal.Quotient.eq_zero_iff_mem]; exact h
    have : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    exact a.ne_zero h0
  obtain ⟨u, hu⟩ := b_mkU (E := E) v (algebraMap (𝓞 F) (𝓞 E) n) 1 n hn (mul_one _)
  have husupp := b_mkU_supp v _ u hu
  have hun : ∀ Q : HeightOneSpectrum (𝓞 E), Q.asIdeal.under (𝓞 F) = v.asIdeal →
      (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q hQ
    have : (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) =
        (1 - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) * (1 - bEps E v) := by rw [hu]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (b_one_sub_eps_mem v Q hQ)
  obtain ⟨u1, b1, hb1, hu1, hu1P, hu1P'⟩ := tpExU_proof' P v hPv a
  have h1 := b_resChar_spec ξ hξ P v hPv u1 a b1 hb1 hu1 hu1P hu1P'
  have h2 := b_resChar_spec ξ hξ P' v hP'v (u * u1⁻¹) a' (algebraMap (𝓞 F) (𝓞 E) n) ha'.symm
    (by rw [map_mul, map_inv]; exact mul_mem husupp (inv_mem hu1))
    (by
      have : ((u * u1⁻¹ : (RInt F E)ˣ) : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) =
          (((u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) -
            toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) * ((u1 : RInt F E) - 1)) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        have e : (u1 : RInt F E) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) = 1 := Units.mul_inv u1
        rw [Units.val_mul]
        linear_combination (toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) * e
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (hun P' hP'v) (Ideal.mul_mem_left _ _ (hu1P' P' hne.symm))))
    (by
      intro Q hQ
      have : ((u * u1⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 =
          ((u : RInt F E) - u1) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.mul_inv, Units.val_mul]
      rw [this]
      apply Ideal.mul_mem_right
      by_cases hQP : Q = P
      · subst hQP
        have hbb : algebraMap (𝓞 F) (𝓞 E) n - b1 ∈ Q.asIdeal := by
          rw [← Ideal.Quotient.eq, hb1, ha]
        have : (u : RInt F E) - u1 = ((u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) -
            ((u1 : RInt F E) - toRInt F E b1) + toRInt F E (algebraMap (𝓞 F) (𝓞 E) n - b1) := by
          rw [map_sub]; ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.sub_mem _ (hun Q hPv) hu1P) (Ideal.mem_map_of_mem _ hbb)
      · have hoff := b_other_of_split v P P' Q hsplit hQP hQ
        have : (u : RInt F E) - u1 = ((u : RInt F E) - 1) - ((u1 : RInt F E) - 1) := by ring
        rw [this]
        exact Ideal.sub_mem _ (tpOff_proof' v Q hoff u husupp) (tpOff_proof' v Q hoff u1 hu1))
  rw [← h1, ← h2, ← map_mul, ← map_mul, mul_comm, inv_mul_cancel_right]
  exact hF (b_mkU_idF v n hn u hu)

theorem tilde_local : TildeLocal := by
  intro F E _ _ _ _ _ L _ σ ξ hσ hξ hF P v hPv u a b hb hu huP huP'
  rw [tilde_norm_quotient σ ξ (norm_quotient_ker_le σ ξ hσ hF)]
  exact b_resChar_spec ξ hξ P v hPv u a b hb hu huP huP'

end B4

def TpExU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)

def TpWild : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ),
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
    (∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) →
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v

def TpApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E), ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E)

def TpComap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), toRInt F E c ∈ P.asIdeal.map (toRInt F E) → c ∈ P.asIdeal

def TpOff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) ≠ v.asIdeal →
    ∀ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)

section D1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem d_under {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal := by
  exact (b_under_of_split v P P' hv).1

theorem d_absNorm_map (hdeg : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal) = Ideal.absNorm v.asIdeal ^ 2 := by
  rw [← Ideal.absNorm_relNorm (R := 𝓞 F), Ideal.relNorm_algebraMap, map_pow,
    ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hdeg]

def d_resMap (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : (𝓞 F ⧸ v.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) (le_of_eq h.symm)

theorem d_resMap_inj (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : Function.Injective (d_resMap v P h) := by
  first
  | exact Ideal.quotientMap_injective' (le_of_eq h)
  | (unfold d_resMap
     exact Ideal.quotientMap_injective' (le_of_eq h))
  | (haveI := v.isMaximal
     letI := Ideal.Quotient.field v.asIdeal
     haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial P.isPrime.ne_top
     exact RingHom.injective _)

theorem d_finite_quot (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot

theorem d_absNorm_le (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm P.asIdeal := by
  haveI := d_finite_quot P
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_injective _ (d_resMap_inj v P h)

theorem d_absNorm_eq (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  have hP := d_absNorm_le v P (d_under hv)
  have hP' := d_absNorm_le v P' (d_under (P := P') (P' := P) (by rw [hv, mul_comm]))
  have hmul := d_absNorm_map hdeg v
  rw [hv, map_mul] at hmul
  have hpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm v.asIdeal ≤
      Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal := by
    calc _ ≤ Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal := Nat.mul_le_mul le_rfl hP'
      _ = _ := by rw [hmul, sq]
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) hP

theorem d_resMap_surj (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Function.Surjective (d_resMap v P (d_under hv)) := by
  have hi := d_resMap_inj v P (d_under hv)
  haveI := d_finite_quot P
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) ≤ Nat.card (𝓞 F ⧸ v.asIdeal) := by
    have := d_absNorm_eq hdeg hv
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at this
    exact this.le
  exact (hi.bijective_of_nat_card_le hc).2

theorem d_res_one (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (b : 𝓞 E) :
    ∃ n : 𝓞 F, b - algebraMap (𝓞 F) (𝓞 E) n ∈ P.asIdeal := by
  obtain ⟨x, hx⟩ := d_resMap_surj hdeg hv (Ideal.Quotient.mk P.asIdeal b)
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq]
  first
  | exact hx.symm
  | simpa [d_resMap] using hx.symm

theorem d_exists_place (F : Type) [Field F] [NumberField F] (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), plc v = p := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨M, hM, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  have hpM : ((p : ℕ) : 𝓞 F) ∈ M := by
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hover.over, Ideal.under_def, Ideal.mem_comap] at h1
    simpa using h1
  have hne : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpM
    exact hp.ne_zero (by exact_mod_cast hpM)
  refine ⟨⟨M, hM.isPrime, hne⟩, ?_⟩
  show ringChar (𝓞 F ⧸ M) = p
  have : Nontrivial (𝓞 F ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM.ne_top
  have h0 : ((p : ℕ) : 𝓞 F ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hpM
  exact ((Nat.dvd_prime hp).mp (ringChar.dvd h0)).resolve_left CharP.ringChar_ne_one

end D1

section D2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom

theorem d_isRes (hEx : ResCharEx) (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : IsResChar ξ P (resChar ξ P) := by
  have h : ∃ χ, IsResChar ξ P χ := (hEx F E L ξ ht P).exists
  rw [resChar, dif_pos h]
  exact h.choose_spec

theorem d_isUnit_mk (P : HeightOneSpectrum (𝓞 E)) {b : 𝓞 E} (hb : b ∉ P.asIdeal) :
    IsUnit (Ideal.Quotient.mk P.asIdeal b) := by
  first
  | (obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hb
     refine isUnit_of_mul_eq_one _ (Ideal.Quotient.mk P.asIdeal y) ?_
     rw [← map_mul, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
     have e : b * y - 1 = -i := by rw [← hyi]; ring
     rw [e]
     exact P.asIdeal.neg_mem hi)
  | (haveI := P.isMaximal
     letI := Ideal.Quotient.field P.asIdeal
     exact isUnit_iff_ne_zero.mpr (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)))

theorem d_lift_intU {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u : (RInt F E)ˣ, uIn u = x := by
  exact b_intU x hx

theorem d_mem_intU (u : (RInt F E)ˣ) : uIn u ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff]
  exact ⟨u.1.2, (u⁻¹).1.2⟩

theorem d_not_mem (hC : TpComap) (P : HeightOneSpectrum (𝓞 E)) (u : (RInt F E)ˣ) (b : 𝓞 E)
    (h : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E)) : b ∉ P.asIdeal := by
  intro hb
  have h1 : toRInt F E b ∈ P.asIdeal.map (toRInt F E) := Ideal.mem_map_of_mem _ hb
  have h2 : (u : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := add_mem h h1
    rwa [sub_add_cancel] at this
  have h3 : (1 : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := Ideal.mul_mem_left _ ((u⁻¹ : (RInt F E)ˣ) : RInt F E) h2
    rwa [Units.inv_mul] at this
  have h4 : (1 : 𝓞 E) ∈ P.asIdeal := hC F E P 1 (by rw [map_one]; exact h3)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h4)

theorem d_other {v : HeightOneSpectrum (𝓞 F)} {P P' Q : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (h1 : Q ≠ P) (h2 : Q ≠ P') :
    Q.asIdeal.under (𝓞 F) ≠ v.asIdeal := by
  exact b_other_of_split v P P' Q hv h1 h2

theorem d_formula (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hdeg : Module.finrank F E = 2)
    (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (hF : (idF F E).range ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal)
    (x : (AfE F E)ˣ) (hx : x ∈ inertAt E v) :
    ∃ a a'' : (𝓞 E ⧸ P.asIdeal)ˣ, ξ x = resChar ξ P a * (resChar ξ P a'')⁻¹ := by
  have hv' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal := by rw [hv, mul_comm]
  have hPv := d_under hv
  have hPv' := d_under hv'
  obtain ⟨u, rfl⟩ := d_lift_intU hx.1
  have hsu := hx.2
  obtain ⟨b, hb⟩ := hA F E P (u : RInt F E)
  obtain ⟨b', hb'⟩ := hA F E P' (u : RInt F E)
  obtain ⟨n, hn⟩ := d_res_one hdeg hv' b'
  have hun : (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) := by
    have h1 : toRInt F E (b' - algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) :=
      Ideal.mem_map_of_mem _ hn
    have h2 := add_mem hb' h1
    rw [map_sub] at h2
    convert h2 using 1
    ring
  have hbP := d_not_mem hC P u b hb
  have hnP' := d_not_mem hC P' u _ hun
  have hnv : n ∉ v.asIdeal := by
    intro h
    apply hnP'
    rw [← hPv'] at h
    exact h
  have hnP : algebraMap (𝓞 F) (𝓞 E) n ∉ P.asIdeal := by
    intro h
    apply hnv
    rw [← hPv]
    exact h
  obtain ⟨a, ha⟩ := d_isUnit_mk P hbP
  obtain ⟨a', ha'⟩ := d_isUnit_mk P' hnP'
  obtain ⟨a'', ha''⟩ := d_isUnit_mk P hnP
  have hc := hConj F E L ξ ht hF v P P' hne hv n a'' a' ha'' ha'
  obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v hPv a
  obtain ⟨u2, b2, hb2, hs2, hc2, ho2⟩ := hExU F E P' v hPv' a'
  have e1 : ξ (uIn u1) = resChar ξ P a := d_isRes hEx ξ ht P v hPv u1 a b1 hb1 hs1 hc1 ho1
  have e2 : ξ (uIn u2) = resChar ξ P' a' := d_isRes hEx ξ ht P' v hPv' u2 a' b2 hb2 hs2 hc2 ho2
  have hdiff : ∀ Q : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u1 * u2 ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q
    by_cases h1 : Q = P
    · subst h1
      have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ hc1
      have t3 := Ideal.mul_mem_left _ (toRInt F E b1) (ho2 Q hne)
      have t4 : toRInt F E (b1 - b) ∈ Q.asIdeal.map (toRInt F E) :=
        Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb1.trans ha))
      have t := sub_mem (sub_mem (sub_mem hb t2) t3) t4
      rw [map_sub] at t
      convert t using 1
      ring
    · by_cases h2 : Q = P'
      · subst h2
        have t2 := Ideal.mul_mem_right (u1 : RInt F E) _ hc2
        have t3 := Ideal.mul_mem_left _ (toRInt F E b2) (ho1 Q hne.symm)
        have t4 : toRInt F E (b2 - algebraMap (𝓞 F) (𝓞 E) n) ∈ Q.asIdeal.map (toRInt F E) :=
          Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb2.trans ha'))
        have t := sub_mem (sub_mem (sub_mem hun t2) t3) t4
        rw [map_sub] at t
        convert t using 1
        ring
      · have hQ := d_other hv h1 h2
        have t1 := hO F E v Q hQ u hsu
        have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ (hO F E v Q hQ u1 hs1)
        have t3 := hO F E v Q hQ u2 hs2
        have t := sub_mem (sub_mem t1 t2) t3
        convert t using 1
        ring
  have hw : uIn (u * (u1 * u2)⁻¹) ∈ wildAt E v := by
    apply hW F E v
    · rw [map_mul, map_inv, map_mul]
      exact mul_mem hsu (inv_mem (mul_mem hs1 hs2))
    · intro Q
      have h1 : ((u * (u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 =
          ((u : RInt F E) - u1 * u2) * (((u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.val_mul, ← Units.val_mul u1 u2, Units.mul_inv]
      rw [h1]
      exact Ideal.mul_mem_right _ _ (hdiff Q)
  have hk : ξ (uIn (u * (u1 * u2)⁻¹)) = 1 := MonoidHom.mem_ker.mp (ht v hw)
  simp only [map_mul, map_inv] at hk
  rw [e1, e2] at hk
  refine ⟨a, a'', ?_⟩
  rw [mul_inv_eq_one.mp hk, eq_inv_of_mul_eq_one_right hc]

theorem d_key (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hdeg : Module.finrank F E = 2)
    (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (hF : (idF F E).range ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (m : ℕ) :
    (∀ x ∈ inertAt E v, ξ x ^ m = 1) ↔ resChar ξ P ^ m = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v (d_under hv) a
    have e1 := d_isRes hEx ξ ht P v (d_under hv) u1 a b1 hb1 hs1 hc1 ho1
    rw [MonoidHom.pow_apply, ← e1, MonoidHom.one_apply]
    exact h _ ⟨d_mem_intU u1, hs1⟩
  · intro h x hx
    obtain ⟨a, a'', e⟩ := d_formula hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv x hx
    have h1 : ∀ c, resChar ξ P c ^ m = 1 := fun c => by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [e, mul_pow, inv_pow, h1, h1, inv_one, mul_one]

end D2

theorem residue_character_ramified_of_quadratic (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (_ : Module.finrank F E = 2) (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      (v ∈ Qprime ξ ↔ resChar ξ P ≠ 1) := by
  intro F E _ _ _ _ _ hdeg L _ ξ ht hF v P P' hne hv
  have hk := d_key hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv 1
  simp only [pow_one] at hk
  rw [Ne, ← hk]
  exact not_congr ⟨fun h x hx => MonoidHom.mem_ker.mp (h hx), fun h x hx => MonoidHom.mem_ker.mpr (h x hx)⟩

theorem inert_order_residue_of_quadratic (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (_ : Module.finrank F E = 2) (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      ∀ n : ℕ, InertOrd ξ v n ↔ orderOf (resChar ξ P) = n := by
  intro F E _ _ _ _ _ hdeg L _ ξ ht hF v P P' hne hv n
  have hk := fun m => d_key hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv m
  unfold InertOrd
  constructor
  · intro h
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hk n).mp ((h n).mpr dvd_rfl))
    · exact (h _).mp ((hk _).mpr (pow_orderOf_eq_one _))
  · rintro rfl m
    rw [hk m, orderOf_dvd_iff_pow_eq_one]

theorem base_prime_of_quadratic (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hDO : DegOnePlc) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (_ : Module.finrank F E = 2) (L : Type) [Field L]
    (S : Set ℕ) (p : ℕ) (δ : Tup F E L S), IsBaseChar p (δ : Chr F E L) → p % 15 = 1 := by
  intro F E _ _ _ _ _ hdeg L _ S p δ h
  obtain ⟨v, hvp⟩ := d_exists_place F p h.1
  obtain ⟨⟨P, P', hne, hv⟩, hd1, _⟩ := IsBaseChar.good δ h v hvp
  have hm := (mem_tupGrp (δ : Chr F E L)).mp δ.2
  have ht := hm.2.2.1
  have hF := hm.2.1
  have hord := (h.2 v).1 hvp
  have hk := d_key hExU hW hA hC hO hEx hConj hdeg (δ : Chr F E L) ht hF v P P' hne hv (p - 1)
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = p := by
    have h1 := d_absNorm_eq hdeg hv
    rw [hDO F v hd1, hvp, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    exact h1
  have hpow : resChar (δ : Chr F E L) P ^ (p - 1) = 1 := by
    apply MonoidHom.ext
    intro a
    rw [MonoidHom.pow_apply, ← map_pow, MonoidHom.one_apply]
    have ha : a ^ (p - 1) = 1 := by
      have := P.isMaximal
      let _ := Ideal.Quotient.field P.asIdeal
      have hc : Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = p - 1 :=
        (Nat.card_units (α := 𝓞 E ⧸ P.asIdeal)).trans (by rw [hcard])
      rw [← hc]
      exact pow_card_eq_one'
    rw [ha, map_one]
  have h15 : 15 ∣ p - 1 := (hord (p - 1)).mp (hk.mpr hpow)
  have h2 := h.1.two_le
  omega

theorem d_finrank_of_conj {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsConjOf σ) : Module.finrank F E = 2 := by
  obtain ⟨hne, hinv, hfix⟩ := h
  have hex : ∃ e, σ e ≠ e := by
    by_contra hc
    push Not at hc
    exact hne (AlgHom.ext hc)
  obtain ⟨e0, he0⟩ := hex
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = e0 - σ e0 := ⟨_, rfl⟩
  have hθ0 : θ ≠ 0 := fun h => he0 (sub_eq_zero.mp (hθ ▸ h)).symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hinv]; ring
  have h2 : (2 : E) ≠ 0 := by
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    exact two_ne_zero
  have h2' : algebraMap F E 2 = 2 := map_ofNat _ 2
  let f : (F × F) →ₗ[F] E := LinearMap.coprod (Algebra.linearMap F E) (LinearMap.toSpanSingleton F E θ)
  have hf : ∀ a b, f (a, b) = algebraMap F E a + b • θ := fun a b => by simp [f]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hab' : algebraMap F E a - b • θ = 0 := by
      have := congrArg σ hab
      rw [map_add, map_smul, hσθ, AlgHom.commutes, map_zero, smul_neg] at this
      rw [sub_eq_add_neg]
      exact this
    have ha : algebraMap F E a = 0 := by
      have : (2 : E) * algebraMap F E a = 0 := by linear_combination hab + hab'
      exact (mul_eq_zero.mp this).resolve_left h2
    have hb : b • θ = 0 := by rw [ha, zero_add] at hab; exact hab
    have ha' : a = 0 := (map_eq_zero _).mp ha
    have hb' : b = 0 := (smul_eq_zero.mp hb).resolve_right hθ0
    rw [ha', hb']
    rfl
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨a, ha⟩ := hfix (e + σ e) (by rw [map_add, hinv]; ring)
    obtain ⟨b, hb⟩ := hfix ((e - σ e) / θ) (by
      rw [map_div₀, map_sub, hinv, hσθ, div_neg, ← neg_div, neg_sub])
    refine ⟨(a / 2, b / 2), ?_⟩
    rw [hf, Algebra.smul_def, map_div₀, map_div₀, ha, hb, h2']
    field_simp
    ring
  have hfin := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [← hfin, Module.finrank_prod, Module.finrank_self]

theorem twist_exists_unit : TpExU := by
  intro F E _ _ _ _ _ P v h a
  exact tpExU_proof' P v h a

theorem twist_wild_trivial : TpWild := by
  intro F E _ _ _ _ _ v u hu h
  exact tpWild_proof' v u hu h

theorem twist_approximation : TpApprox := by
  intro F E _ _ _ _ _ P s
  exact tpApprox_proof' P s

theorem twist_comap : TpComap := by
  intro F E _ _ _ _ _ P c hc
  exact tpComap_proof' P c hc

theorem twist_off_support : TpOff := by
  intro F E _ _ _ _ _ v P hP u hu
  exact tpOff_proof' v P hP u hu

theorem residue_character_ramified : ResCharRam := fun F E _ _ _ _ _ L _ hdeg =>
  residue_character_ramified_of_quadratic twist_exists_unit twist_wild_trivial twist_approximation twist_comap twist_off_support residue_character_exists
    residue_character_conj F E hdeg L

theorem inert_order_residue : InertOrdRes := fun F E _ _ _ _ _ L _ hdeg =>
  inert_order_residue_of_quadratic twist_exists_unit twist_wild_trivial twist_approximation twist_comap twist_off_support residue_character_exists
    residue_character_conj F E hdeg L

theorem base_prime_condition : BasePrime := fun F E _ _ _ _ _ L _ hdeg =>
  base_prime_of_quadratic twist_exists_unit twist_wild_trivial twist_approximation twist_comap twist_off_support residue_character_exists
    residue_character_conj degree_one_places F E hdeg L

end Formalism.L2.DIV

end
