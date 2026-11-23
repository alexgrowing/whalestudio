import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitResidue

theorem exists_isUnit_map_eq {A B : Type} [CommRing A] [CommRing B] [IsArtinianRing A] (φ : A →+* B) (a : A)
    (ha : IsUnit (φ a)) : ∃ b b' : A, b * b' = 1 ∧ φ b = φ a := by
  obtain ⟨n, y, h⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at h
  have h1 : (a * y) ^ n * (a * y) = (a * y) ^ n := by
    rw [mul_pow]; linear_combination y ^ n * h
  have h2 : ∀ m : ℕ, (a * y) ^ n * (a * y) ^ m = (a * y) ^ n := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, ih, h1]
  have h3 := h2 n
  have h4 : φ (a * y) = 1 := by
    have := congrArg φ h
    rw [map_mul, map_pow, map_pow, pow_succ, mul_assoc, ← map_mul] at this
    exact (ha.pow n).mul_left_cancel (this.trans (mul_one _).symm)
  have h5 : φ ((a * y) ^ n) = 1 := by rw [map_pow, h4, one_pow]
  generalize (a * y) ^ n = e at *
  refine ⟨a * e + (1 - e), y * e + (1 - e), ?_, by simp [h5]⟩
  linear_combination e * h1 + (2 - a - y) * h3

theorem exists_unit_mod {O : Type} [CommRing O] (I J : Ideal O) (hIJ : I ⊔ J = ⊤) (N : O) (hI : N ∈ I) (hJ : N ∈ J)
    [Finite (O ⧸ Ideal.span {N})] (u : O) (hu : IsUnit (Ideal.Quotient.mk I u)) :
    ∃ b b' k : O, b * b' = 1 + N * k ∧ b - u ∈ I ∧ b - 1 ∈ J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hIJ)
  have hI' : Ideal.span {N} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hI
  have hJ' : Ideal.span {N} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hJ
  have e1 : Ideal.Quotient.mk I (u * j + i) = Ideal.Quotient.mk I u := by
    rw [Ideal.Quotient.eq, show u * j + i - u = (1 - u) * i by linear_combination u * hij]
    exact I.mul_mem_left _ hi
  have e2 : Ideal.Quotient.mk J (u * j + i) = Ideal.Quotient.mk J 1 := by
    rw [Ideal.Quotient.eq, show u * j + i - 1 = (u - 1) * j by linear_combination hij]
    exact J.mul_mem_left _ hj
  obtain ⟨b, b', h, hb⟩ := exists_isUnit_map_eq
    ((Ideal.Quotient.factor hI').prod (Ideal.Quotient.factor hJ')) (Ideal.Quotient.mk _ (u * j + i)) (by
      rw [Prod.isUnit_iff]
      refine ⟨?_, ?_⟩
      · change IsUnit (Ideal.Quotient.mk I (u * j + i))
        rw [e1]; exact hu
      · change IsUnit (Ideal.Quotient.mk J (u * j + i))
        rw [e2, map_one]; exact isUnit_one)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {N})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨b, b', k, by linear_combination hk, ?_, ?_⟩
  · exact Ideal.Quotient.eq.1 ((congrArg Prod.fst hb).trans e1)
  · exact Ideal.Quotient.eq.1 ((congrArg Prod.snd hb).trans e2)

open GlobalTheory.AdLat GlobalTheory.AdLat.RootNear

theorem exists_unit_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ)
    (b b' k : 𝓞 E) (h : b * b' = 1 + N * k) :
    ∃ y ∈ intHat F E, ∃ y' ∈ intHat F E, ∃ w ∈ intHat F E, y * y' = 1 ∧
      y = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) + (N : RA F E) * w := by
  obtain ⟨y, w, hy⟩ := GlobalTheory.TwistChar.exists_unit_lift F E N (ratHat F E b) (ratHat F E b')
    (ratHat F E k) (by rw [← RingHom.map_mul, h, RingHom.map_add, RingHom.map_one, RingHom.map_mul, map_natCast])
  refine ⟨_, (y : intHat F E).2, _, ((y⁻¹ : (intHat F E)ˣ) : intHat F E).2, _, w.2,
    congrArg Subtype.val y.mul_inv, ?_⟩
  rw [hy]
  push_cast
  rfl

theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
      finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hf : ∀ p, finPart D (e.symm p) = p.2 := fun p =>
    ((he (e.symm p)).2.symm).trans (by rw [e.apply_symm_apply])
  have hi : ∀ p, infPart D (e.symm p) = p.1 := fun p =>
    ((he (e.symm p)).1.symm).trans (by rw [e.apply_symm_apply])
  have hm : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, one_mul]
    exact map_one _
  exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, hi _, hf _, hf _⟩

theorem add_mem_idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∈ I)
    (b u : 𝓞 D.host.E) (hb : b - u ∈ I) (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E) + (N : Af D.host.F ⊗[D.host.F] D.host.E) * w -
      (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.idealHat D I := by
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E) + (N : Af D.host.F ⊗[D.host.F] D.host.E) * w -
      (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((b - u : 𝓞 D.host.E) : D.host.E) * 1 +
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : 𝓞 D.host.E) : D.host.E) * w := by
    have e1 : ((b - u : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) - u := rfl
    have e2 : (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : 𝓞 D.host.E) : D.host.E) =
        (N : Af D.host.F ⊗[D.host.F] D.host.E) :=
      map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) N
    rw [e1, e2, TensorProduct.tmul_sub]
    ring
  rw [e]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hb, 1, h1, rfl⟩) (AddSubgroup.subset_closure ⟨_, hN, w, hw, rfl⟩)

theorem exists_finUnit_congMod : ∀ (D : D7) (I J : Ideal (𝓞 D.host.E)), I ≠ ⊥ → J ≠ ⊥ → I ⊔ J = ⊤ → ∀ u : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk I u) → ∃ x : (AE D)ˣ, FinUnit x ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod I x u ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod J x 1 := by
  intro D I J hI hJ hIJ u hu
  have hS : ∀ w, w ∈ intAE D ↔ w ∈ intHat D.host.F D.host.E := fun w => by
    rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]; rfl
  obtain ⟨N, hN, hNI, hNJ⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : 𝓞 D.host.E) ∈ I ∧ (N : 𝓞 D.host.E) ∈ J := by
    refine ⟨Ideal.absNorm I * Ideal.absNorm J, mul_ne_zero ?_ ?_, ?_, ?_⟩
    · rwa [Ne, Ideal.absNorm_eq_zero_iff]
    · rwa [Ne, Ideal.absNorm_eq_zero_iff]
    · rw [Nat.cast_mul]; exact I.mul_mem_right _ I.absNorm_mem
    · rw [Nat.cast_mul]; exact J.mul_mem_left _ J.absNorm_mem
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  obtain ⟨b, b', k, h, hb, hb1⟩ := exists_unit_mod I J hIJ N hNI hNJ u hu
  obtain ⟨y, hy, y', hy', w, hw, hyy, e⟩ := exists_unit_hat D.host.F D.host.E N b b' k h
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_idele D y y' hyy
  have h1 := (hS 1).2 (one_mem _)
  refine ⟨x, ⟨hx1, ?_, ?_⟩, ?_, ?_⟩
  · rw [hx2]; exact (hS _).2 hy
  · rw [hx3]; exact (hS _).2 hy'
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod
    rw [hx2, e]
    exact add_mem_idealHat D I N hNI b u hb w ((hS w).2 hw) h1
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod
    rw [hx2, e]
    exact add_mem_idealHat D J N hNJ b 1 hb1 w ((hS w).2 hw) h1

end GlobalTheory.UnitResidue
