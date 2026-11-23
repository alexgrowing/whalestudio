import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.ValuedUnif
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.SecEval

theorem exists_quot_maps {K L C : Type*} [CommRing K] [CommRing L] [CommRing C] [Algebra K L] [Algebra K C]
    (A : Subalgebra K L) (J : Ideal A) (H : Submodule A L) (Λ : L →ₐ[K] C) (hJ : ∀ r ∈ J, Λ (r : L) = 0) :
    ∃ (ψ : (A ⧸ J) →ₐ[K] C) (Ψ : (H ⧸ J • (⊤ : Submodule A H)) →ₗ[K] C),
      (∀ x : A, ψ (Ideal.Quotient.mk J x) = Λ x) ∧ ∀ y : H, Ψ (Submodule.Quotient.mk y) = Λ y := by
  have hH : ∀ z ∈ J • (⊤ : Submodule A H), Λ (z : L) = 0 := by
    intro z hz
    refine Submodule.smul_induction_on (p := fun z : H => Λ (z : L) = 0) hz ?_ ?_
    · intro r hr m _
      rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
      have : Λ (algebraMap A L r) = 0 := hJ r hr
      rw [this, zero_mul]
    · intro x y hx hy
      rw [Submodule.coe_add, map_add, hx, hy, add_zero]
  let l : H →ₗ[K] C := Λ.toLinearMap ∘ₗ (H.subtype.restrictScalars K)
  refine ⟨Ideal.Quotient.liftₐ J (Λ.comp A.val) hJ,
    (((J • (⊤ : Submodule A H)).restrictScalars K).liftQ l (fun z hz => hH z hz)) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K (J • (⊤ : Submodule A H))).symm.toLinearMap,
    fun x => rfl, fun y => rfl⟩

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem exists_evalRp (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)
    (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C)
    (hχ : ∀ (a : B.KO) (f : X.Forms), χ (a • f) =
      algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) :
    ∃ Θ : Rp X la N →ₐ[Kp X la N] C, ∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F := by
  letI : Algebra (X.Kl la) C := ((algebraMap (Kp X la N) C).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  letI : Algebra B.KO C := ((algebraMap (Kp X la N) C).comp
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X.Kl la) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X.Kl la) (Kp X la N) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X.Forms →ₐ[B.KO] C :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X.Vl la →ₐ[X.Kl la] C :=
    Algebra.TensorProduct.lift (Algebra.ofId (X.Kl la) C) g (fun _ _ => Commute.all _ _)
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId (Kp X la N) C) vl (fun _ _ => Commute.all _ _), fun F => ?_⟩
  rw [emb_apply]
  erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
  erw [map_one, map_one, one_mul, one_mul]
  rfl

theorem exists_section_maps : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL u : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C), (∀ (a : B.KO) (f : X.Forms), χ (a • f) = algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) → (∀ i : Fin (WeightFamilies.dimY D j), ∑ k, algebraMap (Kp X la N) C (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (Tv X la N (i.succ, k))) * χ (X.inc wL (w k)) = 0) → IsUnit (∑ k, algebraMap (Kp X la N) C (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (Tv X la N (0, k))) * χ (X.inc wL (w k))) → ∃ (Θ : Rp X la N →ₐ[Kp X la N] C) (ψ : OsK X la w →ₐ[Kp X la N] C) (Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C), (∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F) ∧ IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) ∧ (∀ (x : OsK X la w) (a : SectionSheafQuotient X la w u), Ψ (x • a) = ψ x * Ψ a) ∧ (∀ (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))), ψ (toOsK X la w (fr0 X la w k g)) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g) ∧ ∀ f : ↥(Vw X la N u), Ψ (rho0 X la w u f) = Θ f := by
  intro D B P j X la N wL u w C _ _ χ hχ h0 h1
  obtain ⟨Θ, hΘ⟩ := exists_evalRp X la N C χ hχ
  have hsec : ∀ i, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) = ∑ k, algebraMap (Kp X la N) C
      (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (Tv X la N (i, k))) * χ (X.inc wL (w k)) := by
    intro i
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hΘ, Algebra.smul_def]
  have hu : IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := by rw [hsec]; exact h1
  have hu' : IsUnit ((Θ : Rp X la N →+* C) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := hu
  let Λ₀ : Lw X la w →+* C := IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) hu'
  have hΛ₀ : ∀ r, Λ₀ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := fun r => IsLocalization.lift_eq _ r
  let Λ : Lw X la w →ₐ[Kp X la N] C :=
    { Λ₀ with
      commutes' := fun c => by
        show Λ₀ (algebraMap (Kp X la N) (Lw X la w) c) = _
        rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), hΛ₀, AlgHom.commutes] }
  have hΛ : ∀ r, Λ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := hΛ₀
  have hinv : Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) * Λ (w0inv X la w) = 1 := by
    rw [← hΛ, ← map_mul, section_mul_inverse_eq_one, map_one]
  have hfr : ∀ (k : ℕ) (g : Rp X la N),
      Λ (frac X la w k g) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g := by
    intro k g
    rw [frac_apply, map_mul, map_pow, hΛ, mul_assoc, ← mul_pow, mul_comm (Λ _), hinv, one_pow, mul_one]
  have hJ : ∀ r ∈ Jid X la w, Λ (r : Lw X la w) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [coe_sfr, frac_apply, map_mul, hΛ, hsec, h0 i, zero_mul]
    | zero => simp
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]
  obtain ⟨ψ₀, Ψ₀, hψ₀, hΨ₀⟩ := exists_quot_maps (Frac0 X la w) (Jid X la w) (HK X la w u) Λ hJ
  let ψ : OsK X la w →ₐ[Kp X la N] C := ψ₀
  let Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C := Ψ₀
  have hψ : ∀ x, ψ (toOsK X la w x) = Λ x := hψ₀
  have hΨ : ∀ y, Ψ (toA0K X la w u y) = Λ y := hΨ₀
  refine ⟨Θ, ψ, Ψ, hΘ, hu, ?_, ?_, ?_⟩
  · intro x a
    obtain ⟨x, rfl⟩ := toOsK_surjective X la w x
    obtain ⟨y, rfl⟩ := reductionMap_surjective X la w u a
    have e : toOsK X la w x • toA0K X la w u y = toA0K X la w u (x • y) := by
      rw [map_smul]
      exact algebraMap_smul (OsK X la w) x _
    rw [e, hΨ, hΨ, hψ, Submodule.coe_smul, Algebra.smul_def, map_mul]
    rfl
  · intro k g
    rw [hψ, coe_weightZeroFraction, hfr]
  · intro f
    rw [restriction_apply_eq_reduction, hΨ, coe_toHK0, hΛ]

end GlobalTheory.SecEval
