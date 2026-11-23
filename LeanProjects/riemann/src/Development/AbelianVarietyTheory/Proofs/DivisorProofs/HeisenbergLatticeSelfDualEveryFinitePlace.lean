import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

noncomputable section
namespace GlobalTheory.LatSelfDualAll

section Scalar
variable {F : Type} [Field F] [NumberField F]

theorem exists_codiff_sub {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) (c : Fv F v)
    (h : ∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (c * y) = 1) :
    ∃ f : F, f ∈ codiff F ∧ c - algebraMap F (Fv F v) f ∈ v.adicCompletionIntegers F := by
  set α : Af F := singleFin v c with hα
  have hmem : α ∈ adelicIdeal (codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)]
    intro β hβ
    have e : β * α = singleFin v (c * β v) := by
      apply af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, hα, evalV_singleFin_self, evalV_singleFin_self]
        change β u * c = c * β u
        ring
      · rw [map_mul, hα, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
    rw [e]
    exact h _ (hβ v)
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) α
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hle : α - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun w => (hx1 w).trans ?_
    have := FractionalIdeal.count_mono F w (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have hxc : algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    have := sub_mem hmem hle
    rwa [sub_sub_cancel] at this
  refine ⟨x, (algebraMap_mem_adelicIdeal codiff_ne_zero x).1 hxc, ?_⟩
  have h2 := hx1 v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  convert h2 using 2
  change c - _ = evalV F v (α - algebraMap F (Af F) x)
  rw [map_sub, hα, evalV_singleFin_self]
  rfl

end Scalar

section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_of_codiff (σ : E →ₐ[F] E) (B : Base F E) {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s)
    {f : F} (hf : f ∈ codiff F) {y : Fin d → E} (hy : ∀ x ∈ W.L, form σ W.J y x ∈ (algebraMap (𝓞 E) E).range) :
    f • y ∈ W.L := by
  refine (hW.dual _).2 fun x hx o => ?_
  have hform : form σ W.J (f • y) x = algebraMap F E f * form σ W.J y x := by
    rw [form, form, smul_dotProduct, Algebra.smul_def]
  obtain ⟨q, hq⟩ := hy x hx
  set e : E := (o : E) * form σ W.J y x with he
  have hei : IsIntegral ℤ e := (RingOfIntegers.isIntegral_coe o).mul (by rw [← hq]; exact RingOfIntegers.isIntegral_coe q)
  have h1 : Algebra.trace ℚ E ((o : E) * form σ W.J (f • y) x) = Algebra.trace ℚ F (f * Algebra.trace F E e) := by
    rw [hform, ← Algebra.trace_trace (S := F)]
    congr 1
    rw [he, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have ht : IsIntegral ℤ (Algebra.trace F E e) := Algebra.isIntegral_trace hei
  have hm := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 hf
    ((⟨_, ht⟩ : 𝓞 F) : F) ((FractionalIdeal.mem_one_iff _).2 ⟨⟨_, ht⟩, rfl⟩)
  rw [Algebra.traceForm_apply] at hm
  obtain ⟨k, hk⟩ := hm
  rw [h1]
  change IsIntegral ℤ (Algebra.trace ℚ F (f * ((⟨_, ht⟩ : 𝓞 F) : F)))
  rw [← hk]
  exact isIntegral_algebraMap

end Lat

end GlobalTheory.LatSelfDualAll

namespace GlobalTheory.LatSelfDualAll

section Frame
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_formFrame' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (hdual : ∀ y, (∀ x ∈ L, form σ J y x ∈ (algebraMap (𝓞 E) E).range) → y ∈ L) :
    ∃ (k : ℕ) (S T : Matrix (Fin n) (Fin k) E), (∀ j, (fun i => S i j) ∈ L) ∧ (∀ j, (fun i => T i j) ∈ L) ∧
      (∀ j, ∀ x ∈ L, form σ J (fun i => T i j) x ∈ (algebraMap (𝓞 E) E).range) ∧ T * (J * S.map σ)ᵀ = 1 := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := GlobalTheory.AdelicU.SelfDual.exists_frame L hL
  have hJu : IsUnit J.det := Ne.isUnit hJ
  have hJtu : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  have hT : ∀ j, ∀ x ∈ L, form σ J (fun i => ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ) i j) x ∈ (algebraMap (𝓞 E) E).range := by
    intro j x hx
    have h2 : ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ)ᵀ * J = Φ.map σ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.mul_one]
    have e : form σ J (fun i => ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ) i j) x = σ ((Φ *ᵥ x) j) := by
      calc form σ J (fun i => ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ) i j) x
          = (((((Jᵀ)⁻¹ * (Φ.map σ)ᵀ)ᵀ * J) *ᵥ fun i => σ (x i)) j) := by
            simp only [form, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
              Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = σ ((Φ *ᵥ x) j) := by
            rw [h2]; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]; exact GlobalTheory.AdelicU.SelfDual.sig_mem_range σ (hΦ x hx j)
  refine ⟨k, S, (Jᵀ)⁻¹ * (Φ.map σ)ᵀ, hS, fun j => hdual _ (hT j), hT, ?_⟩
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Φ.map σ)ᵀ, ← Matrix.transpose_mul,
    ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ hJtu]

end Frame

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_latAtV (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d}
    (hstd : IsStd B.ψ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (v : Pl F) {t : AF F} (ht : At (evFin F v) t)
    (hψ : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1) {x : Fin n → E} (hx : x ∈ X.L)
    {y : Fin d → E} (hy : y ∈ W.L) (hyd : ∀ x' ∈ W.L, form σ W.J y x' ∈ (algebraMap (𝓞 E) E).range) :
    t • incM F (Matrix.vecMulVec x y) ∈ latAtV X W v := by
  obtain ⟨f, hf, hfc⟩ := exists_codiff_sub hstd v (evFin F v t) hψ
  have ht' : t = GlobalTheory.LatVac.liftV v (evFin F v t) := by
    rw [← GlobalTheory.LatVacArith.liftV_one_mul]; exact GlobalTheory.LatVacArith.eq_liftV_of_at ht
  have hsplit : t = f • GlobalTheory.LatVac.liftV v 1 + GlobalTheory.LatVac.liftV v (evFin F v t - algebraMap F (Fv F v) f) := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, ← ht']
    abel
  rw [hsplit, add_smul]
  refine add_mem (AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _, x, hx, f • y, smul_mem_of_codiff σ B hW hf hyd, ?_⟩)
    (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV _ _, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hfc, x, hx, y, hy,
      rfl⟩)
  ext p q
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, mul_smul_comm,
    GlobalTheory.InertSelfDual.inclR_smul, smul_assoc]
  rw [← algebraMap_smul (AF F) f, smul_smul, smul_smul, mul_comm]

end Gen

end GlobalTheory.LatSelfDualAll

namespace GlobalTheory.LatSelfDualAll

open GlobalTheory.InertSelfDual (exists_traceFamily det_ne_zero_of_herm det_ne_zero_of_skew decomp hTens_frame trace_expand)

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B n d X W r₁ s₁ r₂ s₂ hB hX hW v z hz
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W _ _ _ _ hB hX hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hB.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, -, hTS⟩ := exists_formFrame' σ X.J (det_ne_zero_of_herm σ B hX) X.L hX.lat
      (fun y hy => (hX.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTd', hTS'⟩ := exists_formFrame' σ W.J (det_ne_zero_of_skew σ B hW) W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (X.J * S.map σ)ᵀ * z * (incM F (W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (X.J * S.map σ)ᵀ * (u • z) * (incM F (W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, ∀ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l)) * y) = 1 := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ X.L := by
        have := X.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV X W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      intro y hy
      have := key (-y) (neg_mem hy)
      rwa [htC, map_neg, neg_mul_neg] at this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) * y) = 1 := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (X.J * S.map σ)ᵀ T' (W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have hxi : (fun r => (s i : E) * T r j) ∈ X.L := by
      have := X.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    have hat : At (evFin F v) (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (c i : E) * C j l)) := by
      intro u hu
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    have hmem := smul_mem_latAtV σ B hB.std hX hW v hat (hint' i j l) hxi (hTm' l) (hTd' l)
    convert hmem using 1
    rw [smul_assoc]
    congr 1
    ext p q
    simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
    ring

end GlobalTheory.LatSelfDualAll
