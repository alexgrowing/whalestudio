import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSelfDual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_top_of_unram [Algebra.Unramified (𝓞 F) (𝓞 E)] : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := inferInstance
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hd : P ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
  exact (dvd_differentIdeal_iff.mp hd) inferInstance

theorem mem_of_trace [Algebra.Unramified (𝓞 F) (𝓞 E)] (x : E)
    (hx : ∀ a : 𝓞 E, Algebra.trace F E (x * a) ∈ (algebraMap (𝓞 F) F).range) : x ∈ (algebraMap (𝓞 E) E).range := by
  have h1 := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
  rw [differentIdeal_eq_top_of_unram, FractionalIdeal.coeIdeal_top] at h1
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 := by
    rw [← inv_inv (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)), ← h1, inv_one]
  have : x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    exact hx a'
  rw [hdual, FractionalIdeal.mem_one_iff] at this
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem exists_traceFamily [Algebra.Unramified (𝓞 F) (𝓞 E)] :
    ∃ (k : ℕ) (s c : Fin k → 𝓞 E), ∀ e : E, ∑ i, Algebra.trace F E ((c i : E) * e) • (s i : E) = e := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := F) (E := E)
  let D := LinearMap.BilinForm.toDual (Algebra.traceForm F E) (traceForm_nondegenerate F E)
  have hD : ∀ j x, Algebra.trace F E (D.symm (φ j) * x) = φ j x := fun j x => by
    have := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm F E)
      (hB := traceForm_nondegenerate F E) (φ j) x
    rw [Algebra.traceForm_apply] at this
    exact this
  have hc : ∀ j, D.symm (φ j) ∈ (algebraMap (𝓞 E) E).range := fun j =>
    mem_of_trace _ fun a => by rw [hD]; exact hφ a j
  choose c hc' using hc
  refine ⟨k, s, c, fun e => ?_⟩
  conv_rhs => rw [← hsum e]
  refine Finset.sum_congr rfl fun j _ => ?_
  show Algebra.trace F E (algebraMap (𝓞 E) E (c j) * e) • _ = _
  rw [hc', hD]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h2 : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  intro h0
  have hd := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg] at hd
  rw [Matrix.det_one, mul_one, Fintype.card_fin] at hd
  exact (pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0)) hd.symm

theorem det_ne_zero_of_herm (σ : E →ₐ[F] E) (B : Base F E) {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem det_ne_zero_of_skew (σ : E →ₐ[F] E) (B : Base F E) {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem exists_formFrame (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (hdual : ∀ y, (∀ x ∈ L, form σ J y x ∈ (algebraMap (𝓞 E) E).range) → y ∈ L) :
    ∃ (k : ℕ) (S T : Matrix (Fin n) (Fin k) E), (∀ j, (fun i => S i j) ∈ L) ∧ (∀ j, (fun i => T i j) ∈ L) ∧
      T * (J * S.map σ)ᵀ = 1 := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := GlobalTheory.AdelicU.SelfDual.exists_frame L hL
  have hJu : IsUnit J.det := Ne.isUnit hJ
  have hJtu : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  refine ⟨k, S, (Jᵀ)⁻¹ * (Φ.map σ)ᵀ, hS, fun j => hdual _ fun x hx => ?_, ?_⟩
  · have h2 : ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ)ᵀ * J = Φ.map σ := by
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
  · rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Φ.map σ)ᵀ, ← Matrix.transpose_mul,
      ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hJtu]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem inclR_smul (t : F) (x : E) :
    inclR (F := F) (AF F) (t • x) = algebraMap F (AF F) t • inclR (F := F) (AF F) x := by
  show (1 : AF F) ⊗ₜ[F] (t • x) = _
  rw [TensorProduct.tmul_smul, algebraMap_smul]
  rfl

theorem trace_expand {k : ℕ} (s c : Fin k → 𝓞 E)
    (hsc : ∀ e : E, ∑ i, Algebra.trace F E ((c i : E) * e) • (s i : E) = e) (u : AE F E) :
    u = ∑ i, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (c i : E) * u) • inclR (F := F) (AF F) (s i : E) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • inclR (F := F) (AF F) e := by
      show _ = a • ((1 : AF F) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1]
    simp_rw [mul_smul_comm, map_smul, ← map_mul, trace_inclR, smul_eq_mul]
    conv_lhs => rw [← hsc e]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inclR_smul, smul_smul]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [mul_add, map_add, add_smul, Finset.sum_add_distrib]

theorem incM_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) E) (B : Matrix (Fin n) (Fin p) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem decomp {n d k k' : ℕ} (T : Matrix (Fin n) (Fin k) E) (P : Matrix (Fin k) (Fin n) E)
    (T' : Matrix (Fin d) (Fin k') E) (P' : Matrix (Fin k') (Fin d) E) (h : T * P = 1) (h' : T' * P' = 1)
    (z : Matrix (Fin n) (Fin d) (AE F E)) :
    z = ∑ j, ∑ l, (incM F P * z * (incM F P')ᵀ) j l • incM F (Matrix.vecMulVec (fun i => T i j) (fun i => T' i l)) := by
  have key : incM F T * (incM F P * z * (incM F P')ᵀ) * (incM F T')ᵀ = z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← incM_mul, h, incM_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← incM_mul, h', incM_one, Matrix.transpose_one, Matrix.mul_one]
  conv_lhs => rw [← key]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, incM, Matrix.map_apply,
    Matrix.vecMulVec_apply, map_mul, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hTens_frame (σ : E →ₐ[F] E) {n d k k' : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (S : Matrix (Fin n) (Fin k) E) (S' : Matrix (Fin d) (Fin k') E) (z : Matrix (Fin n) (Fin d) (AE F E)) (e : E)
    (j : Fin k) (l : Fin k') :
    hTens (cA σ) (incM F JA) (incM F JB) z (incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l))) =
      inclR (F := F) (AF F) (σ e) * (incM F (JA * S.map σ)ᵀ * z * (incM F (JB * S'.map σ)ᵀ)ᵀ) j l := by
  simp only [hTens, incM, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply,
    cA_inclR, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertSelfDual

namespace GlobalTheory.InertSelfDual

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw z hz
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V G.W _ _ _ _ hT.base hV hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hT.base.unram
    have hunr : PsiUnr B.ψ v := (hT.base.inert v w hvw).2.2
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, hTS⟩ := exists_formFrame σ G.V.J (det_ne_zero_of_herm σ B hV) G.V.L hV.lat
      (fun y hy => (hV.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTS'⟩ := exists_formFrame σ G.W.J (det_ne_zero_of_skew σ B hW) G.W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (G.V.J * S.map σ)ᵀ * z * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (G.V.J * S.map σ)ᵀ * (u • z) * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (σ e) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ G.V.L := by
        have := G.V.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV G.V G.W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      have := (hunr _).1 key
      rw [htC, map_neg] at this
      exact neg_mem_iff.1 this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (G.V.J * S.map σ)ᵀ T' (G.W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, fun u hu => ?_, hint' i j l, fun r => (s i : E) * T r j, ?_, fun r => T' r l, hTm' l, ?_⟩
    · rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    · have := G.V.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    · rw [smul_assoc]
      congr 1
      ext p q
      simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
      ring

end GlobalTheory.InertSelfDual
