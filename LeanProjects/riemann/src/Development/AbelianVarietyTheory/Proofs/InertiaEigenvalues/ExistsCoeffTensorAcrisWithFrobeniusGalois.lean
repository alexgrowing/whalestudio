import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.MemLoc GlobalTheory.ExpImage
open scoped Formalism.Per

namespace GlobalTheory.HWLCris

section

variable {l : ℕ} [Fact l.Prime]

theorem alg_alg (a : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) a) = algebraMap (Per.Ainf l) (Per.Acris l) a :=
  (GlobalTheory.RingIface.tower l a).symm

theorem exists_acris (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) :
    ∃ (W : Type) (_ : CommRing W) (a : Ainf l →+* W) (c : W →+* P.R.B) (φ : W →+* W)
      (γ : GQ l → (W →+* W)) (t : W), GlobalTheory.Decompl.LAdic.Good l W ∧ (∀ w, c (a w) = AI.ιA w) ∧
      (∀ w, φ (a w) = a (WittVector.frobenius w)) ∧ (∀ x, c (φ x) = P.φB (c x)) ∧
      (∀ g w, γ g (a w) = a (AI.actW g w)) ∧ (∀ g x, c (γ g x) = P.actQ g (c x)) ∧ c t = P.tB ∧
      (l : W) ∣ a AI.μ ^ (l - 1) ∧
      (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : W, ((n.factorial : ℕ) : W) * u =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : W) * a AI.μ ^ (k + 1) ∧
        t - u = (l : W) ^ r * z) ∧
      ∀ m : ℕ, ∃ N : ℕ, ∀ x : W, (l : P.R.BdR) ^ N * P.ιB (c x) ∈ Lat AI m 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  have hlog : IsLogA AI.ε C.t := hC.ε ▸ C.t_log
  have hc : ∀ x, T.eB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := fun x => T.eB.apply_symm_apply _
  haveI := (acris_basic l).1
  refine ⟨Per.Acris l, inferInstance, algebraMap (Per.Ainf l) (Per.Acris l),
    T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l)), phiA l, fun g => sigA g, C.t,
    GlobalTheory.Decompl.LAdic.good_of_complete l _ (acris_basic l).2.1, fun w => T.eB.injective ?_, fun w => ?_,
    fun x => T.eB.injective ?_, fun g w => ?_, fun g x => T.eB.injective ?_, T.eB.injective ?_, ?_,
    fun r => ?_, fun m => ?_⟩
  · rw [hc, T.ιA]
    exact (GlobalTheory.RingIface.aB_eq_alg l w).symm
  · rw [← GlobalTheory.RingBasics.φA_apply]
    exact (GlobalTheory.CrisMaps.phiA_extends l).alg w
  · rw [T.frob, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 x).symm
  · rw [locAinf_actW]
    exact (GlobalTheory.CrisMaps.sigA_extends g).alg w
  · rw [T.actB, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 g x).symm
  · rw [hc, hC.t]
    rfl
  · obtain ⟨w, hw, -⟩ := exists_mu_pow_div l AI.ε he.1
    have hw' : ((l : ℕ) : Per.Acris0 l) * w =
        algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε) ^ (l - 1) :=
      Subtype.ext (by simpa using hw)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw'
    rw [map_mul, map_natCast, map_pow, alg_alg] at h2
    exact ⟨_, h2.symm⟩
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs, z, hz⟩ := hN n hn
    refine ⟨_, z, ?_, hz⟩
    have hs' : ((n.factorial : ℕ) : Per.Acris0 l) * s =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.Acris0 l) *
          (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε)) ^ (k + 1) := by
      apply Subtype.val_injective
      rw [← Subalgebra.val_apply, ← Subalgebra.val_apply]
      simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, AlgHom.commutes]
      exact hs
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hs'
    simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, alg_alg] at h2
    exact h2
  · obtain ⟨j, hj, -, hb⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
    obtain ⟨N, hN⟩ := hb m
    refine ⟨N, fun x => ?_⟩
    obtain ⟨a, h'⟩ := hN x
    refine ⟨a, ?_⟩
    have h1 : T.eD (P.ιB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x)) =
        algebraMap (Per.BdRp l) (Per.BdR l) (j x) := hj x
    rw [T.fil, pow_zero, one_mul, map_sub, map_mul, map_pow, map_natCast, h1, io_apply,
      TiedUnif.eD_ιA T, ← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_pow, ← map_mul,
      ← map_sub]
    refine TiedUnif.alg_mem_FilD m ?_
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h', TiedUnif.ev_aDp, sub_self]

end

variable {l : ℕ} [Fact l.Prime]

theorem root_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem dvd_sub_pow {R : Type} [CommRing R] (x : R) (s : ℕ) :
    (l : R) ∣ (x - 1) ^ l ^ s - (x ^ l ^ s - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) (x - 1) 1 s
  rw [sub_add_cancel, one_pow] at hr
  rw [hr]
  exact ⟨-((x - 1) * 1 * r), by ring⟩

theorem bounded_OL (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (LL : FinExt l)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ) :
    ∃ k : ℕ, ∀ o : ↥(OL LL), (l : P.R.BdR) ^ k * ι (o : ↥LL.1) ∈ Lat AI m 0 := by
  let e := GlobalTheory.Decompl.basisO LL
  choose k hk using fun i => (bounded_and_eventually_sub_mem_Lat l P AI T _
    (EmbFil.emb_mem_fil_zero l P AI T LL ι (e i : ↥LL.1)) m 0).1
  refine ⟨∑ i, k i, fun o => ?_⟩
  have ho : o ∈ Submodule.span ℤ_[l] (Set.range e) := e.mem_span o
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le'
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    rw [hj, pow_add, mul_assoc]
    exact Lat_anti AI (Nat.zero_le _) ((pow_mul_mem_Lat_iff AI).2 (hk i))
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add, mul_add]
    exact add_mem hx hy
  | smul z x _ hx =>
    have := qB_mul_mem_Lat AI T z hx
    rw [Subalgebra.coe_smul, ← algebraMap_smul ℚ_[l] z, map_smul, Algebra.smul_def, mul_left_comm]
    exact this

set_option maxHeartbeats 800000 in

theorem exists_tensor_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  intro l _ P AI T LL β hβ
  obtain ⟨W, _, a, c, φ, γ, t, hg, hca, hφa, hcφ, hγa, hcγ, hct, hμ, hlog, hb⟩ := exists_acris P AI T
  let _ : Algebra ℤ_[l] W := (a.comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  have hz : ∀ z : ℤ_[l], algebraMap ℤ_[l] W z = a (algebraMap ℤ_[l] (Ainf l) z) := fun _ => rfl
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f₁ : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let f₂ : W →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp c
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (c (a (algebraMap ℤ_[l] (Ainf l) z))) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hca, ιA_zl AI T, AlgHom.commutes]
        rfl }
  obtain ⟨κ, hκ⟩ : ∃ κ : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B,
      ∀ o x, κ (o ⊗ₜ[ℤ_[l]] x) = (o : ↥LL.1) ⊗ₜ[ℚ_[l]] c x := by
    refine ⟨(Algebra.TensorProduct.productMap f₁ f₂).toRingHom, fun o x => ?_⟩
    show Algebra.TensorProduct.productMap f₁ f₂ (o ⊗ₜ[ℤ_[l]] x) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] c x) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨b, hb'⟩ : ∃ b : RA LL →+* ↥(OL LL) ⊗[ℤ_[l]] W,
      ∀ o w, b (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] a w :=
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := a, commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  have ext : ∀ f : W →+* W, (∀ z, f (algebraMap ℤ_[l] W z) = algebraMap ℤ_[l] W z) →
      ∃ F : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥(OL LL) ⊗[ℤ_[l]] W,
        ∀ o x, F (o ⊗ₜ[ℤ_[l]] x) = o ⊗ₜ[ℤ_[l]] f x := fun f hf =>
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := f, commutes' := hf } : W →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ := ext φ fun z => by
    rw [hz, hφa, WittVector.frobenius_eq_map_frobenius]
    exact congrArg a (map_zlW l _ z)
  choose Γ hΓ using fun g => ext (γ g) fun z => by rw [hz, hγa, actW_zl]
  let j : W →+* ↥(OL LL) ⊗[ℤ_[l]] W := (Algebra.TensorProduct.includeRight (R := ℤ_[l])).toRingHom
  have hj : ∀ w, b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) = j (a w) := fun w => hb' 1 w
  refine ⟨↥(OL LL) ⊗[ℤ_[l]] W, inferInstance, b, κ, Φ, Γ, j t,
    GlobalTheory.Decompl.LAdic.good_tensor (GlobalTheory.Decompl.basisO LL) l hg, ⟨fun y => ?_, fun o w => ?_, fun x => ?_,
    fun g o w => ?_, fun g x => ?_, ?_⟩, fun s => ?_, fun r => ?_, fun ι m => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hb', hκ, hca, hβ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΦ, hφa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΦ, hκ, hκ, hcφ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΓ, hγa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΓ, hκ, hκ, hcγ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [← hct]
    exact hκ 1 t
  · have hl : 1 < l := (Fact.out : l.Prime).one_lt
    refine ⟨l ^ s * (l - 1), Nat.mul_pos (by positivity) (by omega), ?_⟩
    have h1 := dvd_sub_pow (l := l) (WittVector.teichmuller l (AI.εroot s)) s
    rw [← map_pow, root_pow] at h1
    have h2 := map_dvd a (h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1)))
    rw [map_natCast, map_sub, map_pow a (_ - 1) (l - 1)] at h2
    have h3 := map_dvd j (dvd_add h2 hμ)
    rw [LocAinf.μ, sub_add_cancel, map_natCast, ← pow_mul, map_pow, map_pow] at h3
    rwa [hj]
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨u, z, h1, h2⟩ := hN n hn
    refine ⟨j u, j z, ?_, ?_⟩
    · have := congrArg j h1
      simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at this
      rwa [hj]
    · have := congrArg j h2
      rwa [map_sub, map_mul, map_pow, map_natCast] at this
  · obtain ⟨k, hk⟩ := bounded_OL P AI T LL ι m
    obtain ⟨N, hN⟩ := hb m
    refine ⟨k + N, fun y => ?_⟩
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, mul_zero]
      exact zero_mem _
    | tmul o w =>
      rw [hκ, Algebra.TensorProduct.productMap_apply_tmul, pow_add, mul_mul_mul_comm]
      exact Lat_anti AI (Nat.zero_le _) (Lat_mul AI (hk o) (hN w))
    | add x y hx hy =>
      rw [map_add, map_add, mul_add]
      exact add_mem hx hy

end GlobalTheory.HWLCris
