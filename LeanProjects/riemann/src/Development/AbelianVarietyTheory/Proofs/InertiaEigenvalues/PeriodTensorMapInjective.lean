import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrisInj

theorem li_of_frac {W O F L ι : Type*} [CommRing W] [IsDomain W] [CommRing O] [Algebra W O] [Field F] [Field L]
    [Algebra F L] (o : O →+* L) (ho : Function.Injective o) (hW : Function.Injective (algebraMap W O))
    (hfrac : ∀ y : F, ∃ w s : W, s ≠ 0 ∧ algebraMap F L y * o (algebraMap W O s) = o (algebraMap W O w))
    (v : ι → O) (hv : LinearIndependent W v) : LinearIndependent F fun i => o (v i) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  choose w d hd h using hfrac
  have h1 : ∑ k ∈ s, (w (g k) * ∏ m ∈ s.erase k, d (g m)) • v k = 0 := ho (by
    rw [map_zero, map_sum, ← mul_zero (o (algebraMap W O (∏ m ∈ s, d (g m)))), ← hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_prod_erase s _ hk, Algebra.smul_def, Algebra.smul_def]
    simp only [map_mul]
    rw [← h]
    ring)
  have h2 : w (g i) = 0 :=
    (mul_eq_zero.1 (hv s _ h1 i hi)).resolve_right (Finset.prod_ne_zero_iff.2 fun m _ => hd _)
  have h3 := h (g i)
  rw [h2, map_zero, map_zero] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact (algebraMap F L).injective (h4.trans (map_zero _).symm)
  · exact absurd (hW (ho (h4.trans (by rw [map_zero, map_zero])))) (hd _)

theorem eq_zero_of_sum_tmul {F V B ι : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B]
    [Fintype ι] {v : ι → V} (hv : LinearIndependent F v) {β : ι → B} (h : ∑ i, v i ⊗ₜ[F] β i = 0) (i : ι) :
    β i = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply i : (ι →₀ F) →ₗ[F] F).comp hv.repr)
  have h1 : ∀ k, φ (v k) = (Finsupp.single k (1 : F)) i := fun k => by
    have hm : v k ∈ Submodule.span F (Set.range v) := Submodule.subset_span ⟨k, rfl⟩
    have := LinearMap.congr_fun hφ ⟨v k, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv.repr_eq_single k ⟨v k, hm⟩ rfl] at this
    exact this
  have h2 := congrArg (fun x => TensorProduct.lid F B (φ.rTensor B x)) h
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, map_zero, Finsupp.single_apply] at h2
  simpa using h2

theorem exists_coord {W A O ι : Type*} [CommRing W] [CommRing A] [CommRing O] [Algebra W A] [Algebra W O]
    [Fintype ι] (b : Module.Basis ι W O) (z : A ⊗[W] O) : ∃ a : ι → A, z = ∑ i, a i ⊗ₜ[W] b i := by
  refine ⟨fun i => (Algebra.TensorProduct.basis A b).repr z i, ?_⟩
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem injective_abstract {A O C S F L B ι : Type*} [CommRing A] [CommRing O] [CommRing C] [CommRing S] [Field F]
    [Field L] [Algebra F L] [CommRing B] [Algebra F B] [Fintype ι] (p : A →+* C) (q : O →+* C) (t : C →+* S)
    (o : O →+* L) (κ : L →+* S) (hκ : ∀ c, κ (o c) = t (q c)) (v : ι → O)
    (hv : LinearIndependent F fun i => o (v i)) (hC : ∀ z : C, ∃ a : ι → A, z = ∑ i, p (a i) * q (v i))
    (u : S) (hu : IsUnit u) (hS : ∀ y : S, ∃ (D : ℕ) (z : C), u ^ D * y = t z) (j : A →+* B)
    (hj : Function.Injective j) (Λ : S →+* L ⊗[F] B) (h1 : ∀ c, Λ (κ c) = c ⊗ₜ[F] (1 : B))
    (h2 : ∀ a, Λ (t (p a)) = (1 : L) ⊗ₜ[F] j a) : Function.Injective Λ := by
  refine (injective_iff_map_eq_zero Λ).2 fun y hy => ?_
  obtain ⟨D, z, hz⟩ := hS y
  obtain ⟨a, rfl⟩ := hC z
  have h3 := congrArg Λ hz
  rw [map_mul, hy, mul_zero, map_sum, map_sum] at h3
  simp only [map_mul, ← hκ, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
  have h4 : ∀ i, a i = 0 := fun i => hj ((eq_zero_of_sum_tmul hv h3.symm i).trans (map_zero j).symm)
  simp only [h4, map_zero, zero_mul, Finset.sum_const_zero] at hz
  exact (hu.pow D).mul_right_eq_zero.1 hz

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem coe_thetaW (w : W0 K) :
    ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
  (algebraMap (Om l) ℂ_[l]).injective
    (congrArg Subtype.val ((intToOC_thetaW _ K w).trans (intToOC_thetaW _ (unrExt l (fK K)) w).symm))

theorem exists_frac (y : ↥(K0 K)) : ∃ w s : W0 K, s ≠ 0 ∧
    algebraMap ↥(K0 K) ↥K.1 y * oK K (algebraMap (W0 K) ↥(OL K) s) = oK K (algebraMap (W0 K) ↥(OL K) w) := by
  have hy : (y : Om l) ∈ Kunr l (fK K) := by rw [Kunr_fK]; exact y.2
  obtain ⟨w, s, hs, h⟩ := GlobalTheory.TameFrob.exists_frac l (fK K) ⟨y, hy⟩
  refine ⟨w, s, hs, Subtype.ext ?_⟩
  rw [← coe_thetaW, ← coe_thetaW] at h
  exact h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (B : Type) [CommRing B] [Algebra ↥(K0 K) B] (j : Per.Acris l →+* B),
    Function.Injective j → ∀ Λ : GlobalTheory.AcrisK.BK K →+* ↥K.1 ⊗[↥(K0 K)] B,
    (∀ c : ↥K.1, Λ (inK K c) = c ⊗ₜ[↥(K0 K)] (1 : B)) →
    (∀ a : Per.Acris l, Λ (toB K (inC K a)) = (1 : ↥K.1) ⊗ₜ[↥(K0 K)] j a) → Function.Injective Λ := by
  intro l _ K B _ _ j hj Λ h1 h2
  exact injective_abstract (inC K) (inI K) (toB K) (oK K) (inK K) (inK_oK K)
    (Module.Free.chooseBasis (W0 K) ↥(OL K))
    (li_of_frac (W := W0 K) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1) (thetaW_injective K) (exists_frac K) _
      (Module.Free.chooseBasis (W0 K) ↥(OL K)).linearIndependent)
    (fun z => (exists_coord (A := Per.Acris l) (Module.Free.chooseBasis (W0 K) ↥(OL K)) z).imp fun a ha =>
      ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _))
    (l : GlobalTheory.AcrisK.BK K) (isUnit_l K) exists_pow_mul j hj Λ h1 h2

end GlobalTheory.CrisInj
