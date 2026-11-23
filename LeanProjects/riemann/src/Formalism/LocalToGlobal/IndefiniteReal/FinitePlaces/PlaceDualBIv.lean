import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCoreApprox

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

lemma nsmul_add' {M : Type*} [AddCommGroup M] (n : ℕ) (a b : M) : n • (a + b) = n • a + n • b :=
  smul_add n a b

lemma nsmul_neg' {M : Type*} [AddCommGroup M] (n : ℕ) (a : M) : n • (-a) = -(n • a) :=
  smul_neg n a

lemma ringInt_residues {K : Type} [Field K] [NumberField K] (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (𝓞 K), ∀ x : 𝓞 K, ∃ r ∈ R, ∃ y : 𝓞 K, x = r + (N : 𝓞 K) * y := by
  classical
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI := Fintype.ofFinite (𝓞 K ⧸ I)
  refine ⟨Finset.univ.image (fun q : 𝓞 K ⧸ I => q.out), fun x => ?_⟩
  refine ⟨(Ideal.Quotient.mk I x).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h : x - (Ideal.Quotient.mk I x).out ∈ I :=
    Ideal.Quotient.eq.1 (Quotient.out_eq (Ideal.Quotient.mk I x)).symm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by linear_combination (-1 : 𝓞 K) * hy⟩

lemma finite_part_finite_embedding (w : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finiteEmbeddingTensor D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul β y => rfl
  | add w w' h h' => rw [map_add, map_add, h, h']

lemma integral_of_finite_embedding {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) : IntF (finiteEmbeddingTensor D w) :=
  ⟨by rw [mul_fI_eq, finite_part_finite_embedding], by rw [finite_part_finite_embedding]; exact hw⟩

set_option maxHeartbeats 800000 in

lemma intAE_decomp (N : ℕ) (hN : 0 < N) {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) :
    ∃ x : 𝓞 D.host.E, ∃ w' ∈ intAE D, w = (1 : Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E) + N • w' := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have hN0 : ((N : 𝓞 D.host.F)) ≠ 0 := by exact_mod_cast hN.ne'
    obtain ⟨b, c, hc, hαe⟩ := Formalism.L2.S.Pv.PsiTrCore.exists_decomp α (fun v => hα v) (N : 𝓞 D.host.F) hN0
    have hx : ∃ x : 𝓞 D.host.E, (x : D.host.E) = (b : D.host.F) • (o : D.host.E) := by
      refine ⟨⟨(b : D.host.F) • (o : D.host.E), ?_⟩, rfl⟩
      rw [Algebra.smul_def]
      exact IsIntegral.mul ((RingOfIntegers.isIntegral_coe b).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E))
        (RingOfIntegers.isIntegral_coe o)
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, c ⊗ₜ[D.host.F] (o : D.host.E), AddSubgroup.subset_closure ⟨c, fun v => hc v, o, rfl⟩, ?_⟩
    rw [hαe, TensorProduct.add_tmul, hx, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    congr 1
    have hNc : algebraMap D.host.F (Af D.host.F) (((N : 𝓞 D.host.F) : D.host.F)) = (N : Af D.host.F) := by
      have h1 : ((N : 𝓞 D.host.F) : D.host.F) = (N : D.host.F) := by push_cast; rfl
      rw [h1, map_natCast]
    rw [hNc, ← nsmul_eq_mul]
    exact (TensorProduct.smul_tmul' N c _).symm
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, w₁', hw₁', e₁⟩ := h₁
    obtain ⟨x₂, w₂', hw₂', e₂⟩ := h₂
    refine ⟨x₁ + x₂, w₁' + w₂', add_mem hw₁' hw₂', ?_⟩
    rw [e₁, e₂]
    push_cast
    rw [TensorProduct.tmul_add, nsmul_add']
    abel
  | neg w _ h =>
    obtain ⟨x, w', hw', e⟩ := h
    refine ⟨-x, -w', neg_mem hw', ?_⟩
    rw [e]
    push_cast
    rw [TensorProduct.tmul_neg, nsmul_neg']
    abel

set_option maxHeartbeats 800000 in

lemma intAE_residues (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (Af D.host.F ⊗[D.host.F] D.host.E), ∀ w ∈ intAE D, ∃ r ∈ R, ∃ w' ∈ intAE D, w = r + N • w' := by
  classical
  obtain ⟨RE, hRE⟩ := ringInt_residues (K := D.host.E) N hN
  refine ⟨RE.image (fun r : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)), fun w hw => ?_⟩
  obtain ⟨x, w', hw', e⟩ := intAE_decomp N hN hw
  obtain ⟨r, hr, y, hy⟩ := hRE x
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, y, rfl⟩
  refine ⟨_, Finset.mem_image_of_mem _ hr, (1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E) + w', add_mem h1 hw', ?_⟩
  rw [e, hy]
  push_cast
  have h2 : (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * (y : D.host.E)) =
      N • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (y : D.host.E)) := by
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul]
  rw [TensorProduct.tmul_add, h2, nsmul_add']
  abel

set_option maxHeartbeats 800000 in

lemma intF_residues (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (AE D), ∀ y : AE D, IntF y → ∃ r ∈ R, ∃ y' : AE D, IntF y' ∧ y = r + N • y' := by
  classical
  obtain ⟨R, hR⟩ := intAE_residues (D := D) N hN
  refine ⟨R.image (finiteEmbeddingTensor D), fun y hy => ?_⟩
  obtain ⟨r, hr, w', hw', e⟩ := hR _ hy.2
  refine ⟨finiteEmbeddingTensor D r, Finset.mem_image_of_mem _ hr, finiteEmbeddingTensor D w', integral_of_finite_embedding hw', ?_⟩
  have hy' : y = finiteEmbeddingTensor D (finPart D y) := by rw [← mul_fI_eq, hy.1]
  rw [hy', e, map_add, map_nsmul]

set_option maxHeartbeats 800000 in

lemma mat_residues (m n : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ R : Finset (Mx D m n), ∀ Z : Mx D m n, (∀ i j, IntF (Z i j)) →
      ∃ ρ ∈ R, ∃ Z' : Mx D m n, (∀ i j, IntF (Z' i j)) ∧ Z = ρ + N • Z' := by
  classical
  obtain ⟨R1, hR1⟩ := intF_residues (D := D) N hN
  refine ⟨(Fintype.piFinset fun _ : Fin m => Fintype.piFinset fun _ : Fin n => R1).image Matrix.of,
    fun Z hZ => ?_⟩
  choose r hr y hy hyeq using fun i j => hR1 (Z i j) (hZ i j)
  refine ⟨Matrix.of r, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 fun i =>
    Fintype.mem_piFinset.2 fun j => hr i j), Matrix.of y, hy, ?_⟩
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply]
  exact hyeq i j

set_option maxHeartbeats 800000 in
lemma nsmul_cancel_AE {x y : AE D} {k : ℕ} (hk : 0 < k) (h : k • x = k • y) : x = y := by
  have hk' : ((k : D.host.F)) ≠ 0 := by exact_mod_cast hk.ne'
  have hu : algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * algebraMap D.host.F (AE D) (k : D.host.F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hk', map_one]
  have hkc : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := (map_natCast _ k).symm
  rw [nsmul_eq_mul, nsmul_eq_mul, hkc] at h
  calc x = algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * (algebraMap D.host.F (AE D) (k : D.host.F) * x) := by
        rw [← mul_assoc, hu, one_mul]
    _ = algebraMap D.host.F (AE D) ((k : D.host.F))⁻¹ * (algebraMap D.host.F (AE D) (k : D.host.F) * y) := by
        rw [h]
    _ = y := by rw [← mul_assoc, hu, one_mul]

lemma nsmul_cancel_Mx {m n : ℕ} {X Y : Mx D m n} {k : ℕ} (hk : 0 < k) (h : k • X = k • Y) : X = Y := by
  ext i j
  apply nsmul_cancel_AE hk
  have h1 := congrFun (congrFun h i) j
  simpa using h1

set_option maxHeartbeats 800000 in

lemma exists_finset_half_decomp {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {c' : ℕ} (hc' : 0 < c') (hup : ∀ t ∈ latAll S T ΛS ΛT, ∀ i j, IntF ((c' • t) i j))
    (k : ℕ) (hk : 0 < k) (e₁ : AE D) :
    ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v := by
  classical
  obtain ⟨c, hc, hlow⟩ := lower hS hT
  obtain ⟨RL, hRL⟩ := mat_residues (D := D) T.rank S.rank (k * c * c') (Nat.mul_pos (Nat.mul_pos hk hc) hc')
  let G : WO S T → Prop := fun ρ => ∃ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u ∧
    ∃ Z : WO S T, (∀ i j, IntF (Z i j)) ∧ c' • u = ρ + (k * c * c') • Z
  let pick : WO S T → WO S T := fun ρ => if h : G ρ then h.choose else 0
  refine ⟨(RL.filter G).image pick, fun u hu hhalf => ?_⟩
  obtain ⟨ρ, hρ, Z, hZ, hEq⟩ := hRL (c' • u) (hup u hu)
  have hG : G ρ := ⟨u, hu, hhalf, Z, hZ, hEq⟩
  have hpick : pick ρ = hG.choose := dif_pos hG
  obtain ⟨hu₀, hh₀, Z₀, hZ₀, hEq₀⟩ := hG.choose_spec
  have hZZ : ∀ i j, IntF ((Z - Z₀) i j) := fun i j => by
    rw [Matrix.sub_apply, sub_eq_add_neg]; exact intF_add (hZ i j) (intF_neg (hZ₀ i j))
  have hdiff : u - hG.choose = k • (c • (Z - Z₀)) := by
    apply nsmul_cancel_Mx hc'
    rw [smul_sub, hEq, hEq₀, add_sub_add_left_eq_sub, ← smul_sub, smul_smul, smul_smul]
    congr 1
    ring
  have hlowV := hlow _ hZZ
  generalize hV : c • (Z - Z₀) = V at hdiff hlowV
  refine ⟨pick ρ, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hρ, hG⟩), V, hlowV, fun i j => ?_, ?_⟩
  · apply nsmul_cancel_AE hk
    have h1 : (k • V) i j = (u - hG.choose) i j := by rw [hdiff]
    rw [Matrix.smul_apply, Matrix.sub_apply] at h1
    rw [← mul_smul_comm, h1, mul_sub, hhalf i j, hh₀ i j]
  · rw [hpick, ← hdiff]
    abel

theorem placeLatDualIv (D : D7) : PlaceLatDualIv D := by
  intro ψ _ S T ΛS ΛT hS hT P e _ k hk e₁ _
  obtain ⟨c', hc', hup⟩ := upper hS hT
  exact exists_finset_half_decomp hS hT hc' hup k hk e₁

end Formalism.IndefR.Fin.PDB

end
