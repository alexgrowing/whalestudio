import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsTraceEqFormMulDiagonal

open IsLocalRing MvPowerSeries
open scoped TensorProduct

namespace GlobalTheory.TraceJacobian

theorem det_notMem_span (k : Type) [Field k] (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ)
    (f : σ → MvPowerSeries σ k) (a : Matrix σ σ (MvPowerSeries σ k))
    (hf : ∀ i, f i = ∑ j, a i j * X j)
    (hN : ∀ i, (X i : MvPowerSeries σ k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by
  let e := Fintype.equivFin σ
  let ρ : MvPowerSeries σ k ≃ₐ[k] MvPowerSeries (Fin (Fintype.card σ)) k := renameEquiv k e
  have hX : ∀ j, ρ (X j) = X (e j) := fun j => by simp [ρ]
  have hmap : ∀ s ∈ Ideal.span (Set.range f),
      ρ s ∈ Ideal.span (Set.range fun i => ρ (f (e.symm i))) := by
    intro s hs
    obtain ⟨u, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e j, by simp⟩)
  intro hdet
  refine SocleDet.det_notMem_span k _ N (fun i => ρ (f (e.symm i)))
    ((ρ.toAlgHom.mapMatrix a).submatrix e.symm e.symm) (fun i => ?_) (fun i => ?_) ?_
  · rw [hf, map_sum, ← e.symm.sum_comp]
    simp [hX]
  · have := hmap _ (hN (e.symm i))
    rwa [map_pow, hX, e.apply_symm_apply] at this
  · rw [Matrix.det_submatrix_equiv_self, ← AlgHom.map_det]
    exact hmap _ hdet

theorem exists_eq_C_add_sum {R σ : Type} [CommRing R] [Fintype σ] (s : MvPowerSeries σ R) :
    ∃ u : σ → MvPowerSeries σ R, s = C (constantCoeff s) + ∑ j, X j * u j := by
  have h := SocleDet.mem_span_X_of_coeff Finset.univ (s - C (constantCoeff s)) (fun m hm => by
    have : m = 0 := Finsupp.ext fun j => hm j (Finset.mem_univ j)
    subst this
    simp)
  rw [Finset.coe_univ, Set.image_univ] at h
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨u, by simp only [mul_comm (X _), hu]; ring⟩

theorem exists_ringHom_eval {A B σ : Type} [CommRing A] [CommRing B] [Finite σ] (ι : A →+* B)
    (K : Ideal B) [h : IsAdicComplete K B] (a : σ → B) (ha : ∀ j, a j ∈ K) :
    ∃ θ : MvPowerSeries σ A →+* B, (∀ c, θ (C c) = ι c) ∧ ∀ j, θ (X j) = a j := by
  letI := ι.toAlgebra
  obtain ⟨ψ, hψ⟩ := (mvPowerSeries_eval_of_pow_mem B K σ a fun j => ⟨1, by simpa using ha j⟩).1 h A
  exact ⟨ψ, fun c => ψ.commutes c, hψ⟩

open DiscrJacobian in

theorem exists_trace_eq {A B σ : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Fintype σ] [DecidableEq σ] [Algebra A B] [Algebra (MvPowerSeries σ A) B]
    [IsScalarTower A (MvPowerSeries σ A) B] [Module.Free A B] [Module.Finite A B]
    (hsurj : Function.Surjective (algebraMap (MvPowerSeries σ A) B))
    (f : σ → MvPowerSeries σ A) (hf0 : ∀ i, algebraMap _ B (f i) = 0)
    (ε : B →+* ResidueField A)
    (hε : ∀ s : MvPowerSeries σ A, ε (algebraMap _ B s) = residue A (constantCoeff s))
    (hW : ∀ a : Matrix σ σ B, (∀ i, algebraMap A B (constantCoeff (f i)) =
        ∑ j, a i j * -algebraMap (MvPowerSeries σ A) B (X j)) →
      a.det ∉ (maximalIdeal A).map (algebraMap A B)) :
    ∃ lam : B →ₗ[A] A, ∀ x : B, Algebra.trace A B x =
      lam (x * algebraMap _ B (Matrix.of fun i j => pderiv A j (f i)).det) := by
  let S := MvPowerSeries σ A
  have : Module.Finite S B := Module.Finite.of_restrictScalars_finite A S B
  have : Module.FinitePresentation S B := Module.finitePresentation_of_finite S B
  let t : σ → S ⊗[A] B := fun j => (X j : S) ⊗ₜ[A] (1 : B) - (1 : S) ⊗ₜ[A] algebraMap S B (X j)
  have hker : ∀ z : S ⊗[A] B, mu A S B z = 0 → z ∈ Ideal.span (Set.range t) :=
    mem_span_of_mu_eq_zero (fun j => (X j : S)) X_mem_jacobson fun s =>
      ⟨constantCoeff s, exists_eq_C_add_sum s⟩
  choose a ha using fun i => Ideal.mem_span_range_iff_exists_fun.1
    (hker (f i ⊗ₜ 1) (by simp [S, hf0]))
  let P : Matrix σ σ (S ⊗[A] B) := Matrix.of a
  have hmt : ∀ j, mu A S B (t j) = 0 := fun j => by simp [t]
  have hmu : ∀ i j, mu A S B (a i j) = algebraMap S B (pderiv A j (f i)) := by
    intro i j
    have := congrArg (der (S := S) (B := B) (pderiv A j)) (ha i)
    simp only [map_sum, der_mul, hmt, zero_mul, add_zero, der_tmul, mul_one] at this
    rw [← this, Finset.sum_eq_single j]
    · simp [t, S]
    · intro l _ hl
      simp [t, S, hl]
    · simp
  let q : S →ₐ[A] B := IsScalarTower.toAlgHom A S B
  let π : S ⊗[A] B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.map q (AlgHom.id A B)
  have hπ : ∀ s w, π (s ⊗ₜ w) = algebraMap S B s ⊗ₜ w := fun s w => rfl
  have hDt : ∀ z ∈ Ideal.span (Set.range t), π z * π P.det = 0 := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hz
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := SocleDet.det_mul_mem (RingHom.ker π) P t j fun r => by
      have : (P.mulVec t) r = f r ⊗ₜ 1 := ha r
      rw [this, RingHom.mem_ker, hπ, hf0, TensorProduct.zero_tmul]
    rw [RingHom.mem_ker, map_mul] at this
    rw [map_mul, mul_assoc, mul_comm (π (t j)), this, mul_zero]
  have hD : ∀ x : B, (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) * π P.det = 0 := by
    intro x
    obtain ⟨s, rfl⟩ := hsurj x
    have := hDt _ (hker (s ⊗ₜ 1 - 1 ⊗ₜ algebraMap S B s) (by simp))
    rwa [map_sub, hπ, hπ, map_one] at this
  have hJ : Algebra.TensorProduct.lmul' (S := B) A (π P.det)
      = algebraMap S B (Matrix.of fun i j => pderiv A j (f i)).det := by
    have e : ∀ z, Algebra.TensorProduct.lmul' (S := B) A (π z) = mu A S B z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s w => simp [hπ]
    rw [e, AlgHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    exact hmu i j
  rw [← hJ]
  have hεA : ∀ c, ε (algebraMap A B c) = residue A c := fun c => by
    rw [IsScalarTower.algebraMap_apply A S B, hε]
    simp [S, MvPowerSeries.algebraMap_apply]
  let m : Ideal B := (maximalIdeal A).map (algebraMap A B)
  refine exists_trace_eq_form_mul_diagonal A B _ ε (RingHom.ext hεA) (fun x hx => ?_) hD ?_
  · obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨u, hu⟩ := exists_eq_C_add_sum s
    rw [hε, residue_eq_zero_iff] at hx
    change _ ∈ m.radical
    rw [hu, map_add, map_sum]
    refine add_mem (Ideal.le_radical ?_) (Ideal.sum_mem _ fun j _ => ?_)
    · have : algebraMap S B (C (constantCoeff s)) = algebraMap A B (constantCoeff s) :=
        (IsScalarTower.algebraMap_apply A S B _).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (map_mem_radical hsurj (X_mem_jacobson j))
  · intro s hs lift hlift hmem
    let κ : ResidueField A →+* B ⧸ m :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk m).comp (algebraMap A B)) fun c hc =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hc)
    have hκ : ∀ c, κ (residue A c) = Ideal.Quotient.mk m (algebraMap A B c) := fun c => rfl
    let E : B →ₐ[A] B ⧸ m :=
      { κ.comp ε with commutes' := fun c => by simp [hεA, hκ] }
    have hE : ∀ x, E x = κ (ε x) := fun x => rfl
    let cc : S →ₐ[A] B :=
      { (algebraMap A B).comp (constantCoeff : S →+* A) with
        commutes' := fun r => by simp [S, MvPowerSeries.algebraMap_apply] }
    have hcc : ∀ s, cc s = algebraMap A B (constantCoeff s) := fun s => rfl
    let η : S ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.productMap cc (AlgHom.id A B)
    have hη : ∀ s w, η (s ⊗ₜ w) = algebraMap A B (constantCoeff s) * w := fun s w => rfl
    have e : ∀ z, Algebra.TensorProduct.productMap E (Ideal.Quotient.mkₐ A m) (π z)
        = Ideal.Quotient.mk m (η z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s w =>
        rw [hπ, hη, map_mul, ← hκ, ← hε]; rfl
    have h1 := e P.det
    rw [hs, map_sum, AlgHom.map_det] at h1
    refine hW (η.mapMatrix P) (fun i => ?_) ?_
    · have := congrArg η (ha i)
      simp only [map_sum, map_mul, hη, mul_one] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [t, hη, P, S]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, ← Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.smul_def, map_mul, ← hκ, hlift]
      rfl

theorem dvd_trace_of_ringHom {A B σ : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Fintype σ] [DecidableEq σ] (θ : MvPowerSeries σ A →+* B) (ι : A →+* B)
    (hι : ∀ c, θ (C c) = ι c) (hsurj : Function.Surjective θ)
    (f : σ → MvPowerSeries σ A) (hf0 : ∀ i, θ (f i) = 0)
    (ε : B →+* ResidueField A) (hε : ∀ s, ε (θ s) = residue A (constantCoeff s))
    (hW : ∀ a : Matrix σ σ B, (∀ i, ι (constantCoeff (f i)) = ∑ j, a i j * -θ (X j)) →
      a.det ∉ (maximalIdeal A).map ι)
    (δ : A) (U : B) (hJ : θ (Matrix.of fun i j => pderiv A j (f i)).det = ι δ * U)
    {r : ℕ} (b : Fin r → B) (hb : ∀ g, ∃! c : Fin r → A, g = ∑ i, ι (c i) * b i)
    (g : B) (M : Matrix (Fin r) (Fin r) A) (hM : ∀ j, g * b j = ∑ i, ι (M i j) * b i) :
    δ ∣ M.trace := by
  letI := ι.toAlgebra
  letI := θ.toAlgebra
  haveI : IsScalarTower A (MvPowerSeries σ A) B := IsScalarTower.of_algebraMap_eq fun c => (hι c).symm
  have hsm : ∀ (c : A) (x : B), c • x = ι c * x := fun c x => rfl
  let β : Module.Basis (Fin r) A B := Module.Basis.mk (v := b)
    (Fintype.linearIndependent_iff.2 fun c hc => by
      have := (hb 0).unique (y₁ := c) (y₂ := 0) hc.symm (by simp)
      exact congrFun this)
    (fun x _ => by
      obtain ⟨c, hc, -⟩ := hb x
      exact (Submodule.mem_span_range_iff_exists_fun A).2 ⟨c, hc.symm⟩)
  have hβ : ∀ i, β i = b i := fun i => Module.Basis.mk_apply _ _ i
  haveI : Module.Free A B := Module.Free.of_basis β
  haveI : Module.Finite A B := Module.Finite.of_basis β
  obtain ⟨lam, hlam⟩ := exists_trace_eq (A := A) (B := B) hsurj f hf0 ε hε hW
  have e : Algebra.leftMulMatrix β g = M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hβ, hM]
    simp only [← hsm, ← hβ]
    rw [β.repr_sum_self]
  rw [← e, ← Algebra.trace_eq_matrix_trace, hlam]
  refine ⟨lam (g * U), ?_⟩
  change lam (g * θ _) = _
  rw [hJ, mul_left_comm, ← hsm, map_smul, smul_eq_mul]

end GlobalTheory.TraceJacobian

namespace GlobalTheory

theorem C_dvd_trace_of_jacobian : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∀ (δ : V) (U : (MvPowerSeries σ V)ˣ), δ ≠ 0 → Matrix.det (Matrix.of fun i j : σ => MvPowerSeries.pderiv V j (φ i)) = MvPowerSeries.C δ * (U : MvPowerSeries σ V) → ∀ (r : ℕ) (b : Fin r → MvPowerSeries σ V), (∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i) → ∀ (f : MvPowerSeries σ V) (M : Matrix (Fin r) (Fin r) (MvPowerSeries σ V)), (∀ j, f * b j = ∑ i, MvPowerSeries.subst φ (M i j) * b i) → MvPowerSeries.C δ ∣ M.trace := by
  intro V _ _ _ _ _ σ _ _ φ h0 hM δ U _ hJ r b hb g M hg
  have hs : HasSubst φ := hasSubst_of_constantCoeff_zero h0
  let ι : MvPowerSeries σ V →ₐ[V] MvPowerSeries σ V := substAlgHom hs
  have hι : ∀ c, ι c = subst φ c := fun c => substAlgHom_apply hs c
  have hιX : ∀ j, ι (X j) = φ j := fun j => substAlgHom_X hs j
  have hιC : ∀ c, ι (C c) = C c := fun c => ι.commutes c
  have hcomp := PlaceInt.isAdicComplete_mvPowerSeries_finite (V := V) σ
  have hXm : ∀ j, (X j : MvPowerSeries σ V) ∈ maximalIdeal _ := fun j =>
    (PlaceInt.mem_maximalIdeal_mvPowerSeries_iff _).2 (by simp)
  obtain ⟨θ, hθC, hθX⟩ := TraceJacobian.exists_ringHom_eval (ι : MvPowerSeries σ V →+* _)
    (maximalIdeal _) X hXm
  have hθ : θ.comp (MvPowerSeries.map (C : V →+* MvPowerSeries σ V)) = RingHom.id _ :=
    (mvPowerSeries_eval_of_pow_mem _ (maximalIdeal _) σ X
      fun j => ⟨1, by simpa using hXm j⟩).2 inferInstance V _ _
      (fun t => by simp [hθC, hιC]) (fun j => by simp [hθX]) (fun j => rfl)
  have hθm : ∀ s, θ (MvPowerSeries.map C s) = s := fun s => RingHom.congr_fun hθ s
  have hcc : ∀ c, constantCoeff (ι c) = constantCoeff c := fun c => by
    obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum c
    conv_lhs => rw [hu]
    simp [hιC, hιX, h0]
  refine TraceJacobian.dvd_trace_of_ringHom θ (ι : MvPowerSeries σ V →+* _) hθC
    (fun s => ⟨_, hθm s⟩) (fun i => MvPowerSeries.map C (φ i) - C (X i))
    (fun i => by simp [hθm, hθC, hιX])
    ((residue _).comp ((C : V →+* MvPowerSeries σ V).comp constantCoeff)) (fun s => ?_)
    (fun a ha hdet => ?_) (C δ) U ?_ b (by simpa only [← hι, RingHom.coe_coe] using hb) g M
    (by simpa only [← hι, RingHom.coe_coe] using hg)
  · obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum s
    have : constantCoeff (θ s) = constantCoeff (constantCoeff s) := by
      conv_lhs => rw [hu]
      simp [hθC, hθX, hcc]
    simp only [RingHom.comp_apply, this]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      PlaceInt.mem_maximalIdeal_mvPowerSeries_iff]
    simp
  · obtain ⟨N, hN⟩ := hM
    let red : MvPowerSeries σ V →+* MvPowerSeries σ (ResidueField V) :=
      MvPowerSeries.map (residue V)
    refine TraceJacobian.det_notMem_span (ResidueField V) σ N (fun j => red (φ j))
      (red.mapMatrix a) (fun i => ?_)
      (fun i => hN (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) N)) ?_
    · have h1 := ha i
      simp only [map_sub, constantCoeff_map, h0, map_zero, constantCoeff_C, zero_sub, map_neg,
        RingHom.coe_coe, hιX, hθX, mul_neg, Finset.sum_neg_distrib, neg_inj] at h1
      rw [h1]
      simp [red]
    · rw [← RingHom.map_det]
      refine Ideal.mem_comap.1
        ((Ideal.map_le_iff_le_comap (K := Ideal.comap red _)).2 (fun c hc => ?_) hdet)
      obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum c
      rw [PlaceInt.mem_maximalIdeal_mvPowerSeries_iff, ← residue_eq_zero_iff] at hc
      rw [Ideal.mem_comap, Ideal.mem_comap, hu]
      simp only [RingHom.coe_coe, map_add, map_sum, map_mul, hιC, hιX]
      refine add_mem ?_ (Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))
      simp [red, hc]
  · rw [RingHom.coe_coe, hιC, ← hJ, RingHom.map_det]
    congr 1
    ext i j : 2
    have : pderiv _ j (MvPowerSeries.map (C : V →+* MvPowerSeries σ V) (φ i) - C (X i))
        = MvPowerSeries.map C (pderiv V j (φ i)) := by
      ext m : 1
      simp [coeff_pderiv, coeff_C]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [this, hθm]

end GlobalTheory
