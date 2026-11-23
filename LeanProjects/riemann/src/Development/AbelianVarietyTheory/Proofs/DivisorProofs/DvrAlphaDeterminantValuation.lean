import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantFrameRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisQuotientLatticeEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonicalStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.ShiftLam

theorem ιMulti_sum_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

theorem val_le_of_image_subset {C O W : Type} [Field C] [CommRing O] [Algebra O C]
    [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W]
    (v : Valuation C NNReal) (hv : v.Integers O) {e : W} (he : e ≠ 0) {μ l : C}
    (H : (fun w => l • w) '' (Submodule.span O {e} : Set W) ⊆
      (fun w => μ • w) '' (Submodule.span O {e} : Set W)) :
    v l ≤ v μ := by
  obtain ⟨w, hw, hwe⟩ := H ⟨e, Submodule.subset_span rfl, rfl⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hmu : μ * algebraMap O C o = l := by
    apply smul_left_injective C he
    simp only [mul_smul, algebraMap_smul]
    exact hwe
  rw [← hmu, map_mul]
  exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)

end GlobalTheory.ShiftLam

namespace GlobalTheory.ShiftLam

theorem ringHom_eq_of_apply_gen {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (α : Λ)
    (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (he : σ α = τ α) : σ = τ := by
  let S : Subalgebra ℤ_[p] Λ :=
    { σ.eqLocus τ with
      algebraMap_mem' := fun r => by
        show σ (algebraMap ℤ_[p] Λ r) = τ (algebraMap ℤ_[p] Λ r)
        have h1 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ.comp (algebraMap ℤ_[p] Λ))
        have h2 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (τ.comp (algebraMap ℤ_[p] Λ))
        exact (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h2 r).symm }
  have hle : Algebra.adjoin ℤ_[p] {α} ≤ S := Algebra.adjoin_le (by simpa [S] using he)
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  exact hle hx

end GlobalTheory.ShiftLam

theorem GlobalTheory.DetInv.isShift_of_iota_image : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → IsShift C v D τ (v lam * (∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1)⁻¹) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D τ ι lam hι hlat
  unfold IsShift
  intro a b x g m k hx hgx hm hkm
  obtain ⟨ha, hab, hy⟩ := GlobalTheory.T.dvr_determinant_frame_rank p C v O hv ε hε Λ N h hh D τ a b x _ _ hx hgx hkm
  subst hab
  choose y hy using hy
  obtain ⟨X, hX1, hX2, -, hXdet⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ _ _ hgx hkm
  have hmem : ∀ j, m j ∈ eig C (actH D) τ := fun j => by
    have : m j ∈ filQuot C D τ := hm.2 ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this.1
  let z : Fin (a + b) → eig C (actH D) τ := Fin.append y (fun j => ⟨m j, hmem j⟩)
  have hz1 : ∀ i, z (Fin.castAdd b i) = y i := fun i => Fin.append_left _ _ _
  have hz2 : ∀ j, (z (Fin.natAdd a j) : Fin h → C) = m j := fun j => by
    simp [z, Fin.append_right]
  obtain ⟨c, hc, hcz⟩ := GlobalTheory.T.dvr_alpha_determinant_order p C v O hv ε hε Λ α hα a b h hh D τ z
    (by convert hx using 1; funext i; rw [hz1, hy]) (by convert hm using 1; funext j; exact hz2 j)
  let M : Matrix (Fin (a + b)) (Fin (a + b)) C :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 k)
  have hM : M.det = g.det * k.det := by
    simp only [M, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  let Y : Fin (a + b) → eig C (actH D) τ := fun i => ∑ j, M i j • z j
  have hY1 : ∀ i, Y (Fin.castAdd b i) = ∑ j, g i j • y j := fun i => by
    simp [Y, M, Fin.sum_univ_add, hz1]
  have hY2 : ∀ i, Y (Fin.natAdd a i) = ∑ j, k i j • z (Fin.natAdd a j) := fun i => by
    simp [Y, M, Fin.sum_univ_add]
  have hιX : ι (exteriorPower.ιMulti C (a + b) X) = exteriorPower.ιMulti C (a + b) Y := by
    apply hι
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin a, Fin.castAdd b i' = i := ⟨⟨i, hi⟩, rfl⟩
      rw [hX1, hY1]
      simp [hy]
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
        ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [hX2, hY2]
      simp [hz2]
  have hYz : exteriorPower.ιMulti C (a + b) Y =
      (g.det * k.det) • exteriorPower.ιMulti C (a + b) z := by
    rw [← hM]; exact GlobalTheory.ShiftLam.ιMulti_sum_smul M z
  have himg : ι '' (detLattice C (actT D) τ (a + b) : Set (detLine C (actT D) τ (a + b))) =
      (fun w => (g.det * k.det) • w) ''
        (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) := by
    rw [hXdet]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) z,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show _ = ι _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) X,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show ι _ = _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
  obtain ⟨hind, hsup, hrk⟩ := (GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ (a + b) h hh D).2
  obtain ⟨e, -, -, he, hdet⟩ := GlobalTheory.T.exists_basis_quotient_lattice_eigen C v O Λ h (a + b) hv (actH D) τ hind hsup (hrk τ)
  have hfin : (fun w => (g.det * k.det * c) • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) =
      (fun w => lam • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) := by
    rw [← hdet, ← hlat, himg, hcz, Set.image_image]
    simp only [smul_smul]
  have hval : v (g.det * k.det * c) = v lam :=
    le_antisymm (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.subset)
      (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.symm.subset)
  have hc0 : v c ≠ 0 := by
    rw [hc]
    refine finprod_induction (fun t : NNReal => t ≠ 0) one_ne_zero (fun s t => mul_ne_zero) ?_
    intro σ
    refine pow_ne_zero _ ((Valuation.ne_zero_iff v).2 (sub_ne_zero.2 fun hst => σ.2 ?_))
    exact GlobalTheory.ShiftLam.ringHom_eq_of_apply_gen α hα σ.1 τ (hv.hom_inj hst).symm
  rw [← hc, ← hval, map_mul, map_mul, mul_inv_cancel_right₀ hc0]
