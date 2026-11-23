import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveIffIsUnitDet
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood Module

namespace GlobalTheory.LocAzumaya

theorem exists_den_coords : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] (Λ : Subring B),
    Module.Finite ℤ Λ → ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((D : F) * e.repr x k) := by
  intro F B _ _ _ _ Λ hfin ι _ e
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨D, hD, hDi⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : Fin n × ι => e.repr (s p.1 : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  have key : ∀ y : Λ, y ∈ Submodule.span ℤ (Set.range s) →
      ∀ k, IsIntegral ℤ ((D : F) * e.repr (y : B) k) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro k
      exact hDi _ (Finset.mem_image.2 ⟨(j, k), Finset.mem_univ _, rfl⟩)
    | zero => intro k; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro k
      simpa [mul_add] using (hy k).add (hz k)
    | smul a y _ hy =>
      intro k
      have : (D : F) * e.repr ((a • y : Λ) : B) k = (a : F) * ((D : F) * e.repr (y : B) k) := by
        have hc : ((a • y : Λ) : B) = (a : F) • (y : B) := by
          have h0 : ((a • y : Λ) : B) = a • (y : B) := rfl
          rw [h0, zsmul_eq_mul, Algebra.smul_def, map_intCast]
        rw [hc]
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring
      rw [this]
      have ha : IsIntegral ℤ (a : F) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F a))
      exact ha.mul (hy k)
  intro k
  exact key ⟨x, hx⟩ (by rw [hs]; trivial) k
theorem exists_coords_of_mem_locOrder : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (Λ : Subring B) (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    (∀ i, e i ∈ Λ) → (∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F) →
    ∀ y ∈ locOrder ℓ Λ, ∃ c : ι → ℚ_[ℓ] ⊗[ℚ] F, (∀ i, c i ∈ cenOrder ℓ F) ∧
      y = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
  intro ℓ _ F B _ _ _ _ _ _ Λ ι _ e he hco
  classical
  have hexp : ∀ x : B, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x =
      ∑ i, cenMap ℓ F B ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
    intro x
    conv_lhs => rw [← e.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨fun i => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i, fun i => hco x hx i, hexp x⟩
  | algebraMap r =>
    refine ⟨fun i => algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr 1 i),
      fun i => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (hco 1 Λ.one_mem i), ?_⟩
    have h1 : ∀ a : ℚ_[ℓ] ⊗[ℚ] F, cenMap ℓ F B (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * a) =
        algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) r * cenMap ℓ F B a := by
      intro a
      rw [map_mul, IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F),
        IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B), AlgHom.commutes]
    simp only [h1, mul_assoc]
    rw [← Finset.mul_sum, ← hexp 1, Algebra.TensorProduct.one_def.symm, mul_one]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun i => c i + c' i, fun i => Subalgebra.add_mem _ (hc i) (hc' i), ?_⟩
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun k => ∑ i, ∑ j, c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k), fun k => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hc i) (hc' j)) (hco _ (Λ.mul_mem (he i) (he j)) k)
    · have hprod : ∀ i j, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
          ∑ k, cenMap ℓ F B (c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k)) *
            ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e k) := by
        intro i j
        have hcomm := (GlobalTheory.LocMatrix.cenMap_commute ℓ F B (c' j) ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)).eq
        have h1 : cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
            cenMap ℓ F B (c i * c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (e i * e j)) := by
          rw [map_mul, ← one_mul (1 : ℚ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            mul_assoc, ← mul_assoc ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i), ← hcomm]
          simp only [mul_assoc]
        rw [h1, hexp (e i * e j), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul]
      rw [Finset.sum_mul_sum]
      simp only [hprod, map_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]

theorem exists_coordProj (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] {ι : Type} [DecidableEq ι] (e : Basis ι F B)
    (k : ι) : ∃ π : ℚ_[ℓ] ⊗[ℚ] B →ₗ[ℚ] ℚ_[ℓ] ⊗[ℚ] F,
      (∀ b : B, π ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k) ∧
      ∀ (a : ℚ_[ℓ] ⊗[ℚ] F) (i : ι),
        π (cenMap ℓ F B a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)) = if i = k then a else 0 := by
  refine ⟨LinearMap.lTensor ℚ_[ℓ] ((e.coord k).restrictScalars ℚ), fun b => by simp, fun a i => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Algebra.smul_def]
    simp only [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, map_smul, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  | add a a' ha ha' =>
    rw [map_add, add_mul, map_add, ha, ha']
    split_ifs <;> simp

theorem basisLoc : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ), Module.Finite ℤ Λ →
    ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
    ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
        (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
        ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
          ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
  intro F B _ _ _ _ _ _ Λ hΛ hfin ι _ e he
  classical
  obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
    fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
  have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
  let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
      ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
  have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
      ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [hsmul, v]
  have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
      ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
      ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro c b h k
    obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
    have h' := congrArg π h
    rw [hsum, map_sum, hπ1] at h'
    simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h'
    exact h'
  have hli : LinearIndependent (cenOrder ℓ F) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
      rw [hc, TensorProduct.tmul_zero]; rfl
    have := hcoef c 0 h0 k
    apply Subtype.ext
    simpa using this
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
    rintro y -
    obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
    rw [hsum, hy]
  let f := Basis.mk hli hsp
  have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
  refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
  apply hcoef (fun i => f.repr y i) b _ k
  have hs := f.sum_repr y
  simp only [hfv] at hs
  rw [hs, hy]

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ e : Basis (Fin (Module.finrank F B)) F B, ∀ i, e i ∈ Λ := by
  let b := Module.finBasis F B
  choose m hm hmb using fun i => hspan (b i)
  let u : Fin (Module.finrank F B) → Fˣ := fun i => Units.mk0 (m i : F) (by exact_mod_cast (hm i).ne')
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Basis.unitsSMul_apply]
  convert hmb i using 1
  simp [u, Algebra.smul_def]

theorem cenMap_injective (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [Nontrivial B] : Function.Injective (cenMap ℓ F B) := by
  let g : F →ₗ[ℚ] B := ((Algebra.ofId F B).restrictScalars ℚ).toLinearMap
  have hg : Function.Injective g := (algebraMap F B).injective
  have heq : ⇑(cenMap ℓ F B) = ⇑(LinearMap.lTensor ℚ_[ℓ] g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul q f => simp [cenMap, g]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [heq]
  exact Module.Flat.lTensor_preserves_injective_linearMap g hg

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

theorem locOrder_isAzumaya : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := basisLoc F B Λ hΛ hfin _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  haveI : Nontrivial B := inferInstance
  haveI : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    simp only [GlobalTheory.LocMatrix.algebraMap_cenAlgebra, GlobalTheory.LocMatrix.coe_cenIncl] at h
    exact Subtype.ext (cenMap_injective ℓ F B h)
  haveI := Module.Projective.of_basis f
  haveI := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩

end GlobalTheory.LocAzumaya
