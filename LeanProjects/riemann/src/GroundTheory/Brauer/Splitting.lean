import Mathlib
import GroundTheory.Brauer.BaseChange
import GroundTheory.Brauer.DoubleCentralizer
import GroundTheory.Brauer.Degree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct Module

universe u v w

section SubalgebraOfDivisionRing

variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]

theorem inv_mem_of_finiteDimensional (S : Subalgebra K D) [FiniteDimensional K S] {x : D}
    (hx : x ∈ S) : x⁻¹ ∈ S := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero]; exact S.zero_mem
  let f : S →ₗ[K] S := LinearMap.mulLeft K (⟨x, hx⟩ : S)
  have hf : Function.Injective f := by
    intro a b hab
    have h : x * (a : D) = x * b := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel₀ h0 h)
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hf) 1
  have h1 : x * (b : D) = 1 := congrArg Subtype.val hb
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact b.2

noncomputable abbrev divisionRingOfFiniteDimensional (S : Subalgebra K D)
    [FiniteDimensional K S] : DivisionRing S :=
  DivisionRing.ofIsUnitOrEqZero fun a ↦ by
    by_cases h : a = 0
    · exact Or.inr h
    · refine Or.inl ⟨⟨a, ⟨(a : D)⁻¹, inv_mem_of_finiteDimensional S a.2⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext (mul_inv_cancel₀ fun h' ↦ h (Subtype.ext h'))
      · exact Subtype.ext (inv_mul_cancel₀ fun h' ↦ h (Subtype.ext h'))

noncomputable abbrev fieldOfIsMulCommutative (S : Subalgebra K D) [FiniteDimensional K S]
    [IsMulCommutative S] : Field S :=
  { divisionRingOfFiniteDimensional S with
    mul_comm := fun a b ↦ (isMulCommutative_iff.mp inferInstance) a b }

theorem isSimpleRing_of_finiteDimensional (S : Subalgebra K D) [FiniteDimensional K S] :
    IsSimpleRing S :=
  letI := divisionRingOfFiniteDimensional S
  DivisionRing.isSimpleRing S

theorem isSeparable_coe_iff {A : Type*} [Ring A] [Algebra K A] {S : Subalgebra K A} (x : S) :
    IsSeparable K (x : A) ↔ IsSeparable K x := by
  unfold IsSeparable
  rw [← minpoly.algHom_eq S.val Subtype.val_injective x]
  rfl

end SubalgebraOfDivisionRing

section SplitByEmbedding

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]

def RightMul (_ι : L →ₐ[K] A) : Type _ := A

namespace RightMul

variable (ι : L →ₐ[K] A)

instance : AddCommGroup (RightMul ι) := inferInstanceAs (AddCommGroup A)

instance : Module K (RightMul ι) := inferInstanceAs (Module K A)

instance : Module Aᵐᵒᵖ (RightMul ι) := inferInstanceAs (Module Aᵐᵒᵖ A)

def toOp : L →+* Aᵐᵒᵖ :=
  (ι.toOpposite fun x y ↦ (Commute.all x y).map ι).toRingHom

instance : Module L (RightMul ι) := Module.compHom (RightMul ι) (toOp ι)

def of (x : A) : RightMul ι := x

def val {ι : L →ₐ[K] A} (x : RightMul ι) : A := x

@[simp] theorem val_of (x : A) : (of ι x).val = x := rfl

@[simp] theorem of_val (x : RightMul ι) : of ι x.val = x := rfl

theorem val_smul (l : L) (x : RightMul ι) : (l • x).val = x.val * ι l := rfl

theorem val_add (x y : RightMul ι) : (x + y).val = x.val + y.val := rfl

theorem val_smul_K (k : K) (x : RightMul ι) : (k • x).val = k • x.val := rfl

instance : IsScalarTower K L (RightMul ι) where
  smul_assoc k l x := by
    change x.val * ι (k • l) = k • (x.val * ι l)
    rw [map_smul, mul_smul_comm]

instance : SMulCommClass L K (RightMul ι) where
  smul_comm l k x := by
    change (k • x.val) * ι l = k • (x.val * ι l)
    rw [smul_mul_assoc]

instance [FiniteDimensional K A] : FiniteDimensional K (RightMul ι) :=
  inferInstanceAs (FiniteDimensional K A)

instance [Nontrivial A] : Nontrivial (RightMul ι) := inferInstanceAs (Nontrivial A)

def leftMul (a : A) : Module.End L (RightMul ι) where
  toFun x := of ι (a * x.val)
  map_add' x y := mul_add a x.val y.val
  map_smul' l x := (mul_assoc a x.val (ι l)).symm

def leftMulAlgHom : A →ₐ[K] Module.End L (RightMul ι) where
  toFun := leftMul ι
  map_one' := LinearMap.ext fun x ↦ one_mul x.val
  map_mul' a b := LinearMap.ext fun x ↦ mul_assoc a b x.val
  map_zero' := LinearMap.ext fun x ↦ zero_mul x.val
  map_add' a b := LinearMap.ext fun x ↦ add_mul a b x.val
  commutes' k := LinearMap.ext fun x ↦ by
    change algebraMap K A k * x.val = (k • x).val
    rw [val_smul_K, Algebra.smul_def]

noncomputable def actionHom : L ⊗[K] A →ₐ[L] Module.End L (RightMul ι) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (leftMulAlgHom ι)
    fun l a ↦ Algebra.commutes l (leftMulAlgHom ι a)

end RightMul

open RightMul in

theorem nonempty_algEquiv_matrix_of_algHom [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (ι : L →ₐ[K] A) (h : finrank K L ^ 2 = finrank K A) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (finrank K L)) (Fin (finrank K L)) L) := by
  have hA : 0 < finrank K A := Module.finrank_pos
  have hL : 0 < finrank K L := by
    rcases Nat.eq_zero_or_pos (finrank K L) with h0 | h0
    · rw [h0] at h; omega
    · exact h0
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hL
  have : Module.Finite L (RightMul ι) := Module.Finite.of_restrictScalars_finite K L _
  have hM : finrank L (RightMul ι) = finrank K L := by
    have h2 := Module.finrank_mul_finrank K L (RightMul ι)
    change finrank K L * finrank L (RightMul ι) = finrank K A at h2
    rw [← h, sq] at h2
    exact Nat.eq_of_mul_eq_mul_left hL h2
  have hinj : Function.Injective (actionHom ι) := RingHom.injective (actionHom ι).toRingHom
  have hdim : finrank L (L ⊗[K] A) = finrank L (Module.End L (RightMul ι)) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap, hM, ← h, sq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (actionHom ι).toLinearMap) hdim).mp hinj
  exact ⟨(AlgEquiv.ofBijective (actionHom ι) ⟨hinj, hsurj⟩).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq L (RightMul ι) hM))⟩

end SplitByEmbedding

section MaximalSubfield

variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]

theorem le_centralizer_of_isMulCommutative (F : Subalgebra K D) [IsMulCommutative F] :
    F ≤ Subalgebra.centralizer K (F : Set D) := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance) (⟨y, hy⟩ : F) ⟨x, hx⟩)

theorem isMulCommutative_adjoin_insert (F : Subalgebra K D) [IsMulCommutative F] {y : D}
    (hy : y ∈ Subalgebra.centralizer K (F : Set D)) :
    IsMulCommutative (Algebra.adjoin K (insert y (F : Set D))) := by
  refine Algebra.isMulCommutative_adjoin K fun a ha b hb ↦ ?_
  rw [Subalgebra.mem_centralizer_iff] at hy
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (hy b hb).symm
  · exact hy a ha
  · exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance) (⟨a, ha⟩ : F) ⟨b, hb⟩)

theorem maximal_isMulCommutative_iff_centralizer_eq (F : Subalgebra K D) [IsMulCommutative F] :
    Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ↔
      Subalgebra.centralizer K (F : Set D) = F := by
  constructor
  · intro hmax
    refine le_antisymm (fun x hx ↦ ?_) (le_centralizer_of_isMulCommutative F)
    have hG := isMulCommutative_adjoin_insert F hx
    have hle : F ≤ Algebra.adjoin K (insert x (F : Set D)) :=
      fun z hz ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
    exact hmax.2 hG hle (Algebra.subset_adjoin (Set.mem_insert x _))
  · intro hc
    refine ⟨inferInstance, fun G hG hle ↦ ?_⟩
    have hG' : IsMulCommutative G := hG
    rw [← hc]
    intro y hy
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hG') ⟨z, hle hz⟩ ⟨y, hy⟩)

variable [Algebra.IsCentral K D] [FiniteDimensional K D]

theorem centralizer_eq_iff_finrank_sq (F : Subalgebra K D) [IsMulCommutative F] :
    Subalgebra.centralizer K (F : Set D) = F ↔ finrank K F ^ 2 = finrank K D := by
  have := isSimpleRing_of_finiteDimensional F
  have h := finrank_mul_finrank_centralizer F
  constructor
  · intro hc
    rw [hc] at h
    rw [sq]
    exact h
  · intro hsq
    have hF : 0 < finrank K F := Module.finrank_pos
    have hdim : finrank K F = finrank K (Subalgebra.centralizer K (F : Set D)) := by
      apply Nat.eq_of_mul_eq_mul_left hF
      rw [h, ← sq, hsq]
    exact (Subalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_eq
      (Subalgebra.toSubmodule.monotone (le_centralizer_of_isMulCommutative F)) hdim)).symm

theorem tfae_maximal_subfield (F : Subalgebra K D) [IsMulCommutative F] :
    List.TFAE [Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F,
      Subalgebra.centralizer K (F : Set D) = F, finrank K F ^ 2 = finrank K D,
      finrank K F = degree K D] := by
  tfae_have 1 ↔ 2 := maximal_isMulCommutative_iff_centralizer_eq F
  tfae_have 2 ↔ 3 := centralizer_eq_iff_finrank_sq F
  tfae_have 3 ↔ 4 :=
    ⟨fun h ↦ ((degree_eq_iff K D _).mpr h.symm).symm,
      fun h ↦ ((degree_eq_iff K D _).mp h.symm).symm⟩
  tfae_finish

theorem finrank_eq_degree_of_maximal (F : Subalgebra K D) [IsMulCommutative F]
    (hF : Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F) :
    finrank K F = degree K D :=
  ((tfae_maximal_subfield F).out 0 3).mp hF

theorem nonempty_algEquiv_matrix_of_maximal (F : Subalgebra K D) [IsMulCommutative F]
    (hF : Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F) :
    letI := fieldOfIsMulCommutative F
    Nonempty (F ⊗[K] D ≃ₐ[F] Matrix (Fin (degree K D)) (Fin (degree K D)) F) := by
  let _ := fieldOfIsMulCommutative F
  have h2 : finrank K F ^ 2 = finrank K D := ((tfae_maximal_subfield F).out 0 2).mp hF
  rw [← finrank_eq_degree_of_maximal F hF]
  exact nonempty_algEquiv_matrix_of_algHom F.val h2

theorem exists_maximal_isSeparable :
    ∃ F : Subalgebra K D, IsMulCommutative F ∧
      Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ∧ ∀ x ∈ F, IsSeparable K x := by
  classical
  let P : ℕ → Prop := fun d ↦ ∃ F : Subalgebra K D, IsMulCommutative F ∧
    (∀ x ∈ F, IsSeparable K x) ∧ finrank K F = d
  have hbot : IsMulCommutative (⊥ : Subalgebra K D) := isMulCommutative_iff.mpr fun a b ↦ by
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp a.2
    apply Subtype.ext
    change (a : D) * b = b * a
    rw [← hk]
    exact Algebra.commutes k (b : D)
  have hP1 : P 1 := by
    refine ⟨⊥, hbot, fun x hx ↦ ?_, Subalgebra.finrank_bot⟩
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.mp hx
    exact isSeparable_algebraMap k
  have hD : 1 ≤ finrank K D := Module.finrank_pos
  obtain ⟨F, hFc, hFs, hFd⟩ := Nat.findGreatest_spec hD hP1
  refine ⟨F, hFc, (maximal_isMulCommutative_iff_centralizer_eq F).mpr ?_, hFs⟩
  refine le_antisymm (fun x hx ↦ ?_) (le_centralizer_of_isMulCommutative F)
  by_contra hxF
  set C := Subalgebra.centralizer K (F : Set D)
  let _ : DivisionRing C := divisionRingOfFiniteDimensional C
  let _ : Field F := fieldOfIsMulCommutative F
  have : IsSimpleRing F := isSimpleRing_of_finiteDimensional F
  have hFC : F ≤ C := le_centralizer_of_isMulCommutative F

  let _ : Algebra F C := RingHom.toAlgebra' (Subalgebra.inclusion hFC).toRingHom
    fun c z ↦ Subtype.ext ((Subalgebra.mem_centralizer_iff K).mp z.2 c c.2)
  have : IsScalarTower K F C := IsScalarTower.of_algebraMap_eq fun k ↦ rfl
  have : Module.Finite F C := Module.Finite.of_restrictScalars_finite K F C
  have : Algebra.IsAlgebraic F C := Algebra.IsAlgebraic.of_finite F C
  have : Algebra.IsCentral F C := ⟨fun z hz ↦ by
    have hzC : (z : D) ∈ Subalgebra.centralizer K (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val ((Subalgebra.mem_center_iff.mp hz) ⟨g, hg⟩)
    have hcc : Subalgebra.centralizer K (C : Set D) = F := centralizer_centralizer F
    rw [hcc] at hzC
    exact Algebra.mem_bot.mpr ⟨⟨z, hzC⟩, Subtype.ext rfl⟩⟩
  have hne : (⊥ : Subalgebra F C) ≠ ⊤ := by
    intro h
    have hmem : (⟨x, hx⟩ : C) ∈ (⊥ : Subalgebra F C) := h ▸ Algebra.mem_top
    obtain ⟨f, hf⟩ := Algebra.mem_bot.mp hmem
    apply hxF
    have hfx : (f : D) = x := congrArg Subtype.val hf
    exact hfx ▸ f.2

  obtain ⟨y, hyF, hysep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
  have hyC : (y : D) ∈ C := y.2
  have hyF' : (y : D) ∉ F := fun h ↦ hyF (Algebra.mem_bot.mpr ⟨⟨y, h⟩, Subtype.ext rfl⟩)
  set G := Algebra.adjoin K (insert (y : D) (F : Set D))
  have hGc : IsMulCommutative G := isMulCommutative_adjoin_insert F hyC
  have hFG : F ≤ G := fun z hz ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
  have hyG : (y : D) ∈ G := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hGC : G ≤ C := Algebra.adjoin_le (Set.insert_subset hyC fun z hz ↦ hFC hz)

  let _ : Field G := fieldOfIsMulCommutative G
  let _ : Algebra F G := (Subalgebra.inclusion hFG).toRingHom.toAlgebra
  have : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq fun k ↦ rfl
  have : Algebra.IsSeparable K F := ⟨fun z ↦ (isSeparable_coe_iff z).mp (hFs z z.2)⟩
  let yG : G := ⟨y, hyG⟩
  let ψ : G →ₐ[F] C :=
    { (Subalgebra.inclusion hGC).toRingHom with commutes' := fun f ↦ rfl }
  have hψ : Function.Injective ψ := fun a b h ↦ Subtype.ext (congrArg Subtype.val h :)
  have hyGsep : IsSeparable F yG := by
    unfold IsSeparable
    rw [← minpoly.algHom_eq ψ hψ yG]
    exact hysep
  have hyKsep : IsSeparable K yG := IsSeparable.of_algebra_isSeparable_of_isSeparable K hyGsep
  have hGsep : ∀ z ∈ G, IsSeparable K z := by
    have hle : G ≤ (separableClosure K G).toSubalgebra.map G.val := by
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · exact ⟨yG, mem_separableClosure_iff.mpr hyKsep, rfl⟩
      · intro f hf
        exact ⟨⟨f, hFG hf⟩, mem_separableClosure_iff.mpr
          ((isSeparable_coe_iff (⟨f, hFG hf⟩ : G)).mp (hFs f hf)), rfl⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hle hz
    exact (isSeparable_coe_iff w).mpr (mem_separableClosure_iff.mp hw)

  have hPG : P (finrank K G) := ⟨G, hGc, hGsep, rfl⟩
  have hGD : finrank K G ≤ finrank K D := Submodule.finrank_le (Subalgebra.toSubmodule G)
  have hle := Nat.le_findGreatest hGD hPG
  have hlt : Subalgebra.toSubmodule F < Subalgebra.toSubmodule G :=
    SetLike.lt_iff_le_and_exists.mpr ⟨hFG, (y : D), hyG, hyF'⟩
  have hlt' : finrank K F < finrank K G := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end MaximalSubfield

section Splitting

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

theorem nonempty_algEquiv_matrix_of_algHom_field {L : Type*} [Field L] [Algebra K L] {E : Type*}
    [Field E] [Algebra K E] (σ : L →ₐ[K] E) {n : ℕ}
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty (E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  let _ : Algebra L E := σ.toRingHom.toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun k ↦ (σ.commutes k).symm
  exact ⟨(baseChangeTower K L E A).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans <|
    (baseChangeMatrix L E L (Fin n)).trans (Algebra.TensorProduct.rid L E E).mapMatrix⟩

theorem nonempty_algEquiv_matrix_of_matrix {L : Type*} [Field L] [Algebra K L] {D : Type*}
    [Ring D] [Algebra K D] {m k : ℕ} (eA : A ≃ₐ[K] Matrix (Fin m) (Fin m) D)
    (eD : L ⊗[K] D ≃ₐ[L] Matrix (Fin k) (Fin k) L) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (m * k)) (Fin (m * k)) L) :=
  ⟨(Algebra.TensorProduct.congr AlgEquiv.refl eA).trans <|
    (baseChangeMatrix K L D (Fin m)).trans <| eD.mapMatrix.trans <|
      (Matrix.compAlgEquiv (Fin m) (Fin k) L L).trans
        (Matrix.reindexAlgEquiv L L finProdFinEquiv)⟩

end Splitting

section SeparableSplitting

variable {K : Type u} [Field K]

theorem exists_isGalois_splits (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨m, _, D, _, _, _, ⟨eA⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Algebra.IsCentral K (Matrix (Fin m) (Fin m) D) := Algebra.IsCentral.of_algEquiv K _ _ eA
  have : Algebra.IsCentral K D := isCentral_of_isCentral_matrix (ι := Fin m)
  obtain ⟨F, hFc, hFmax, hFs⟩ := exists_maximal_isSeparable (K := K) (D := D)
  let _ : Field F := fieldOfIsMulCommutative F
  obtain ⟨eD⟩ := nonempty_algEquiv_matrix_of_maximal F hFmax
  have : Algebra.IsSeparable K F := ⟨fun z ↦ (isSeparable_coe_iff z).mp (hFs z z.2)⟩
  let σ : F →ₐ[K] SeparableClosure K := IsSepClosed.lift (K := K) (L := F) (M := SeparableClosure K)
  let _ : Algebra F (SeparableClosure K) := σ.toRingHom.toAlgebra
  have : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (σ.commutes k).symm
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_of_matrix eA eD
  exact ⟨IntermediateField.normalClosure K F (SeparableClosure K), inferInstance, inferInstance, inferInstance,
    inferInstance, _, nonempty_algEquiv_matrix_of_algHom_field
      (IsScalarTower.toAlgHom K F (IntermediateField.normalClosure K F (SeparableClosure K))) e⟩

theorem exists_isSeparable_splits (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      Algebra.IsSeparable K L ∧
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  obtain ⟨L, _, _, h1, h2, h3⟩ := exists_isGalois_splits (K := K) A
  exact ⟨L, _, _, h1, inferInstance, h3⟩

theorem BrauerGroup.exists_mem_relBrauer (x : BrauerGroup.{u, u} K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      x ∈ BrauerGroup.relBrauer K L := by
  induction x using Quotient.inductionOn with
  | h A =>
    obtain ⟨L, _, _, h1, h2, n, ⟨e⟩⟩ := exists_isGalois_splits (K := K) A
    exact ⟨L, _, _, h1, h2, (BrauerGroup.mk_mem_relBrauer_iff A).mpr ⟨n, ⟨e⟩⟩⟩

end SeparableSplitting

end GroundTheory.Brauer
