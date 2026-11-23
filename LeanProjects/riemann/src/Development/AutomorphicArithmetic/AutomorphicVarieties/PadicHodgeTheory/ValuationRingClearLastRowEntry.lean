import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CommutingUpperTriangularDistinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtBasic
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc

private def TriangularForm {ι A C : Type} [CommRing A] [CommRing C] (M : ι → Matrix (Fin 3) (Fin 3) A) (d : ι → Fin 3 → A)
    (S T : Set ι) (φ : A →+* C) (h : GL (Fin 3) C) : Prop :=
  (∀ g ∈ S, ∀ a b, b < a →
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b = 0) ∧
  ∀ g ∈ T, ∀ a,
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a a = φ (d g a)

section

variable {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → Matrix (Fin 3) (Fin 3) A}
  {d : ι → Fin 3 → A} {S T : Set ι}

private theorem conjugate_entry_map (X : Matrix (Fin 3) (Fin 3) A) (φ : A →+* C) (ψ : C →+* C') (h : GL (Fin 3) C) (a b : Fin 3) :
    ((((Matrix.GeneralLinearGroup.map ψ h)⁻¹ : GL (Fin 3) C') : Matrix (Fin 3) (Fin 3) C') * X.map (ψ.comp φ) *
      (Matrix.GeneralLinearGroup.map ψ h : Matrix (Fin 3) (Fin 3) C')) a b =
    ψ ((((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X.map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b) := by
  rw [← map_inv, ← Matrix.map_apply (f := ψ), Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem triangular_form_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (H : TriangularForm M d S T φ h) :
    TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h) :=
  ⟨fun g hg a b hab => by rw [conjugate_entry_map, H.1 g hg a b hab, map_zero],
    fun g hg a => by rw [conjugate_entry_map, H.2 g hg a]; rfl⟩

private theorem triangular_form_of_injective_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (hψ : Function.Injective ψ)
    (H : TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h)) : TriangularForm M d S T φ h :=
  ⟨fun g hg a b hab => hψ (by rw [← conjugate_entry_map, H.1 g hg a b hab, map_zero]),
    fun g hg a => hψ (by rw [← conjugate_entry_map, H.2 g hg a]; rfl)⟩

private theorem triangular_mul_diag {X Y : Matrix (Fin 3) (Fin 3) C} (hX : X.BlockTriangular id) (hY : Y.BlockTriangular id)
    (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · simp

private theorem triangular_form_borel_change {φ : A →+* C} {h : GL (Fin 3) C} (hT : T ⊆ S) (H : TriangularForm M d S T φ h) (k : GL (Fin 3) C)
    (hk : ((k * h : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id) : TriangularForm M d S T φ k⁻¹ := by
  obtain ⟨b, hb⟩ : ∃ b, b = k * h := ⟨_, rfl⟩
  rw [← hb] at hk
  obtain rfl : k = b * h⁻¹ := by rw [hb, mul_inv_cancel_right]
  have hi : ((b⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hk
  have e : ∀ X : Matrix (Fin 3) (Fin 3) C, (((b * h⁻¹)⁻¹⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X *
      ((b * h⁻¹)⁻¹ : GL (Fin 3) C) = b * (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X * h) *
      (b⁻¹ : GL (Fin 3) C) := fun X => by
    simp only [inv_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hU : ∀ g ∈ S, (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * h).BlockTriangular id :=
    fun g hg a b hab => H.1 g hg a b hab
  refine ⟨fun g hg a c hac => ?_, fun g hg a => ?_⟩
  · rw [e]
    exact ((hk.mul (hU g hg)).mul hi) hac
  · rw [e, triangular_mul_diag (hk.mul (hU g (hT hg))) hi, triangular_mul_diag hk (hU g (hT hg)), H.2 g hg a, mul_right_comm,
      ← triangular_mul_diag hk hi, Units.mul_inv, Matrix.one_apply_eq, one_mul]

end

private theorem exists_sl2_valuation_kill {F : Type} [Field F] (V : ValuationSubring F) (a b : F) :
    ∃ x y z w : V, x * w - y * z = 1 ∧ (z : F) * a + w * b = 0 := by
  by_cases ha : a = 0
  · exact ⟨0, -1, 1, 0, by simp, by simp [ha]⟩
  by_cases hb : b = 0
  · exact ⟨1, 0, 0, 1, by simp, by simp [hb]⟩
  rcases V.mem_or_inv_mem (b / a) with h | h
  · exact ⟨1, 0, -⟨_, h⟩, 1, by simp, by simp [ha]⟩
  · exact ⟨0, -1, 1, -⟨_, h⟩, by simp, by simp [hb]⟩

private theorem valuation_ring_clear_last_row_entry {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) (c : Fin 3) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 2 c = 0 ∧
      (Y 1 0 = 0 → Y 2 0 = 0 → (k.map V.subtype * Y) 1 0 = 0 ∧ (k.map V.subtype * Y) 2 0 = 0) := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 1 c) (Y 2 c)
  refine ⟨!![1, 0, 0; 0, x, y; 0, z, w], ?_, ?_, fun e1 e2 => ⟨?_, ?_⟩⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]

private theorem valuation_ring_clear_first_column {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 1 0 = 0 ∧
      (k.map V.subtype * Y) 2 0 = Y 2 0 := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 0 0) (Y 1 0)
  refine ⟨!![x, y, 0; z, w, 0; 0, 0, 1], ?_, ?_, ?_⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upper_triangular_of_entries_zero {F : Type} [Field F] {Z : Matrix (Fin 3) (Fin 3) F} (h1 : Z 1 0 = 0) (h2 : Z 2 0 = 0)
    (h3 : Z 2 1 = 0) : Z.BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa

private theorem iwasawa_triangularization {F : Type} [Field F] (V : ValuationSubring F) (X : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : GL (Fin 3) V, ((k : Matrix (Fin 3) (Fin 3) V).map V.subtype * X).BlockTriangular id := by
  obtain ⟨k1, d1, a1, -⟩ := valuation_ring_clear_last_row_entry V X 0
  obtain ⟨k2, d2, a2, b2⟩ := valuation_ring_clear_first_column V (k1.map V.subtype * X)
  obtain ⟨k3, d3, a3, b3⟩ := valuation_ring_clear_last_row_entry V (k2.map V.subtype * (k1.map V.subtype * X)) 1
  obtain ⟨b3, c3⟩ := b3 a2 (b2.trans a1)
  obtain ⟨k, hk⟩ := (Matrix.isUnit_iff_isUnit_det (k3 * (k2 * k1))).2
    (by rw [Matrix.det_mul, Matrix.det_mul, d1, d2, d3, one_mul, one_mul]; exact isUnit_one)
  refine ⟨k, ?_⟩
  rw [hk, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  exact upper_triangular_of_entries_zero b3 c3 a3

private theorem exists_common_ring_same_kernel {A K L : Type} [CommRing A] [Field K] [Field L] (f : A →+* K) (g : A →+* L)
    (h : RingHom.ker f = RingHom.ker g) :
    ∃ (T : Type) (_ : CommRing T) (_ : Nontrivial T) (i : K →+* T) (j : L →+* T), i.comp f = j.comp g := by
  letI : Algebra (A ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  letI : Algebra (A ⧸ RingHom.ker f) L := (Ideal.Quotient.lift _ g fun a ha => by rwa [h] at ha).toAlgebra
  have h2 : Function.Injective (algebraMap (A ⧸ RingHom.ker f) L) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, h]
    exact ha
  refine ⟨TensorProduct (A ⧸ RingHom.ker f) K L, inferInstance,
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ (RingHom.kerLift_injective f) h2,
    (Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f)).toRingHom,
    Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun a => ?_⟩
  exact ((Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f) (A := K) (B := L)).commutes
    (Ideal.Quotient.mk _ a)).trans
    ((Algebra.TensorProduct.includeRight (A := K) (B := L)).commutes (Ideal.Quotient.mk _ a)).symm

private theorem triangular_form_finite_extension {ι A K B : Type} [CommRing A] [Field K] [CommRing B] [Nontrivial B]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (f : A →+* K) (i : K →+* B)
    (h : GL (Fin 3) B) (H : TriangularForm M d S T (i.comp f) h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  classical
  letI := i.toAlgebra
  let s : Set B := Set.range (fun p : Fin 3 × Fin 3 => (h : Matrix (Fin 3) (Fin 3) B) p.1 p.2) ∪
    Set.range (fun p : Fin 3 × Fin 3 => ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  let B₀ := Algebra.adjoin K s
  haveI : Algebra.FiniteType K B₀ := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  let X : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inl ⟨(a, b), rfl⟩)⟩
  let Y : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inr ⟨(a, b), rfl⟩)⟩
  have hXY : X * Y = 1 := by
    apply Matrix.map_injective (f := B₀.val.toRingHom) Subtype.val_injective
    show (X * Y).map B₀.val.toRingHom = (1 : Matrix (Fin 3) (Fin 3) B₀).map B₀.val.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h.mul_inv
  let h₀ : GL (Fin 3) B₀ := ⟨X, Y, hXY, mul_eq_one_comm.1 hXY⟩
  have H0 : TriangularForm M d S T ((algebraMap K B₀).comp f) h₀ :=
    triangular_form_of_injective_map B₀.val.toRingHom Subtype.val_injective H
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B₀
  letI := Ideal.Quotient.field m
  exact ⟨B₀ ⧸ m, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing K (B₀ ⧸ m), _,
    triangular_form_map (Ideal.Quotient.mk m) H0⟩

private theorem triangular_form_specialization {ι A F K : Type} [CommRing A] [Field F] [Field K]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (hT : T ⊆ S) (φ : A →+* F) (f : A →+* K)
    (hf : RingHom.ker φ ≤ RingHom.ker f) (h : GL (Fin 3) F) (H : TriangularForm M d S T φ h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  haveI := RingHom.ker_isPrime f
  have hu : ∀ y : (RingHom.ker f).primeCompl, IsUnit (φ y) := fun y => Ne.isUnit fun e => y.2 (hf e)
  obtain ⟨V, hV, hl⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker f)) hu)
  let g₀ : Localization.AtPrime (RingHom.ker f) →+* V := (IsLocalization.lift hu).codRestrict V.toSubring hV
  haveI : IsLocalHom g₀ := hl
  let g : A →+* V := g₀.comp (algebraMap _ _)
  have hg : V.subtype.comp g = φ := RingHom.ext fun a => IsLocalization.lift_eq hu a
  have hk : RingHom.ker f = RingHom.ker ((residue V).comp g) := by
    ext a
    rw [RingHom.mem_ker (f := (residue V).comp g), RingHom.comp_apply, residue_eq_zero_iff,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (isUnit_map_iff g₀ _).not.symm
  obtain ⟨k, hk'⟩ := iwasawa_triangularization V h
  have H1 := triangular_form_borel_change hT H (Matrix.GeneralLinearGroup.map V.subtype k) hk'
  rw [← map_inv, ← hg] at H1
  have H2 := triangular_form_map (residue V) (triangular_form_of_injective_map V.subtype Subtype.val_injective H1)
  obtain ⟨B, _, _, i, j, e⟩ := exists_common_ring_same_kernel f _ hk
  have H3 := triangular_form_map j H2
  rw [← e] at H3
  exact triangular_form_finite_extension f i _ H3

private theorem triangular_in_iff_triangular_form {O A C D : Type} [CommRing O] [CommRing A] [CommRing C] [Algebra O A] [Algebra O C] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (u : D →* GG 3 A) (hu : HasMult η u) (φ : A →ₐ[O] C)
    (h : GL (Fin 3) C) : UpperTheory.V.UnitaryThreeInertia.TriIn η Ψ I (push φ u) h ↔
      TriangularForm (fun g => (u g).mat) (fun g a => algebraMap O A (UpperTheory.V.UnitaryThreeInertia.psi Ψ a g)) {g | η g = 1}
        {g | g ∈ I ∧ η g = 1} φ h := by
  have e : ∀ g, η g = 1 → (conjBy h⁻¹ (push φ u) g).mat =
      ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (u g).mat.map (φ : A →+* C) * h := by
    intro g hg
    have h1 : (push φ u g).right = 1 := (hu g).trans hg
    have h2 : (push φ u g).left.val = (u g).mat.map (φ : A →+* C) := rfl
    rw [← h2]
    simp [conjBy, GG.mat, h1]
  have hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a := by decide
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg a => ?_⟩
    · rw [← e g hg]
      exact h1 g hg a b ((hw a b).2 hab)
    · rw [← e g hg.2, h2 g hg.1 hg.2 a]
      exact (φ.commutes _).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg hg' a => ?_⟩
    · rw [e g hg]
      exact h1 g hg a b ((hw a b).1 hab)
    · rw [e g hg', h2 g ⟨hg, hg'⟩ a]
      exact φ.commutes _

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.lemma2c :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (K : Type) [Field K] [Algebra O K] (r : GQ l →* GG 3 K), D.On U r → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Algebra O K') (_ : IsScalarTower O K K') (_ : FiniteDimensional K K') (h : GL (Fin 3) K'), UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) ((GG.map (algebraMap K K')).comp r) h := by
  intro hP l _ O _ _ _ _ _ _ _ D U K _ _ r ⟨f, hr, hf⟩
  obtain ⟨-, hp, hl, -⟩ := UpperTheory.V.Loc.rtBasic hP D U
  haveI : IsDomain (D.Rt U) := Ideal.Quotient.isDomain _
  let φ : U.R →ₐ[O] FractionRing (D.Rt U) :=
    (IsScalarTower.toAlgHom O (D.Rt U) (FractionRing (D.Rt U))).comp (Ideal.Quotient.mkₐ O _)
  have hφ : RingHom.ker φ = D.It U := by
    ext a
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (D.Rt U) (FractionRing (D.Rt U)))
  have hl0 : ((l : ℕ) : FractionRing (D.Rt U)) ≠ 0 := fun e => hl (by rw [← hφ, RingHom.mem_ker, map_natCast, e])
  haveI : CharZero (FractionRing (D.Rt U)) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h0
    have h1 : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 h0
    have h2 := congrArg ((algebraMap O (FractionRing (D.Rt U))).comp (algebraMap ℤ_[l] O))
      (PadicInt.unitCoeff_spec h1)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at h2
    exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl0) h2.symm
  obtain ⟨⟨h, H⟩, -⟩ := UpperTheory.V.Loc.lemma2b hP D U _ (push φ U.r.hom) ⟨φ, rfl, hφ.ge⟩
  rw [UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult] at H
  obtain ⟨K', _, _, _, h', H'⟩ := UpperTheory.V.Loc.triangular_form_specialization (fun g hg => hg.2) _ (f : U.R →+* K) (hφ.le.trans hf) h H
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h', ?_⟩
  subst hr
  exact (UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult ((IsScalarTower.toAlgHom O K K').comp f) h').2 H'
