import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingTensorOfFractionFieldsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TensorTower

theorem isFractionRing_of_injective {A F : Type} [CommRing A] [Field F] [Algebra A F]
    (hi : Function.Injective (algebraMap A F))
    (hs : ∀ z : F, ∃ x y : A, algebraMap A F y ≠ 0 ∧ z * algebraMap A F y = algebraMap A F x) :
    IsFractionRing A F := by
  haveI : IsDomain A := hi.isDomain (algebraMap A F)
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} e => ⟨1, by simp [hi e]⟩⟩
  · exact (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero y.2) |>.isUnit
  · obtain ⟨x, y, hy, e⟩ := hs z
    exact ⟨⟨x, y, mem_nonZeroDivisors_of_ne_zero fun h => hy (by simp [h])⟩, e⟩

theorem isFractionRing_subring {K : Type} [Field K] (R : Subring K)
    (h : ∀ f : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ f * b = a) : IsFractionRing R K :=
  isFractionRing_of_injective Subtype.val_injective fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, e⟩

theorem exists_residue {κ : Type} [Field κ] [Algebra ℂ κ] (B : Subring κ)
    (hB : IsLocModel (algebraMap ℂ κ) B) (hr : RatRes (algebraMap ℂ κ) B) :
    ∃ ev : B →+* ℂ, ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔ ev b = a := by
  haveI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ).codRestrict B hB.const_mem
  let g : ℂ →+* IsLocalRing.ResidueField B := (IsLocalRing.residue B).comp c0
  have key : ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔
      IsLocalRing.residue B b = g a := fun b a => by
    rw [show (b : κ) - algebraMap ℂ κ a = ((b - c0 a : B) : κ) from rfl, nonUnit_iff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    show _ ↔ Ideal.Quotient.mk _ b = Ideal.Quotient.mk _ (c0 a)
    rw [Ideal.Quotient.eq]
  have hbij : Function.Bijective g := ⟨g.injective, fun y => by
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr b b.2
    exact ⟨a, ((key b a).1 ha).symm⟩⟩
  let e := RingEquiv.ofBijective g hbij
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue B), fun b a => ?_⟩
  rw [key]
  show _ ↔ e.symm _ = a
  rw [e.symm_apply_eq]
  rfl

theorem exists_isEtTower_tensor : ∀ {K κ L : Type} [Field K] [Field κ] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ) L] [IsScalarTower ℂ (K ⊗[ℂ] κ) L] [IsFractionRing (K ⊗[ℂ] κ) L]
    (R : Subring K) (B : Subring κ) (hB : IsLocModel (algebraMap ℂ κ) B) (r : ℕ) (τ : Fin r → B),
  IsLocModel (algebraMap ℂ K) R → IsIntegrallyClosed R → RatRes (algebraMap ℂ K) R →
  RatRes (algebraMap ℂ κ) B → (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) →
  (MvPolynomial.eval₂Hom ((algebraMap ℂ κ).codRestrict B hB.const_mem) τ).FormallyEtale →
  ∃ (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (j : B →+* T),
    IsEtTower (algebraMap ℂ K) R (algebraMap ℂ L) T ι ψ (fun i => j (τ i)) ∧
    (∀ a : R, (ι a : L) = algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ 1)) ∧
    (∀ b : B, (j b : L) = algebraMap (K ⊗[ℂ] κ) L (1 ⊗ₜ (b : κ))) ∧
    (∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) → ((ψ (j b) : R) : K) = algebraMap ℂ K a) ∧
    (∀ t : T, ∃ s s' : T, s ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧
      s' ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧ IsUnit (ψ s') ∧ (t : L) * s' = s) := by
  intro K κ L _ _ _ _ _ _ _ _ _ R B hB r τ hR hRn hRr hBr hm he
  haveI := hR.isLocalRing
  haveI := hB.isLocalRing
  letI iR : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI iB : Algebra ℂ B := ((algebraMap ℂ κ).codRestrict B hB.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ B κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing R K := isFractionRing_subring R hR.frac
  haveI : IsFractionRing B κ := isFractionRing_subring B hB.frac
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.isFractionRing_tensor_of_fraction_fields (k := ℂ) (R := R) (B := B) (K := K) (κ := κ) (L := L)
  set f := (algebraMap (K ⊗[ℂ] κ) L).comp (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom ℂ R K) (IsScalarTower.toAlgHom ℂ B κ)).toRingHom with hf
  letI iA : Algebra (R ⊗[ℂ] B) L := f.toAlgebra
  haveI : IsFractionRing (R ⊗[ℂ] B) L := isFractionRing_of_injective hinj hsurj
  haveI : IsDomain (R ⊗[ℂ] B) := hinj.isDomain f
  haveI : Nontrivial (R ⊗[ℂ] B) := IsDomain.toNontrivial
  have hft : ∀ (a : R) (b : B), algebraMap (R ⊗[ℂ] B) L (a ⊗ₜ b) =
      algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ (b : κ)) := fun a b => rfl

  obtain ⟨ev, hev⟩ := exists_residue B hB hBr
  have hevc : ∀ a : ℂ, ev (algebraMap ℂ B a) = a := fun a =>
    (hev _ a).1 (by
      rw [show ((algebraMap ℂ B a : B) : κ) = algebraMap ℂ κ a from rfl, sub_self]
      exact nonUnit_zero B)
  let ev' : B →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  let φ : R ⊗[ℂ] B →ₐ[ℂ] R := Algebra.TensorProduct.lift (AlgHom.id ℂ R)
    ((Algebra.ofId ℂ R).comp ev') (fun _ _ => Commute.all _ _)
  have hφ : ∀ (a : R) (b : B), φ (a ⊗ₜ b) = a * algebraMap ℂ R (ev b) := fun a b => by
    simp [φ, ev']
  let q : Ideal (R ⊗[ℂ] B) := (IsLocalRing.maximalIdeal R).comap φ
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hq : q.primeCompl ≤ nonZeroDivisors (R ⊗[ℂ] B) := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (R ⊗[ℂ] B) L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  have hu : ∀ y : q.primeCompl, IsUnit (φ.toRingHom y) := fun y => by
    by_contra hy
    exact y.2 (show (y : R ⊗[ℂ] B) ∈ q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : A →+* R := IsLocalization.lift hu
  have hψ : ∀ x, ψ (algebraMap _ A x) = φ x := IsLocalization.lift_eq hu
  let a : R ⊗[ℂ] B →+* A := algebraMap _ A
  have ha : ∀ x, (a x : L) = algebraMap (R ⊗[ℂ] B) L x := fun x => rfl
  let ι : R →+* A := a.comp Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A := a.comp Algebra.TensorProduct.includeRight.toRingHom
  have hcL : ∀ z : ℂ, algebraMap (R ⊗[ℂ] B) L (algebraMap ℂ _ z) = algebraMap ℂ L z := fun z => by
    rw [Algebra.TensorProduct.algebraMap_apply, hft, IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ) L,
      Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcl : ∀ x, a x ∈ Subring.closure (Set.range ι ∪ Set.range j) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have e : a (x ⊗ₜ y) = ι x * j y := by
        simp [ι, j, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨y, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  have hmem : ∀ z : ℂ, algebraMap ℂ L z ∈ A.toSubring := fun z => by
    rw [← hcL]; exact A.algebraMap_mem _
  have hevτ : ∀ i, ev (τ i) = 0 := fun i => by
    refine (hev _ 0).1 ?_
    rw [map_zero, sub_zero]
    refine (nonUnit_iff (τ i)).2 fun hu => ?_
    have : τ i ∈ IsLocalRing.maximalIdeal B := by
      rw [hm]; exact Ideal.subset_span ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 this hu
  refine ⟨A.toSubring, ι, ψ, j, ⟨hR, hRn, ⟨hmem, IsLocalization.AtPrime.isLocalRing A q, ?_, ?_⟩,
    fun z => ?_, fun x => ?_, fun i => ?_, ?_⟩, fun x => rfl, fun y => rfl, fun b z hbz => ?_,
    fun t => ?_⟩
  · have e : (algebraMap ℂ L).codRestrict A.toSubring hmem = a.comp (algebraMap ℂ (R ⊗[ℂ] B)) :=
      RingHom.ext fun z => Subtype.ext (hcL z).symm
    rw [e]
    haveI : Algebra.EssFiniteType ℂ R := RingHom.essFiniteType_algebraMap.1 hR.essFiniteType
    haveI : Algebra.EssFiniteType ℂ B := RingHom.essFiniteType_algebraMap.1 hB.essFiniteType
    haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] B) := Algebra.EssFiniteType.comp ℂ R _
    have h1 : (algebraMap (R ⊗[ℂ] B) A).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
    have h2 : (algebraMap ℂ (R ⊗[ℂ] B)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
    exact h2.comp h1
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R ⊗[ℂ] B) z
    have hy' : algebraMap (R ⊗[ℂ] B) L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · exact (ha _).trans (hcL z)
  · show ψ (a (x ⊗ₜ 1)) = x
    rw [hψ, hφ, map_one, map_one, mul_one]
  · show ψ (a (1 ⊗ₜ τ i)) = 0
    rw [hψ, hφ, hevτ, map_zero, mul_zero]
  · have e : MvPolynomial.eval₂Hom ι (fun i => j (τ i)) =
        a.comp (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℂ] B)
          (fun i => (1 : R) ⊗ₜ[ℂ] τ i)) := by
      ext x <;> simp [ι, j]
    rw [e]
    have h1 : (algebraMap (R ⊗[ℂ] B) A).FormallyEtale :=
      RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl)
    exact (GlobalTheory.T.formallyEtale_baseChange_eval_hom τ he).comp h1
  · show ((ψ (a (1 ⊗ₜ b)) : R) : K) = _
    rw [hψ, hφ, one_mul, (hev b z).1 hbz]
    rfl
  · obtain ⟨⟨x, y⟩, e⟩ := IsLocalization.surj q.primeCompl (S := A) t
    refine ⟨a x, a y, hcl x, hcl y, ?_, congrArg Subtype.val e⟩
    rw [hψ]; exact hu y

end GlobalTheory.FieldPair.TensorTower
