import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair.EtForm

open KaehlerDifferential MvPolynomial TrivSqZeroExt

section PolyDer

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  [Algebra R S] [IsScalarTower k R S] {r : ℕ}
  [Algebra (MvPolynomial (Fin r) R) S] [IsScalarTower R (MvPolynomial (Fin r) R) S]

def coeffHom (δ : Derivation k R S) : R →+* TrivSqZeroExt S S where
  toFun a := inl (algebraMap R S a) + inr (δ a)
  map_one' := by ext <;> simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr, map_one,
    Derivation.map_one_eq_zero, add_zero, fst_one, snd_one]
  map_mul' a b := by
    ext
    · simp only [fst_add, fst_inl, fst_inr, fst_mul, map_mul, add_zero]
    · simp only [snd_add, snd_inl, snd_inr, snd_mul, fst_add, fst_inl, fst_inr, zero_add, add_zero,
        Derivation.leibniz, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        Algebra.smul_def]
      ring
  map_zero' := by ext <;> simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr, map_zero,
    add_zero, fst_zero, snd_zero]
  map_add' a b := by
    ext <;> simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr, map_add, add_zero,
      zero_add]

def polyHom (δ : Derivation k R S) (v : Fin r → S) : MvPolynomial (Fin r) R →+* TrivSqZeroExt S S :=
  eval₂Hom (coeffHom δ) fun i => inl (algebraMap (MvPolynomial (Fin r) R) S (X i)) + inr (v i)

theorem polyHom_C (δ : Derivation k R S) (v : Fin r → S) (a : R) :
    polyHom δ v (C a) = inl (algebraMap R S a) + inr (δ a) := by
  simp [polyHom, coeffHom]

theorem polyHom_X (δ : Derivation k R S) (v : Fin r → S) (i : Fin r) :
    polyHom δ v (X i) = inl (algebraMap (MvPolynomial (Fin r) R) S (X i)) + inr (v i) := by
  simp [polyHom]

theorem polyHom_fst (δ : Derivation k R S) (v : Fin r → S) (p : MvPolynomial (Fin r) R) :
    fst (polyHom δ v p) = algebraMap (MvPolynomial (Fin r) R) S p := by
  have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (polyHom δ v) =
      algebraMap (MvPolynomial (Fin r) R) S := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, polyHom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fstHom_apply, fst_add, fst_inl, fst_inr, add_zero, IsScalarTower.algebraMap_apply R (MvPolynomial (Fin r) R) S, MvPolynomial.algebraMap_eq]
    · intro i
      simp only [RingHom.comp_apply, polyHom_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fstHom_apply, fst_add, fst_inl, fst_inr, add_zero]
  exact RingHom.congr_fun this p

def polyDer (δ : Derivation k R S) (v : Fin r → S) : Derivation k (MvPolynomial (Fin r) R) S where
  toFun p := snd (polyHom δ v p)
  map_add' p q := by
    show snd (polyHom δ v (p + q)) = snd (polyHom δ v p) + snd (polyHom δ v q)
    rw [map_add, snd_add]
  map_smul' c p := by
    show snd (polyHom δ v (c • p)) = c • snd (polyHom δ v p)
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, polyHom_fst, MvPolynomial.algebraMap_apply,
      polyHom_C, snd_add, snd_inl, snd_inr, Derivation.map_algebraMap, zero_add, smul_zero, add_zero,
      ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin r) R) S,
      ← IsScalarTower.algebraMap_apply k R S, algebraMap_smul]
  map_one_eq_zero' := by simp
  leibniz' p q := by
    show snd (polyHom δ v (p * q)) = p • snd (polyHom δ v q) + q • snd (polyHom δ v p)
    rw [map_mul, TrivSqZeroExt.snd_mul, polyHom_fst, polyHom_fst]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, Algebra.smul_def,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem polyDer_C (δ : Derivation k R S) (v : Fin r → S) (a : R) : polyDer δ v (C a) = δ a := by
  simp [polyDer, polyHom_C]

theorem polyDer_X (δ : Derivation k R S) (v : Fin r → S) (i : Fin r) : polyDer δ v (X i) = v i := by
  simp [polyDer, polyHom_X]

end PolyDer

section Basis

variable {k K R S : Type} [Field k] [CharZero k] [Field K] [CommRing R] [CommRing S]
  [Algebra k K] [Algebra k R] [Algebra k S] [Algebra R K] [IsScalarTower k R K]
  [Algebra R S] [IsScalarTower k R S] {r n : ℕ}
  [Algebra (MvPolynomial (Fin r) R) S] [IsScalarTower R (MvPolynomial (Fin r) R) S]
  [IsScalarTower k (MvPolynomial (Fin r) R) S] [Algebra.FormallyEtale (MvPolynomial (Fin r) R) S]

def semiσ (σ : K →+* S) (hσR : ∀ a : R, σ (algebraMap R K a) = algebraMap R S a) : K →ₗ[R] S where
  toFun := σ
  map_add' := map_add σ
  map_smul' a f := by rw [Algebra.smul_def, map_mul, hσR, RingHom.id_apply, Algebra.smul_def]

def dualForm (DD : Derivation k (MvPolynomial (Fin r) R) S) : Ω[S⁄k] →ₗ[S] S :=
  (LinearMap.liftBaseChange S DD.liftKaehlerDifferential) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin r) R) S).symm.toLinearMap

omit [CharZero k] in
theorem dualForm_D (DD : Derivation k (MvPolynomial (Fin r) R) S) (p : MvPolynomial (Fin r) R) :
    dualForm DD (D k S (algebraMap _ S p)) = DD p := by
  simp only [dualForm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul, one_smul,
    Derivation.liftKaehlerDifferential_comp_D]

theorem exists_basis_kaehler (σ : K →+* S) (hσR : ∀ a : R, σ (algebraMap R K a) = algebraMap R S a)
    (hσk : ∀ c : k, σ (algebraMap k K c) = algebraMap k S c) (x : Fin n → R)
    (hx : IsTranscendenceBasis k (fun i => algebraMap R K (x i))) :
    ∃ b : Module.Basis (Fin (r + n)) S Ω[S⁄k], ∀ i, b i = D k S (Fin.append
      (fun j => algebraMap (MvPolynomial (Fin r) R) S (X j)) (fun j => algebraMap R S (x j)) i) := by
  classical

  haveI := hx.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k
      (Set.range (fun i => algebraMap R K (x i)))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bK, hbK⟩ := exists_basis_kaehler_of_algebraicIndependent hx.1

  set A := MvPolynomial (Fin r) R
  let Y : Fin (r + n) → A := Fin.append (fun j => X j) (fun j => C (x j))
  have hY : (fun i => algebraMap A S (Y i)) = Fin.append
      (fun j => algebraMap A S (X j)) (fun j => algebraMap R S (x j)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Y]
    · simp only [Y, Fin.append_right]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

  let δx : Fin n → Derivation k R S := fun m =>
    (semiσ σ hσR).compDer (((bK.coord m).compDer (D k K)).compAlgebraMap R)
  have hδx (m i : Fin n) : δx m (x i) = if i = m then 1 else 0 := by
    change σ (bK.coord m (D k K (algebraMap R K (x i)))) = _
    rw [← hbK, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  let DD : Fin (r + n) → Derivation k A S :=
    Fin.append (fun j => polyDer 0 (Pi.single j 1)) (fun m => polyDer (δx m) 0)
  have hDD (j i : Fin (r + n)) : DD j (Y i) = if i = j then 1 else 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [DD, Y, Fin.append_left]
      rw [polyDer_X, Pi.single_apply]
      exact if_congr (Fin.castAdd_injective _ _).eq_iff.symm rfl rfl
    · simp only [DD, Y, Fin.append_left, Fin.append_right]
      rw [polyDer_C, Derivation.zero_apply, if_neg]
      intro h; have := congrArg Fin.val h; simp at this; omega
    · simp only [DD, Y, Fin.append_left, Fin.append_right]
      rw [polyDer_X, Pi.zero_apply, if_neg]
      intro h; have := congrArg Fin.val h; simp at this; omega
    · simp only [DD, Y, Fin.append_right]
      rw [polyDer_C, hδx]
      exact if_congr (Fin.natAdd_injective _ _).eq_iff.symm rfl rfl
  have hΦ (j i : Fin (r + n)) : dualForm (DD j) (D k S (algebraMap A S (Y i))) =
      if i = j then 1 else 0 := by
    rw [dualForm_D, hDD]

  have hli : LinearIndependent S (fun i => D k S (algebraMap A S (Y i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (dualForm (DD j)) hg
    simp only [map_sum, map_smul, hΦ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_zero] at this
    exact this

  letI : Algebra K S := σ.toAlgebra
  haveI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq fun c => (hσk c).symm
  let W := Submodule.span S (Set.range fun i => D k S (algebraMap A S (Y i)))
  have hC (a : R) : D k S (algebraMap R S a) ∈ W := by
    have e : algebraMap R S a = algebraMap K S (algebraMap R K a) := (hσR a).symm
    rw [e, ← KaehlerDifferential.map_D k k K S, ← bK.sum_repr (D k K (algebraMap R K a)), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, ← algebraMap_smul S, hbK, KaehlerDifferential.map_D]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd r i, ?_⟩)
    simp only [Y, Fin.append_right]
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      show algebraMap K S (algebraMap R K (x i)) = algebraMap R S (x i) from hσR _]
  have hA (p : A) : D k S (algebraMap A S p) ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, Derivation.leibniz]
      refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd n i, ?_⟩))
        (Submodule.smul_mem _ _ hp)
      simp [Y]
  have hsp : ⊤ ≤ W := by
    rintro ω -
    obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale k A S).surjective ω
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul s m =>
      rw [tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ _ ?_
      have hm : m ∈ Submodule.span A (Set.range (D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem m hm =>
        obtain ⟨p, rfl⟩ := hm
        rw [KaehlerDifferential.map_D]
        exact hA p
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul a m _ hm =>
        rw [map_smul, ← algebraMap_smul S]
        exact Submodule.smul_mem _ _ hm
  refine ⟨Module.Basis.mk hli hsp, fun i => ?_⟩
  rw [Module.Basis.mk_apply, ← hY]

end Basis

end GlobalTheory.FieldPair.EtForm

namespace GlobalTheory.FieldPair

section Main

variable {L : Type} [Field L] {cL : ℂ →+* L}

theorem isUnit_of_ord_eq_zero (P : Place cL) {u : P.ring} (hu : (u : L) ≠ 0) (h : P.ord u = 0) :
    IsUnit u := by
  have hinv : (u : L)⁻¹ ∈ P.ring := by
    rw [← P.ord_nonneg_iff (inv_ne_zero hu), P.ord_inv, h, neg_zero]
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hu))

end Main

theorem formOrd_dForm_append_eq_zero : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) →
  P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = 0 := by
  intro K L _ _ cK cL n r R T ι ψ τ x P hT hx hP h0

  letI : Algebra ℂ K := cK.toAlgebra
  letI : Algebra ℂ R := (cK.codRestrict R hT.base.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra ℂ P.ring := P.const.toAlgebra
  let j : T →+* P.ring := T.subtype.codRestrict P.ring fun t => hP.1 _ t.2
  have hj (t : T) : ((j t : P.ring) : L) = t := rfl
  have hc (c : ℂ) : j (ι (algebraMap ℂ R c)) = algebraMap ℂ P.ring c := Subtype.ext (hT.const c)
  letI : Algebra R P.ring := (j.comp ι).toAlgebra
  haveI : IsScalarTower ℂ R P.ring := IsScalarTower.of_algebraMap_eq fun c => (hc c).symm

  let α : MvPolynomial (Fin r) R →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra (MvPolynomial (Fin r) R) P.ring := (j.comp α).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) P.ring := IsScalarTower.of_algebraMap_eq fun a => by
    change j (ι a) = j (α (MvPolynomial.C a))
    simp [α]
  haveI : IsScalarTower ℂ (MvPolynomial (Fin r) R) P.ring := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ R (MvPolynomial (Fin r) R),
      ← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin r) R) P.ring]
    exact (hc c).symm

  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) P.ring := by
    letI : Algebra (MvPolynomial (Fin r) R) T := α.toAlgebra
    haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) T := hT.etale
    letI : Algebra T P.ring := j.toAlgebra
    haveI : IsScalarTower (MvPolynomial (Fin r) R) T P.ring := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let M : Submonoid T := (IsUnit.submonoid P.ring).comap j
    haveI : IsLocalization M P.ring :=
      { map_units := fun y => y.2
        surj := fun f => by
          obtain ⟨a, ha, b, hb, hb0, hord, e⟩ := hP.2 f f.2
          refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, isUnit_of_ord_eq_zero P (u := j ⟨b, hb⟩) hb0 hord⟩), ?_⟩
          exact Subtype.ext e
        exists_of_eq := fun {a b} e => ⟨1, by
          have : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
          rw [Subtype.ext this]⟩ }
    haveI : Algebra.FormallyEtale T P.ring := .of_isLocalization M
    exact Algebra.FormallyEtale.comp (MvPolynomial (Fin r) R) T P.ring

  have hι0 (g : R) (hg : g ≠ 0) : (ι g : L) ≠ 0 := fun e => hg (by
    have : ι g = 0 := Subtype.ext e
    rw [← hT.retr g, this, map_zero])
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 Subtype.val_injective
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hT.base.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show f = a / b
    rw [← e, mul_div_cancel_right₀ f hb0]
  have hunit : ∀ y : nonZeroDivisors R, IsUnit ((j.comp ι) y) := fun y =>
    have hy : (y : R) ≠ 0 := nonZeroDivisors.ne_zero y.2
    isUnit_of_ord_eq_zero P (u := j (ι y)) (hι0 _ hy) (h0 _ hy)
  let σ : K →+* P.ring := IsLocalization.lift (M := nonZeroDivisors R) hunit
  have hσR (a : R) : σ (algebraMap R K a) = algebraMap R P.ring a := IsLocalization.lift_eq hunit a
  have hσk (c : ℂ) : σ (algebraMap ℂ K c) = algebraMap ℂ P.ring c := by
    rw [IsScalarTower.algebraMap_apply ℂ R K, hσR, ← IsScalarTower.algebraMap_apply]

  obtain ⟨b, hb⟩ := EtForm.exists_basis_kaehler (k := ℂ) (S := P.ring) (r := r) σ hσR hσk x hx
  have hω := isFreeGen_dForm (α := P.const) _ b hb
  have e := P.formOrd_toRat hω
  have e2 := formMap_dForm (D := r + n) P.ring.subtype (α := P.const) (β := cL) rfl
    (Fin.append (fun j => algebraMap (MvPolynomial (Fin r) R) P.ring (MvPolynomial.X j))
      fun j => algebraMap R P.ring (x j))
  have key : (fun i => P.ring.subtype (Fin.append
      (fun j => algebraMap (MvPolynomial (Fin r) R) P.ring (MvPolynomial.X j))
      (fun j => algebraMap R P.ring (x j)) i)) =
      Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left, Fin.append_left]
      change ((j (α (MvPolynomial.X i)) : P.ring) : L) = (τ i : L)
      simp [α, hj]
    · rw [Fin.append_right, Fin.append_right]
      rfl
  rw [Place.toRat, e2, key] at e
  exact e

end GlobalTheory.FieldPair
