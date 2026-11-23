import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra (K ⊗[ℂ] κ') L]

theorem isLocalization_locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) :
    letI := (toQ (L := L) 𝔭).toAlgebra
    IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  refine ⟨fun s => isUnit_toQ 𝔭 hinj s.2, fun x => ?_, fun {a b} h => ⟨1, ?_⟩⟩
  · obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
    exact ⟨(a, ⟨s, hs⟩), e⟩
  · have : a = b := Subtype.ext (hinj (congrArg Subtype.val h))
    rw [this]

theorem formallyEtale_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) : (toQ (L := L) 𝔭).FormallyEtale := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  haveI := isLocalization_locAt (L := L) 𝔭 hinj
  exact Algebra.FormallyEtale.of_isLocalization 𝔭.primeCompl

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]

theorem isFreeGen_locAt {n k' : ℕ} (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime]
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭)
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
    (hτ : TrBasis (algebraMap ℂ κ') τ') (z : Fin n → E.ring)
    (b : Module.Basis (Fin n) E.ring (Omega E.const)) (hb : ∀ i, b i = dFun E.const (z i)) :
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc)
      (Fin.append (fun i => toQ 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)
        (fun i => toQ 𝔭 ⟨(z i : K) ⊗ₜ 1, tmul_mem (z i).2 1⟩))) := by
  letI : Algebra ℂ E.ring := E.const.toAlgebra
  let f : E.ring ≃ₐ[ℂ] placeAlg E :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let θ : E.ring ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') (placeAlg E) :=
    (Algebra.TensorProduct.congr f AlgEquiv.refl).trans (tensEquiv (placeAlg E))
  have hθ (a : E.ring) (c : κ') : (θ (a ⊗ₜ c) : K ⊗[ℂ] κ') = (a : K) ⊗ₜ c := rfl
  have hθe : (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E)).FormallyEtale := by
    letI := (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E)).toAlgebra
    exact Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId (E.ring ⊗[ℂ] κ') (tens (κ' := κ') (placeAlg E)))
        θ.bijective)
  let ψ : E.ring ⊗[ℂ] κ' →+* locAt (L := L) 𝔭 :=
    (toQ (L := L) 𝔭).comp (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E))
  have hψ : ψ.FormallyEtale := RingHom.FormallyEtale.comp hθe (formallyEtale_toQ 𝔭 hinj)
  let ρ : E.ring →+* locAt (L := L) 𝔭 := ψ.comp Algebra.TensorProduct.includeLeftRingHom
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := E.ring) τ'
    (GlobalTheory.DiagLoc.formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toQ (L := L) 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hψ using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      rfl
  have hρ : ρ.comp E.const = (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have := GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial E.const
    ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) ρ hρ z b hb
    (fun i => toQ (L := L) 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩) hφ
  exact this

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

variable {K : Type} [Field K] [Algebra ℂ K]

theorem exists_unit_mul_zpow (E : Place (algebraMap ℂ K)) {t : E.ring} (ht : Irreducible t)
    {f : K} (hf : f ≠ 0) : ∃ u : E.ring, IsUnit u ∧ f = (u : K) * (t : K) ^ E.ord f := by
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set v : K := f * (t : K) ^ (-E.ord f) with hv
  have hv0 : v ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ ht0)
  have hvo : E.ord v = 0 := by
    rw [hv, E.ord_mul hf (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  obtain ⟨h1, h2⟩ := (E.ord_eq_zero_iff hv0).1 hvo
  refine ⟨⟨v, h1⟩, IsUnit.of_mul_eq_one (⟨v⁻¹, h2⟩ : E.ring) (Subtype.ext (mul_inv_cancel₀ hv0)), ?_⟩
  change f = v * _
  rw [hv, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem exists_matrix_dFun {K : Type} [Field K] (c₀ : ℂ →+* K) {n : ℕ} (E : Place (c₀)) (z : Fin n → E.ring)
    (b : Module.Basis (Fin n) E.ring (Omega E.const)) (hb : ∀ i, b i = dFun E.const (z i))
    (x : Fin n → K) (hx : TrBasis (c₀) x) :
    ∃ c : Matrix (Fin n) (Fin n) K,
      (∀ i, dFun (c₀) (x i) = ∑ j, c i j • (dFun (c₀) (z j : K) : Omega (c₀))) ∧
      c.det ≠ 0 ∧ E.formOrd (dForm (c₀) x) = E.ord c.det := by
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin n) K (Omega (c₀)),
      ∀ j, b' j = dFun (c₀) (z j : K) := by
    letI := E.const.toAlgebra
    letI := (c₀).toAlgebra
    haveI : IsScalarTower ℂ E.ring K := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨fracKaehlerBasis K b, fun j => ?_⟩
    simp only [fracKaehlerBasis_apply, hb, dFun, KaehlerDifferential.map_D]
    rfl
  let c : Matrix (Fin n) (Fin n) K := fun i j => b'.repr (dFun (c₀) (x i)) j
  have hc : ∀ i, dFun (c₀) (x i) = ∑ j, c i j • dFun (c₀) (z j : K) :=
    fun i => by
      simp_rw [← hb']
      exact (b'.sum_repr _).symm
  have hω := isFreeGen_dForm z b hb
  have hdet : dForm (c₀) x = c.det • E.toRat n (dForm E.const z) := by
    have hz : E.toRat n (dForm E.const z) = dForm c₀ (fun j => (z j : K)) :=
      formMap_dForm _ _ z
    rw [dForm_eq_det_smul x (fun j => (z j : K)) c hc, hz]
  have hc0 : c.det ≠ 0 := by
    intro h0
    have hfree := isFreeGen_dForm_of_trBasis (c₀) hx
    rw [hdet, h0, zero_smul] at hfree
    exact one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp))
  exact ⟨c, hc, hc0, by rw [hdet]; exact E.formOrd_smul_toRat hω hc0⟩

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem dForm_append_eq_det_smul {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {r n : ℕ} (a : Fin r → A) (f w : Fin n → A) (c : Matrix (Fin n) (Fin n) A)
    (h : ∀ i, dFun α (f i) = ∑ j, c i j • dFun α (w j)) :
    dForm α (Fin.append a f) = c.det • dForm α (Fin.append a w) := by
  let M : Matrix (Fin (r + n)) (Fin (r + n)) A :=
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) A) 0 0 c).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm
  have hM : M.det = c.det := by
    simp [M, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Fin.append_left, Fin.append_right, Matrix.one_apply]
  · simp [M, Fin.append_left, Fin.append_right, h]

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem exists_isFreeGen_locAt_formOrd : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.formOrd (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ n k' x τ' E 𝔭 _ t hc hx hτ _ ht
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨z, b, hb⟩ : ∃ (z : Fin n → E.ring) (b : Module.Basis (Fin n) E.ring (Omega E.const)),
      ∀ i, b i = dFun E.const (z i) := by
    letI := E.const.toAlgebra
    letI := (algebraMap ℂ K).toAlgebra
    haveI : IsScalarTower ℂ E.ring K := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ E.ring := E.essFiniteType
    haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ E.ring
    obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ K b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [h1, Cardinal.mk_fin] at h2
    obtain rfl : n = m + 1 := by exact_mod_cast h2
    exact ⟨z, b, hb⟩
  obtain ⟨c, hcx, hc0, hord⟩ := exists_matrix_dFun (algebraMap ℂ K) E z b hb x hx
  obtain ⟨u, hu, hfu⟩ := exists_unit_mul_zpow E ht hc0
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  let j : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hj : j.comp (algebraMap ℂ K) = algebraMap ℂ L := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let y : Fin (k' + n) → locAt (L := L) 𝔭 :=
    Fin.append (fun i => toQ 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)
      (fun i => toQ 𝔭 ⟨(z i : K) ⊗ₜ 1, tmul_mem (z i).2 1⟩)
  have hy : (fun i => (y i : L)) = Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => j (z i : K)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [y, Fin.append_left]
    · simp [y, Fin.append_right, j]
  refine ⟨y, toQ 𝔭 ⟨(u : K) ⊗ₜ 1, tmul_mem u.2 1⟩, isFreeGen_locAt τ' E 𝔭 hc hinj hτ z b hb,
    IsUnit.of_mul_eq_one (toQ 𝔭 ⟨(v : K) ⊗ₜ 1, tmul_mem v.2 1⟩) ?_, ?_⟩
  · rw [← map_mul, ← map_one (toQ (L := L) 𝔭)]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← Subring.coe_mul, hv]
    rfl
  · rw [hy, hord]
    refine (dForm_append_eq_det_smul (algebraMap ℂ L)
      (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i)) (fun i => j (x i)) (fun i => j (z i : K))
      (c.map j) fun i => ?_).trans ?_
    letI := (algebraMap ℂ K).toAlgebra
    letI := (algebraMap ℂ L).toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq' hj.symm
    have e := congrArg (KaehlerDifferential.map ℂ ℂ K L) (hcx i)
    rw [map_sum] at e
    simp only [map_smul, KaehlerDifferential.map_D] at e
    simp only [Matrix.map_apply]
    rw [show dFun (algebraMap ℂ L) (j (x i)) = KaehlerDifferential.D ℂ L (algebraMap K L (x i)) from rfl, e]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← algebraMap_smul L (c i l)]
    rfl
    congr 1
    rw [show (c.map j).det = j c.det from (RingHom.map_det j c).symm]
    generalize E.ord c.det = a at hfu ⊢
    rw [hfu, map_mul, map_zpow₀]
    rfl

end GlobalTheory.GraphLocal
