import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParamFrame

theorem linearIndependent_toCotangent {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m : ℕ} (r : Fin m → R) (hrsp : FinalTheorems.Rsp R m r) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R) :
    LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
  classical
  haveI : IsRegularLocalRing R := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hrsp.2, ← hrsp.1]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range r)
    have h2 : (Set.range r).ncard ≤ m := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
    rw [← hrsp.2] at this
    exact_mod_cast this
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
  have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hrsp.1
  rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
  rw [← Set.range_comp] at hsp
  exact hsp.ge

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.AdaptedFrame in

theorem exists_frame_of_rsp : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) (c : ℕ) (a : Fin c → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U.1 y hy (a i)) → ∃ (V : Y.Opens) (hV : V ≤ U.1) (_ : y ∈ V) (z : Fin n → Γ(Y, V)) (e : Fin c ↪ Fin n), (∀ j, z (e j) = resG Y hV (a j)) ∧ IsFrame (dOn q z) := by
  classical
  intro k _ _ X _ _ p n _ y O hyO m s hrsp
  let f : Fin m → X.presheaf.stalk y := fun i => X.presheaf.germ O.1 y hyO (s i)
  have hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := linearIndependent_toCotangent f hrsp hf
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : Fin m → Γ(X, U) := fun j => resG X hUO (s j)
  have hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]

  let a : Fin m → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra k (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := k) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄k] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D k (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)
      rw [map_sum] at e1
      change KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hWU.trans hUO, hyW, fun i => resG X hWU (z i), ⟨e, he⟩, fun j => ?_, ?_⟩
  · simp only [z, z₀, Function.Embedding.coeFn_mk, he.extend_apply]
    exact resG_resG _ _ _
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.ParamFrame
