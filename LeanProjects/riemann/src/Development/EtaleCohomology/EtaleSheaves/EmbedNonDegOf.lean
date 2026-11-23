import Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf
  LateralTheory.E.GeometricData

namespace LateralTheory.E.EmbedNonDeg₂

theorem germ_res {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem rA_res {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {W X : Z.Opens}
    (h : W ≤ X) (a : A) : Z.presheaf.map (homOfLE h).op (rA p X a) = rA p W a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := X) le_top (homOfLE h).op
  simp only [rA, RingHom.comp_apply]
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e

theorem int_adjoin {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : Polynomial A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (t : K)
    (hc : ∀ a, φ (f (Polynomial.C a)) = algebraMap A K a) (hX : φ (f Polynomial.X) = t) (x : S) :
    IsIntegral (Algebra.adjoin A {t}) (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  let ψ : Polynomial A →+* Algebra.adjoin A {t} :=
    (Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton A t⟩ : Algebra.adjoin A {t})).toRingHom
  have key : (algebraMap (Algebra.adjoin A {t}) K).comp ψ = φ.comp f := by
    apply Polynomial.ringHom_ext
    · intro a; simp [ψ, hc]
    · simp [ψ, hX]
  refine ⟨P.map ψ, hm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, key, ← Polynomial.hom_eval₂, hP, map_zero]

theorem int_A {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (hc : ∀ a, φ (f a) = algebraMap A K a) (x : S) :
    IsIntegral A (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  refine ⟨P, hm, ?_⟩
  have : algebraMap A K = φ.comp f := RingHom.ext fun a => (hc a).symm
  rw [this, ← Polynomial.hom_eval₂, hP, map_zero]

theorem range_loc {A K : Type} [CommRing A] [Field K] [Algebra A K] {Z : Scheme.{0}} {U W : Z.Opens}
    (hU : IsAffineOpen U) (s : Γ(Z, U)) (hW : Z.basicOpen s = W) (hle : W ≤ U)
    (φU : Γ(Z, U) →+* K) (φW : Γ(Z, W) →+* K)
    (hres : ∀ x, φW (Z.presheaf.map (homOfLE hle).op x) = φU x) (B : Subalgebra A K)
    (hB : ∀ k, k ∈ B ↔ ∃ x, φU x = k) (hs : φU s ≠ 0) (hinv : (φU s)⁻¹ ∈ φW.range) :
    φW.range = (AdjoinInv B (φU s)).toSubring := by
  subst hW
  have := hU.isLocalization_basicOpen s
  ext k; constructor
  · intro hk0
    obtain ⟨z, rfl⟩ := hk0
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e1⟩ := IsLocalization.surj (Submonoid.powers s) z
    have e2 := congrArg φW e1
    rw [map_mul] at e2
    change φW z * φW (Z.presheaf.map (homOfLE hle).op (s ^ n)) = φW (Z.presheaf.map (homOfLE hle).op x) at e2
    rw [hres, hres, map_pow] at e2
    have e3 : φW z = φU x * ((φU s)⁻¹) ^ n := by
      rw [← e2, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]
    change φW z ∈ AdjoinInv B (φU s)
    rw [e3]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _)
    · exact Algebra.subset_adjoin (Or.inl ((hB _).mpr ⟨x, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  · intro hk
    have hBW : ∀ k ∈ B, k ∈ φW.rangeS := by
      intro k hk; obtain ⟨x, rfl⟩ := (hB k).mp hk
      exact ⟨_, hres x⟩
    let R : Subalgebra A K :=
      { toSubsemiring := φW.rangeS, algebraMap_mem' := fun a => hBW _ (B.algebraMap_mem a) }
    have hle' : AdjoinInv B (φU s) ≤ R := by
      rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro k (hk | hk)
      · exact hBW k hk
      · rw [Set.mem_singleton_iff.mp hk]; obtain ⟨y, hy⟩ := hinv; exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hle' hk
    exact ⟨y, hy⟩

theorem EmbedNonDeg_of : EmbedNonDeg := by
  intro A _ _ Z p hI hTop hN
  obtain ⟨U, V, s, s', hU, hV, hUV, hsU, hsV, ⟨z, hz⟩, hss, hiU, hiV⟩ := hN
  have hzU : z ∈ U := (inf_le_left : U ⊓ V ≤ U) hz
  have hzV : z ∈ V := (inf_le_right : U ⊓ V ≤ V) hz
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : Nonempty (U ⊓ V : Z.Opens) := ⟨⟨z, hz⟩⟩
  have : Nonempty (U ⊔ V : Z.Opens) := ⟨⟨z, (le_sup_left : U ≤ U ⊔ V) hzU⟩⟩
  let φU : Γ(Z, U) →+* Z.functionField := (Z.germToFunctionField U).hom
  let φV : Γ(Z, V) →+* Z.functionField := (Z.germToFunctionField V).hom
  let φW : Γ(Z, U ⊓ V) →+* Z.functionField := (Z.germToFunctionField (U ⊓ V)).hom
  let φT : Γ(Z, U ⊔ V) →+* Z.functionField := (Z.germToFunctionField (U ⊔ V)).hom
  let _ : Algebra A Z.functionField := (φU.comp (rA p U)).toAlgebra
  have hcU : ∀ a, φU (rA p U a) = algebraMap A Z.functionField a := fun a => rfl
  have rL : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x) = φU x :=
    fun x => germ_res U (U ⊓ V) inf_le_left x
  have rR : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x) = φV x :=
    fun x => germ_res V (U ⊓ V) inf_le_right x
  have hcV : ∀ a, φV (rA p V a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rL, ← rR, rA_res, rA_res]
  have hmul : φU s * φV s' = 1 := by
    have h := congrArg φW hss
    rw [map_mul, map_one, rL, rR] at h
    exact h
  have ht : φU s ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hs0' : φV s' ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hs'inv : φV s' = (φU s)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φU.rangeS, algebraMap_mem' := fun a => ⟨rA p U a, hcU a⟩ }
  let C : Subalgebra A Z.functionField :=
    { toSubsemiring := φV.rangeS, algebraMap_mem' := fun a => ⟨rA p V a, hcV a⟩ }
  have hWB : φW.range = (AdjoinInv B (φU s)).toSubring :=
    range_loc hU s hsU inf_le_left φU φW rL B (fun _ => Iff.rfl) ht ⟨_, (rR s').trans hs'inv⟩
  have hWC : φW.range = (AdjoinInv C (φV s')).toSubring :=
    range_loc hV s' hsV inf_le_right φV φW rR C (fun _ => Iff.rfl) hs0'
      ⟨_, (rL s).trans (by rw [hs'inv, inv_inv])⟩
  have hglue : AdjoinInv B (φU s) = Algebra.adjoin A ((C : Set Z.functionField) ∪ {φU s}) := by
    have h2 := Subalgebra.toSubring_injective (hWB.symm.trans hWC)
    rw [h2, AdjoinInv, hs'inv, inv_inv]
  have hTop' : (rA p (U ⊔ V)).IsIntegral := by rw [hUV]; exact hTop
  have hcT : ∀ a, φT (rA p (U ⊔ V) a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rA_res p (le_sup_left : U ≤ U ⊔ V) a]
    exact (germ_res (U ⊔ V) U le_sup_left _).symm
  have hBC : ∀ x ∈ B, x ∈ C → IsIntegral A x := by
    intro x hxB hxC
    obtain ⟨u, hu⟩ := hxB
    obtain ⟨v, hv⟩ := hxC
    have heq : Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op u =
        Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op v :=
      Z.germToFunctionField_injective (U ⊓ V) (((rL u).trans (hu.trans hv.symm)).trans (rR v).symm)
    let g := (Z.sheaf.objSupIsoProdEqLocus U V).inv ⟨(u, v), heq⟩
    have hg : Z.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op g = u :=
      Z.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hx : x = φT g := by
      rw [← hu, ← hg]; exact germ_res (U ⊔ V) U le_sup_left g
    rw [hx]
    exact int_A (rA p (U ⊔ V)) hTop' φT hcT g
  have intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {φU s}) b := by
    intro b hb
    obtain ⟨x, rfl⟩ := hb
    exact int_adjoin (Polynomial.eval₂RingHom (rA p U) s) hiU φU (φU s)
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcU a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]) x
  have intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {(φU s)⁻¹}) c := by
    intro c hc
    obtain ⟨x, rfl⟩ := hc
    exact int_adjoin (Polynomial.eval₂RingHom (rA p V) s') hiV φV (φU s)⁻¹
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcV a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact hs'inv) x
  refine ⟨Z.functionField, inferInstance, inferInstance, B, C, φU s,
    ⟨ht, ⟨s, rfl⟩, ⟨s', hs'inv⟩, intB, intC, hglue⟩, hBC, ?_⟩
  exact ⟨U, V, φU, φV, φW, hU, hV, hsU ▸ hU.basicOpen s, hUV,
    Z.germToFunctionField_injective U, Z.germToFunctionField_injective V,
    Z.germToFunctionField_injective (U ⊓ V), SetLike.ext fun _ => Iff.rfl, SetLike.ext fun _ => Iff.rfl, hWB,
    rL, rR, fun a => rfl, hcV⟩

end LateralTheory.E.EmbedNonDeg₂
