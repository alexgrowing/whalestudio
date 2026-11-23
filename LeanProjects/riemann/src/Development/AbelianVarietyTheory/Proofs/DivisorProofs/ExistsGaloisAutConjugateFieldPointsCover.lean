import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} := fun a ha =>
    M.ringOn_anti (fun z (hz : q z = x) => show q z ∈ V by rw [hz]; exact hxV) ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)

  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) := by
    refine GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => ?_
    rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K) with hz
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := by
    intro a ha
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have hcz := M.ringOn_le_O hzU hc
    have hdz := M.ringOn_le_O hzU hd
    have hq : c / d ∈ M.O z := ha
    have e1 := val_mul hsp hq hdz
    have e1' := val_mul hsp' hq hdz
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr hdz hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := by rw [← h d (hsub d hd)]; exact hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  have hW : z ∈ W := h₁ (x := IsLocalRing.closedPoint K) trivial
  ext f
  have e1 := val_valF ((top_le_preimage_iff y W).1 h₁) f
  have e2 := val_valF ((top_le_preimage_iff y' W).1 h₂) f
  have e3 := hO _ (valF_mem_O hW f)
  rw [e1, e2] at e3
  unfold valF at e3
  rw [dif_pos h₁, dif_pos h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  have hσB : ∀ (σ : L ≃ₐ[F] L) (b : L), b ∈ B → σ b ∈ B := fun σ b hb =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 hb))
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ =>
    ((σ : L →+* L).comp B.subtype).codRestrict B fun b => hσB σ b b.2
  have hσB_apply : ∀ σ (b : B), ((σB σ b : B) : L) = σ b := fun _ _ => rfl

  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := by
    intro b
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := by
      intro τ
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
      rfl
    have hcoeff : ∀ n, ∃ a : A, algebraMap A L a = (P.coeff n : L) := by
      intro n
      have hfix : ∀ τ : L ≃ₐ[F] L, τ (P.coeff n : L) = P.coeff n := by
        intro τ
        have := congrArg (fun p => Polynomial.coeff p n) (hPmap τ)
        simpa [Polynomial.coeff_map] using this
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 hfix
      change algebraMap F L f = _ at hf
      have hint : IsIntegral A (algebraMap F L f) := by rw [hf]; exact (hB _).1 (P.coeff n).2
      have hint' : IsIntegral A f := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective]
        exact hint
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have hmap : P.map e = P.map e' := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoeff n
      exact hA _ ⟨a, ha⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ =>
    (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun σ b => by
    simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨σ, hσ⟩ := claim b
    refine Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [zero_vadd]
    exact (hmemH σ b).2 hσ
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  have hcσ : c = σB σ b := Subtype.ext hc
  subst hcσ
  have hn : (H σ).index ≠ 0 := hfin.index_ne_zero
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  haveI : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := by
    intro b
    letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b := by
      constructor
      · intro hb
        exact IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb
      · intro hb
        refine IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => ?_) hb
        show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
        rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]
    rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hz : q (y (IsLocalRing.closedPoint K)) = z₁ := rfl
  have hz' : q (y' (IsLocalRing.closedPoint K)) = z₁ := by rw [hz₁, hyy]; rfl
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz'))
  have he : ∀ b : B, e b = M₂.val y b := fun _ => rfl
  have he' : ∀ b : B, e' b = M₂.val y' b := fun _ => rfl
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    rw [he, he', ← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  haveI := hF
  have key : y ≫ s = y' := by
    refine eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => ?_
    have hys : (y ≫ s) ≫ q = y ≫ q := by rw [Category.assoc, hs2]
    rw [hys] at hb
    have hbB : b ∈ B := hb
    have hσB : σ b ∈ B := (hB _).2
      (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hbB))
    rw [hs3]
    exact (hσ ⟨b, hbB⟩ ⟨σ b, hσB⟩ rfl).symm
  refine ⟨σ, s, hs1, key, fun b => ?_⟩
  rw [← key]
  exact hs3 K y b

end GlobalTheory.Poinc.FieldConj
