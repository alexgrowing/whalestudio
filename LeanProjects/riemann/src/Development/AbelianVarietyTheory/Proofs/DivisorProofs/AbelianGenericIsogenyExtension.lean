import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeExtensionCompleteToDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeExtensionOverCodimOnePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedLatticeLagrangianSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisiblePolarizationLiftGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleHomDualExtendsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleWeilPairingIntegralExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionLagrangianSignStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleEndomorphismCommuteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianExtensionAbelianGenericHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleTowerBaseChangeMapExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleInclusionCompatibleTowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheoremStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAntisymmetricOfSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAdjointEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDegEqPowMulCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.Cris (dp0)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

theorem adapted_comap {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {H : Type 1} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    [Module.Finite K H] {D D₁ : Type} [AddCommGroup D] [Module K D] [Module R D] [IsScalarTower R K D]
    [AddCommGroup D₁] [Module K D₁] (E : H ≃ₗ[K] D) {β : LinearMap.BilinForm K H} {F : Submodule K H}
    {Ω : Submodule R H} {p : ℕ} {Fr : H → H} {Fr' : D → D} {W : Submodule K D} {Ω' Λ : Submodule R D} {V : D → D₁}
    {i : D → D₁} (β₁ : Function.Injective β) (β₂ : ∀ s w, β s w = -β w s) (β₃ : IsLagr β F)
    (β₄ : IsLagr β (Submodule.span K (Set.range Fr))) (hF : ∀ c, c ∈ F ↔ E c ∈ W) (hΩ : ∀ c, c ∈ Ω ↔ E c ∈ Ω')
    (f₁ : ∀ x, ∀ y ∈ F, Fr (x + y) = Fr x) (v₁ : ∀ z, E (Fr z) = Fr' (E z))
    (v₂ : ∀ (s z : H) (n : ℕ) (r : Fin n → K) (w : Fin n → H), V (E s) = ∑ l, r l • i (E (w l)) →
      β s (Fr z) = ∑ l, r l * β (w l) z ^ p)
    (a₁ : Λ.FG) (a₂ : Λ ⊓ W.restrictScalars R = Ω')
    (a₃ : ∀ x ∈ Λ, ∃ (n : ℕ) (r : Fin n → R) (y : Fin n → D), (∀ l, y l ∈ Ω') ∧
      V x = ∑ l, algebraMap R K (r l) • i (y l))
    (a₄ : Λ ⊓ (Submodule.span K (Set.range Fr')).restrictScalars R = Submodule.span R (Fr' '' (Λ : Set D)))
    (a₅ : Λ ⊔ W.restrictScalars R = LinearMap.BilinForm.dualSubmodule
      (LinearMap.compl₁₂ β E.symm.toLinearMap E.symm.toLinearMap) Ω') :
    ∃ L : Submodule R H, (∀ c, c ∈ L ↔ E c ∈ Λ) ∧ L.FG ∧ IsAdapted β F Ω L ∧
      IsAdapted β (Submodule.span K (Set.range Fr)) (Submodule.span R (Fr '' (β.dualSubmodule Ω : Set H))) L := by
  let ER : H ≃ₗ[R] D := E.restrictScalars R
  let o := (Submodule.orderIsoMapComap ER).symm
  have ho : ∀ N c, c ∈ o N ↔ E c ∈ N := fun _ _ => Iff.rfl
  have o₁ : o (W.restrictScalars R) = F.restrictScalars R := Submodule.ext fun c => (hF c).symm
  have o₂ : o Ω' = Ω := Submodule.ext fun c => (hΩ c).symm
  have o₃ : o (LinearMap.BilinForm.dualSubmodule (LinearMap.compl₁₂ β E.symm.toLinearMap E.symm.toLinearMap) Ω') =
      β.dualSubmodule Ω :=
    Submodule.ext fun c => (ho _ c).trans ⟨fun H y hy => by simpa using H (E y) ((hΩ y).1 hy),
      fun H y hy => by simpa using H (E.symm y) ((hΩ _).2 (by simpa using hy))⟩
  have o₄ : o ((Submodule.span K (Set.range Fr')).restrictScalars R) =
      (Submodule.span K (Set.range Fr)).restrictScalars R := Submodule.ext fun c => by
    have k : (Submodule.span K (Set.range Fr)).map E.toLinearMap = Submodule.span K (Set.range Fr') := by
      rw [Submodule.map_span, ← Set.range_comp, ← E.surjective.range_comp Fr']
      exact congrArg (fun z => Submodule.span K (Set.range z)) (funext v₁)
    rw [ho, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, ← k, Submodule.mem_map_equiv,
      E.symm_apply_apply]
  have o₅ : o (Submodule.span R (Fr' '' (Λ : Set D))) = Submodule.span R (Fr '' (o Λ : Set H)) := by
    rw [OrderIso.symm_apply_eq]
    change _ = Submodule.map ER.toLinearMap _
    rw [Submodule.map_span]
    refine congrArg _ (Set.ext fun x => ⟨?_, ?_⟩)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := E.surjective y
      exact ⟨_, ⟨c, hy, rfl⟩, v₁ c⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨E c, hc, (v₁ c).symm⟩
  have fg : (o Λ).FG := by
    have k := a₁.map ER.symm.toLinearMap
    rwa [Submodule.map_equiv_eq_comap_symm] at k
  have H₁ : o Λ ⊓ F.restrictScalars R = Ω := by rw [← o₁, ← o.map_inf, a₂, o₂]
  have H₂ : o Λ ⊔ F.restrictScalars R = β.dualSubmodule Ω := by rw [← o₁, ← o.map_sup, a₅, o₃]
  have H₃ : o Λ ⊓ (Submodule.span K (Set.range Fr)).restrictScalars R = Submodule.span R (Fr '' (o Λ : Set H)) := by
    rw [← o₄, ← o.map_inf, a₄, o₅]
  have H₄ : Fr '' (β.dualSubmodule Ω : Set H) = Fr '' (o Λ : Set H) := by
    rw [← H₂]
    refine Set.Subset.antisymm ?_ (Set.image_mono (SetLike.coe_mono le_sup_left))
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hc
    exact ⟨x, hx, (f₁ x y hy).symm⟩
  have H₅ : o Λ ≤ β.dualSubmodule (o Λ ⊓ (Submodule.span K (Set.range Fr)).restrictScalars R) := by
    rw [H₃]
    intro c hc y hy
    induction hy using Submodule.span_induction with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul K r x, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hx
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨n, r, y, y₁, y₂⟩ := a₃ (E c) hc
      rw [v₂ c z n (fun l => algebraMap R K (r l)) (fun l => E.symm (y l)) (by simpa using y₂)]
      refine Submodule.sum_mem _ fun l _ => ?_
      obtain ⟨b, hb⟩ := Submodule.mem_one.1
        (H₂.le (Submodule.mem_sup_left hz) (E.symm (y l)) ((hΩ _).2 (by simpa using y₁ l)))
      exact Submodule.mem_one.2 ⟨r l * (-b) ^ p, by rw [map_mul, map_pow, map_neg, hb, ← β₂]⟩
  refine ⟨o Λ, ho _, fg, ⟨H₁, H₂⟩, ?_⟩
  rw [H₄, ← H₃]
  exact T.adapted_lattice_lagrangian_symplectic R K H β F _ _ β₁ β₂ β₃ β₄ fg ⟨rfl, H₁ ▸ H₂⟩ H₅

set_option maxHeartbeats 600000 in

theorem exists_lattice (hX : CovTop.HypothesesXH) (hB : Published.BarsottiTateDieudonne) (h5 : Published.AbelianDeRham)
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (hK : (p : K) = 0) (G : Over (Sp R)) [GrpObj G]
    (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left) (hG : IsSemiAbelian G) (hA : IsAbelianScheme A)
    (hφ : IsGrpPullback A G (spMap (algebraMap R K)) φ) (P : LB (A ⊗ A).left) (hP : IsDual A A P)
    (hs : LBIso (swap P) P) (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A)
    (hψ : IsCorrForm (dp0 K) (𝟙 _) A A P ψ) (hβ : ∀ s y, ψ (β s) y = y s)
    [Module R (primDR A)] [IsScalarTower R K (primDR A)] :
    ∃ Λ : Submodule R (primDR A), Λ.FG ∧ IsAdapted β (PrimitiveSubmodule A) (intForms G A φ) Λ ∧
      IsAdapted β (conjDR p K hK A) (Submodule.span R (frobDR p K hK A ''
        (LinearMap.BilinForm.dualSubmodule β (intForms G A φ) : Set (primDR A)))) Λ ∧
      ∀ (f f' : G ⟶ G) (u u' : A ⟶ A) [IsMonHom f] [IsMonHom f'] [IsMonHom u] [IsMonHom u'],
        u.left ≫ φ = φ ≫ f.left → u'.left ≫ φ = φ ≫ f'.left →
        LBIso (ev P (fst A A ≫ u) (snd A A)) (ev P (fst A A) (snd A A ≫ u')) →
        ∀ s ∈ Λ, primPull (dp0 K) (𝟙 _) u s ∈ Λ := by
  have hR : (p : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, hK, map_zero])
  have hn : IsNilpotent (p : K) := hK ▸ IsNilpotent.zero
  obtain ⟨e, ε, eN, eF, eT, eW⟩ := hB.2 p
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim K A hA
  obtain ⟨𝒜, ⟨t⟩⟩ := SemiAbelianTower.exists_tower p K A (isSemiAbelian_of_isAbelianScheme A hA)
    (AbTorsionAnyBase.isFinite_and_flat_torsion _ A hA)
  obtain ⟨Γ', ⟨s⟩⟩ := T.semiabelian_extension_abelian_generic_henselian hX.ray p R K G A φ hG hA hφ
  obtain ⟨κ, hκ, κ₁, κ₂⟩ := T.pdivisible_tower_base_change_map_exists p R K G A φ hG hφ Γ' s 𝒜 t hR
  obtain ⟨w, hw⟩ := T.weil_pairing_exists_of_cube_theorem hX.cube p K A hA P hP 𝒜 t
  obtain ⟨h, hh⟩ := T.pdivisible_base_change_iso_semiabelian hX.cube p R K G A φ hG hφ Γ' s 𝒜 t κ hκ hA P hP w hw
  have w₁ := T.weil_pairing_antisymmetric_of_symmetric hX.cube p K A hA P hP hs 𝒜 t w hw
  obtain ⟨w₂, w₃⟩ := T.de_rham_polarization_form_primitive h5 hX.conj hX.cube p K hK A g hA hg P hP hs ψ β hψ hβ e ε eF eT eW hn 𝒜 t w hw
  obtain ⟨_, β₁, β₂, β₃, β₄⟩ := SymmPoincare.skew_lagrangian h5 hX.conj p K hK A g hA hg P hP hs ψ β hψ hβ
  obtain ⟨v₁, v₂⟩ := FrobAdjoint.frob_adjoint_verschiebung h5 hX.cube p K hK A g hA hg P hP hs ψ β hψ hβ e eN hn 𝒜 t
  letI : Module R 𝒜.RigExt := Module.compHom _ (algebraMap R K)
  haveI : IsScalarTower R K 𝒜.RigExt := .of_algebraMap_smul fun _ _ => rfl
  have hΩ := T.pdivisible_base_change_char_p p R K G A φ hG hφ Γ' s 𝒜 t κ hR hκ hA e eF eT hn
  have hN := fun (u : A ⟶ A) [IsMonHom u] => eN.primPull hn hA hA t t u
  have hF := eF hn hA t
  generalize e hn hA t = E at w₃ v₁ v₂ hΩ hN hF
  have hF' : ∀ c, c ∈ PrimitiveSubmodule A ↔ E c ∈ LinearMap.range 𝒜.rigOfOmega := fun c => by
    rw [← hF, Submodule.mem_map_equiv, E.symm_apply_apply]
  let B : LinearMap.BilinForm K 𝒜.RigExt := LinearMap.compl₁₂ β E.symm.toLinearMap E.symm.toLinearMap
  have hBL : IsLagr B (LinearMap.range 𝒜.rigOfOmega) := fun x => by
    obtain ⟨c, rfl⟩ := E.surjective x
    rw [← hF', β₃]
    exact ⟨fun H y hy => by simpa [B] using H (E.symm y) ((hF' _).2 (by simpa using hy)),
      fun H y hy => by simpa [B] using H (E y) ((hF' _).1 hy)⟩
  obtain ⟨a₁, a₂⟩ := T.pdivisible_polarization_lift_generic_fibre hB.1 p R K hR hK Γ' 𝒜 κ w κ₂ w₂ h hh
  have a₃ := T.pdivisible_hom_dual_extends_integral p R K hR hK Γ' 𝒜 κ w κ₂ w₂ h hh
  have a₄ := T.pdivisible_weil_pairing_integral_extension hB.1 p R K hR hK Γ' 𝒜 κ w κ₂ w₂ h hh κ₁ w₁
  have a₅ := T.rigidified_extension_lagrangian_sign p R K hR hK Γ' 𝒜 κ w B (-ε) κ₂ hBL w₃
  have f₁ : ∀ x, ∀ y ∈ PrimitiveSubmodule A, frobDR p K hK A (x + y) = frobDR p K hK A x := fun x y hy => by
    have k : frobDR p K hK A y = 0 := (hX.conj p K hK A g hA hg _ (frobMor p K hK A (cast_left p K hK A))).1 y hy
    rw [map_add, k, add_zero]
  obtain ⟨L, ho, fg, l₁, l₂⟩ := adapted_comap E β₁.1 β₂ β₃ β₄ hF' hΩ f₁ v₁ v₂ a₁ a₂ a₃ a₄ a₅
  refine ⟨L, fg, l₁, l₂, fun f f' u u' _ _ _ _ e₁ e₂ e₃ c hc => ?_⟩
  · obtain ⟨g₁, k₁⟩ := T.pdivisible_inclusion_compatible_towers p R K G A φ hG hφ Γ' s 𝒜 t κ hκ f u e₁
    obtain ⟨g₂, k₂⟩ := T.pdivisible_inclusion_compatible_towers p R K G A φ hG hφ Γ' s 𝒜 t κ hκ f' u' e₂
    rw [ho, hN]
    exact T.pdivisible_endomorphism_commute_extension p R K hR hK Γ' 𝒜 κ w _ _ g₁ g₂ k₁ k₂
      (T.weil_pairing_adjoint_endomorphism hX.cube p K A hA P hP 𝒜 t w hw u u' e₃) _ ((ho c).1 hc)

theorem hasLatticesComplete (hX : CovTop.HypothesesXH) (hB : Published.BarsottiTateDieudonne) (h5 : Published.AbelianDeRham)
    {O : Type} [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] {C : Scheme.{0}}
    [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [hG : IsSemiAbelian G] (i : OAct O G) {T : Scheme.{0}} {f₀ : T ⟶ C}
    {A : Over T} [GrpObj A] {j : OAct O A} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f₀ φ)
    (hA : IsAbelianScheme A) (hj : IsActPull j i f₀ φ) {P : LB (A ⊗ A).left} (hP : IsSelfDual c j P) {g : ℕ}
    (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g f₀) (hd : IsDRDatumOn q k c i j h P hg d₀) :
    HasLatticesComplete d₀ := by
  intro R _ _ _ _ _ K _ _ _ f ξ w
  have := hG.comm
  have := hA.comm
  have hK : (q : K) = 0 := by
    have k₀ := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (cast_eq_zero q k (ξ ≫ f₀))
    rwa [map_natCast, map_zero] at k₀
  let G' := (Over.pullback f).obj G
  let A' := (Over.pullback ξ).obj A
  have g₁ : IsGrpPullback G' G f _ := isGrpPullback_pullback G f
  have a₁ : IsGrpPullback A' A ξ _ := isGrpPullback_pullback A ξ
  have act : ∀ {S S' : Scheme.{0}} (b : S' ⟶ S) {H : Over S} (u : H ⟶ H),
      ((Over.pullback b).map u).left ≫ pullback.fst H.hom b = pullback.fst H.hom b ≫ u.left :=
    fun _ _ _ => pullback.lift_fst _ _ _
  have a₂ : IsActPull (OAct.pullback ξ A j) j ξ _ := ⟨a₁, fun x => act ξ _⟩
  have hA' : IsAbelianScheme A' :=
    { comm := inferInstance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have n := (a₁.comp h).congr w.symm rfl
  obtain ⟨χ, χ₁, χ₂⟩ := g₁.1.exists_lift _ _ (n.1.w.trans (Category.assoc _ _ _).symm)
  have hχ := g₁.cancel (n.congr rfl χ₁.symm) χ₂
  obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback a₁ a₁
  obtain ⟨s₁, s₂, s₃⟩ := AbDatum.isSelfDual_baseChange O c T _ ξ A A' j _ _ a₁ a₂ P m m₁ m₂ hP
  letI : Module R (primDR A') := Module.compHom _ (algebraMap R K)
  haveI : IsScalarTower R K (primDR A') := .of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ψ, β, E, hψ, hβ, E₁, E₂, E₃, E₄⟩ := GlobalTheory.T.polarization_vector_bundle_abelian_pullback h5 O c q k C G i T f₀ A j φ h hA P hP.1.isLB g hg d₀ hd R K hK
    f ξ w G' _ g₁ A' _ _ a₂ χ hχ χ₁ m m₁ m₂
  obtain ⟨Λ, fg, l₁, l₂, l₃⟩ := exists_lattice hX hB h5 q R K hK G' A' χ (IsSemiAbelian.pullback f G hG) hA' hχ _
    s₁ s₂ ψ β hψ hβ
  obtain ⟨N, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 fg
  have key : InLat R (fun l => E.symm (b l)) = fun s => E s ∈ Λ := funext fun s => propext <| by
    rw [← hb, Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun r => ?_
    rw [← E.apply_eq_iff_eq, map_sum, eq_comm]
    simp only [E₁, E.apply_symm_apply, algebraMap_smul]
  refine ⟨N, fun l => E.symm (b l), ?_⟩
  rw [key]
  refine ⟨fun x s hs => ?_, E₃.latSeq l₁, E₄.latSeq l₂⟩
  have sq : ∀ x, ((OAct.pullback ξ A j).act x).left ≫ χ = χ ≫ ((OAct.pullback f G i).act x).left := fun x =>
    g₁.1.hom_ext (by
      rw [Category.assoc, Category.assoc, χ₁, ← Category.assoc, a₂.2, Category.assoc, hj.2]
      exact (congrArg (χ ≫ ·) (act f _)).trans (by rw [← Category.assoc, χ₁, Category.assoc]) |>.symm)
      (by rw [Category.assoc, Category.assoc, Over.w, χ₂, Over.w_assoc])
  have := (OAct.pullback ξ A j).hom
  have := (OAct.pullback f G i).hom
  change E _ ∈ Λ
  rw [E₂]
  exact l₃ _ _ _ _ (sq x) (sq (c x)) (s₃ x) _ hs

end GlobalTheory.BadPt

namespace GlobalTheory.BadPt

theorem exists_datum_near : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.Published.BarsottiTateDieudonne → GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → ∀ (G₀ : Over C) [GrpObj G₀] [IsSemiAbelian G₀] (i₀ : OAct O G₀), AbGen c i₀ → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G) (φ₀ : G.left ⟶ G₀.left), IsActPull i i₀ (frob C q (natCast_eq_zero C q k)) φ₀ → ∀ (U : C.Opens) (A : Over U.toScheme) [GrpObj A] (j : OAct O A) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G U.ι φ), genericPoint C ∈ U → IsAbelianScheme A → IsActPull j i U.ι φ → ∀ P : LB (A ⊗ A).left, IsSelfDual c j P → ∀ (g : ℕ) (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g U.ι), IsDRDatumOn q k c i j h P hg d₀ → ∀ x : C, x ∉ U → ∃ V : C.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧ ∃ d : DieuDatumOn q k c i g V.ι, ∃ ψ, Agree (b := C.homOfLE (inf_le_left : V ⊓ U ≤ V)) (c := C.homOfLE (inf_le_right : V ⊓ U ≤ U)) d d₀ (by simp) ψ := by
  intro hX hB h2 O _ c q _ k _ _ _ C _ _ hC G₀ _ _ i₀ _ G _ _ i φ₀ _ U A _ j φ h hU hA hj P hP g hg d₀ hd
  exact T.lattice_extension_over_codim_one_points k C hC O _ _ _ _ _ _ _ _ _ g g g g hg hg.dual (hg.dual.frobPull _ _) (hg.frobPull _ _) U hU d₀
    (T.lattice_extension_complete_to_dvr C _ U.ι O _ _ _ _ _ _ _ _ _ g g g g hg hg.dual (hg.dual.frobPull _ _) (hg.frobPull _ _) d₀
      (hasLatticesComplete hX hB h2.p5 c q k i h hA hj hP hg d₀ hd))

end GlobalTheory.BadPt
