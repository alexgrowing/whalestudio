import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

theorem mem_basicOpen_of_isClosed [AlgebraicGeometry.IsIntegral X] {t : Γ(X, ⊤)} {ξ : X}
    (hξ : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U →
      Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    {L : LB X} (s : L.Sec) {b : L.ι} (hb : ξ ∈ X.basicOpen (s.f b)) {Z : Set X} (hZ : IsClosed Z)
    (hZt : Z ⊆ X.basicOpen t)
    (hs : ∀ y ∈ X.basicOpen t, y ∉ Z → ∃ c, y ∈ X.basicOpen (s.f c))
    {x : X} (hx : x ∉ X.basicOpen t) {a : L.ι} (ha : x ∈ L.U a) : x ∈ X.basicOpen (s.f a) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (U := L.U a ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) (x := x) ⟨ha, fun h ↦ hx (hZt h)⟩
  have hWa : W ≤ L.U a := fun y hy ↦ (hWU hy).1
  have hξW : ξ ∈ W := ((hξ x).1 hx).mem_open W.isOpen hxW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hpr := hp W hW hξW
  set p := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with hpd
  set σ := X.presheaf.map (homOfLE hWa).op (s.f a) with hσd
  have hpb : X.basicOpen p = W ⊓ X.basicOpen t := X.basicOpen_res _ _
  have hσb : X.basicOpen σ = W ⊓ X.basicOpen (s.f a) := X.basicOpen_res _ _
  have hle : X.basicOpen p ≤ X.basicOpen σ := fun y hy ↦ by
    obtain ⟨h₁, h₂⟩ := hpb.le hy
    obtain ⟨c, hc⟩ := hs y h₂ (hWU h₁).2
    exact hσb.ge ⟨h₁, mem_basicOpen_of_chart s (hWa h₁) hc⟩
  have hrad : p ∈ (Ideal.span {σ}).radical := by
    rw [← PrimeSpectrum.basicOpen_le_basicOpen_iff]
    have := hW.fromSpec.preimage_mono hle
    rwa [hW.fromSpec_preimage_basicOpen, hW.fromSpec_preimage_basicOpen] at this
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr m).1 (Ideal.mem_span_singleton.1 hm)
  obtain rfl | hi0 := eq_or_ne i 0
  · have hu : IsUnit σ := associated_one_iff_isUnit.1 (by simpa using hi)
    exact (hσb.le ((X.basicOpen_of_isUnit hu).ge hxW)).2
  · obtain ⟨q, hq⟩ := (dvd_pow_self p hi0).trans hi.symm.dvd
    have h₁ : ξ ∈ X.basicOpen σ := hσb.ge ⟨hξW, mem_basicOpen_of_chart s (hWa hξW) hb⟩
    rw [hq, Scheme.basicOpen_mul] at h₁
    exact absurd (hpb.le h₁.1).2 ((hξ ξ).2 specializes_rfl)

end SpecialFibreGenerator

open SpecialFibreGenerator TopologicalSpace in

theorem exists_sec_generates_specialFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : LB G.left), N.IsLB → ∀ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ a, a ∈ nonzeroLocus s) → IsClosed ((pullback.fst G.hom (jK V)) '' {a | a ∉ nonzeroLocus s}) → ∃ θ : H0 N 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  intro V _ _ _ G _ _ hG N hN s ⟨a₀, ha₀⟩ hZ
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hN s (by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ha₀
    exact ⟨k, fun h ↦ by rw [h, Scheme.basicOpen_zero] at hk; exact hk⟩)
  have hξ := DvrModel.notMem_basicOpen_iff_specializes hϖ hs
  have hr := DvrModel.opensRange_generic hϖ hK
  refine ⟨secAlong σ (𝟙 _), fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := LB.mem_of_cover hN x
  refine mem_nonzeroLocus_secAlong σ (𝟙 _) (a := a) ?_
  refine mem_basicOpen_of_isClosed hξ (DvrModel.prime_res_generic hϖ hs) σ (b := b)
    (((hξ x₀).1 ((DvrModel.notMem_basicOpen_iff _ hϖ x₀).2 hx₀)).mem_open
      (Scheme.basicOpen _ _).isOpen hb) hZ ?_ (fun y hy hyZ ↦ ?_)
    ((DvrModel.notMem_basicOpen_iff _ hϖ x).2 hx) ha
  · rintro _ ⟨y, -, rfl⟩
    exact hr.le ⟨y, rfl⟩
  · obtain ⟨z, rfl⟩ := hr.ge hy
    have hz : z ∈ nonzeroLocus s := by_contra fun h ↦ hyZ ⟨z, h, rfl⟩
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
    refine ⟨k ⟨⟩, ?_⟩
    have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
      zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
    have h := congrArg (Scheme.basicOpen _) (hσ k)
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
      Scheme.basicOpen_of_isUnit _ (((h0.isUnit.map _).map _).map _)] at h
    exact (h.ge ⟨Scheme.basicOpen_le _ _ hk, hk⟩).2

end GlobalTheory
