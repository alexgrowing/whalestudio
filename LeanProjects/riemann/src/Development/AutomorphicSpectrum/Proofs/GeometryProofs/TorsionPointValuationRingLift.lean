import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

section Helpers

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_root_through {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V), Finite {x : Over.mk t ⟶ G // x ^ n = 1})
    (O C : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (c : Sp O ⟶ G.left) (K : Type) [Field K] (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (y : Sp K ⟶ G.left)
    (hy : y ≫ (mulA G n).left = r ≫ c) :
    ∃ c' : Sp O ⟶ G.left, c' ≫ (mulA G n).left = c ∧
      c' (IsLocalRing.closedPoint O) = y (IsLocalRing.closedPoint K) := by
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulA G n).left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (mulA G n).left := IsSeparated.of_comp _ G.hom
  have : LocallyQuasiFinite (mulA G n).left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [GlobalTheory.IntDiv.comp_mulA]
      exact h K t
  have : Flat (mulA G n).left :=
    GlobalTheory.flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.IntDiv.flat_fibre G _ _ _) (GlobalTheory.IntDiv.flat_fibre G _ _ _)
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c)
    (pullback.lift y r hy (IsLocalRing.closedPoint K))
    ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y r hy)).trans hr)
  refine ⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs], ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ hs').trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_fst y r hy))))

theorem exists_torsion_point_through {R V O C K : Type} [CommRing R] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] [Field K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (n : ℕ)
    (hA : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1})
    (α : R →+* V) (ρV : V →+* O) (ρ : R →+* O) (hρ : ρV.comp α = ρ) (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (yG : Over.mk (r ≫ spMap ρ) ⟶ G)
    (hyN : yG ^ n = 1) :
    ∃ y : Over.mk (spMap ρ) ⟶ G, y ^ n = 1 ∧
      y.left (IsLocalRing.closedPoint O) = yG.left (IsLocalRing.closedPoint K) := by
  let j : Sp V ⟶ Sp R := spMap α
  have hjρ : spMap ρV ≫ j = spMap ρ := by
    rw [← hρ]
    simp only [j, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hGV : IsSemiAbelian ((Over.pullback j).obj G) := IsSemiAbelian.pullback j G hG
  have := hGV.comm
  have := hGV.smooth
  have := hGV.separated
  have := hGV.quasiCompact
  have := hGV.geomConnected
  have hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V),
      Finite {x : Over.mk t ⟶ ((Over.pullback j).obj G) // x ^ n = 1} := by
    intro K _ _ t
    obtain ⟨E⟩ := hGV.fibres K t
    have := (IsSemiAbelian.pullback t ((Over.pullback j).obj G) hGV).comm
    exact GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
      (GlobalTheory.TorsionLift.ptsEquiv t ((Over.pullback j).obj G) (𝟙_ _) t (by simp)) n
      (hA K ((Over.pullback t).obj ((Over.pullback j).obj G)) ⟨E⟩)
  let s : Sp K ⟶ Sp V := r ≫ spMap ρV
  have hs : s ≫ j = r ≫ spMap ρ := by simp only [s, Category.assoc, hjρ]
  let e₀ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk s) (r ≫ spMap ρ) hs
  obtain ⟨yV, hyV₀⟩ := e₀.surjective yG
  have hyV : yV ^ n = 1 := by
    apply e₀.injective
    rw [map_pow, hyV₀, hyN, map_one]
  let rr : Over.mk s ⟶ Over.mk (spMap ρV) := Over.homMk r rfl
  let c : Sp O ⟶ ((Over.pullback j).obj G).left := (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)).left
  have hc : yV.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n).left = r ≫ c := by
    have h1 : yV ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n =
        rr ≫ (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)) := by
      rw [GlobalTheory.IntDiv.comp_mulA, hyV, MonObj.comp_one]
    exact congrArg (fun q => q.left) h1
  obtain ⟨c', hc', hcl⟩ := exists_root_through ((Over.pullback j).obj G) n hfin O C c K r hr yV.left hc
  have hcw : c' ≫ ((Over.pullback j).obj G).hom = spMap ρV := by
    have h1 := Over.w (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n)
    have h2 : c ≫ ((Over.pullback j).obj G).hom = spMap ρV :=
      Over.w (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G))
    rw [← h1, ← Category.assoc, hc', h2]
  let c₂ : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G) := Over.homMk c' hcw
  have hc₂ : c₂ ^ n = 1 := by
    rw [← GlobalTheory.IntDiv.comp_mulA]
    exact Over.OverMorphism.ext hc'
  let e₁ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk (spMap ρV)) (spMap ρ) hjρ
  refine ⟨e₁ c₂, by rw [← map_pow, hc₂, map_one], ?_⟩
  have h1 : (e₁ c₂).left = c' ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  have h2 : (e₀ yV).left = yV.left ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  rw [h1, ← hyV₀, h2]
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  rw [hcl]
  exact (Scheme.Hom.comp_apply _ _ _).symm

end Helpers

theorem ker_ne_bot_of_finite (L : Type) [Field L] [NumberField L] (k : Type) [Field k] [Finite k] (a : 𝓞 L →+* k) :
    RingHom.ker a ≠ ⊥ := by
  intro h
  have hinj : Function.Injective a := (RingHom.injective_iff_ker_eq_bot a).2 h
  have : Infinite (𝓞 L) := Infinite.of_injective (Nat.cast : ℕ → 𝓞 L) Nat.cast_injective
  exact not_finite_iff_infinite.2 this (Finite.of_injective a hinj)

theorem exists_valuationSubring_of_ne_top (L : Type) [Field L] [NumberField L] (p : Ideal (𝓞 L)) (hp : p ≠ ⊤) :
    ∃ (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O),
      (∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L)) ∧
      ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O := by
  let f : 𝓞 L →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap (𝓞 L) L)
  have hf : Function.Injective f :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (RingOfIntegers.coe_injective)
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hI : p.map f.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : f.range) ∈ p.map f.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h1
    have : x = 1 := hf (by simpa [Subtype.ext_iff] using hx1)
    exact hp ((Ideal.eq_top_iff_one _).2 (this ▸ hx))
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (p.map f.rangeRestrict) hI
  refine ⟨B, f.codRestrict B fun x => hAB ⟨x, rfl⟩, fun a => rfl, fun a ha => ?_⟩
  have h1 : f a ∈ B.nonunits := hB ⟨f.rangeRestrict a, Ideal.mem_map_of_mem _ ha, rfl⟩
  exact ValuationSubring.coe_mem_nonunits_iff.1 h1

theorem exists_lift_atPrime {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (p : Ideal R) [p.IsMaximal]
    (ρ : R →+* O) (hρ : ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρV : Localization.AtPrime p →+* O, ρV.comp (algebraMap R (Localization.AtPrime p)) = ρ := by
  have hu : ∀ y : p.primeCompl, IsUnit (ρ y) := by
    intro y
    by_contra hy
    have h1 : p ≤ (IsLocalRing.maximalIdeal O).comap ρ := hρ
    have h2 : (IsLocalRing.maximalIdeal O).comap ρ ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    have h3 := (Ideal.IsMaximal.eq_of_le ‹_› h2 h1).symm
    have h4 : (y : R) ∈ (IsLocalRing.maximalIdeal O).comap ρ := by
      simpa [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] using hy
    exact y.2 (h3 ▸ h4)
  exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩

theorem exists_factor_of_finite {R k K : Type} [CommRing R] [Field k] [Finite k] [Field K] [IsAlgClosed K]
    (a : R →+* k) (b : R →+* K) [(RingHom.ker a).IsMaximal] (h : RingHom.ker a ≤ RingHom.ker b) :
    ∃ φ : k →+* K, φ.comp a = b := by
  letI : Field (R ⧸ RingHom.ker a) := Ideal.Quotient.field _
  let a' : (R ⧸ RingHom.ker a) →+* k := Ideal.Quotient.lift _ a fun x hx => hx
  let b' : (R ⧸ RingHom.ker a) →+* K := Ideal.Quotient.lift _ b fun x hx => h hx
  letI := a'.toAlgebra
  letI := b'.toAlgebra
  have : Module.Finite (R ⧸ RingHom.ker a) k := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (R ⧸ RingHom.ker a) k := Algebra.IsAlgebraic.of_finite _ _
  let φ : k →ₐ[R ⧸ RingHom.ker a] K := IsAlgClosed.lift
  refine ⟨φ.toRingHom, RingHom.ext fun x => ?_⟩
  have h1 : φ (a' (Ideal.Quotient.mk _ x)) = b' (Ideal.Quotient.mk _ x) := φ.commutes _
  simp only [a', b', Ideal.Quotient.lift_mk] at h1
  exact h1

theorem exists_geometric_closedPoint {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (ρ : R →+* O) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (b : R →+* K) (r : Sp K ⟶ Sp O), r ≫ spMap ρ = spMap b ∧
      (∀ x, ρ x ∈ IsLocalRing.maximalIdeal O → b x = 0) ∧
      r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let g : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have : IsLocalHom g := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (IsLocalRing.residue O x) := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have : g x = 0 := by simp [g, h]
      exact hx.ne_zero this
    exact (isUnit_map_iff (IsLocalRing.residue O) x).1 h1
  refine ⟨K, inferInstance, inferInstance, g.comp ρ, spMap g, ?_, fun x hx => ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have h1 : IsLocalRing.residue O (ρ x) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hx
    simp [g, h1]
  · exact IsLocalRing.comap_closedPoint g

theorem exists_torsion_point_reducing_to : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  intro L _ _ G _ _ hG w hw
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let π : Sp (𝓞 L) ⟶ Sp ℤ := spMap (Int.castRingHom (𝓞 L))
  have : LocallyOfFiniteType π := by
    have h1 : (algebraMap ℤ (𝓞 L)).Finite := RingHom.finite_algebraMap.2 inferInstance
    rw [algebraMap_int_eq] at h1
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 h1.finiteType
  obtain ⟨hA, hB⟩ := GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.1
  obtain ⟨N, hN1, hN⟩ := hB (Sp (𝓞 L)) π G w hw
  have : Finite (G.left.residueField w) :=
    (GlobalTheory.jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (G.left.fromSpecResidueField w ≫ G.hom)
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 L →+* G.left.residueField w, CommRingCat.ofHom a = ψ := ⟨ψ.hom, rfl⟩
  have hp0 : RingHom.ker a ≠ ⊥ := ker_ne_bot_of_finite L _ a
  have hpp : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  have hpm : (RingHom.ker a).IsMaximal := hpp.isMaximal hp0
  obtain ⟨O, ρ, hρL, hρp⟩ := exists_valuationSubring_of_ne_top L (RingHom.ker a) hpp.ne_top
  obtain ⟨ρV, hρV⟩ := exists_lift_atPrime (RingHom.ker a) ρ hρp
  have hV : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker a)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hp0 _
  obtain ⟨K, _, _, b, r, hb, hbk, hr⟩ := exists_geometric_closedPoint ρ
  obtain ⟨φ, hφ⟩ := exists_factor_of_finite a b (fun x hx => hbk x (hρp x hx))
  have hy₀ : (Spec.map (CommRingCat.ofHom φ) ≫ G.left.fromSpecResidueField w) ≫ G.hom = r ≫ spMap ρ := by
    rw [hb, Category.assoc, ← hψ, ← hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let yG : Over.mk (r ≫ spMap ρ) ⟶ G := Over.homMk _ hy₀
  have hyl : ∀ z, yG.left z = w := fun z =>
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  have hyN : yG ^ N = 1 := hN K _ yG
    (Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, hyl _⟩, by rintro _ ⟨z, rfl⟩; exact hyl z⟩)
  obtain ⟨y, hy, hyw⟩ := exists_torsion_point_through (C := AlgebraicClosure L) G hG N
    (fun K _ _ G _ _ hE => hA K G hE N hN1) (algebraMap (𝓞 L) (Localization.AtPrime (RingHom.ker a))) ρV ρ hρV r hr yG hyN
  exact ⟨N, O, ρ, y, hN1, hy, hyw.trans (hyl _), hρL⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
