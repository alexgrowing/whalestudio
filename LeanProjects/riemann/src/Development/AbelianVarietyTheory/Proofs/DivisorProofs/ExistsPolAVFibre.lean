import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_polAV_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S X : Scheme.{0}} {t : SAB H S} {u : SAB H X} {x : S ⟶ X} (m : SABMap t u x) (hp : IsProper u.G.hom)
    (ha : RelAmple u.G u.PP.L) (hk : KTriv u.G u.PP.L) {C : Type} [Field C] (y : Sp C ⟶ S) :
    letI := H.starRing
    ∃ (A : PolAV (Sp C)) (oA : A.OAct (𝓞 E)) (φ : A.A.left ⟶ t.G.left), IsGrpPullback A.A t.G y φ ∧
      (∀ a, (oA.act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧ LBIso A.L (u.PP.L.pull (φ ≫ m.φ)) := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull y t
  generalize (⟨(Over.pullback y).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨w, g, -⟩ := n.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (y ≫ x) (IsLocalRing.closedPoint C)) trivial
  have hy : ∀ z, (y ≫ x) z ∈ U := fun z =>
    (congrArg (fun V => z ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (y ≫ x) hc)).mpr trivial
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hp
  have hA' := relAmple_pull n.cart.1 u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy ha
  have hK' := kTriv_pull n.cart u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hk
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hL : LBIso t'.PP.L (u.PP.L.pull (m₁.φ ≫ m.φ)) := hn ▸ ⟨w, g⟩
  exact ⟨GenericPol.toPolAV t' d hd hp' hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, m₁.φ, m₁.cart,
    m₁.act, hL⟩

theorem exists_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → v.Integers O → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O), (∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) → ∃ (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ hpO _ _ _ _ inst hstar hv T io y₀ hy k kO hk
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨G, t', m₁, m₂, -⟩ := y₀.2.2
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  have hinj : Function.Injective ((algebraMap O C).comp kO) := fun a b h => by
    simp only [RingHom.comp_apply, hk] at h
    exact IsFractionRing.injective T.V T.Fr (k.injective h)
  have hp0 : ∀ {R : Type} [CommRing R] (f : R →+* O), (p : R) ≠ 0 := fun f h =>
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : C) ≠ 0) (by
      rw [← map_natCast ((algebraMap O C).comp f), h, map_zero])
  have hpu : ∀ {R : Type} [CommRing R] (f : R →+* O), ¬ IsUnit (p : R) := fun f h =>
    hpO.out (by simpa using h.map f)
  haveI : IsLocalHom kO := ⟨fun a ha => by
    by_contra hau
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hu
      exact hau (hu ▸ u.isUnit)
    rw [hu, map_mul, map_pow] at ha
    have h1 : IsUnit (kO ϖ) := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
    obtain ⟨n', u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 kO) hϖ
    refine hpO.out ?_
    rw [← map_natCast kO, hu', map_mul, map_pow]
    exact (u'.isUnit.map kO).mul (h1.pow _)⟩
  obtain ⟨T', φ', G', m, hi, hf, -, -, U, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  obtain ⟨f', -, hf'⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ' hi hf.to_isIntegral kO hinj
  have hI : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal T'.V ^ n, f' a ∈ Ideal.span {(p : O)} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 f') hϖ
    refine ⟨n, fun a ha => ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨f' (b * ↑u⁻¹), ?_⟩
    rw [← map_natCast f', ← map_mul, hu, _root_.mul_assoc, Units.inv_mul_cancel_left]
  obtain ⟨A, oA, φ, hφ, hφa, hL⟩ :=
    exists_polAV_fibre m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (spMap k)
  have e1 : spMap f' ≫ spMap φ' = spMap kO := by rw [spMap_spMap, hf']
  have e2 : spMap k ≫ spMap (algebraMap T.V T.Fr) = spMap ((algebraMap O C).comp f') ≫ spMap φ' := by
    rw [spMap_spMap, spMap_spMap, RingHom.comp_assoc, hf']
    exact congrArg _ (RingHom.ext fun a => (hk a).symm)
  have h2 : IsGrpPullback A.A G.G (spMap ((algebraMap O C).comp f') ≫ spMap φ') (φ ≫ m₂.φ) :=
    (hφ.comp m₂.cart).congr e2 rfl
  obtain ⟨j, hj1, hj2⟩ : ∃ j : A.A.left ⟶ G'.G.left, j ≫ m.φ = φ ≫ m₂.φ ∧
      j ≫ G'.G.hom = A.A.hom ≫ spMap ((algebraMap O C).comp f') :=
    ⟨m.cart.1.lift _ _ (h2.1.w.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  have hj : IsGrpPullback A.A G'.G (spMap ((algebraMap O C).comp f')) j :=
    m.cart.cancel (h2.congr rfl hj1.symm) hj2
  have hja : ∀ a, (oA.act a).left ≫ j = j ≫ (G'.act.toRingAct.act a).left := fun a => m.cart.1.hom_ext
    (by
      change _ = (j ≫ (G'.act.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, m.act, hj1, reassoc_of% hj1, reassoc_of% (hφa a), m₂.act])
    (by rw [Category.assoc, Category.assoc, Over.w, hj2, Over.w_assoc])
  obtain ⟨ε⟩ : Nonempty (Eps p C) := inferInstance
  obtain ⟨-, -, -, -, -, P, -, -, -, -, hA, -, -, -, -, π, -, hπ, -, -, -, hgen, hπa, -⟩ :=
    exists_point_of_unif U.U.toUnifPre G'.semi U.lin hv ε f' hI A oA j hj hja
  clear hja hφa hj
  clear oA
  subst hA
  refine ⟨P, φ ≫ m₁.φ, hk, G, t', m₁, m₂, π ≫ m.φ, φ, (hπ.comp m.cart).congr e1 rfl, fun a => ?_, hφ, ?_, rfl, hL⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (m.act a)
  · rw [← Category.assoc, eq_of_heq hgen, hj1]

end GlobalTheory.CompHt
