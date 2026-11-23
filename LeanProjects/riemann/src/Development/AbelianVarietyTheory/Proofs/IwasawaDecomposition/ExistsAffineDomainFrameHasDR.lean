import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

theorem gen_mem {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] {q : X} (hq : q ∈ U)
    (hV : q ∈ V) : ⊤ ≤ (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro q' _
  have hg : (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q') ⤳ hU.primeIdealOf ⟨q, hq⟩ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    have e : (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal = ⊥ := by
      let q₀ : PrimeSpectrum (FractionRing Γ(X, U)) := q'
      have := q₀.isPrime
      change Ideal.comap _ q₀.asIdeal = ⊥
      rw [Ideal.eq_bot_of_prime q₀.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    change (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal ≤ _
    rw [e]
    exact bot_le
  have h2 := hg.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf ⟨q, hq⟩] at h2
  exact h2.mem_open V.2 hV

theorem tan_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) {x : Sp R ⟶ X} {x' : Sp S ⟶ X}
    (hx : spMap ρ ≫ x = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h2 : ∀ i, IsTanAtG t x (v i))
    (h3 : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    (∀ i, IsTanAtG t x' (spMap (dualMap ρ) ≫ v i)) ∧
      ∀ u, IsTanAtG t x' u → ∃! cf, IsCombAtG t x' (fun i => spMap (dualMap ρ) ≫ v i) cf u := by
  subst hx
  have B := GlobalTheory.T.isTanBasis_of_unique_combination E H X t R x n v h2 h3
  exact ⟨fun i => GlobalTheory.LieMet.isTan_map ρ rfl (h2 i), fun u hu => B.2 _ ρ u hu⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isLocallyNoetherian_model (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsLocallyNoetherian Z.X := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.s := by
    unfold Pre.s
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian Z.s

set_option maxHeartbeats 1600000 in

theorem intFrame_restrict (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : IntFrame Z hU (w₀.bc ρ) := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  refine ⟨fun σ => ?_, fun k _ φ hr => ?_⟩
  · obtain ⟨n, v, e, h1, h2, h3⟩ := hfr.1 σ
    obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
    exact ⟨n, _, e, fun i => congrArg (spMap (dualMap ρ) ≫ ·) (h1 i), b1, b2⟩
  · have e1 : spMap (φ.comp ρ) ≫ hU₀.fromSpec = spMap φ ≫ hU.fromSpec := by
      rw [← eρ, ← Category.assoc, ModelRelProbe.spMap_comp]
    rw [Vecs.bc_bc, ← e1]
    exact hfr.2 k _ (by rwa [e1])

theorem exists_tanBasis (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)),
      GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨n, v, -, -, h2, h3⟩ := hfr.1 σ
  obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
  exact ⟨n, _, GlobalTheory.T.isTanBasis_of_unique_combination E H _ _ _ _ n _ b1 b2⟩

theorem exists_coeff_gen (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(Z.X, U)] {z : Z.X} (hzU : z ∈ U) :
    ∃ (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), Function.Injective β ∧
      spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  obtain ⟨β, eβ⟩ : ∃ β : ↥(Z.i.c.V W) →+* Γ(Z.X, U), spMap β = hU.fromSpec ≫ Z.s :=
    ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, Spec.map_preimage _⟩
  obtain ⟨q, hqU, hqo⟩ := Z.dense.inter_open_nonempty U U.2 ⟨z, hzU⟩
  have hqo' : q ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := by rw [Z.cover]; exact hqo
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.1 hqo'
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 _ (gen_mem hU hqU hqa)
  have hφ' : spMap φ ≫ Z.chart a = spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec := hφ
  obtain ⟨y, hy⟩ := Pull.exists_open_lift Z hφ'
  refine ⟨β, y, ?_, by rw [hy, Category.assoc]⟩
  have cs := Pull.affineOpenChart_comp_structure_eq_spMap Z hφ'
  rw [Z.π_s, Category.assoc, ← eβ, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp] at cs
  have e : (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))).comp β = (φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) cs)
  refine Function.Injective.of_comp (f := algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ?_
  have e' : (⇑(algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ∘ ⇑β) = ⇑((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) :=
    congrArg DFunLike.coe e
  rw [e']
  exact (φ.comp (Z.alg a)).injective.comp (Z.i.c.V W).subtype_injective

theorem exists_small_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z hDR z
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isLocallyNoetherian_model hp hW Z
  obtain ⟨U₀, hU₀, w₀, hz, hfr⟩ := hDR.2 z
  obtain ⟨U, hU, hd, hzU, hle, hic⟩ := exists_affine_domain U₀ hz
  obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U), spMap ρ ≫ hU₀.fromSpec = hU.fromSpec :=
    ⟨(Z.X.presheaf.map (homOfLE hle).op).hom, hU₀.map_fromSpec hU _⟩
  obtain ⟨g, e, he⟩ := exists_tanBasis Z hU₀ hU ρ eρ hfr
  obtain ⟨β, y, hβ, hy⟩ := exists_coeff_gen Z hU hzU
  exact ⟨U, hU, hd, w₀.bc ρ, g, e, β, y, hzU, hic, hβ, intFrame_restrict Z hU₀ hU ρ eρ hfr, he, hy⟩

end GlobalTheory.HTLine
