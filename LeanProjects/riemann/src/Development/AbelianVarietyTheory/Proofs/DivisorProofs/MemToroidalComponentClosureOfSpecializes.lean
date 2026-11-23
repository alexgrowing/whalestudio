import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option autoImplicit false

namespace GlobalTheory.CompHS

theorem exists_generisation_of_mem_closure {T : Type} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {U : Set T} (hU : IsOpen U) {y : T} (hy : y ∈ closure U) : ∃ g ∈ U, g ⤳ y := by
  haveI : NoetherianSpace (closure U) := NoetherianSpace.set _
  haveI : QuasiSober (closure U) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hd : Dense (Subtype.val ⁻¹' U : Set (closure U)) := fun z => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right subset_closure]
    exact z.2
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨y, hy⟩ : closure U)
  have hg := (isIrreducible_irreducibleComponent (x := (⟨y, hy⟩ : closure U))).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  obtain ⟨o, ho, hne, hle⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨p, hp, hpU⟩ := hd.inter_open_nonempty o ho hne
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set (closure U)) := hU.preimage continuous_subtype_val
  exact ⟨_, (hg.mem_open_set_iff hU').2 ⟨p, hle hp, hpU⟩,
    (hg.specializes mem_irreducibleComponent).map continuous_subtype_val⟩

theorem exists_generic_generisation (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, fun y hy => ?_⟩
  have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := this
  exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
    (X.fromSpecStalk x).continuous

theorem mem_barComp_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  intro E _ _ _ H Dw l Xo c Y Z x hx b hb
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := {}
  intro hcl
  have hopen := Y.j.isOpenEmbedding.isOpenMap
  have hc := (TrivOrderTieCompare.isClopen_comp Z)
  obtain ⟨w, hw, hwb⟩ := exists_generisation_of_mem_closure (hopen _ hc.compl.isOpen) hcl
  obtain ⟨ξ, hξ⟩ := exists_generic_generisation Y.X b (Y.normal b).1
  obtain ⟨u, hu, rfl⟩ := (hξ w hwb).mem_open (hopen _ hc.compl.isOpen) hw
  obtain ⟨v, hv, hv'⟩ := (hξ _ hb).mem_open (hopen _ hc.isOpen) ⟨x, hx, rfl⟩
  exact hu (Y.j.isOpenEmbedding.injective hv' ▸ hv)

end GlobalTheory.CompHS
