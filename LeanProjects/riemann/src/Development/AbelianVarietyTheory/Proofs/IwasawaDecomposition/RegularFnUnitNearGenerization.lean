import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimGenerizationDropStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenAvoidingNonGenericStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.ShrinkCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem traitOrdPt_of_isUnit (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (U : Z.X.Opens) (f : Γ(Z.X, U)) (q : Z.X) (hq : q ∈ U)
    (hu : IsUnit ((Z.X.presheaf.germ U q hq).hom f)) (hab : q ∈ abLocus Z.t.G) : TraitOrdPt φ Z U f q := by
  intro W _ _ _ hW ϖ hϖ χ t m P hχ be hbe hmon hU hcx
  subst hcx
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  have hs : Subsingleton P.D.toPre.X := (closed_mem_abLocus_iff T P).1
    ((abLocus_pullback abLocusOne Z.t.semi m.cart.1 _).1 hab)
  have h0 : φ.evalZ be = 0 := φ.eval_of_subsingleton _
  refine ⟨0, by rw [h0]; simp, ?_⟩
  rw [pow_zero, associated_one_iff_isUnit]
  exact hu.map _

theorem isUnit_germ_of_dim_zero {X : Scheme.{0}} {U : X.Opens} {f : Γ(X, U)} (hf : IsRegularFn f) (q : X) (hq : q ∈ U)
    (hd : ringKrullDim (X.presheaf.stalk q) ≤ 0) : IsUnit ((X.presheaf.germ U q hq).hom f) := by
  have hr := isRegularFn_iff_germ.1 hf q hq
  set a := (X.presheaf.germ U q hq).hom f
  by_contra hna
  have hm : a ∈ maximalIdeal (X.presheaf.stalk q) := hna
  have : a ∈ nilradical (X.presheaf.stalk q) := by
    rw [nilradical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    intro p ⟨_, hp⟩
    have : p = maximalIdeal _ := by
      haveI : Ring.KrullDimLE 0 (X.presheaf.stalk q) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
      exact IsLocalRing.eq_maximalIdeal hp.isMaximal'
    exact this ▸ hm
  obtain ⟨n, hn⟩ := this
  have := pow_mem hr n
  rw [hn] at this
  exact zero_notMem_nonZeroDivisors this

theorem eq_of_specializes_of_dim_zero {X : Scheme.{0}} (q η : X) (hd : ringKrullDim (X.presheaf.stalk q) ≤ 0)
    (h : η ⤳ q) : η = q := by
  have : η ∈ Set.range (X.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact h
  obtain ⟨p, rfl⟩ := this
  haveI : Ring.KrullDimLE 0 (X.presheaf.stalk q) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p = IsLocalRing.closedPoint _ :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal p.isPrime.isMaximal')
  rw [hp]; exact Scheme.fromSpecStalk_closedPoint

theorem mem_genericPoints_of_dim_zero {X : Scheme.{0}} (q : X) (hd : ringKrullDim (X.presheaf.stalk q) ≤ 0) :
    q ∈ genericPoints X := by
  show closure {q} ∈ irreducibleComponents X
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  obtain ⟨η, hη⟩ := QuasiSober.sober hT.closure isClosed_closure
  have hs : η ⤳ q := specializes_iff_mem_closure.2 (by
    rw [hη.def]; exact subset_closure (hle (subset_closure rfl)))
  rw [eq_of_specializes_of_dim_zero q η hd hs] at hη
  rw [hη.def]; exact subset_closure

theorem mem_abLocus_of_dim_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (q : Z.X), ringKrullDim (Z.X.presheaf.stalk q) ≤ 0 → q ∈ abLocus Z.t.G := by
  intro E _ _ _ H D l Xo c Z q hd
  obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1
  obtain ⟨u, rfl⟩ := (GlobalTheory.densePart_basic Z.X _ Z.j h₁ h₂ h₃ h₄).1 (mem_genericPoints_of_dim_zero q hd)
  have : Z.jQ u ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G := by
    rw [Z.ab_gen]; exact ⟨u, rfl⟩
  exact this

theorem exists_shrink : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ (z : Z.X) (U : Z.X.Opens) (f : Γ(Z.X, U)), z ∈ U → IsRegularFn f → (∀ q ∈ U, q ⤳ z → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q) → ∃ (V : Z.X.Opens) (hVU : V ≤ U), z ∈ V ∧ ∀ q ∈ V, ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z V (resG Z.X hVU f) q := by
  intro E _ _ _ H D l Xo c Z Cn φ _ _ z U f hz hf hyp
  haveI : IsLocallyNoetherian Z.X := (GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1).1
  obtain ⟨V, hVU, hzV, hV⟩ := GlobalTheory.T.exists_open_avoiding_non_generic Z.X (fun q => ringKrullDim (Z.X.presheaf.stalk q) ≤ 1)
    ((Z.X.basicOpen f : Set Z.X) ∩ abLocus Z.t.G) ((Z.X.basicOpen f).isOpen.inter (GlobalTheory.T.isOpen_abelian_locus Z)) U z hz
    fun q hq hd η hη hne => by
      have hd0 := GlobalTheory.T.krull_dim_generization_drop Z.X q η hη hne hd
      have hηU : η ∈ U := hη.mem_open U.isOpen hq
      exact ⟨(Z.X.mem_basicOpen f η hηU).2 (isUnit_germ_of_dim_zero hf η hηU hd0), mem_abLocus_of_dim_zero Z η hd0⟩
  refine ⟨V, hVU, hzV, fun q hq hd => ?_⟩
  rcases hV q hq hd with ⟨hb, hab⟩ | hs
  · have hu := (Z.X.mem_basicOpen f q (hVU hq)).1 hb
    refine traitOrdPt_of_isUnit φ Z V _ q hq ?_ hab
    rw [germ_resG]; exact hu
  · exact TraitOrdPt.of_associated hq (hVU hq) (by rw [germ_resG]) (hyp q (hVU hq) hs hd)

end GlobalTheory.ShrinkCentre
