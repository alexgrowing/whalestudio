import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointInOpenOfEtaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvrStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem associated_of_isEtaleCompletion {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) (hφ : IsEtaleCompletion φ) (a b : A) (h : Associated (φ a) (φ b)) :
    Associated a b := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ.1
  haveI : IsLocalHom (algebraMap A R) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hn
    have hm : φ x ∈ maximalIdeal R := hφ.2.1 ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal x).2 hn)
    exact (mem_maximalIdeal _).1 hm hx
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)
  have key : ∀ x y : A, φ x ∣ φ y → x ∣ y := by
    intro x y hxy
    rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) (Ideal.span {x}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact hxy
  exact associated_of_dvd_dvd (key _ _ h.dvd) (key _ _ h.symm.dvd)

theorem associated_of_associated_heightOne {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      Associated (algebraMap A (Localization.AtPrime p) a) (algebraMap A (Localization.AtPrime p) b)) :
    Associated a b := by
  have hK : ∀ x y : A, x ≠ 0 → (∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      algebraMap A (Localization.AtPrime p) x ∣ algebraMap A (Localization.AtPrime p) y) → x ∣ y := by
    intro x y hx hdiv
    have hx' : algebraMap A (FractionRing A) x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hx
    have hmem : algebraMap A (FractionRing A) y / algebraMap A (FractionRing A) x ∈
        (algebraMap A (FractionRing A)).range := by
      rw [(GlobalTheory.normal_domain_height_one.{0, 0, 0} A (FractionRing A)).2.1]
      intro p _ hp
      rw [GlobalTheory.mem_primeLocalSubalgebra_iff]
      obtain ⟨c, hc⟩ := hdiv p hp
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
      have e : y * s = x * r := by
        apply IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
        rw [map_mul, hc, map_mul, mul_assoc, IsLocalization.mk'_spec]
      refine ⟨s, s.2, r, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, eq_div_iff hx', ← map_mul, ← map_mul, mul_comm r x, ← e, mul_comm]
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul, hz, mul_div_cancel₀ _ hx']
  exact associated_of_dvd_dvd (hK a b ha fun p _ hp => (h p hp).dvd) (hK b a hb fun p _ hp => (h p hp).symm.dvd)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem germ_ne_zero_of_isRegularFn {X : Scheme.{0}} {U : X.Opens} {f : Γ(X, U)} (hf : GlobalTheory.Cartier.IsRegularFn f)
    (x : X) (hx : x ∈ U) : (X.presheaf.germ U x hx).hom f ≠ 0 := by
  intro h
  obtain ⟨W, hxW, i, j, hw⟩ := X.presheaf.germ_eq x hx hx f 0 (by rw [h, map_zero])
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  have h0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (leOfHom i) f = 0 := by
    change (X.presheaf.map (homOfLE (leOfHom i)).op).hom f = 0
    rw [show homOfLE (leOfHom i) = i from Subsingleton.elim _ _, hw, map_zero]
  have hnz := hf W (leOfHom i)
  rw [h0] at hnz
  haveI : Nontrivial Γ(X, W) := RingHom.domain_nontrivial (X.presheaf.germ W x hxW).hom
  exact zero_notMem_nonZeroDivisors hnz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem associated_germ_of_traitOrdPt_of_codimOne (Z : GMod Xo c)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)) (hC : HasCones Cn Z)
    {U V : Z.X.Opens} {f : Γ(Z.X, U)} {g : Γ(Z.X, V)} {q : Z.X} (hU : q ∈ U) (hV : q ∈ V)
    (hd : ringKrullDim (Z.X.presheaf.stalk q) = 1) (hf : TraitOrdPt φ Z U f q) (hg : TraitOrdPt φ Z V g q) :
    Associated ((Z.X.presheaf.germ U q hU).hom f) ((Z.X.presheaf.germ V q hV).hom g) := by
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  obtain ⟨R, _, _, _, ξ, t, m, P, k, γ, hCN, hcl, hEt, -, -, -, -⟩ := hC q
  subst hcl
  haveI := (Z.normal (ξ (closedPoint R))).1
  haveI := (Z.normal (ξ (closedPoint R))).2
  have hR : CDvr R := GlobalTheory.T.etale_completion_of_dim_one_normal _ hd hEt hCN
  haveI : IsDiscreteValuationRing R := hR.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hj := GlobalTheory.T.generic_point_in_open_of_etale Z ξ hEt
  obtain ⟨be, hbe, hmon⟩ := GlobalTheory.T.exists_monomial_level_form_dvr hR ϖ hϖ t P
  obtain ⟨n, hn, hfn⟩ := hf R hR ϖ hϖ ξ t m P hj be hbe hmon hU rfl
  obtain ⟨n', hn', hgn⟩ := hg R hR ϖ hϖ ξ t m P hj be hbe hmon hV rfl
  have hnn : n = n' := by exact_mod_cast hn.trans hn'.symm
  subst hnn
  exact associated_of_isEtaleCompletion _ hEt _ _ (hfn.trans hgn.symm)

theorem associated_germ_of_traitOrdPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → ∀ (U V : Z.X.Opens) (f : Γ(Z.X, U)) (g : Γ(Z.X, V)), IsRegularFn f → IsRegularFn g → (∀ q, q ∈ U → q ∈ V → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q ∧ TraitOrdPt φ Z V g q) → ∀ (x : Z.X) (hx : x ∈ U) (hx' : x ∈ V), Associated ((Z.X.presheaf.germ U x hx).hom f) ((Z.X.presheaf.germ V x hx').hom g) := by
  intro E _ _ _ H D l Xo c Z Cn φ hC U V f g hfr hgr hord x hx hx'
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI := (Z.normal x).1
  haveI := (Z.normal x).2
  refine associated_of_associated_heightOne _ _ (germ_ne_zero_of_isRegularFn hfr x hx) (germ_ne_zero_of_isRegularFn hgr x hx') ?_
  intro p _ hp
  obtain ⟨q, e, hqx, he⟩ := GlobalTheory.T.stalk_generization_germ_compat x p
  have hqU : q ∈ U := hqx.mem_open U.isOpen hx
  have hqV : q ∈ V := hqx.mem_open V.isOpen hx'
  have hd : ringKrullDim (Z.X.presheaf.stalk q) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
    rfl
  obtain ⟨hf, hg⟩ := hord q hqU hqV hd.le
  have ha := associated_germ_of_traitOrdPt_of_codimOne Z Cn φ hC hqU hqV hd hf hg
  rw [← he U hqU hx f, ← he V hqV hx' g]
  exact ha.map e

end GlobalTheory.TorRef
