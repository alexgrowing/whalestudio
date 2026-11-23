import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeDedekindTwist
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.VectorBundleLabels

theorem finrank_eq_of_isVB {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Lat ξ Li} {r : ℕ} {V : Submodule Ω Li} (h : L.IsVB r V)
    (q : Cpt ξ) : Module.finrank Ω V = r := by
  obtain ⟨U, hU, b, hb, hf⟩ := h q trivial
  rw [← hb, finrank_span_eq_card (hf q trivial hU).1, Fintype.card_fin]

theorem isVBOn_of_eqOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L L' : Lat ξ Li} {r : ℕ} {V : Submodule Ω Li} {T : Set (Cpt ξ)}
    (h : L.IsVB r V) (he : ∀ q ∈ T, L' q = L q) : L'.IsVBOn T r V := fun p _ => by
  obtain ⟨U, hU, b, hb, hf⟩ := h p trivial
  exact ⟨U, hU, b, hb, fun q hq hqU => ⟨(hf q trivial hqU).1, (he q hq).trans (hf q trivial hqU).2⟩⟩

theorem genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    {U : X.Opens} (hpU : p.1 ∈ U) (heU : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) heU).hom s) := by
  have e : (X.presheaf.stalkSpecializes p.2).hom ((X.presheaf.germ U p.1 hpU).hom s) =
      (X.presheaf.germ U (genPt ξ) heU).hom s :=
    ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hpU p.2) s
  exact congrArg (fun t : X.presheaf.stalk (genPt ξ) => (Scheme.stalkClosedPointTo ξ).hom t) e

theorem exists_eq_div_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ u v : X.presheaf.stalk p.1, genMap ξ p v ≠ 0 ∧ a = genMap ξ p u / genMap ξ p v := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have heU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨g, hg⟩ : ∃ g : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom g = a := hξ.bij.2 a
  letI alg : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, heU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, heU⟩
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal.primeCompl g
  have hunit := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) h
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have germ_val : ∀ s : Γ(X, U), genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) s) :=
    fun s => genMap_germ p hpU heU s
  have hv : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) (h : Γ(X, U))) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨(X.presheaf.germ U p.1 hpU).hom f, (X.presheaf.germ U p.1 hpU).hom h, ?_, ?_⟩
  · rw [germ_val]
    exact hv
  · rw [germ_val, germ_val, eq_div_iff hv, ← hg]
    exact (map_mul ψ _ _).symm.trans (congrArg ψ hfh)

theorem normalCpt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) : Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, v, -, e⟩ := exists_eq_div_genMap hξ p z
    exact ⟨u, v, e⟩
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

end PositivityTheory.Xgn.VectorBundleLabels

theorem PositivityTheory.Xgn.vector_bundle_lattice_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hpp hpS hdisc hgenf t
  classical
  have hp : p.Prime := hpp.out
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hN : Flat.NormalCpt 𝔐.ξ := PositivityTheory.Xgn.VectorBundleLabels.normalCpt_of_isCptGen hgen 𝔐.normal
  have hvb : (𝔐.V t).IsVB (labelRk D t) (𝔐.Vgen t) := 𝔐.vb t
  refine ⟨?_, ?_⟩
  · have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
    obtain ⟨hLat, -⟩ := GlobalTheory.T.lie_omega_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M hgen hsm
    obtain ⟨hinj, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
    have hσinj : Function.Injective 𝔐.emb := fun a b hab =>
      hinj (RingHom.ext fun x => 𝔐.cst.injective (RingHom.congr_fun hab x))
    letI : Fintype (CMType H ⊕ CMType H) := by
      haveI : Finite (CMType H ⊕ CMType H) := Nat.finite_of_card_ne_zero (by
        rw [hcard]; exact Module.finrank_pos.ne')
      exact Fintype.ofFinite _
    have h := (GlobalTheory.T.lattice_eigen_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li E 𝔐.ρ 𝔐.M.lat (overPrime 𝔐.ξ p) (Module.finrank Ω 𝔐.Li)
      (CMType H ⊕ CMType H) 𝔐.emb hgen hσinj (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      (HcVb.isVBOn_of_isVB hLat _)
      (fun q _ a e he => by
        haveI := 𝔐.t.act.hom a
        exact HcVb.lat_stable 𝔐.M (𝔐.t.act.act a) (𝔐.ρ a) (𝔐.act a) q e he)
      (fun q _ s' a => HcVb.integers_regular hN _ q a)
      (fun q hq => HcVb.unitAt_discr fun r hr hd =>
        not_not.1 (hq r hr fun e => hdisc (e ▸ hd)))).1 t
    have hrk : Module.finrank Ω (eigSp 𝔐.ρ (𝔐.emb t)) = labelRk D t :=
      PositivityTheory.Xgn.VectorBundleLabels.finrank_eq_of_isVB hvb ⟨genPt 𝔐.ξ, specializes_rfl⟩
    rw [hrk] at h
    exact h
  · refine PositivityTheory.Xgn.VectorBundleLabels.isVBOn_of_eqOn hvb fun q hq => ?_
    by_cases hf : InFibre 𝔐.ξ p q
    · exact (Lat.patch_of_unique S (𝔐.dR t) (fun p => 𝔐.HT p t) hpS hf
        fun p' hp' h' => inFibre_unique hp (𝔐.S_prime _ hp') hf h').symm
    · have hno : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q := fun r hr => by
        by_cases e : r = p
        · exact e ▸ hf
        · exact hq r hr e
      rw [hgenf t q hno]
      exact (Lat.patch_of_not S (𝔐.dR t) (fun p => 𝔐.HT p t) fun r hr => hno r (𝔐.S_prime r hr)).symm
