import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HtWSpanSingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEq
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.LatticeHeightUnit

theorem genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    {U : X.Opens} (hpU : p.1 ∈ U) (heU : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) heU).hom s) := by
  exact congrArg (fun f => (CommRingCat.Hom.hom f) s)
    (TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hpU p.2 (Scheme.stalkClosedPointTo ξ))

theorem exists_eq_div_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ u v : X.presheaf.stalk p.1, genMap ξ p v ≠ 0 ∧ a = genMap ξ p u / genMap ξ p v := by
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show (p.1 : X) ∈ (⊤ : X.Opens) from trivial)
  have heW : genPt ξ ∈ W := p.2.mem_open W.isOpen hpW
  obtain ⟨w, rfl⟩ := hξ.bij.2 a
  let _ : Algebra Γ(X, W) (X.presheaf.stalk ((⟨genPt ξ, heW⟩ : W) : X)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨genPt ξ, heW⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk ((⟨genPt ξ, heW⟩ : W) : X))
      (hW.primeIdealOf ⟨genPt ξ, heW⟩).asIdeal := hW.isLocalization_stalk ⟨genPt ξ, heW⟩
  obtain ⟨⟨f, g⟩, hfg⟩ := IsLocalization.mk'_surjective (S := X.presheaf.stalk ((⟨genPt ξ, heW⟩ : W) : X))
    (hW.primeIdealOf ⟨genPt ξ, heW⟩).asIdeal.primeCompl w
  dsimp only at hfg
  have h2 := IsLocalization.mk'_eq_iff_eq_mul.1 hfg
  have h3 : (X.presheaf.germ W (genPt ξ) heW).hom f =
      (show ↑(X.presheaf.stalk (genPt ξ)) from w) * (X.presheaf.germ W (genPt ξ) heW).hom g := h2
  have hu := IsLocalization.map_units (M := (hW.primeIdealOf ⟨genPt ξ, heW⟩).asIdeal.primeCompl)
    (X.presheaf.stalk ((⟨genPt ξ, heW⟩ : W) : X)) g
  have hu' : IsUnit ((X.presheaf.germ W (genPt ξ) heW).hom g) := hu
  have hne : (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ W (genPt ξ) heW).hom g) ≠ 0 :=
    (hu'.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨(X.presheaf.germ W p.1 hpW).hom f, (X.presheaf.germ W p.1 hpW).hom g, ?_, ?_⟩
  · rw [genMap_germ p hpW heW]
    exact hne
  · have h4 : (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ W (genPt ξ) heW).hom f) =
        (Scheme.stalkClosedPointTo ξ).hom w *
          (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ W (genPt ξ) heW).hom g) :=
      (congrArg (Scheme.stalkClosedPointTo ξ).hom h3).trans (map_mul _ _ _)
    rw [genMap_germ p hpW heW, genMap_germ p hpW heW, h4, mul_div_assoc, div_self hne, _root_.mul_one]

theorem normalCpt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (hX : IsNormalScheme X) : Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨_, hic⟩ := hX p.1
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun u v h => hξ.inj p (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩
  have : IsIntegrallyClosed (regAt ξ p) := IsIntegrallyClosed.of_equiv e
  have hfr : IsFractionRing (regAt ξ p) Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      refine IsUnit.mk0 _ ?_
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      intro h
      exact hy0 (Subtype.ext h)
    · intro z
      obtain ⟨u, v, hv, huv⟩ := exists_eq_div_genMap hξ p z
      have hv' : (⟨genMap ξ p v, v, rfl⟩ : regAt ξ p) ≠ 0 := fun h => hv (congrArg Subtype.val h)
      refine ⟨⟨⟨genMap ξ p u, u, rfl⟩, ⟨⟨genMap ξ p v, v, rfl⟩, mem_nonZeroDivisors_of_ne_zero hv'⟩⟩, ?_⟩
      show z * genMap ξ p v = genMap ξ p u
      rw [huv, div_mul_cancel₀ _ hv]
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha
  rw [← hy]
  exact y.2

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  constructor
  intro Y g h hgh
  have key : ∀ (x : Y) (φ : Y.residueField x ⟶ CommRingCat.of Ω),
      spMap a ≫ (Scheme.SpecToEquivOfField Ω Y).symm ⟨x, φ⟩ =
        (Scheme.SpecToEquivOfField K Y).symm ⟨x, φ ≫ CommRingCat.ofHom a⟩ := by
    intro x φ
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, spMap, Spec.map_comp, Category.assoc]
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective g
  obtain ⟨⟨x', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective h
  rw [key, key] at hgh
  have h2 := (Scheme.SpecToEquivOfField K Y).symm.injective hgh
  rw [Scheme.SpecToEquivOfField_eq_iff] at h2
  obtain ⟨e, he⟩ := h2
  have : Mono (CommRingCat.ofHom a) := ConcreteCategory.mono_of_injective _ a.injective
  apply congrArg
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨e, ?_⟩
  dsimp only at he ⊢
  apply (cancel_mono (CommRingCat.ofHom a)).1
  rw [Category.assoc]
  exact he

theorem pow_descend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  have hmk : g = Over.homMk (U := Over.mk (spMap a ≫ ξ)) (V := Over.mk ξ) (spMap a) rfl ≫ g₀ := by
    ext
    simp [e]
  have : Epi (Over.homMk (U := Over.mk (spMap a ≫ ξ)) (V := Over.mk ξ) (spMap a) rfl) :=
    @Over.epi_of_epi_left _ _ _ _ _ _ (epiSp a)
  apply (cancel_epi (Over.homMk (U := Over.mk (spMap a ≫ ξ)) (V := Over.mk ξ) (spMap a) rfl)).1
  rw [MonObj.comp_pow, ← hmk, hg, MonObj.comp_one]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem isVBOn_of_isVB {L : Lat ξ Li} {r : ℕ} {V : Submodule Ω Li} (h : L.IsVB r V) (T : Set (Cpt ξ)) :
    L.IsVBOn T r V := by
  intro p _
  obtain ⟨U, hpU, b, hb, hf⟩ := h p (Set.mem_univ _)
  exact ⟨U, hpU, b, hb, fun q _ hq => hf q (Set.mem_univ _) hq⟩

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  apply hN q
  have h1 : IsIntegral ℤ a := NumberField.RingOfIntegers.isIntegral a
  have h2 : IsIntegral ℤ (σ a) := h1.map σ.toIntAlgHom
  exact h2.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => exact ⟨by simp, by simp, by simp⟩
  | prime p hp => exact h p hp dvd_rfl
  | mul a b iha ihb =>
    have ha0 : a ≠ 0 := by rintro rfl; simp at hn
    have hb0 : b ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨a1, a2, a3⟩ := iha ha0 (fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b))
    obtain ⟨b1, b2, b3⟩ := ihb hb0 (fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a))
    refine ⟨?_, ?_, ?_⟩
    · push_cast
      exact mul_ne_zero a1 b1
    · push_cast
      exact Subring.mul_mem _ a2 b2
    · push_cast
      rw [mul_inv]
      exact Subring.mul_mem _ a3 b3

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) := by
  exact unitAt_nat _ (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F))
    fun p hp hpd => h p hp (Int.ofNat_dvd_left.mpr hpd)

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
  exact Ideal.absNorm_mem _

theorem htOm_eq_omLat {G : Over X} [GrpObj G] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ) (q : Cpt ξ)
    (hu : unitAt ξ q (n : Ω))
    (h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ),
      xk.left = spMap i ≫ (1 : Over.mk ξ ⟶ G).left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → (c : k) = 1) :
    M.htOm L n q = M.omLat q := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro w ⟨x, -, hx⟩
    exact hx.1
  · intro w hw
    have hw' : ∀ e ∈ M.lat q, w e ∈ regAt ξ q := hw
    apply Submodule.subset_span
    refine ⟨1, one_pow n, hw, ⊤, 1, by simp, ?_, ?_⟩
    · intro k _ _ i xk g c h hxk hgn hW
      rw [HtLatCheck.secVal_one, h1 k i xk g c hxk hgn hW]
    · intro e v hext h
      refine ⟨(n : Ω)⁻¹ * w e, Subring.mul_mem _ hu.2.2 (hw' e (Submodule.subset_span ⟨v, hext⟩)), ?_⟩
      rw [HtLatCheck.secVal_one, TrivSqZeroExt.snd_one, map_zero, zero_add, ← _root_.mul_assoc,
        mul_inv_cancel₀ hu.1, _root_.one_mul]

end PositivityTheory.Xgn.LatticeHeightUnit

open PositivityTheory.Xgn.LatticeHeightUnit in
theorem PositivityTheory.Xgn.lattice_height_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hgt hpd t q hq
  obtain ⟨gt⟩ := hgt
  have hp : p.Prime := Fact.out
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨_, hsm, -, -, -, -⟩ := 𝔐.t.semi
  have hvb : 𝔐.M.lat.IsVBOn {q} (Module.finrank Ω 𝔐.Li) ⊤ :=
    isVBOn_of_isVB (lieLat_isVB_of_smooth 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M hgen hsm).1 {q}
  have hunit : ∀ r : ℕ, r.Prime → unitAt 𝔐.ξ q (r : Ω) := fun r hr => not_not.1 (hq r hr)
  have hchar : CharZero Ω := by
    rcases CharP.char_is_prime_or_zero Ω (ringChar Ω) with h | h
    · exact absurd ringChar.Nat.cast_ringChar (hunit _ h).1
    · have := ringChar.of_eq h
      exact CharP.charP_to_charZero Ω
  have hun : unitAt 𝔐.ξ q ((p ^ 𝔐.R p : ℕ) : Ω) := by
    obtain ⟨a1, a2, a3⟩ := hunit p hp
    refine ⟨?_, ?_, ?_⟩
    · push_cast
      exact pow_ne_zero _ a1
    · push_cast
      exact Subring.pow_mem _ a2 _
    · push_cast
      rw [← inv_pow]
      exact Subring.pow_mem _ a3 _
  have h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ 𝔐.ξ) ⟶ 𝔐.t.G)
      (c : kˣ), xk.left = spMap i ≫ (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left → g ^ (p ^ 𝔐.R p) = 1 →
        Out.WeilIs 𝔐.t.G 𝔐.t.PP.L ((p ^ 𝔐.R p : ℕ) : ℤ) xk g (unitOn c) → (c : k) = 1 := by
    intro k _ _ i xk g c hxk hgn hW
    obtain ⟨x, hx⟩ := 𝔐.tors p hpS k i g hgn
    have hxn : x ^ (p ^ 𝔐.R p) = 1 := pow_descend i hx hgn
    obtain ⟨τ, hτ⟩ := (gt.t₂.onto x).1 hxn
    obtain ⟨x', hx'⟩ : ∃ x' : Fin (D.p + D.q) → 𝓞 E, qmk (p ^ 𝔐.R p) x' = τ := by
      refine ⟨fun j => (Ideal.Quotient.mk_surjective (Multiplicative.toAdd τ j)).choose, ?_⟩
      rw [← ofAdd_toAdd τ]
      unfold qmk
      congr 1
      funext j
      exact (Ideal.Quotient.mk_surjective (Multiplicative.toAdd τ j)).choose_spec
    have h0 : gt.t₂.pt (qmk (p ^ 𝔐.R p) (0 : Fin (D.p + D.q) → 𝓞 E)) = 1 := by
      have : qmk (p ^ 𝔐.R p) (0 : Fin (D.p + D.q) → 𝓞 E) = 1 := by
        unfold qmk
        simp
        rfl
      rw [this, map_one]
    have hx0 : xk.left = spMap i ≫ (gt.t₂.pt (qmk (p ^ 𝔐.R p) 0)).left := by
      rw [h0]
      exact hxk
    have hg1 : g.left = spMap i ≫ (gt.t₂.pt (qmk (p ^ 𝔐.R p) x')).left := by
      rw [hx', hτ]
      exact hx
    have hW' : Out.WeilIs 𝔐.t.G 𝔐.t.PP.L ((p : ℤ) ^ 𝔐.R p) xk g (unitOn c) := by
      rw [← Nat.cast_pow]
      exact hW
    have hw := (gt.weil 0 x' k i xk g c hx0 hg1).1 hW'
    rw [map_zero, AddMonoidHom.zero_apply, ZMod.val_zero, pow_zero, map_one] at hw
    exact hw
  have hom : 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = 𝔐.M.omLat q :=
    htOm_eq_omLat 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) q hun h1
  rcases t with τ | τ
  · have key := LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M 𝔐.t.PP.L
      (p ^ 𝔐.R p) (Module.finrank Ω 𝔐.Li) (𝓞 E) 𝔐.ρ (𝔐.emb (Sum.inl τ)) q hvb hom
    show 𝔐.M.htW 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inl τ)) (differentIdeal ℤ (𝓞 E)) q =
      𝔐.M.eigLat 𝔐.ρ (𝔐.emb (Sum.inl τ)) q
    apply key.2
    · intro a
      exact integers_regular (normalCpt_of_isCptGen hgen 𝔐.normal) (𝔐.emb (Sum.inl τ)) q a
    · refine ⟨((discr E).natAbs : 𝓞 E), natAbs_discr_mem_different E, ?_⟩
      rw [map_natCast]
      exact unitAt_natAbs_discr (fun r hr _ => hunit r hr)
  · have key := LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M 𝔐.t.PP.L
      (p ^ 𝔐.R p) (Module.finrank Ω 𝔐.Li) (𝓞 E) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q hvb hom
    exact key.1
