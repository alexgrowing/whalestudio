import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstantsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamilyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrimeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isLocalRing_regAt (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem coordLat_locFree (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) (c : ∀ k, J k) (hc : mseg y c ≠ 0) :
    LocFree (chartRing O (mseg y) c) r (coordLat O y L b c) ∧ ∀ g ∈ chartRing O (mseg y) c, ∀ e : Fin r → Ω,
      (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → g ≠ 0 → g⁻¹ ∈ regAt ξ q →
        Fintype.linearCombination Ω b e ∈ L q) → ∃ n : ℕ, g ^ n • e ∈ coordLat O y L b c := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.dvr_localization_constants X Ω ξ K J y hT A hA m O c hc
  let Q : Type := {q : Cpt ξ // InChart ξ (mseg y) c q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt ξ q}
  let Λ : Q → AddSubgroup (Fin r → Ω) := fun q =>
    (L q.1).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom
  have hcoord : coordLat O y L b c = ⨅ q, Λ q := by
    ext e
    simp only [coordLat, AddSubgroup.mem_iInf, Subtype.forall, Λ, Q]
    exact ⟨fun h q hq => h q hq.1 hq.2, fun h q h1 h2 => h q ⟨h1, h2⟩⟩
  have hinj : Function.Injective (Fintype.linearCombination Ω b) :=
    hli.fintypeLinearCombination_injective
  have hfr : ∀ q : Q, ∃ g ∈ chartRing O (mseg y) c, g ≠ 0 ∧ g⁻¹ ∈ regAt ξ q.1 ∧
      ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q' : Q, g⁻¹ ∈ regAt ξ q'.1 → ∀ e, e ∈ Λ q' ↔
        ∃ a : Fin r → Ω, (∀ i, a i ∈ regAt ξ q'.1) ∧ e = ∑ i, a i • f i := by
    intro q
    obtain ⟨U, hU, f, hfs, hf⟩ := hVB q.1 q.2.2
    obtain ⟨g, hg, hgu, hgU⟩ := h4 q.1 q.2.1 q.2.2 U hU
    have hmem : ∀ i, ∃ f' : Fin r → Ω, Fintype.linearCombination Ω b f' = f i := by
      intro i
      have : f i ∈ Submodule.span Ω (Set.range b) := by
        rw [hsp, ← hfs]; exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
      exact ⟨a, by rw [Fintype.linearCombination_apply]; exact ha⟩
    choose f' hf' using hmem
    refine ⟨g, hg, hgu.1, hgu.2.2, f', ?_, fun q' hq' e => ?_⟩
    · have hl := (hf q.1 q.2.2 hU).1
      have : (Fintype.linearCombination Ω b) ∘ f' = f := funext hf'
      rw [← this] at hl
      exact hl.of_comp _
    · have hu : unitAt ξ q'.1 g := ⟨hgu.1, h1 g hg q'.1 q'.2.1 q'.2.2, hq'⟩
      have hq'U := hgU q'.1 q'.2.1 q'.2.2 hu
      have hfrm := (hf q'.1 q'.2.2 hq'U).2
      show Fintype.linearCombination Ω b e ∈ L q'.1 ↔ _
      rw [hfrm]
      constructor
      · intro he
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).1 he
        refine ⟨fun i => (a i : Ω), fun i => (a i).2, hinj ?_⟩
        rw [← ha, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
      · rintro ⟨a, ha, rfl⟩
        refine (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).2 ⟨fun i => ⟨a i, ha i⟩, ?_⟩
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
  have key := GlobalTheory.T.regular_lattice_local_free (chartRing O (mseg y) c) Q (fun q => regAt ξ q.1) r Λ (fun q => isLocalRing_regAt q.1)
    (fun q a ha => h1 a ha q.1 q.2.1 q.2.2)
    (fun P hP => by
      obtain ⟨q, hq1, hq2, hq⟩ := h2 P hP
      refine ⟨⟨q, hq1, hq2⟩, fun s => ?_⟩
      rw [hq s]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h1 _ s.2 q hq1 hq2, h.2⟩⟩)
    (fun q a ha => by
      obtain ⟨s, hs, hu, hsa⟩ := h3 q.1 q.2.1 q.2.2 a ha
      exact ⟨s, hs, hu.1, hu.2.2, hsa⟩)
    hfr
  rw [hcoord]
  refine ⟨key.1, fun g hg e he => key.2 g hg e fun q h h' => ?_⟩
  exact he q.1 q.2.1 q.2.2 h h'

theorem coordLat_family (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) :
    IsLatFamily O y (coordLat O y L b) := by
  have key := coordLat_locFree X Ω ξ K J y hT A hA m O V L r Vg b hli hsp hVB
  refine ⟨fun s hs a ha v hv => (key s hs).1.1 a ha v hv, fun s t hs ht v hv => ?_⟩
  have hg : mseg y s / mseg y t ∈ chartRing O (mseg y) t := Algebra.subset_adjoin ⟨s, rfl⟩
  refine (key t ht).2 _ hg v fun q hq hO hg0 hgi => ?_
  have hqs : InChart ξ (mseg y) s q := by
    refine ⟨hs, fun c' => ?_⟩
    have e : mseg y c' / mseg y s = mseg y c' / mseg y t * (mseg y s / mseg y t)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hq.2 c') hgi
  have := (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hqs) hO)
  exact this

theorem coordLat_mono {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → L q ≤ L' q) :
    coordLat O y L b c ≤ coordLat O y L' b c := by
  intro v hv
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  exact h q hO (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)

theorem coordLat_le_divLat {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (a : Ω) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ e ∈ L' q, a • e ∈ L q) :
    coordLat O y L' b c ≤ divLat a (coordLat O y L b c) := by
  intro v hv
  show a • v ∈ coordLat O y L b c
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  have := h q hO _ (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)
  show Fintype.linearCombination Ω b (a • v) ∈ L q
  rw [map_smul]
  exact this

theorem mem_dotDual' {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} (L : AddSubgroup (Fin n → Ω))
    (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem dotDual_anti {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} {L L' : AddSubgroup (Fin n → Ω)}
    (h : L ≤ L') : dotDual R L' ≤ dotDual R L := fun v hv =>
  (mem_dotDual' R L v).2 fun l hl => (mem_dotDual' R L' v).1 hv l (h hl)

theorem dotDual_le_divLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    {L L' : AddSubgroup (Fin n → Ω)} (a : Ω) (h : L' ≤ divLat a L) : dotDual R L ≤ divLat a (dotDual R L') := by
  intro v hv
  show a • v ∈ dotDual R L'
  refine (mem_dotDual' R L' _).2 fun l hl => ?_
  have h2 := (mem_dotDual' R L v).1 hv _ (show a • l ∈ L from h hl)
  rwa [dotProduct_smul, ← smul_dotProduct]

theorem unit_of_place {A : Type} [CommRing A] [Algebra A Ω] {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] {p : ℕ} (hpm : (p : A) ∈ m) (hp : p.Prime) {q : Cpt ξ}
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : q ∈ overPrime ξ p := by
  intro r hr hrp hf
  have hco : IsCoprime (r : ℤ) (p : ℤ) := by
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hr hp).2 hrp)
  obtain ⟨a, b, hab⟩ := hco
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hrO : IsUnit (r : O) := by
    by_contra hn
    have hr' : (r : O) ∈ IsLocalRing.maximalIdeal O := hn
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : (1 : O) = (a : O) * (r : O) + (b : O) * (p : O) := by
        have := congrArg (Int.cast : ℤ → O) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hr') (Ideal.mul_mem_left _ _ hpO)
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this
  obtain ⟨u, hu⟩ := hrO.exists_right_inv
  have hu' : (r : Ω) * algebraMap O Ω u = 1 := by
    have := congrArg (algebraMap O Ω) hu
    simpa using this
  have hr0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
  refine hf ⟨hr0, natCast_mem _ r, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hu']
  exact hO u

theorem lat_main : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _ _
    _ _ _ w hw t
  have hpp : p.Prime := Fact.out
  have hG : Nonempty (GenTors 𝔐 p) := GlobalTheory.T.arith_variety_hodge_prime_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS hfree hp2 hdisc
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpq hfree
  obtain ⟨-, -, -, hcon, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar A
  have hE := GlobalTheory.T.generic_torsion_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hG hdisc
  obtain ⟨hV1, hV2⟩ := GlobalTheory.T.cm_flag_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hdisc hE t
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hO : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → q ∈ overPrime 𝔐.ξ p :=
    fun q h => unit_of_place (A := A) (m := m) (O := O) hpm hpp h
  have hres : ∀ (L : Lat 𝔐.ξ 𝔐.Li), L.IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) →
      L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q} (labelRk D t) (𝔐.Vgen t) := by
    intro L hL q hq
    obtain ⟨U, hU, f, hf, hfr⟩ := hL q (hO q hq)
    exact ⟨U, hU, f, hf, fun q' hq' hq'U => hfr q' (hO q' hq') hq'U⟩
  have hdF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1)
  have hhF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2)
  have hdL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1) c' hc').1
  have hhL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2) c' hc').1
  obtain ⟨hdD, hdDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hdF hdL
  obtain ⟨hhD, hhDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hhF hhL
  have hpt : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, algebraMap O Ω w • e ∈ 𝔐.dR t q := by
    intro q hq
    by_cases hf : InFibre 𝔐.ξ p q
    · exact GlobalTheory.T.cp_ratio_unramified_odd_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hp2 hdisc κ _ hκ hw hS q hf (hq w) t
    · have hall : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q := fun r hr => by
        by_cases hrp : r = p
        · exact hrp ▸ hf
        · exact hO q hq r hr hrp
      rw [hE t q hall]
      exact ⟨le_rfl, fun e he => (𝔐.dR t q).smul_mem (⟨_, hq w⟩ : regAt 𝔐.ξ q) he⟩
  refine ⟨hdF, hhF, hdD, hhD, fun c' hc' => ⟨hdL c' hc', hhL c' hc', hdDL c' hc', hhDL c' hc', ?_, ?_, ?_, ?_⟩⟩
  · exact coordLat_mono y (b t) c' fun q hq => (hpt q hq).1
  · exact coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2
  · exact dotDual_anti _ (coordLat_mono y (b t) c' fun q hq => (hpt q hq).1)
  · exact dotDual_le_divLat _ _ (coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2)

end GlobalTheory.CompanionTheory.Ar.Num.FamLat
