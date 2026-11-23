import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NormBound
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalCyclotomic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

theorem exists_prime_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (h : (n : O) ∈ P) : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : O) ∈ P := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact absurd (by simpa using h) ((Ideal.ne_top_iff_one _).1 hP.ne_top)
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨r, h1, h2, h3⟩ := ih (right_ne_zero_of_mul hn) h
      exact ⟨r, h1, h2.mul_left _, h3⟩

theorem lie_cast {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {w w' : Sp F ⟶ X} (h : w = w') (ML : LieModel G w V) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End F V) (hact : ML.IsActOf act ρ) :
    ∃ MC : LieModel G w' V, (∀ x, (MC.pt x).left = (ML.pt x).left) ∧
      (∀ e x, M.ValAt w' e (MC.pt x) ↔ M.ValAt w e (ML.pt x)) ∧ MC.IsActOf act ρ := by
  subst h
  exact ⟨ML, fun _ => rfl, fun _ _ => Iff.rfl, hact⟩

theorem centre_loc {X : Scheme.{0}} {O : Type} [CommRing O] (z : Sp O ⟶ X) (P : Ideal O) [hP : P.IsPrime] :
    centre (spMap (algebraMap O (Localization.AtPrime P)) ≫ z) = z (⟨P, hP⟩ : PrimeSpectrum O) := by
  have e : (spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint (Localization.AtPrime P)) =
      (⟨P, hP⟩ : PrimeSpectrum O) := by
    apply PrimeSpectrum.ext
    show (IsLocalRing.maximalIdeal _).comap (algebraMap O (Localization.AtPrime P)) = P
    exact Localization.AtPrime.comap_maximalIdeal
  show z ((spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint _)) = _
  rw [e]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)

omit [∀ k, Fintype (J k)] in
theorem inFibre_loc (P : Ideal (𝓞 L)) [P.IsPrime] {p : ℕ} (hp : (p : 𝓞 L) ∈ P) :
    InFibre 𝔐.ξ p ⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z), 𝔐.all _⟩ := fun hu => by
  have h := (PositivityTheory.HtPt.Gh.unitAt_centre_iff 𝔐.tie.gen _ (𝔐.all _) p).1 hu
  rw [← map_natCast (algebraMap (𝓞 L) (Localization.AtPrime P))] at h
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).1 h hp

set_option maxHeartbeats 800000 in

theorem loc {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
    (ML : LieModel 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (ρ : 𝓞 E →+* Module.End L V)
    (hact : ML.IsActOf 𝔐.t.act.act ρ) (σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L))
    (hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)))
    (hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s)) (κ : ℕ → Ω) (k : ℕ → 𝓞 L)
    (hκ : ∀ p ∈ S, HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p (κ p) ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (κ p) (algebraMap (𝓞 L) L (k p)))
    (hdisc : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) (s : CMType H ⊕ CMType H)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] (cc : Localization.AtPrime P →+* L)
    (hc : cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L) :
    (∀ x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)),
      (∃ v : epsAt z ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G z v ∧
        (ML.pt x).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) →
      ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) ∧
    ∀ x, (∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) → ∀ d ∈ differentIdeal ℤ (𝓞 E),
      (∏ p ∈ S, k p) • σ₀ s d • x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)) ∧
      ∃ w : epsAt (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z) ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G _ w ∧
        (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)).left = spMap (dualMap cc) ≫ w.left := by
  classical
  have hξ := 𝔐.tie.gen
  let A := Localization.AtPrime P
  letI : Algebra A L := cc.toAlgebra
  have hc' : ∀ a, algebraMap A L (algebraMap (𝓞 L) A a) = algebraMap (𝓞 L) L a := fun a => RingHom.congr_fun hc a
  haveI : IsScalarTower (𝓞 L) A L := IsScalarTower.of_algebraMap_eq fun a => (hc' a).symm
  letI : Module A V := Module.compHom V cc
  haveI : IsScalarTower A L V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (𝓞 L) A V := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul L (algebraMap (𝓞 L) A r) x, hc', algebraMap_smul]
  haveI : IsFractionRing A L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A L
  have inj := IsFractionRing.injective A L
  let zA : Sp A ⟶ 𝔐.X := spMap (algebraMap (𝓞 L) A) ≫ z
  have hzL : spMap (algebraMap (𝓞 L) L) ≫ z = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ zA := by
    rw [← hc, ← Category.assoc]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  obtain ⟨MC, hM1, hM2, hM3⟩ := lie_cast 𝔐.M hzL ML _ ρ hact
  have hq : (⟨centre zA, 𝔐.all _⟩ : Cpt 𝔐.ξ) = ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ :=
    Subtype.ext (centre_loc z P)
  have hmv : ∀ (e : 𝔐.Li) (q q' : Cpt 𝔐.ξ), q = q' → e ∈ 𝔐.V s q → e ∈ 𝔐.V s q' := by
    rintro e _ _ rfl h; exact h
  have hfib : ∀ x, x ∈ 𝔐.M.fibAt (𝔐.V s) zA MC ↔ ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L)
      {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
    intro x
    have e1 : 𝔐.M.fibAt (𝔐.V s) zA MC = Submodule.span A
        {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
          𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
      unfold LieModel.fibAt
      congr 1
      ext w
      exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, hmv e _ _ hq h1, (hM2 _ _).1 h2⟩,
        fun ⟨e, h1, h2⟩ => ⟨𝔐.all _, e, hmv e _ _ hq.symm h1, (hM2 _ _).2 h2⟩⟩
    rw [e1, IsLocalization.mem_span_iff P.primeCompl]
    have e2 : ∀ (t : P.primeCompl) (u : V), (t : 𝓞 L) • IsLocalization.mk' A (1 : 𝓞 L) t • u = u := fun t u => by
      rw [← algebraMap_smul A (t : 𝓞 L), smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    constructor
    · rintro ⟨u, hu, t, rfl⟩
      exact ⟨t, t.2, by rwa [e2]⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨_, h, ⟨t, ht⟩, by rw [smul_comm]; exact (e2 ⟨t, ht⟩ x).symm⟩
  have hlat := GlobalTheory.T.lie_lattice_eval_fraction_field 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M A zA L V MC hξ 𝔐.t.semi.smooth (𝔐.all _) (𝔐.all _)
  have hval : ∀ {a : Ω} {r : A} {n : 𝓞 L}, ValAt 𝔐.ξ zA a r →
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a (algebraMap (𝓞 L) L n) →
      ValAt 𝔐.ξ zA a (algebraMap (𝓞 L) A n) := fun {a r n} h1 h2 => by
    have h3 := LieTangent.valAt_base hξ (algebraMap A L) h1
    rw [← hzL] at h3
    have h4 := LieTangent.valAt_unique hξ h3 h2
    rw [← hc'] at h4
    rwa [← inj h4]
  let σA : CMType H ⊕ CMType H → (𝓞 E →+* A) := fun s => (algebraMap (𝓞 L) A).comp (σ₀ s)
  have hσA : ∀ s a, ValAt 𝔐.ξ zA (𝔐.emb s a) (σA s a) := fun s a => by
    obtain ⟨r, hr⟩ := emb_value 𝔐 zA s a
    exact hval hr (hσ s a)
  have hσe : ∀ s, (algebraMap A L).comp (σA s) = (algebraMap (𝓞 L) L).comp (σ₀ s) := fun s =>
    RingHom.ext fun a => hc' _
  have main : 𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A ≤
      𝔐.M.fibAt (𝔐.V s) zA MC ∧ ∀ w ∈ 𝔐.M.fibAt (𝔐.V s) zA MC, ∀ d ∈ differentIdeal ℤ (𝓞 E),
      algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • w ∈
        𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A := by
    by_cases hex : ∃ p ∈ S, (p : 𝓞 L) ∈ P
    · obtain ⟨p, hpS, hp⟩ := hex
      have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 (𝔐.S_prime p hpS).ne_zero
      have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hp)
      haveI : IsDiscreteValuationRing A :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP0 A
      obtain ⟨v, hv, hv1⟩ := exists_val A L
      have hvp : v (p : L) < 1 := by
        have := hv1 (algebraMap (𝓞 L) A p) fun h => (IsLocalization.AtPrime.isUnit_to_map_iff A P _).1 h hp
        rwa [hc', map_natCast] at this
      obtain ⟨h1, h2, h3⟩ := hκ p hpS
      obtain ⟨r, hr⟩ := exists_value zA (𝔐.all _) (h2 _ (inFibre_loc 𝔐 z P hp)).1
      obtain ⟨a1, a2⟩ := on_S 𝔐 zA MC ρ hM3 hpS (κ p) h1 h2 v hv hvp s (σA s) (hσA s) _ (hval hr h3)
      refine ⟨a1, fun w hw d hd => ?_⟩
      rw [← Finset.prod_erase_mul S k hpS, map_mul, mul_smul]
      exact Submodule.smul_mem _ _ (a2 w hw d hd)
    · have hun : ∀ n : ℕ, (n : 𝓞 L) ∉ P → IsUnit (n : A) := fun n hn => by
        rw [← map_natCast (algebraMap (𝓞 L) A)]
        exact IsLocalization.map_units A (⟨n, hn⟩ : P.primeCompl)
      have e := off_S 𝔐 zA MC ρ hM3 σA hσA (by simpa only [hσe] using hinj)
        (fun p hp => hun p fun h => hex ⟨p, hp, h⟩)
        (hun _ fun h => by
          obtain ⟨r, h1, h2, h3⟩ := exists_prime_mem P _ (Int.natAbs_ne_zero.2 (discr_ne_zero E)) h
          exact hex ⟨r, hdisc r h1 (Int.natCast_dvd.2 h2), h3⟩) s
      refine ⟨e.ge, fun w hw d _ => ?_⟩
      rw [← e]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw)
  rw [hσe] at main
  refine ⟨fun x hx ⟨v, hv, hxv⟩ => (hfib x).1 (main.1 ⟨(hlat x).2 ?_, hx⟩), fun x hx d hd => ?_⟩
  · refine ⟨LieCarrier.epsHom (algebraMap (𝓞 L) A) z zA rfl ≫ v, LieFib.isTanAt_epsHom _ _ _ _ _ hv, ?_⟩
    rw [hM1, hxv, ← hc]
    exact (congrArg (· ≫ v.left) (LieFib.spec_dualMap_comp _ cc)).trans (Category.assoc _ _ _)
  · obtain ⟨h1, h2⟩ := main.2 x ((hfib x).2 hx) d hd
    have e : algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • x = (∏ p ∈ S, k p) • σ₀ s d • x := by
      rw [algebraMap_smul]
      exact congrArg _ (algebraMap_smul A (σ₀ s d) x)
    rw [e] at h1 h2
    obtain ⟨w, hw, hw'⟩ := (hlat _).1 h1
    exact ⟨h2, w, hw, (hM1 _).symm.trans hw'⟩

end LevelTowerAlt.LocalPrimeBound
