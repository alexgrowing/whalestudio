import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedeanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedeanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantValuationDifferentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonarchValuationOfPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsElementSamePrimeCountStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW

open UniqueFactorizationMonoid

theorem exists_different_val (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [hp : Fact p.Prime]
    (μ : 𝓞 E →*₀ ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∀ x, μ x ≤ 1) (hu : ∀ x y, μ (x + y) ≤ max (μ x) (μ y))
    (hμp : μ (p : 𝓞 E) = (p : ℝ)⁻¹) :
    ∃ d₀ ∈ differentIdeal ℤ (𝓞 E),
      μ d₀ = (p : ℝ) ^ (-((padicValInt p (discr E) : ℝ) / Module.finrank ℚ E)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpos : (0 : ℝ) < p := by linarith
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨P, c, hPp, hPb, hpP, hc, hμ⟩ := GlobalTheory.T.nonarch_valuation_of_prime (𝓞 E) μ (p : 𝓞 E) hp0 h0 h1 hu
    (by rw [hμp]; exact inv_lt_one_of_one_lt₀ hp1) (by rw [hμp]; exact (inv_pos.2 hpos).ne')
  obtain ⟨d₀, hd, hd0, hcount⟩ := GlobalTheory.T.exists_element_same_prime_count (𝓞 E) (differentIdeal ℤ (𝓞 E)) P differentIdeal_ne_bot hPp hPb
  refine ⟨d₀, hd, ?_⟩
  have hk := GlobalTheory.T.discriminant_valuation_different E p P hPp hpP
  have he := hμ _ hp0
  have hv := hμ _ hd0
  rw [hcount] at hv
  rw [hμp] at he
  generalize (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P = e at hk he
  generalize (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P = v at hk hv
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    have := inv_lt_one_of_one_lt₀ hp1
    linarith
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he0
  have hn' : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk' : (padicValInt p (discr E) : ℝ) * e = v * Module.finrank ℚ E := by exact_mod_cast hk
  have hq : (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E = v / e := by
    field_simp
    linarith
  rw [hv, hq, ← Real.rpow_natCast c v]
  have hc1 : c = ((p : ℝ)⁻¹) ^ ((e : ℝ)⁻¹) := by
    rw [he, ← Real.rpow_natCast c e, ← Real.rpow_mul hc.le, mul_inv_cancel₀ he', Real.rpow_one]
  rw [hc1, ← Real.rpow_mul (inv_pos.2 hpos).le, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]
  congr 1
  field_simp

section Abs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {c : Coeff l}

theorem absT_nonneg (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (x : T.Fr) :
    0 ≤ FinRd.absT p la T e x := by
  unfold FinRd.absT
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem absT_add_le (p : ℕ) [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (he : 0 < e)
    (hr : 0 < ramOverZ la) (x y : T.Fr) :
    FinRd.absT p la T e (x + y) ≤ max (FinRd.absT p la T e x) (FinRd.absT p la T e y) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hd : (0 : ℝ) < (e : ℝ) * (ramOverZ la : ℝ) := by
    have h1 : (0 : ℝ) < e := by exact_mod_cast he
    have h2 : (0 : ℝ) < ramOverZ la := by exact_mod_cast hr
    positivity
  by_cases hx : x = 0
  · subst hx
    rw [zero_add]
    exact le_max_right _ _
  by_cases hy : y = 0
  · subst hy
    rw [add_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy]
    have h0 : FinRd.absT p la T e (0 : T.Fr) = 0 := by simp [FinRd.absT]
    rw [h0]
    exact le_max_of_le_left (absT_nonneg p la T e x)
  have key : ∀ u : T.Fr, u ≠ 0 → vV T.V u ≤ vV T.V (x + y) →
      FinRd.absT p la T e (x + y) ≤ FinRd.absT p la T e u := by
    intro u hu h
    unfold FinRd.absT
    rw [if_neg hxy, if_neg hu]
    refine Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg ?_)
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) hd.le
  rcases min_le_iff.1 (min_le_vV_add (V := T.V) hx hy hxy) with h | h
  · exact le_max_of_le_left (key x hx h)
  · exact le_max_of_le_right (key y hy h)

theorem absT_natCast (p : ℕ) [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr)
    (e : ℕ) (hla : (p : 𝓞 c.F) ∈ la.asIdeal) (ho : OverLa la T.V io e) :
    FinRd.absT p la T e (io (p : c.F)) = (p : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr := FinRd.ram_pos (c := c) hla
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  have hv : vLa la (p : c.F) = ramOverZ la := by
    rw [← hres]
    exact Formalism.L2.Pj.Crude.crv_vLa_char la
  have hne : io (p : c.F) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hp.out.ne_zero
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold FinRd.absT
  rw [if_neg hne, ho.2, hv, Real.rpow_neg hpos.le]
  have : (((e : ℤ) * (ramOverZ la : ℤ) : ℤ) : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ)) = 1 := by
    push_cast
    field_simp
  rw [this, Real.rpow_one]

end Abs

section Fib

open GlobalTheory.CompanionTheory.Ar.LieModel

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : CategoryTheory.Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type}
  [AddCommGroup Li] [Module Ω Li] {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [Field C] [Algebra R C]
  {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]

theorem fibAt_mono (M : LieModel G ξ Li) {L L' : Lat ξ Li} (z : Spec (CommRingCat.of R) ⟶ X)
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC)
    (h : ∀ hh : genPt ξ ⤳ centre z, L ⟨centre z, hh⟩ ≤ L' ⟨centre z, hh⟩) : M.fibAt L z MC ≤ M.fibAt L' z MC :=
  Submodule.span_mono fun _ ⟨hh, e, he, hv⟩ => ⟨hh, e, h hh he, hv⟩

theorem smul_mem_fibAt [IsCommMonObj G] [IsScalarTower R C EC] (hξ : IsCptGen ξ) (hsm : Smooth G.hom)
    (M : LieModel G ξ Li) {L L' : Lat ξ Li} (z : Spec (CommRingCat.of R) ⟶ X)
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) {a : Ω} {D : R} (ha : ValAt ξ z a D)
    (h : ∀ (hh : genPt ξ ⤳ centre z) (e : Li), e ∈ L ⟨centre z, hh⟩ → a • e ∈ L' ⟨centre z, hh⟩) {w : EC}
    (hw : w ∈ M.fibAt L z MC) : D • w ∈ M.fibAt L' z MC := by
  have hr := LieTangent.valAt_base hξ (algebraMap R C) ha
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨hh, e, he, hv⟩ := hw
    refine Submodule.subset_span ⟨hh, a • e, h hh e he, ?_⟩
    obtain ⟨h', s, hs, hs'⟩ := hr
    obtain ⟨ev, h1, h2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M C _ h' EC MC hξ hsm
    obtain ⟨hel, rfl⟩ := (h1 e w).1 hv
    let a' : regAt ξ ⟨_, h'⟩ := ⟨a, ⟨s, hs⟩⟩
    have e2 := h2 a' (algebraMap R C D) ⟨e, hel⟩ ⟨h', s, hs, hs'⟩
    rw [← algebraMap_smul C D, ← e2]
    exact (h1 _ _).2 ⟨(a' • (⟨e, hel⟩ : M.lat ⟨_, h'⟩)).2, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul t x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ t hx

end Fib

theorem fib_V_htDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∈ SS → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), ∀ s : CMType H ⊕ CMType H, Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC ≤ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC ∧ ∃ D : T.V, (p : ℝ) ^ (-((padicValInt p (discr E) : ℝ) / Module.finrank ℚ E)) ≤ FinRd.absT p la T e (algebraMap T.V T.Fr D) ∧ ∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC, D • w ∈ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC := by
  intro E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR hp EC _ _ _ _
    MC ρC s
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hsm : Smooth Or.𝔐.t.G.hom := Or.𝔐.t.semi.smooth
  have hF := GlobalTheory.T.root_origin_frame_nonarchimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hv hG la T io e y evT zT t hI zV hR
  obtain ⟨σ, hσ, hσ'⟩ := GlobalTheory.T.root_origin_frame_archimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hv hG la T io e y evT zT t hI
    zV hR s
  have hla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have ho : OverLa la T.V io e := hI.2.1
  have hr := FinRd.ram_pos (c := c) hla
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hVq : ∀ hh : genPt Or.𝔐.ξ ⤳ centre zV, Or.𝔐.V s ⟨centre zV, hh⟩ = Or.𝔐.HT p s ⟨centre zV, hh⟩ := fun hh =>
    Lat.patch_of_unique SS _ _ hp hF fun p' hp' h' => by
      by_contra hne
      exact Lat.not_inFibre_of_coprime _
        ((Nat.coprime_primes (Or.𝔐.S_prime _ hp) (Or.𝔐.S_prime _ hp')).2 (Ne.symm hne)) hF h'
  obtain ⟨hf1, hf2, -, hf4⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e ho.1 hr
  have hreg : ∀ (hh : genPt Or.𝔐.ξ ⤳ centre zV) (a : 𝓞 E), Or.𝔐.emb s a ∈ regAt Or.𝔐.ξ ⟨centre zV, hh⟩ := fun hh a => by
    obtain ⟨_, g, hg, _⟩ := hσ a
    exact ⟨g, hg⟩
  rcases s with τ | τ
  · have hsub : ∀ hh : genPt Or.𝔐.ξ ⤳ centre zV,
        Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb (.inl τ)) ⟨centre zV, hh⟩ ≤
          Or.𝔐.V (.inl τ) ⟨centre zV, hh⟩ := fun hh x hx => by
      rw [hVq hh]
      refine Submodule.subset_span ⟨Or.𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ hx, fun d _ => ?_⟩
      exact Submodule.smul_mem _ (⟨_, hreg hh d⟩ : regAt Or.𝔐.ξ ⟨centre zV, hh⟩) hx
    let μ : 𝓞 E →*₀ ℝ :=
      { toFun := fun a => FinRd.absT p la T e (io (labelEmb c (.inl τ) a))
        map_zero' := by simp [FinRd.absT]
        map_one' := by simpa using hf2
        map_mul' := fun a b => by rw [map_mul, map_mul, hf1] }
    have hμ : ∀ a, μ a = FinRd.absT p la T e (io (labelEmb c (.inl τ) a)) := fun _ => rfl
    obtain ⟨d₀, hd₀, hval⟩ := exists_different_val E p μ (fun a => absT_nonneg p la T e _)
      (fun a => (hf4 _).2 ⟨σ a, hσ' a⟩)
      (fun a b => by
        simp only [hμ, map_add]
        exact absT_add_le p la T e ho.1 hr _ _)
      (by
        rw [hμ, map_natCast]
        exact absT_natCast p la T io e hla ho)
    refine ⟨fibAt_mono _ _ _ hsub, σ d₀, ?_, fun w hw => ?_⟩
    · rw [hσ' d₀, ← hμ, hval]
    · refine smul_mem_fibAt hξ hsm _ zV MC (hσ d₀) (fun hh x hx => ?_) hw
      rw [hVq hh] at hx
      change x ∈ Or.𝔐.M.htW Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb (.inl τ)) (differentIdeal ℤ (𝓞 E)) _ at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hx.2 _ hd₀
      | zero => simp
      | add a b _ _ ha hb =>
        rw [smul_add]
        exact add_mem ha hb
      | smul t a _ ha =>
        have : Or.𝔐.emb (.inl τ) d₀ • t • a = t • (Or.𝔐.emb (.inl τ) d₀ • a) := by
          rw [show t • a = (t : RM.Ω) • a from rfl,
            show t • (Or.𝔐.emb (.inl τ) d₀ • a) = (t : RM.Ω) • (Or.𝔐.emb (.inl τ) d₀ • a) from rfl, smul_comm]
        rw [this]
        exact Submodule.smul_mem _ t ha
  · refine ⟨fibAt_mono _ _ _ fun hh => (hVq hh).ge, 1, ?_, fun w hw => ?_⟩
    · rw [map_one, hf2]
      exact Real.rpow_le_one_of_one_le_of_nonpos hp1
        (neg_nonpos.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    · rw [one_smul]
      exact fibAt_mono _ _ _ (fun hh => (hVq hh).le) hw

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW
