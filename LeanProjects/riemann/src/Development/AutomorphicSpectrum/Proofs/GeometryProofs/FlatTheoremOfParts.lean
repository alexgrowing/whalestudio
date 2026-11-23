import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormZeroOutsideDenomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCptStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameComplexCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreUniformisedFrameStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingValuationSubringStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.TopA

theorem exists_padic_emb (F : IntermediateField ℚ ℂ) [NumberField F] (p : Nat.Primes) :
    Nonempty (F →+* ℂ_[p]) :=
  ⟨(IsAlgClosed.lift (M := ℂ_[p]) (R := ℚ) (S := F)).toRingHom⟩

theorem eq_of_clopen_irred {X : Type*} [TopologicalSpace X] {U U' : Set X} (hU : IsClopen U)
    (hUi : IsIrreducible U) (hU' : IsClopen U') (hUi' : IsIrreducible U') {u : X} (hu : u ∈ U) (hu' : u ∈ U') :
    U = U' :=
  (hUi.isConnected.isPreconnected.subset_isClopen hU' ⟨u, hu, hu'⟩).antisymm
    (hUi'.isConnected.isPreconnected.subset_isClopen hU ⟨u, hu', hu⟩)

theorem finite_primes_dvd {n : ℕ} (hn : n ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ n}.Finite :=
  ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun p hp =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp

theorem model_hyp {K : Type} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V] :
    Function.Injective V.subtype ∧ IsNoetherianRing V ∧
      ∀ x : K, ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  refine ⟨Subtype.val_injective, inferInstance, fun x => ?_⟩
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_place {l : Level H} (c : Coeff l) [NumberField c.F] (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) :
    ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ IsDiscreteValuationRing (c.V W) ∧
      ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W := by
  obtain ⟨W, hp, hW⟩ := GlobalTheory.T.padic_embedding_valuation_subring c.F p κ
  obtain ⟨V, hV, hκ, -, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p κ
  have hmem : ∀ x : c.F, x ∈ c.V W ↔ ‖κ x‖ ≤ 1 := fun x => (hW x).symm
  have heq : c.V W = V := by ext x; rw [hmem, hκ]
  refine ⟨W, hp, ?_, fun x => (hmem x).symm⟩
  rw [heq]; exact hV

theorem exists_cpt {D : Datum H} {l : Level H} (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    {U : Set (Xo.XF c)} (hU : IsClopen U) (hUi : IsIrreducible U) : Nonempty (CptOver Y U) := by
  obtain ⟨u, hu⟩ := hUi.nonempty
  obtain ⟨U', Z, hu', hc, hi⟩ := GlobalTheory.T.exists_clopen_irreducible_cpt E H D l Xo c O β Y u hβ
  rw [eq_of_clopen_irred hU hUi hc hi hu hu']
  exact ⟨Z⟩

theorem local_gen (hA0 : FlatLineGenerator) (hA1 : FlatLineGeneratorComponent) (hC : FinConstAll) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (U : Set (Xo.XF c)) (τ : E →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (hpq : 1 ≤ D.p + D.q)
    (hτ : τ (H.rt : E) = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hU : IsClopen U) (hUi : IsIrreducible U)
    (hP : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P))
    (W : ValuationSubring ℂ) [IsDiscreteValuationRing (c.V W)] (Y : Model Xo c (c.V W).subtype)
    (hSF : Y.SplitFibres) (hN3 : Y.N3) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (hκ : ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W) :
    ∃ φ : FrameFn Xo c, IsFlatGen U τ φ FU i ∧ (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧
      ∃ t, HasFinNorm U τ φ p κ t := by
  obtain ⟨Z⟩ := exists_cpt Xo c Y (model_hyp (c.V W)) hU hUi
  have hG : Z.IsGeom := GlobalTheory.T.generic_fibre_uniformised_frame E H D l Xo c _ _ Y U Z g ty FU i hty (fun y hy hr => (hP y hy).1 hr)
  obtain ⟨φ, hl, hf, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ (model_hyp (c.V W)) hpq hτ hG
  obtain ⟨hinf, hfg⟩ := hA1 E H D l Xo c _ _ Y U Z τ φ (model_hyp (c.V W)) hpq hτ hG hl hf
  refine ⟨φ, hfg g ty FU i hty (fun P y hPer hu hy => (hP y hy).2 ⟨P, hPer, hu⟩), fun s => ?_, ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s
    exact ⟨t, ht⟩
  · refine hC E H D l Xo c _ _ Y U Z τ p κ φ hτ Subtype.val_injective (fun x => (hκ x).trans ?_) hSF hN3 hG hf hl
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem hasFinNorm_of_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {U : Set (Xo.XF c)}
    {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (hl : IsLineFn U τ φ) {a : c.F} (ha : a ≠ 0)
    (he : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ' F y v w = β a * φ F y v w)
    {p : Nat.Primes} {κ : c.F →+* ℂ_[p]} {t : ℝ} (ht : HasFinNorm U τ φ' p κ t) :
    HasFinNorm U τ φ p κ (t - Real.log ‖κ a‖) := by
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht V K j β y v w T tK m m' hj hjβ hfr hv hw
  have hja : j (β a) = κ a := by rw [← hjβ]; rfl
  have h2 : ‖κ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero κ).mpr ha)
  have h3 : ‖j (φ K y v w)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero j).mpr (hl.ne K β y v w hfr))
  rw [he K β y v w hfr, map_mul, hja, norm_mul, Real.log_mul h2 h3] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.TopA

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.TopA in

theorem thmFlatA_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  intro hI hA0 hA1 _ E _ _ _ H D Xo l c _ U τ g ty FU i hpq hτ hg hty hU hUi hP
  have hC : FinConstAll := GlobalTheory.T.finite_constant_all_holds
  obtain ⟨-, hI'⟩ := hI
  obtain ⟨Ys, hYs, -⟩ := hI' E H D hpq Xo
  have key : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ φ : FrameFn (Xo l) c, IsFlatGen U τ φ FU i ∧
      (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧ ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨W, hpW, hdvr, hκ⟩ := exists_place c p κ
    haveI := hdvr
    obtain ⟨-, hYi⟩ := hYs p W p.2 hpW
    obtain ⟨hSF, hN3, -⟩ := hYi ⟨l, c, hg p p.2⟩
    exact local_gen hA0 hA1 hC U τ FU i hpq hτ hty hU hUi hP W (Ys p W p.2 hpW ⟨l, c, hg p p.2⟩) hSF hN3 p κ hκ
  obtain ⟨κ₀⟩ := exists_padic_emb c.F ⟨2, Nat.prime_two⟩
  obtain ⟨φ, hφ, hinf, -⟩ := key _ κ₀
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨φ', hφ', -, t, ht⟩ := key p κ
    obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ φ' φ g ty FU i hty hφ' hφ
      (fun y hy hr => (hP y hy).1 hr)
    exact ⟨_, hasFinNorm_of_eq hφ.line ha he ht⟩
  let N : LogNorms c.F := ⟨fun s => (hinf s).choose, fun p κ => (hfin p κ).choose -
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  have hN : HasNorms U τ φ N := ⟨fun s => (hinf s).choose_spec, fun p κ => by
    simp only [N, sub_add_cancel]
    exact (hfin p κ).choose_spec⟩
  refine ⟨φ, N, hφ, hN, ?_⟩
  obtain ⟨n, hn, hn0⟩ := GlobalTheory.T.finite_norm_zero_outside_denom E H D l (Xo l) c U τ φ hτ hU.isOpen hUi.nonempty hφ.line
  have hS := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (((finite_primes_dvd hn.ne').union (finite_primes_dvd H.d_prime.ne_zero)).union hS).subset ?_
  rintro p ⟨ι₀, hι⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  obtain ⟨-, -, -, -, hd⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p ι₀
  have hd' : ‖((H.d : ℕ) : ℂ_[p])‖ = 1 := by simpa using hd H.d h2
  have h0 := hn0 p ι₀ _ h1 (hN.2 p ι₀)
  rw [h3 (ι₀.comp (tauIn c τ)), hd', Real.log_one] at h0
  simp only [sub_zero, mul_zero, add_zero] at h0
  exact hι h0

end GlobalTheory.CompanionTheory.Ar.Flat
