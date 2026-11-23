import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanImageOfForallHeightOneOverPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem height_comap_eq_one_of_flat_of_mem {R R₁ : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing R₁] [IsNoetherianRing R₁] (ρ : R →+* R₁) (hρ : ρ.Flat) {f : R} (hf : f ≠ 0)
    (q : Ideal R₁) [q.IsPrime] (hq : q.height = 1) (hfq : ρ f ∈ q) : (q.comap ρ).height = 1 := by
  letI := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  haveI : Algebra.HasGoingDown R R₁ := Algebra.HasGoingDown.of_flat
  haveI : (q.comap ρ).IsPrime := Ideal.comap_isPrime ρ q
  haveI : q.LiesOver (q.comap ρ) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.comap ρ) q
  have hle : (q.comap ρ).height ≤ 1 := by rw [← hq, h]; exact le_self_add
  refine le_antisymm hle ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro hb
  have : f ∈ q.comap ρ := hfq
  rw [hb, Ideal.mem_bot] at this
  exact hf this

end GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem spanBy_mono {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {T T' : Set F₁}
    (h : T ⊆ T') : spanBy c T ⊆ spanBy c T' := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact ⟨n, r, t, fun i => h (ht i), rfl⟩

theorem spanBy_sections_eq_of_flat : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin V₀ hV0 hVadd hVsmul _ W W₁
    htor hWcl hgauss
  have hW0 : ∀ p : Ideal R, p.IsPrime → f ∈ p → (0 : F) ∈ W p := fun p hp hfp => by
    obtain ⟨m, hm⟩ := htor p hp hfp 0
    simpa using hm
  set P := {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal} with hPdef
  have hP : P.Finite := GlobalTheory.finite_height_eq_one_mem hf

  have key : ∀ S : Finset (PrimeSpectrum R), (∀ p ∈ S, p ∈ P) →
      spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal}) =
        spanBy c₁ (θ '' V₀) ∩ {x | ∀ p ∈ S, x ∈ spanBy c₁ (θ '' W p.asIdeal)} := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => intro _; ext x; simp
    | insert a S ha ih =>
      intro hS
      have haP := hS a (Finset.mem_insert_self a S)
      obtain ⟨hadd, hsmul, -⟩ := hWcl a.asIdeal a.2 haP.1 haP.2
      have hSP : ∀ p ∈ S, p ∈ P := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have e : {u | u ∈ V₀ ∧ ∀ p ∈ insert a S, u ∈ W p.asIdeal} =
          {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} ∩ W a.asIdeal := by
        ext u; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
          forall_eq_or_imp]; tauto
      rw [e, GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint R R₁ F F₁ ρ c₀ c₁ θ hρ hc₀ hcomm hlin {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} (W a.asIdeal)
        ⟨hV0, fun p hp => hW0 p.asIdeal p.2 (hSP p hp).2⟩
        (fun a' ha' b hb => ⟨hVadd a' ha'.1 b hb.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).1 a' (ha'.2 p hp) b (hb.2 p hp)⟩)
        (fun r a' ha' => ⟨hVsmul r a' ha'.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).2.1 r a' (ha'.2 p hp)⟩)
        (hW0 a.asIdeal a.2 haP.2) hadd hsmul, ih hSP]
      ext x; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
        forall_eq_or_imp]; tauto
  have hS := key hP.toFinset (fun p hp => hP.mem_toFinset.mp hp)
  have e1 : {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p} =
      {u | u ∈ V₀ ∧ ∀ p ∈ hP.toFinset, u ∈ W p.asIdeal} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
    exact and_congr_right fun _ => ⟨fun h p hp => h p.asIdeal p.2 hp.1 hp.2,
      fun h p hp h1 hfp => h ⟨p, hp⟩ ⟨h1, hfp⟩⟩
  rw [e1, hS]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
  refine and_congr_right fun hx => ?_
  have hxr : x ∈ spanBy c₁ (Set.range θ) := spanBy_mono c₁ (Set.image_subset_range θ V₀) hx
  have hd : ∃ d : R₁, d ≠ 0 ∧ c₁ d * x ∈ spanBy c₁ (Set.range θ) := ⟨1, one_ne_zero, by simpa⟩
  constructor
  · intro h q hq hq1 hfq
    have h1 := height_comap_eq_one_of_flat_of_mem ρ hρ hf q hq1 hfq
    refine ((hgauss q hq hq1 hfq) x hd).mpr ⟨1, (Ideal.ne_top_iff_one q).mp hq.ne_top, ?_⟩
    simpa using h ⟨q.comap ρ, Ideal.comap_isPrime ρ q⟩ ⟨h1, hfq⟩
  · intro h p hp
    obtain ⟨hadd, hsmul, hinv⟩ := hWcl p.asIdeal p.2 hp.1 hp.2
    refine GlobalTheory.T.mem_span_image_of_forall_height_one_over_prime R R₁ F F₁ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin p.asIdeal p.2 hp.1 hp.2
      (W p.asIdeal) (htor p.asIdeal p.2 hp.2) hadd hsmul hinv x hxr fun q hq hq1 hfq hqp => ?_
    have := ((hgauss q hq hq1 hfq) x hd).mp (h q hq hq1 hfq)
    rwa [hqp] at this

end GlobalTheory.Desc
