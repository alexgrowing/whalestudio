import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)
open GlobalTheory.Mem.Chr (unitIdl)

namespace UpperTheory.V.Af.Tw

def lev (K : Type) [Field K] [NumberField K] (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v⟩

theorem lev_mem_nhds (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) :
    (lev K N : Set (Ideles K)) ∈ nhds (1 : Ideles K) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Ideles K => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Ideles K => (x⁻¹).val.2 := h1.comp continuous_inv
  have h3 : Continuous fun x : Ideles K =>
      (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹ :=
    (h1.sub continuous_const).mul continuous_const
  have hU := ((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_
  · have : ((1 : Ideles K).val.2 - 1) = 0 := sub_self _
    simp only [this, zero_mul]
    exact zero_mem _
  · rintro y ⟨⟨hy, hy'⟩, hy''⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
        congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
    · have e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1 := hy'' v
      haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
      have h0 : Valued.v (N : v.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.2 hN
      rw [map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul] at e
      exact e

theorem ideleMap_mem_lev (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (y : Ideles K) : ideleMap K L y ∈ lev L N ↔ y ∈ lev K N := by
  have he : ∀ w : HeightOneSpectrum (𝓞 L), (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  have h1 : ∀ w : HeightOneSpectrum (𝓞 L), Valued.v ((ideleMap K L y).val.2 w) = 1 ↔
      Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := fun w => by
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)]
  have h2 : ∀ w : HeightOneSpectrum (𝓞 L),
      Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L) ↔
      Valued.v (y.val.2 (w.under (𝓞 K)) - 1) ≤ Valued.v (N : (w.under (𝓞 K)).adicCompletion K) := fun w => by
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)]
  have hs : ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  constructor
  · rintro ⟨a, b⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨w, rfl⟩ := hs v
      exact (h1 w).1 (a w)
    · obtain ⟨w, rfl⟩ := hs v
      exact (h2 w).1 (b w)
  · rintro ⟨a, b⟩
    exact ⟨fun w => (h1 w).2 (a _), fun w => (h2 w).2 (b _)⟩

theorem eq_one_of_mem_lev (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : 3 ≤ N) (ε : Kˣ)
    (h : diagUnits K ε ∈ lev K N) (hε : ∀ φ : K →+* ℂ, ‖φ ε‖ = 1) : ε = 1 := by
  have hN0 : (N : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  by_contra hne
  have hb0 : ((ε : K) - 1) / N ≠ 0 := div_ne_zero (sub_ne_zero.2 fun h => hne (Units.ext h)) hN0
  have hint : IsIntegral ℤ (((ε : K) - 1) / N) := by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (((ε : K) - 1) / N) fun v => by
      have e : Valued.v (algebraMap K (v.adicCompletion K) ε - 1) ≤ Valued.v (N : v.adicCompletion K) := h.2 v
      rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, ← map_natCast (algebraMap K (v.adicCompletion K)),
        GlobalTheory.UpIdeleMod.valued_algebraMap, GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      rw [map_div₀]
      exact div_le_one_of_le₀ e zero_le
    rw [← hr]
    exact r.isIntegral_coe
  have hlt : ∀ φ : K →+* ℂ, ‖φ (((ε : K) - 1) / N)‖ < 1 := fun φ => by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]
    have := norm_sub_le (φ ε) 1
    rw [hε, norm_one] at this
    linarith
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hb0 hint fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact (hlt φ).ne (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp, map_one]) hn.ne')

def Unr {F : Type} (L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v → (w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal = 1

def IsType (F : Type) {L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (Φ : Set (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
    ∃ w' : HeightOneSpectrum (𝓞 L), w' ≠ w ∧ w'.under (𝓞 F) = w.under (𝓞 F) ∧ (w ∈ Φ ↔ w' ∉ Φ)

def Glue : Prop :=
  ∀ (I J K B : Type) [CommGroup I] [CommGroup J] [CommGroup K] [CommGroup B], KStar.Choice.IsDiv B →
    ∀ (i : J →* I) (d : K →* I) (c : I →* I) (σ : K →* K) (U V : Subgroup I) (N : J →* B) (g : I →* B) (n M l : ℕ),
      0 < M → l.Prime → (∀ a, c (i a) = i a) → (∀ x, c (d x) = d (σ x)) → (∀ u ∈ U, c u ∈ U) →
      (∀ a, i a ∈ U → g (i a) = N a) → (∀ x, σ x = x → ∃ a, i a = d x ∧ N a = 1) →
      (∀ x, d (σ x / x) ∈ U → (σ x / x) ^ n = 1) → (∀ x, d (σ x / x) ∈ V → σ x = x) → (∀ u ∈ U, u ^ M ∈ V) →
      ∃ ψ θ : I →* B, (∀ a, ψ (i a) = N a) ∧ (∀ x, ψ (d x) = 1) ∧ (∀ u ∈ U, ψ u = g u * θ (u / c u)) ∧
        (∀ u ∈ V, θ u = 1) ∧ ∃ k : ℕ, 0 < k ∧ (n.Coprime l → k.Coprime l) ∧ ∀ u ∈ U, θ u ^ k = 1

def LevPow : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ), N ≠ 0 → ∃ M : ℕ, 0 < M ∧ ∀ u ∈ unitIdl K, u ^ M ∈ lev K N

def Kron : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ n : ℕ,
    (∀ l : ℕ, l.Prime → (¬ ∃ ζ : K, IsPrimitiveRoot ζ l) → n.Coprime l) ∧
    ∀ y : Kˣ, diagUnits K y ∈ unitIdl K → (∀ φ : K →+* ℂ, ‖φ y‖ = 1) → y ^ n = 1

def SplitIso : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L], Module.finrank F L = 2 →
    ∀ w w' : HeightOneSpectrum (𝓞 L), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ r : w.adicCompletion L →+* (w.under (𝓞 F)).adicCompletion F, Continuous r ∧
        ∀ x, r (finiteCompletionMap F L w x) = x

def PhiPart : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L], Module.finrank F L = 2 →
    ∀ (l : ℕ), l ≠ 0 → ∀ Φ : Set (HeightOneSpectrum (𝓞 L)), IsType F l Φ →
      ∃ p : Ideles L →* Ideles F, Continuous p ∧
        (∀ (a : Ideles F) (v : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
          (p (ideleMap F L a)).val.2 v = a.val.2 v) ∧
        (∀ (x : Ideles L) (v : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (p x).val.2 v = 1) ∧
        ∀ x : Ideles L, (∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w ∈ Φ → x.val.2 w = 1) → p x = 1

def AwayTriv : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (N : Ideles F →* B) (S : Set (HeightOneSpectrum (𝓞 F))), Continuous N → (∀ z : Ideles F, z.val.2 = 1 → N z = 1) →
    (∀ v, v ∉ S → ∀ x, IsUnitAt v x → N (localIdele F v x) = 1) →
    ∀ b : Ideles F, (∀ v, v ∉ S → Valued.v (b.val.2 v) = 1) → (∀ v ∈ S, b.val.2 v = 1) → N b = 1

def IdeleExt : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Algebra F L], IsTotallyReal F →
    Module.finrank F L = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ Φ : Set (HeightOneSpectrum (𝓞 L)), IsType F l Φ →
    ∀ N : Ideles F →* (Qbar l)ˣ, Continuous N → (∀ k, N (diagUnits F k) = 1) → (∀ z : Ideles F, z.val.2 = 1 → N z = 1) →
      (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ x, IsUnitAt v x → N (localIdele F v x) = 1) →
      ∃ ψ : Ideles L →* (Qbar l)ˣ, Continuous ψ ∧ (∀ a, ψ (ideleMap F L a) = N a) ∧ (∀ k, ψ (diagUnits L k) = 1) ∧
        (∀ z : Ideles L, z.val.2 = 1 → ψ z = 1) ∧
        ∃ k : ℕ, 0 < k ∧ ((¬ ∃ ζ : L, IsPrimitiveRoot ζ l) → k.Coprime l) ∧
          ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), IsUnitAt w x →
            (((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ψ (localIdele L w x) = 1) ∧ (w ∉ Φ → ψ (localIdele L w x) ^ k = 1)

def InfTriv : Prop :=
  ∀ (F Ω B : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space B] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ ν : G F Ω →* B, Continuous ν →
    (∀ c, IsConjEl c → ν c = 1) → ∀ (z : Ideles F) (σ : G F Ω), z.val.2 = 1 → art z = toAb F Ω σ → ν σ = 1

def Descend : Prop :=
  ∀ (F Ω B : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space B] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ ψ : Ideles F →* B, Continuous ψ →
    (∀ k, ψ (diagUnits F k) = 1) → (∀ z : Ideles F, z.val.2 = 1 → ψ z = 1) →
    ∃ κ : G F Ω →* B, Continuous κ ∧ ∀ (x : Ideles F) (σ : G F Ω), art x = toAb F Ω σ → κ σ = ψ x

def UniExp : Prop :=
  ∀ (F Ω B : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space B] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ (l : ℕ), l ≠ 0 →
    ∀ χ : G F Ω →* B, Continuous χ →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ∃ k : ℕ, k.Coprime l ∧ ∀ s ∈ Ine (F := F) A, χ s ^ k = 1) →
    ∃ k : ℕ, k.Coprime l ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ s ∈ Ine (F := F) A, χ s ^ k = 1

def ResOpen : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω],
    Topology.IsOpenEmbedding (resG F L Ω) ∧ (resG F L Ω).range.index = Module.finrank F L

def VerGroup : Prop :=
  ∀ (H Γ B : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] (r : H →* Γ), Topology.IsOpenEmbedding r → r.range.index = 2 →
    ∀ κ : H →* B, Continuous κ → ∃ ν : Γ →* B, Continuous ν ∧ ∀ g : Γ, g ∉ r.range →
      (∀ s s' : H, r s' = g * r s * g⁻¹ → κ s * κ s' = ν (r s)) ∧ ∀ t : H, r t = g * g → κ t = ν g

def ConjPlace : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], Module.finrank F L = 2 →
    ∀ g : G F Ω, g ∉ (resG F L Ω).range → ∀ (w w' : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w →
      w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) → ∃ A' : ValuationSubring Ω, IsPlaceOver A' w' ∧
        ∀ s s' : G L Ω, resG F L Ω s' = g * resG F L Ω s * g⁻¹ →
          (s ∈ Ine (F := L) A → s' ∈ Ine (F := L) A') ∧ ∀ q : ℕ, IsFrob A q s → IsFrob A' q s'

def UnrAE : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L],
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Unr L v

def LocProd : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ), ∃ y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ,
      ideleMap F L (localIdele F v x) = ∏ w ∈ aboveF (L := L) F v, localIdele L w (y w) ∧
      (Unr L v → IsUnifAt v x → ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v → IsUnifAt w (y w))

def FrobSplit : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], Module.finrank F L = 2 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), Unr L v → IsPlaceOver A v →
      ∀ s : G L Ω, IsFrob A (normV v) (resG F L Ω s) → ∃ w w' : HeightOneSpectrum (𝓞 L), w' ≠ w ∧
        (∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧ IsPlaceOver A w ∧
        normV w = normV v ∧ normV w' = normV v

def FrobInert : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], Module.finrank F L = 2 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), Unr L v → IsPlaceOver A v →
      ∀ σ : G F Ω, IsFrob A (normV v) σ → σ ∉ (resG F L Ω).range → ∃ w : HeightOneSpectrum (𝓞 L),
        (∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v ↔ u = w) ∧ IsPlaceOver A w ∧
        ∀ t : G L Ω, resG F L Ω t = σ * σ → IsFrob A (normV w) t

def VerArt : Prop :=
  ∀ (F L Ω B : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    [T2Space B], Module.finrank F L = 2 → ∀ (art : Ideles F →* Gab F Ω) (artL : Ideles L →* Gab L Ω), IsGlobalArtin art →
    IsGlobalArtin artL → ∀ (κ : G L Ω →* B) (ν : G F Ω →* B), Continuous κ → Continuous ν →
    (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω),
      w.under (𝓞 F) = v → IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, κ s = 1) →
    (∀ (a : Ideles F) (σ : G F Ω) (τ : G L Ω), art a = toAb F Ω σ → artL (ideleMap F L a) = toAb L Ω τ → κ τ = ν σ) →
    VerEq κ ν

end UpperTheory.V.Af.Tw
