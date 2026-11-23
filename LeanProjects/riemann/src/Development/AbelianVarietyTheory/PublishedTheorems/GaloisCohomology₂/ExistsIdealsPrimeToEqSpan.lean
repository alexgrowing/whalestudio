import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals
open scoped nonZeroDivisors

namespace GlobalTheory.Published

def RayCharacterArtin : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ (A : Type) [CommGroup A] (f : idealsPrimeTo 𝔪 →* A),
    (∀ (x : 𝓞 F) (J : idealsPrimeTo 𝔪), x - 1 ∈ 𝔪 →
      (J.1 : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {x} : Ideal (𝓞 F)) → f J = 1) →
    ∃ φ : G F Ω →* A,
      IsOpen (φ.ker : Set (G F Ω)) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ 𝔪 → ∀ B : ValuationSubring Ω, IsPlaceOver B v →
        ∀ σ ∈ Ine (F := F) B, φ σ = 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔪) (B : ValuationSubring Ω), IsPlaceOver B v →
        ∀ σ : G F Ω, IsFrob B (normV v) σ → φ σ = f (primeElt 𝔪 v hv)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (𝔫 : Ideal (𝓞 F)), 𝔪 = v.asIdeal ^ n * 𝔫 → ¬ v.asIdeal ∣ 𝔫 →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ a : A,
          (∃ σ ∈ Ine (F := F) B, φ σ = a) ↔
            ∃ (x : 𝓞 F) (J : idealsPrimeTo 𝔪), x ∉ v.asIdeal ∧ x - 1 ∈ 𝔫 ∧
              (J.1 : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {x} : Ideal (𝓞 F)) ∧ f J = a) ∧
      (∀ φ' : G F Ω →* A, IsOpen (φ'.ker : Set (G F Ω)) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔪) (B : ValuationSubring Ω), IsPlaceOver B v →
          ∀ σ : G F Ω, IsFrob B (normV v) σ → φ' σ = f (primeElt 𝔪 v hv)) → φ' = φ)

end GlobalTheory.Published

namespace GlobalTheory.RayChar

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Mem.Chr GlobalTheory.Mem.UnitIndex GlobalTheory.Idele WithZero

theorem exists_extend {Γ A : Type} [CommGroup Γ] [CommGroup A] (H D : Subgroup Γ)
    (hs : ∀ a, ∃ d ∈ D, d⁻¹ * a ∈ H) (h : H →* A) (hk : ∀ a : H, a.1 ∈ D → h a = 1) :
    ∃ ψ : Γ →* A, (∀ a : H, ψ a = h a) ∧ ∀ d ∈ D, ψ d = 1 := by
  let π : H →* Γ ⧸ D := (QuotientGroup.mk' D).comp H.subtype
  have hπ : Function.Surjective π := fun q => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd, ha⟩ := hs a
    exact ⟨⟨_, ha⟩, QuotientGroup.eq.2 (by simpa using hd)⟩
  let l := π.liftOfSurjective hπ ⟨h, fun a ha => hk a ((QuotientGroup.eq_one_iff _).1 ha)⟩
  refine ⟨l.comp (QuotientGroup.mk' D), fun a => π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hπ) _ a, fun d hd => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff d).2 hd, map_one]

variable {E : Type} [Field E] [NumberField E]

abbrev ex (𝔪 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 E)) : ℤ :=
  FractionalIdeal.count E v (𝔪 : FractionalIdeal (𝓞 E)⁰ E)

theorem ex_eq_zero_iff {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (v : HeightOneSpectrum (𝓞 E)) :
    ex 𝔪 v = 0 ↔ ¬ v.asIdeal ∣ 𝔪 := by
  classical
  rw [ex, FractionalIdeal.count_coe E v hm, ← Associates.count_ne_zero_iff_dvd hm v.irreducible, not_not]
  norm_cast

theorem exp_ex_le_one (𝔪 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 E)) : exp (-ex 𝔪 v) ≤ 1 := by
  have := FractionalIdeal.count_coe_nonneg E v 𝔪
  rw [← exp_zero, exp_le_exp]
  exact neg_nonpos.2 this

theorem exp_ex_lt_one {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 E)} (hv : v.asIdeal ∣ 𝔪) :
    exp (-ex 𝔪 v) < 1 := by
  have h1 : 0 ≤ ex 𝔪 v := FractionalIdeal.count_coe_nonneg E v 𝔪
  have h2 : ex 𝔪 v ≠ 0 := fun h => (ex_eq_zero_iff hm v).1 h hv
  rw [← exp_zero, exp_lt_exp]
  omega

theorem ex_mul {𝔪 𝔫 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (hn : 𝔫 ≠ ⊥) (v : HeightOneSpectrum (𝓞 E)) :
    ex (𝔪 * 𝔫) v = ex 𝔪 v + ex 𝔫 v := by
  rw [ex, FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul E v (FractionalIdeal.coeIdeal_ne_zero.2 hm)
    (FractionalIdeal.coeIdeal_ne_zero.2 hn)]

abbrev at' (v : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) : v.adicCompletion E :=
  algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E x)

theorem at'_le_one (v : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) : Valued.v (at' v x) ≤ 1 := by
  rw [valued_algebraMap]; exact v.valuation_le_one x

theorem mem_iff_at {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (x : 𝓞 E) :
    x ∈ 𝔪 ↔ ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → Valued.v (at' v x) ≤ exp (-ex 𝔪 v) := by
  have h : x ∈ 𝔪 ↔ algebraMap (𝓞 E) E x ∈ (𝔪 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => IsFractionRing.injective (𝓞 E) E e ▸ hy⟩
  rw [h, mem_iff_valuation_le (FractionalIdeal.coeIdeal_ne_zero.2 hm)]
  refine forall_congr' fun v => ?_
  rw [← valued_algebraMap]
  refine ⟨fun h _ => h, fun h => ?_⟩
  by_cases hv : v.asIdeal ∣ 𝔪
  · exact h hv
  · have : exp (-ex 𝔪 v) = 1 := by rw [(ex_eq_zero_iff hm v).2 hv]; simp
    exact (at'_le_one v x).trans this.ge

theorem at'_sub_one (v : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) : at' v (x - 1) = at' v x - 1 := by simp [at']

theorem valued_eq_one {v : HeightOneSpectrum (𝓞 E)} {y : v.adicCompletion E} (h : Valued.v (y - 1) < 1) :
    Valued.v y = 1 := by
  have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion E) _) h
  rwa [add_sub_cancel] at this

abbrev cmp (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) : v.adicCompletion E := (a : AdeleRing (𝓞 E) E).2 v

theorem cmp_mul (a b : Ideles E) (v : HeightOneSpectrum (𝓞 E)) : cmp (a * b) v = cmp a v * cmp b v := rfl

theorem cmp_inv (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) : cmp a⁻¹ v = (cmp a v)⁻¹ :=
  eq_inv_of_mul_eq_one_right (congrArg (fun z : AdeleRing (𝓞 E) E => z.2 v) a.mul_inv)

theorem cmp_diag (k : Eˣ) (v : HeightOneSpectrum (𝓞 E)) :
    cmp (diagUnits E k) v = algebraMap E (v.adicCompletion E) k := rfl

theorem cmp_local_self (v : HeightOneSpectrum (𝓞 E)) (u : (v.adicCompletion E)ˣ) : cmp (localIdele E v u) v = u := by
  classical
  exact Function.update_self v (u : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))

theorem cmp_local_ne {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) (u : (v.adicCompletion E)ˣ) :
    cmp (localIdele E v u) w = 1 := by
  classical
  exact Function.update_of_ne h (u : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))

def congrIdl (𝔪 : Ideal (𝓞 E)) : Subgroup (Ideles E) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 →
    Valued.v (cmp a v) = 1 ∧ Valued.v (cmp a v - 1) ≤ exp (-ex 𝔪 v)}
  one_mem' := fun v _ => by
    have : cmp (1 : Ideles E) v = 1 := rfl
    simp [this]
  mul_mem' := fun {a b} ha hb v hv => by
    refine ⟨by rw [cmp_mul, map_mul, (ha v hv).1, (hb v hv).1, one_mul], ?_⟩
    have e : cmp (a * b) v - 1 = cmp a v * (cmp b v - 1) + (cmp a v - 1) := by rw [cmp_mul]; ring
    rw [e]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha v hv).1, one_mul]; exact (hb v hv).2) (ha v hv).2
  inv_mem' := fun {a} ha v hv => by
    have h0 : cmp a v ≠ 0 := fun h => by simpa [h] using (ha v hv).1
    refine ⟨by rw [cmp_inv, map_inv₀, (ha v hv).1, inv_one], ?_⟩
    have e : cmp a⁻¹ v - 1 = -((cmp a v)⁻¹ * (cmp a v - 1)) := by rw [cmp_inv]; field_simp; ring
    rw [e, Valuation.map_neg, map_mul, map_inv₀, (ha v hv).1, inv_one, one_mul]
    exact (ha v hv).2

theorem mem_congrIdl {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) {a : Ideles E} : a ∈ congrIdl 𝔪 ↔
    ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → Valued.v (cmp a v - 1) ≤ exp (-ex 𝔪 v) :=
  ⟨fun h v hv => (h v hv).2, fun h v hv => ⟨valued_eq_one ((h v hv).trans_lt (exp_ex_lt_one hm hv)), h v hv⟩⟩

theorem continuous_cmp (v : HeightOneSpectrum (𝓞 E)) : Continuous fun a : Ideles E => cmp a v :=
  ((RestrictedProduct.continuous_eval v).comp continuous_snd).comp Units.continuous_val

theorem isOpen_congrIdl {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) : IsOpen (congrIdl 𝔪 : Set (Ideles E)) := by
  have h := (Ideal.finite_factors hm).isOpen_biInter (f := fun v : HeightOneSpectrum (𝓞 E) =>
    {a : Ideles E | Valued.v (cmp a v - 1) ≤ exp (-ex 𝔪 v)}) fun v _ =>
      (isOpen_valued_le (K := E) v _).preimage ((continuous_cmp v).sub continuous_const)
  convert h using 1
  ext a
  simp [mem_congrIdl hm]

theorem exists_diag {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (a : Ideles E) :
    ∃ d ∈ (diagUnits E).range, d⁻¹ * a ∈ congrIdl 𝔪 := by
  let S := (Ideal.finite_factors hm).toFinset
  have ho : IsOpen (⋂ v : S, {y : (GlobalTheory.FrobDense.Loc S)ˣ |
      Valued.v ((y : GlobalTheory.FrobDense.Loc S).2 v * cmp a⁻¹ v.1 - 1) ≤ exp (-ex 𝔪 v.1)}) :=
    isOpen_iInter_of_finite fun v => by
      have h1 : Continuous fun y : (GlobalTheory.FrobDense.Loc S)ˣ => (y : GlobalTheory.FrobDense.Loc S).2 v :=
        ((continuous_apply v).comp continuous_snd).comp Units.continuous_val
      have h2 : Continuous fun y : (GlobalTheory.FrobDense.Loc S)ˣ =>
          (y : GlobalTheory.FrobDense.Loc S).2 v * cmp a⁻¹ v.1 - 1 := (h1.mul continuous_const).sub continuous_const
      exact h2.isOpen_preimage _ (isOpen_valued_le (K := E) v.1 (-ex 𝔪 v.1))
  obtain ⟨k, hk⟩ := (GlobalTheory.FrobDense.denseRange_units S).exists_mem_open ho
    ⟨Units.map (GlobalTheory.FrobDense.proj S) a, Set.mem_iInter.2 fun v => by
      show Valued.v (cmp (a * a⁻¹) v.1 - 1) ≤ _
      have : cmp (1 : Ideles E) v.1 = 1 := rfl
      simp [this]⟩
  refine ⟨_, ⟨k, rfl⟩, ?_⟩
  have : diagUnits E k * a⁻¹ ∈ congrIdl 𝔪 := (mem_congrIdl hm).2 fun v hv =>
    Set.mem_iInter.1 hk ⟨v, (Set.Finite.mem_toFinset _).2 hv⟩
  simpa [mul_comm] using (congrIdl 𝔪).inv_mem this

def idl : Ideles E →* (FractionalIdeal (𝓞 E)⁰ E)ˣ := ((idealHom E).comp (finIdele E)).toHomUnits

theorem valued_cmp (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (cmp a v) = exp (-FractionalIdeal.count E v (idl a : FractionalIdeal (𝓞 E)⁰ E)) := by
  have : (idl a : FractionalIdeal (𝓞 E)⁰ E) = idealOf (finIdele E a) := rfl
  rw [this, count_idealOf]
  exact valued_idele (finIdele E a) v

theorem idl_diag (k : Eˣ) :
    (idl (diagUnits E k) : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (k : E) :=
  idealOf_unitEmbedding k

theorem idl_eq {a : Ideles E} {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (h : ∀ v, Valued.v (cmp a v) = exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) : idl a = J :=
  Units.ext (eq_of_count_eq (idl a).ne_zero J.ne_zero fun v => by
    have := (valued_cmp a v).symm.trans (h v)
    rwa [exp_inj, neg_inj] at this)

theorem idl_unit {a : Ideles E} (h : a ∈ unitIdl E) : idl a = 1 :=
  idl_eq fun v => by rw [Units.val_one, FractionalIdeal.count_one]; exact h v

def idlPrime (𝔪 : Ideal (𝓞 E)) : congrIdl 𝔪 →* idealsPrimeTo 𝔪 :=
  (idl.comp (congrIdl 𝔪).subtype).codRestrict _ fun a v hv => by
    have := (valued_cmp a.1 v).symm.trans (a.2 v hv).1
    rwa [← exp_zero, exp_inj, neg_eq_zero] at this

theorem exists_quot {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (k : Eˣ) (hk : diagUnits E k ∈ congrIdl 𝔪) :
    ∃ α β : 𝓞 E, β ≠ 0 ∧ α - 1 ∈ 𝔪 ∧ β - 1 ∈ 𝔪 ∧ (k : E) * β = α := by
  classical
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (k : E)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
  by_cases ht : 𝔪 = ⊤
  · exact ⟨c, d, hd0, ht ▸ Submodule.mem_top, ht ▸ Submodule.mem_top, by rw [← hcd]; exact div_mul_cancel₀ _ hdE⟩
  have hD : Ideal.span {d} ≠ ⊥ := by simpa using hd0
  have hI : 𝔪 * Ideal.span {d} ≠ ⊥ := mul_ne_zero hm hD
  let g : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E := fun v => if v.asIdeal ∣ 𝔪 then 1 else 0
  have hg : ∀ v, Valued.v (g v) ≤ 1 := fun v => by
    by_cases hv : v.asIdeal ∣ 𝔪 <;> simp [g, hv]
  obtain ⟨β, hβ⟩ := exists_sub_mem_adelicIdeal_of_integral (K := E) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    (a := ⟨g, Filter.Eventually.of_forall hg⟩) hg
  rw [mem_adelicIdeal_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)] at hβ
  have hβ' : ∀ v, Valued.v (g v - at' v β) ≤ exp (-(ex 𝔪 v + ex (Ideal.span {d}) v)) := fun v => by
    rw [← ex_mul hm hD]; exact hβ v
  have h1 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → Valued.v (at' v β - 1) ≤ exp (-ex 𝔪 v) := fun v hv => by
    have := hβ' v
    simp only [g, if_pos hv] at this
    rw [Valuation.map_sub_swap, neg_add, exp_add] at this
    exact this.trans (mul_le_of_le_one_right' (exp_ex_le_one _ v))
  have hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E) * β) ≤ 1 := fun v => by
    rw [← valued_algebraMap, map_mul, map_mul]
    by_cases hv : v.asIdeal ∣ 𝔪
    · rw [show Valued.v (algebraMap E (v.adicCompletion E) (k : E)) = 1 from (hk v hv).1, one_mul]
      exact at'_le_one v β
    · have := hβ' v
      simp only [g, if_neg hv] at this
      rw [zero_sub, Valuation.map_neg, (ex_eq_zero_iff hm v).2 hv, zero_add, ex,
        FractionalIdeal.coeIdeal_span_singleton, ← valuation_eq_exp_neg_count v hdE, ← valued_algebraMap] at this
      refine (mul_le_mul_right this _).trans ?_
      rw [← map_mul, ← map_mul, ← hcd, div_mul_cancel₀ _ hdE]
      exact at'_le_one v c
  obtain ⟨α, hα⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hint
  have hβ1 : β - 1 ∈ 𝔪 := (mem_iff_at hm _).2 fun v hv => by rw [at'_sub_one]; exact h1 v hv
  refine ⟨α, β, ?_, (mem_iff_at hm _).2 fun v hv => ?_, hβ1, hα.symm⟩
  · rintro rfl
    exact ht ((Ideal.eq_top_iff_one _).2 (by simpa using 𝔪.neg_mem hβ1))
  · have e : at' v (α - 1) = cmp (diagUnits E k) v * (at' v β - 1) + (cmp (diagUnits E k) v - 1) := by
      rw [at'_sub_one, at', hα, map_mul, cmp_diag]; ring_nf
    rw [e]
    exact Valuation.map_add_le _ (by rw [map_mul, (hk v hv).1, one_mul]; exact h1 v hv) (hk v hv).2

theorem diag_mem {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) {x : 𝓞 E} (hx : x - 1 ∈ 𝔪) (h0 : (x : E) ≠ 0) :
    diagUnits E (Units.mk0 (x : E) h0) ∈ congrIdl 𝔪 :=
  (mem_congrIdl hm).2 fun v hv => by
    have := (mem_iff_at hm _).1 hx v hv
    rwa [at'_sub_one] at this

theorem ne_zero_of_eq_span {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {x : 𝓞 E}
    (h : (J : FractionalIdeal (𝓞 E)⁰ E) = (Ideal.span {x} : Ideal (𝓞 E))) : (x : E) ≠ 0 := fun h0 => by
  have hx : x = 0 := by exact_mod_cast h0
  exact J.ne_zero (by rw [h, hx]; simp)

variable {A : Type} [CommGroup A]

theorem exists_idelic {𝔪 : Ideal (𝓞 E)} (hm : 𝔪 ≠ ⊥) (f : idealsPrimeTo 𝔪 →* A)
    (hf : ∀ (x : 𝓞 E) (J : idealsPrimeTo 𝔪), x - 1 ∈ 𝔪 →
      (J.1 : FractionalIdeal (𝓞 E)⁰ E) = (Ideal.span {x} : Ideal (𝓞 E)) → f J = 1) :
    ∃ ψ : Ideles E →* A, (∀ a : congrIdl 𝔪, ψ a = f (idlPrime 𝔪 a)) ∧ ∀ d ∈ (diagUnits E).range, ψ d = 1 := by
  refine exists_extend _ _ (exists_diag hm) (f.comp (idlPrime 𝔪)) ?_
  rintro ⟨_, hk⟩ ⟨k, rfl⟩
  obtain ⟨α, β, hβ, h1, h2, e⟩ := exists_quot hm k hk
  have hβE : (β : E) ≠ 0 := by exact_mod_cast hβ
  have hαE : (α : E) ≠ 0 := e ▸ mul_ne_zero k.ne_zero hβE
  have ha := hf α (idlPrime 𝔪 ⟨_, diag_mem hm h1 hαE⟩) h1
    ((idl_diag _).trans (FractionalIdeal.coeIdeal_span_singleton α).symm)
  have hb := hf β (idlPrime 𝔪 ⟨_, diag_mem hm h2 hβE⟩) h2
    ((idl_diag _).trans (FractionalIdeal.coeIdeal_span_singleton β).symm)
  have e' : (⟨_, diag_mem hm h1 hαE⟩ : congrIdl 𝔪) = ⟨_, hk⟩ * ⟨_, diag_mem hm h2 hβE⟩ :=
    Subtype.ext (by
      show diagUnits E _ = diagUnits E _ * diagUnits E _
      rw [← map_mul]
      exact congrArg _ (Units.ext e.symm))
  rwa [e', map_mul, map_mul, hb, mul_one] at ha

section Values

variable {𝔪 : Ideal (𝓞 E)} {f : idealsPrimeTo 𝔪 →* A} {ψ : Ideles E →* A}

theorem map_unit (h1 : ∀ a : congrIdl 𝔪, ψ a = f (idlPrime 𝔪 a)) {a : Ideles E} (hu : a ∈ unitIdl E)
    (hc : a ∈ congrIdl 𝔪) : ψ a = 1 := by
  rw [h1 ⟨a, hc⟩, show idlPrime 𝔪 ⟨a, hc⟩ = 1 from Subtype.ext (idl_unit hu), map_one]

theorem local_mem_unitIdl {v : HeightOneSpectrum (𝓞 E)} {u : (v.adicCompletion E)ˣ} (hu : IsUnitAt v u) :
    localIdele E v u ∈ unitIdl E := fun w => by
  show Valued.v (cmp _ w) = 1
  by_cases h : w = v
  · subst h; rw [cmp_local_self]; exact hu
  · rw [cmp_local_ne h, map_one]

theorem local_mem_congrIdl {v : HeightOneSpectrum (𝓞 E)} (hv : ¬ v.asIdeal ∣ 𝔪) (u : (v.adicCompletion E)ˣ) :
    localIdele E v u ∈ congrIdl 𝔪 := fun w hw => by
  rw [cmp_local_ne (by rintro rfl; exact hv hw)]
  simp

theorem map_unif (h1 : ∀ a : congrIdl 𝔪, ψ a = f (idlPrime 𝔪 a)) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ 𝔪) {u : (v.adicCompletion E)ˣ} (hu : IsUnifAt v u) :
    ψ (localIdele E v u) = f (primeElt 𝔪 v hv) := by
  rw [h1 ⟨_, local_mem_congrIdl hv u⟩]
  refine congrArg f (Subtype.ext (idl_eq fun w => ?_))
  show Valued.v (cmp (localIdele E v u) w) = exp (-FractionalIdeal.count E w (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E))
  by_cases h : w = v
  · subst h; rw [cmp_local_self, FractionalIdeal.count_self]; exact hu
  · rw [cmp_local_ne h, map_one, FractionalIdeal.count_maximal_coprime E w (Ne.symm h)]; rfl

theorem ex_split {v : HeightOneSpectrum (𝓞 E)} {n : ℕ} {𝔫 : Ideal (𝓞 E)} (hn : 𝔫 ≠ ⊥) {w : HeightOneSpectrum (𝓞 E)}
    (h : w ≠ v) : ex (v.asIdeal ^ n * 𝔫) w = ex 𝔫 w := by
  rw [ex_mul (pow_ne_zero _ v.ne_bot) hn, ex, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_maximal_coprime E w (Ne.symm h), mul_zero, zero_add]

theorem map_local_unit (hm : 𝔪 ≠ ⊥) (h1 : ∀ a : congrIdl 𝔪, ψ a = f (idlPrime 𝔪 a))
    (h2 : ∀ d ∈ (diagUnits E).range, ψ d = 1) {v : HeightOneSpectrum (𝓞 E)} {n : ℕ} {𝔫 : Ideal (𝓞 E)}
    (hd : 𝔪 = v.asIdeal ^ n * 𝔫) {u : (v.adicCompletion E)ˣ} (hu : IsUnitAt v u) {x : 𝓞 E} (h0 : (x : E) ≠ 0)
    (hx : x - 1 ∈ 𝔫) (hxu : Valued.v (at' v x - u) ≤ exp (-ex 𝔪 v)) :
    ∃ J : idealsPrimeTo 𝔪, (J.1 : FractionalIdeal (𝓞 E)⁰ E) = (Ideal.span {x} : Ideal (𝓞 E)) ∧
      f J = (ψ (localIdele E v u))⁻¹ := by
  have hn : 𝔫 ≠ ⊥ := by rintro rfl; simp at hd; exact hm hd
  have hc : diagUnits E (Units.mk0 (x : E) h0) * (localIdele E v u)⁻¹ ∈ congrIdl 𝔪 :=
    (mem_congrIdl hm).2 fun w hw => by
      rw [cmp_mul, cmp_inv]
      by_cases h : w = v
      · subst h
        have e : cmp (diagUnits E (Units.mk0 (x : E) h0)) w * ((u : w.adicCompletion E))⁻¹ - 1 =
            (at' w x - u) * ((u : w.adicCompletion E))⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ u.ne_zero]; rfl
        rw [cmp_local_self, e, map_mul, map_inv₀, show Valued.v (u : w.adicCompletion E) = 1 from hu, inv_one, mul_one]
        exact hxu
      · have hw' : w.asIdeal ∣ 𝔫 := by
          by_contra hw'
          exact (ex_eq_zero_iff hm w).1 (by rw [hd, ex_split hn h]; exact (ex_eq_zero_iff hn w).2 hw') hw
        have := (mem_iff_at hn _).1 hx w hw'
        rw [at'_sub_one] at this
        rw [cmp_local_ne h, inv_one, mul_one, hd, ex_split hn h]
        exact this
  refine ⟨idlPrime 𝔪 ⟨_, hc⟩, ?_, ?_⟩
  · show ((idl (_ * _) : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) = _
    rw [map_mul, map_inv, idl_unit (local_mem_unitIdl hu), inv_one, mul_one, idl_diag]
    exact (FractionalIdeal.coeIdeal_span_singleton x).symm
  · rw [← h1]
    show ψ (_ * _) = _
    rw [map_mul, map_inv, h2 _ ⟨_, rfl⟩, one_mul]

theorem exists_integer_near (hm : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 E)} {n : ℕ} {𝔫 : Ideal (𝓞 E)}
    (hd : 𝔪 = v.asIdeal ^ n * 𝔫) (hv : ¬ v.asIdeal ∣ 𝔫) {u : (v.adicCompletion E)ˣ} (hu : IsUnitAt v u) :
    ∃ x : 𝓞 E, x ∉ v.asIdeal ∧ x - 1 ∈ 𝔫 ∧ Valued.v (at' v x - u) ≤ exp (-ex 𝔪 v) := by
  have hn : 𝔫 ≠ ⊥ := by rintro rfl; simp at hd; exact hm hd
  have hI : 𝔪 * v.asIdeal ≠ ⊥ := mul_ne_zero hm v.ne_bot
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal_of_integral (K := E) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    (a := (localIdele E v u : AdeleRing (𝓞 E) E).2) fun w => (local_mem_unitIdl hu w).le
  rw [mem_adelicIdeal_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)] at hx
  have hx' : ∀ w, Valued.v (at' w x - cmp (localIdele E v u) w) ≤ exp (-ex 𝔪 w) * exp (-ex v.asIdeal w) := fun w => by
    rw [← exp_add, ← neg_add, ← ex_mul hm v.ne_bot, Valuation.map_sub_swap]; exact hx w
  have hv' := hx' v
  rw [cmp_local_self] at hv'
  refine ⟨x, fun hxv => ?_, (mem_iff_at hn _).2 fun w hw => ?_,
    hv'.trans (mul_le_of_le_one_right' (exp_ex_le_one _ v))⟩
  · have h3 : Valued.v (at' v x - u) < 1 :=
      (hv'.trans (mul_le_of_le_one_left' (exp_ex_le_one _ v))).trans_lt (exp_ex_lt_one v.ne_bot dvd_rfl)
    have h4 : Valued.v (at' v x) < 1 := by
      rw [valued_algebraMap]; exact (HeightOneSpectrum.valuation_lt_one_iff_mem v x).2 hxv
    have h5 := Valuation.map_sub_lt _ h4 h3
    rw [sub_sub_cancel, show Valued.v (u : v.adicCompletion E) = 1 from hu] at h5
    exact lt_irrefl _ h5
  · have h : w ≠ v := by rintro rfl; exact hv hw
    have := (hx' w).trans (mul_le_of_le_one_right' (exp_ex_le_one _ w))
    rwa [cmp_local_ne h, hd, ex_split hn h, ← at'_sub_one] at this

end Values

end GlobalTheory.RayChar

namespace GlobalTheory.Published

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Mem.Chr GlobalTheory.RayChar

theorem GlobalArtinReciprocity.rayCharacterArtin (H : GlobalArtinReciprocity) : RayCharacterArtin := by
  intro F Ω _ _ _ _ _ 𝔪 hm A _ f hf
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨ψ, h1, h2⟩ := exists_idelic hm f hf
  have hopen : IsOpen (ψ.ker : Set (Ideles F)) :=
    Subgroup.isOpen_mono (H₁ := unitIdl F ⊓ congrIdl 𝔪) (fun a h => map_unit h1 h.1 h.2)
      (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (isOpen_congrIdl hm))
  have hker : art.ker ≤ ψ.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le h2 ?_) (ψ.ker.isClosed_of_isOpen hopen)
    rintro _ ⟨y, -, rfl⟩
    exact map_unit h1 (fun v => map_one (Valued.v : Valuation (v.adicCompletion F) _))
      fun v hv => (congrIdl 𝔪).one_mem v hv
  let χ : Gab F Ω →* A := art.liftOfSurjective ha.quot.surjective ⟨ψ, hker⟩
  have hχ : ∀ a, χ (art a) = ψ a := fun a =>
    art.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv ha.quot.surjective) _ a
  let φ : G F Ω →* A := (χ.comp (toAb F Ω))⁻¹
  have hφ : ∀ σ a, art a = toAb F Ω σ → φ σ = (ψ a)⁻¹ := fun σ a e => by
    rw [← hχ, e]; rfl
  have hφo : IsOpen (φ.ker : Set (G F Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (ψ.ker.map art).comap (toAb F Ω)) ?_
      ((ha.quot.isOpenMap _ hopen).preimage QuotientGroup.continuous_mk)
    rintro σ ⟨a, h, e⟩
    rw [MonoidHom.mem_ker, hφ σ a e, MonoidHom.mem_ker.1 h, inv_one]
  have hfr : ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔪) (B : ValuationSubring Ω), IsPlaceOver B v →
      ∀ σ : G F Ω, IsFrob B (normV v) σ → φ σ = f (primeElt 𝔪 v hv) := fun v hv B hB σ hσ => by
    obtain ⟨u, hu, e⟩ := (ha.frob v B hB _).2 ⟨σ, hσ, rfl⟩
    have := hφ _ _ e
    rwa [map_inv, inv_inj, map_unif h1 hv hu] at this
  refine ⟨φ, hφo, fun v hv B hB σ hσ => ?_, hfr, fun v n 𝔫 hd hv B hB a => ⟨?_, ?_⟩, fun φ' ho' hfr' => ?_⟩
  · obtain ⟨u, hu, e⟩ := (ha.ine v B hB _).2 ⟨σ, hσ, rfl⟩
    rw [hφ _ _ e, map_unit h1 (local_mem_unitIdl hu) (local_mem_congrIdl hv u), inv_one]
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨u, hu, e⟩ := (ha.ine v B hB _).2 ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx1, hx2, hx3⟩ := exists_integer_near hm hd hv hu
    have h0 : (x : F) ≠ 0 := fun h => hx1 (by rw [show x = 0 by exact_mod_cast h]; exact zero_mem _)
    obtain ⟨J, hJ, e'⟩ := map_local_unit hm h1 h2 hd hu h0 hx2 hx3
    exact ⟨x, J, hx1, hx2, hJ, by rw [e', hφ _ _ e]⟩
  · rintro ⟨x, J, hx1, hx2, hJ, rfl⟩
    have h0 := ne_zero_of_eq_span hJ
    have hu : IsUnitAt v (atFin v (Units.mk0 (x : F) h0)) := valued_algebraMap_eq_one F v x hx1
    obtain ⟨J', hJ', e'⟩ := map_local_unit hm h1 h2 hd hu h0 hx2 (by
      rw [show at' v x - ((atFin v (Units.mk0 (x : F) h0) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 0 from
        sub_self _, map_zero]
      exact zero_le)
    obtain ⟨σ, hσ, e⟩ := (ha.ine v B hB _).1 ⟨_, hu, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    rw [hφ _ _ e.symm, ← e', show J' = J from Subtype.ext (Units.ext (hJ'.trans hJ.symm))]
  · let _ : TopologicalSpace A := ⊥
    have : DiscreteTopology A := ⟨rfl⟩
    have h := GlobalTheory.FrobDense.eq_one_of_frob F Ω art ha A (φ' * φ⁻¹)
      ((continuous_of_isOpen_ker' φ' ho').mul (continuous_of_isOpen_ker' φ hφo).inv)
      (Ideal.finite_factors hm).toFinset fun v hv B hB σ hσ => by
        have hv' : ¬ v.asIdeal ∣ 𝔪 := fun h => hv ((Set.Finite.mem_toFinset _).2 h)
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hfr' v hv' B hB σ hσ, hfr v hv' B hB σ hσ, mul_inv_cancel]
    exact mul_inv_eq_one.1 h

theorem exists_idealsPrimeTo_eq_span {F : Type} [Field F] [NumberField F] {𝔪 𝔫 : Ideal (𝓞 F)}
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (hd : 𝔪 = v.asIdeal ^ n * 𝔫) {x : 𝓞 F} (hx : x ∉ v.asIdeal)
    (hx' : x - 1 ∈ 𝔫) :
    ∃ J : idealsPrimeTo 𝔪, (J.1 : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {x} : Ideal (𝓞 F)) := by
  have h0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have h1 : IsCoprime (Ideal.span {x}) v.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have := v.isMaximal.eq_of_le hne le_sup_right
    exact hx (this ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
  have h2 : IsCoprime (Ideal.span {x}) 𝔫 :=
    Ideal.isCoprime_iff_exists.2 ⟨x, Ideal.mem_span_singleton_self x, _, 𝔫.neg_mem hx', by ring⟩
  have hc : IsCoprime (Ideal.span {x}) 𝔪 := hd ▸ h1.pow_right.mul_right h2
  refine ⟨⟨Units.mk0 _ (FractionalIdeal.coeIdeal_ne_zero.2 (by simpa using h0 : Ideal.span {x} ≠ ⊥)),
    fun w hw => ?_⟩, rfl⟩
  rw [Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]
  exact count_span_eq_zero h0 hc w hw

theorem kills_of_rayPrincipal {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
    {A : Type} [CommGroup A] (f : idealsPrimeTo 𝔪 →* A) (hf : ∀ J : idealsPrimeTo 𝔪, J.1 ∈ rayPrincipal 𝔪 → f J = 1)
    (x : 𝓞 F) (J : idealsPrimeTo 𝔪) (hx : x - 1 ∈ 𝔪)
    (hJ : (J.1 : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {x} : Ideal (𝓞 F))) : f J = 1 := by
  have h0 := ne_zero_of_eq_span hJ
  refine hf J ⟨Units.mk0 (x : F) h0, ⟨x, 1, ⟨fun h => h0 (by simp [h]), one_ne_zero,
    Ideal.isCoprime_iff_exists.2 ⟨x, Ideal.mem_span_singleton_self x, _, 𝔪.neg_mem hx, by ring⟩,
    by simp [← Ideal.one_eq_top, isCoprime_one_left], hx, fun φ => ?_⟩, by simp⟩, Units.ext ?_⟩
  · exact absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => Complex.conj_ofReal (φ y)))
      (IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ))
  · rw [coe_toPrincipalIdeal, hJ, FractionalIdeal.coeIdeal_span_singleton]
    rfl

example {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (𝔪 : Ideal (𝓞 F)) (x : 𝓞 F) (J : idealsPrimeTo 𝔪)
    (hx : x - 1 ∈ 𝔪) (hJ : (J.1 : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {x} : Ideal (𝓞 F))) :
    (QuotientGroup.mk J : RayClassGroup 𝔪) = 1 :=
  kills_of_rayPrincipal (A := RayClassGroup 𝔪) (QuotientGroup.mk' ((rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪)))
    (fun I h => (QuotientGroup.eq_one_iff I).2 h) x J hx hJ

end GlobalTheory.Published

end
