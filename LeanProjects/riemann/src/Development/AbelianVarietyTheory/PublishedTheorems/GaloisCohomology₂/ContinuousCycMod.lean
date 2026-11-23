import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameQuot

def proKer (l : ℕ) (H : Type*) [Group H] [TopologicalSpace H] : Subgroup H :=
  sInf {U : Subgroup H | U.Normal ∧ IsOpen (U : Set H) ∧ ∃ n : ℕ, U.index = l ^ n}

theorem mem_proKer {l : ℕ} {H : Type*} [Group H] [TopologicalSpace H] {x : H} :
    x ∈ proKer l H ↔
      ∀ U : Subgroup H, U.Normal → IsOpen (U : Set H) → (∃ n : ℕ, U.index = l ^ n) → x ∈ U := by
  simp [proKer, Subgroup.mem_sInf]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

variable (F) in

def ineKer (A : ValuationSubring Ω) (l : ℕ) : Subgroup (G F Ω) :=
  (proKer l (Ine (F := F) A)).map (Ine (F := F) A).subtype

theorem ineKer_le_Ine (A : ValuationSubring Ω) (l : ℕ) : ineKer F A l ≤ Ine (F := F) A :=
  Subgroup.map_subtype_le _

theorem coe_mem_ineKer {A : ValuationSubring Ω} {l : ℕ} {σ : Ine (F := F) A} :
    (σ : G F Ω) ∈ ineKer F A l ↔ σ ∈ proKer l (Ine (F := F) A) :=
  Subgroup.mem_map_iff_mem (Ine (F := F) A).subtype_injective

variable (F) in

def IsProGen (A : ValuationSubring Ω) (l : ℕ) (γ : G F Ω) : Prop :=
  γ ∈ Ine (F := F) A ∧
    Ine (F := F) A ≤ (Subgroup.zpowers γ ⊔ ineKer F A l).topologicalClosure

variable (F) in

abbrev trivDec (A : ValuationSubring Ω) (l n : ℕ) :
    Representation (ZMod (l ^ n)) (Dec (F := F) A) (ZMod (l ^ n)) :=
  Representation.trivial (ZMod (l ^ n)) (Dec (F := F) A) (ZMod (l ^ n))

variable (F) in

abbrev muDec (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Representation (ZMod (l ^ n)) (Dec (F := F) A) (ZMod (l ^ n)) :=
  charRep ((cycMod F Ω l n).comp (Dec (F := F) A).subtype)

theorem continuous_cycMod (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Continuous fun σ : G F Ω => ((cycMod F Ω l n σ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
  have h1 : Continuous (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) := by
    refine continuous_of_continuousAt_zero (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ?_
    rw [ContinuousAt, map_zero, nhds_discrete (ZMod (l ^ n)), Filter.tendsto_pure]
    have hl : (0 : ℝ) < (l : ℝ) ^ (-n : ℤ) :=
      zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
    rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow] at hx
    exact hx
  exact h1.comp (Units.continuous_val.comp (continuous_cycZ F Ω l))

theorem contAction_muDec (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ContAction (muDec F A l n) :=
  (((continuous_cycMod l n).comp continuous_subtype_val).comp continuous_fst).mul continuous_snd

variable (F) in

def cupMu (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    H1 (trivDec F A l n) →ₗ[ZMod (l ^ n)] H1 (muDec F A l n) →ₗ[ZMod (l ^ n)] H2 (muDec F A l n) :=
  cupProductH1H1 (trivDec F A l n) (muDec F A l n) (muDec F A l n) (LinearMap.mul _ _)
    continuous_of_discreteTopology
    (fun g x y => by
      simp only [Representation.trivial_apply, charRep_apply, LinearMap.mul_apply']
      ring)
    (contAction_muDec A l n)

theorem cupMu_mk {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime] {n : ℕ}
    (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)) (f : Z2 (muDec F A l n))
    (hf : ∀ g h, f.1 (g, h) = z.1 g * muDec F A l n g (y.1 h)) :
    cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk f := by
  obtain rfl : f = cupCocycleZ1Z1 (trivDec F A l n) (muDec F A l n) (muDec F A l n) (LinearMap.mul _ _)
      continuous_of_discreteTopology
      (fun g x y => by
        simp only [Representation.trivial_apply, charRep_apply, LinearMap.mul_apply']
        ring)
      (contAction_muDec A l n) z y := Subtype.ext (funext fun p => hf p.1 p.2)
  rfl

def IsUnifRoot (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (x : Ω) : Prop :=
  ∃ ϖ : 𝓞 F, ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧ x ^ N = algebraMap F Ω (ϖ : F)

theorem exists_isUnifRoot [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    ∃ x : Ω, IsUnifRoot v N x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨ϖ, h1, h2⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (ϖ : F)) hN
  exact ⟨x, ϖ, by simpa using h1, h2, hx⟩

def IsInvariantMap (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) {l : ℕ} [Fact l.Prime]
    {n : ℕ} (ζ : Ω) (inv : H2 (muDec F A l n) →ₗ[ZMod (l ^ n)] ZMod (l ^ n)) : Prop :=
  ∀ x : Ω, IsUnifRoot v (l ^ n) x →
  ∀ κ : Z1 (muDec F A l n), (∀ g : Dec (F := F) A, (g : G F Ω) x = ζ ^ (κ.1 g).val * x) →
  ∀ χ : Z1 (trivDec F A l n), (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ.1 g = 0) →
  ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
    inv (cupMu F A l n (Submodule.Quotient.mk χ) (Submodule.Quotient.mk κ)) = χ.1 φ

end GlobalTheory.TameQuot

namespace GlobalTheory.Published

open GlobalTheory.TameQuot

def TameQuotient : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)),
    IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
      IsClosed (ineKer F A l : Set (G F Ω)) ∧
      ((ineKer F A l).subgroupOf (Dec (F := F) A)).Normal ∧
      (∀ U : Subgroup (ineKer F A l), U.Normal → IsOpen (U : Set (ineKer F A l)) →
        U.index.Coprime l) ∧
      (∃ t : Ine (F := F) A →* Multiplicative ℤ_[l], Continuous t ∧ Function.Surjective t ∧
        ∀ σ : Ine (F := F) A, t σ = 1 ↔ (σ : G F Ω) ∈ ineKer F A l) ∧
      (∃ γ : G F Ω, IsProGen F A l γ) ∧
      ∀ φ γ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) → IsProGen F A l (γ : G F Ω) →
        (Subgroup.closure {φ, γ} ⊔ (ineKer F A l).subgroupOf (Dec (F := F) A)).topologicalClosure
          = ⊤ ∧
        (((γ ^ normV v)⁻¹ * (φ * γ * φ⁻¹) : Dec (F := F) A) : G F Ω) ∈ ineKer F A l ∧
        ∀ (H : Type) [Group H] [Finite H] (a c : H), (∃ k : ℕ, c ^ l ^ k = 1) →
          a * c * a⁻¹ = c ^ normV v →
          ∃ f : Dec (F := F) A →* H, IsOpen (f.ker : Set (Dec (F := F) A)) ∧
            (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ ineKer F A l → f σ = 1) ∧ f φ = a ∧ f γ = c

def TameSymbol : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)),
    IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → normV v ≡ 1 [MOD l ^ n] →
    ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ n) →
      (∃ inv : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n),
        IsInvariantMap A v ζ inv.toLinearMap) ∧
      ∀ x : Ω, IsUnifRoot v (l ^ n) x →
      ∀ (γ : Dec (F := F) A) (c : ZMod (l ^ n)), (γ : G F Ω) ∈ Ine (F := F) A →
        (γ : G F Ω) x = ζ ^ c.val * x →
        (IsProGen F A l (γ : G F Ω) → IsUnit c) ∧
        ∀ inv : H2 (muDec F A l n) →ₗ[ZMod (l ^ n)] ZMod (l ^ n), IsInvariantMap A v ζ inv →
        ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
        ∀ (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)),
          (Submodule.Quotient.mk y : H1 (muDec F A l n)) ∈
            H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) →
          c * inv (cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y)) =
            -(z.1 γ * y.1 φ)

def TameLocal : Prop := TameQuotient ∧ TameSymbol

theorem TameSymbol.of_equiv (hT : TameSymbol) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hq : normV v ≡ 1 [MOD l ^ n]) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (e : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n)) :
    ∃ u : (ZMod (l ^ n))ˣ, ∀ x : Ω, IsUnifRoot v (l ^ n) x →
      ∀ (γ : Dec (F := F) A) (c : ZMod (l ^ n)), (γ : G F Ω) ∈ Ine (F := F) A →
        (γ : G F Ω) x = ζ ^ c.val * x →
        ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
        ∀ (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)),
          (Submodule.Quotient.mk y : H1 (muDec F A l n)) ∈
            H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) →
          c * e (cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y)) =
            u * (z.1 γ * y.1 φ) := by
  obtain ⟨⟨inv, hinv⟩, h⟩ := hT F Ω l n A v hA hl hq ζ hζ
  have key : ∀ (a b : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n)) w,
      a w = a (b.symm 1) * b w := fun a b w => by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one,
      LinearEquiv.symm_apply_apply]
  have hu : e (inv.symm 1) * inv (e.symm 1) = 1 := by
    rw [← key, LinearEquiv.apply_symm_apply]
  refine ⟨-(Units.mkOfMulEqOne _ _ hu), fun x hx γ c hγ hc φ hφ z y hy => ?_⟩
  have h1 := (h x hx γ c hγ hc).2 _ hinv φ hφ z y hy
  rw [LinearEquiv.coe_coe] at h1
  rw [key e inv, mul_left_comm, h1]
  simp

end GlobalTheory.Published
