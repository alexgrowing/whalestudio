import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowCardEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace GlobalTheory.TameQuot

open GlobalTheory.WeilDeligne

theorem exists_hom_of_cocycle : ∀ (D H : Type) [Group D] [Group H] (N M q : ℕ), 0 < N → 0 < M → ∀ (κ : D → ZMod N) (χ : D →* (ZMod N)ˣ) (d : D →* Multiplicative (ZMod M)) (φ : D) (a c : H), (∀ g h, κ (g * h) = κ g + (χ g : ZMod N) * κ h) → d φ = Multiplicative.ofAdd 1 → (χ φ : ZMod N) = (q : ZMod N) → κ (φ ^ M) = 0 → (∀ g, d g = 1 → χ g = 1) → c ^ N = 1 → a ^ M = 1 → a * c * a⁻¹ = c ^ q → ∃ f : D →* H, f φ = a ∧ ∀ g, d g = 1 → f g = c ^ (κ g).val := by
  intro D H _ _ N M q hN hM κ χ d φ a c hκ hd hχ hφM hdχ hc ha hac
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero M := ⟨hM.ne'⟩
  have h1 : κ 1 = 0 := by simpa using hκ 1 1
  have hadd : ∀ s t : ZMod N, c ^ (s + t).val = c ^ s.val * c ^ t.val := fun s t => by
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hc]
  have hconj : ∀ (b : ℕ) (s : ZMod N), c ^ ((q : ZMod N) ^ b * s).val * a ^ b = a ^ b * c ^ s.val := by
    intro b s
    have e : ∀ b : ℕ, a ^ b * c * (a ^ b)⁻¹ = c ^ q ^ b := fun b => by
      induction b with
      | zero => simp
      | succ b ih =>
        calc a ^ (b + 1) * c * (a ^ (b + 1))⁻¹ = a ^ b * (a * c * a⁻¹) * (a ^ b)⁻¹ := by
              rw [pow_succ]; group
          _ = c ^ q ^ (b + 1) := by rw [hac, ← conj_pow, ih, ← pow_mul, pow_succ]
    rw [← Nat.cast_pow, ZMod.val_mul, ← pow_eq_pow_mod _ hc, ZMod.val_natCast, pow_mul,
      ← pow_eq_pow_mod _ hc, ← e, conj_pow]
    group
  have hcj : ∀ g e, χ e = 1 → κ (g * e * g⁻¹) = (χ g : ZMod N) * κ e := fun g e he => by
    have h0 := hκ g g⁻¹
    rw [mul_inv_cancel, h1] at h0
    rw [mul_assoc, hκ, hκ, he, Units.val_one, one_mul, mul_add, add_left_comm, ← h0, add_zero]
  have hinv : κ (φ ^ M)⁻¹ = 0 := by
    have h0 := hκ (φ ^ M)⁻¹ (φ ^ M)
    rw [inv_mul_cancel, h1, hφM, mul_zero, add_zero] at h0
    exact h0.symm
  let Φ : D → ℕ → H := fun g b => c ^ (κ (g * (φ ^ b)⁻¹)).val * a ^ b
  have hper : ∀ g b j, Φ g (b + M * j) = Φ g b := fun g b j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← ih]
      simp only [Φ]
      rw [mul_add, mul_one, ← add_assoc, pow_add a _ M, ha, mul_one, add_comm _ M, pow_add φ M,
        mul_inv_rev, ← mul_assoc, hκ, hinv, mul_zero, add_zero]
  have hmod : ∀ g b, Φ g (b % M) = Φ g b := fun g b => by
    rw [← hper g (b % M) (b / M), Nat.mod_add_div]
  have hker : ∀ g, χ (g * (φ ^ (d g).toAdd.val)⁻¹) = 1 := fun g => hdχ _ (by
    rw [map_mul, map_inv, map_pow, hd, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    simp)
  refine ⟨MonoidHom.mk' (fun g => Φ g (d g).toAdd.val) fun g h => ?_, ?_, fun g hg => ?_⟩
  · rw [map_mul, toAdd_mul, ZMod.val_add, hmod]
    have e1 := hker g
    have e2 := hker h
    generalize (d g).toAdd.val = b at *
    generalize (d h).toAdd.val = b' at *
    simp only [Φ]
    have e : g * h * (φ ^ (b + b'))⁻¹ = g * (φ ^ b)⁻¹ * (φ ^ b * (h * (φ ^ b')⁻¹) * (φ ^ b)⁻¹) := by
      rw [pow_add]; group
    rw [e, hκ, e1, Units.val_one, one_mul, hcj _ _ e2, map_pow, Units.val_pow_eq_pow_val, hχ, hadd,
      pow_add a, mul_assoc, ← mul_assoc _ (a ^ b), hconj]
    simp only [mul_assoc]
  · change Φ φ (d φ).toAdd.val = a
    rw [hd, toAdd_ofAdd, ← Nat.cast_one, ZMod.val_natCast, hmod]
    simp [Φ, h1]
  · change Φ g (d g).toAdd.val = _
    simp [Φ, hg]

theorem isProGen_iff_isUnit : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (t : Ine (F := F) A →* Multiplicative ℤ_[l]), Continuous t → Function.Surjective t → (∀ σ : Ine (F := F) A, t σ = 1 ↔ (σ : G F Ω) ∈ ineKer F A l) → ∀ γ : Ine (F := F) A, IsProGen F A l (γ : G F Ω) ↔ IsUnit (t γ).toAdd := by
  intro F Ω _ _ _ _ _ l _ A t ht hs hk γ
  have := compactSpace_Ine (E := F) A
  have c2 : Continuous fun σ => (t σ).toAdd := continuous_toAdd.comp ht
  constructor
  · intro hγ
    let S : Subgroup (Ine (F := F) A) :=
      { carrier := {σ | ‖(t σ).toAdd‖ ≤ ‖(t γ).toAdd‖}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          show ‖(t (a * b)).toAdd‖ ≤ _
          rw [map_mul, toAdd_mul]
          exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
        inv_mem' := fun {a} ha => by
          show ‖(t a⁻¹).toAdd‖ ≤ _
          rw [map_inv, toAdd_inv, norm_neg]
          exact ha }
    have hS : IsClosed (S : Set (Ine (F := F) A)) := isClosed_le c2.norm continuous_const
    have hc : IsClosed ((S.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ hS
    have h1 : Subgroup.zpowers (γ : G F Ω) ⊔ ineKer F A l ≤ S.map (Ine (F := F) A).subtype := by
      refine sup_le (Subgroup.zpowers_le.2 ⟨γ, le_refl ‖(t γ).toAdd‖, rfl⟩) fun τ hτ => ?_
      refine ⟨⟨τ, ineKer_le_Ine A l hτ⟩, ?_, rfl⟩
      show ‖(t _).toAdd‖ ≤ _
      rw [(hk _).2 hτ]
      simp
    obtain ⟨σ₀, h0⟩ := hs (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, e⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 σ₀.2)
    obtain rfl : τ = σ₀ := Subtype.ext e
    have : ‖(t τ).toAdd‖ ≤ ‖(t γ).toAdd‖ := hτ
    rw [h0, toAdd_ofAdd, norm_one] at this
    exact PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one _) this)
  · refine fun hu => ⟨γ.2, fun σ hσ => ?_⟩
    set C := (Subgroup.zpowers (γ : G F Ω) ⊔ ineKer F A l).topologicalClosure with hC
    have hC' : IsClosed (C : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _
    let S : Subgroup (Ine (F := F) A) := C.subgroupOf _
    have hS : IsClosed (S : Set (Ine (F := F) A)) := hC'.preimage continuous_subtype_val
    have : CompactSpace S := isCompact_iff_compactSpace.1 hS.isCompact
    have hγS : γ ∈ S :=
      Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    obtain ⟨τ, hτ⟩ := surjective_of_isUnit (t := t.comp S.subtype) (ht.comp continuous_subtype_val)
      (σ := ⟨γ, hγS⟩) hu (t ⟨σ, hσ⟩)
    have h2 : t (τ.1⁻¹ * ⟨σ, hσ⟩) = 1 := by
      rw [map_mul, map_inv, ← hτ]; simp
    have h3 : τ.1⁻¹ * ⟨σ, hσ⟩ ∈ S :=
      Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ((hk _).1 h2))
    have h4 := S.mul_mem τ.2 h3
    rw [mul_inv_cancel_left] at h4
    exact h4

theorem exists_pow_of_finite {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : L ≃ₐ[K] L) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, σ x = x ^ Fintype.card K ^ i := by
  first
  | exact @_root_.GlobalTheory.CardinalPower.exists_pow_card_eq
  | exact _root_.GlobalTheory.CardinalPower.exists_pow_card_eq
  | (apply _root_.GlobalTheory.CardinalPower.exists_pow_card_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.CardinalPower.exists_pow_card_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CardinalPower.exists_pow_card_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CardinalPower.exists_pow_card_eq ..)

theorem mem_Ine_of_integral {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {τ : G F Ω} (hτ : τ ∈ Dec (F := F) A)
    (h : ∀ b : IntCl F Ω, A.valuation (τ b - b) < 1) : τ ∈ Ine (F := F) A := by
  refine ⟨hτ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have h1 : A.valuation (τ s - s) < 1 := h ⟨s, hs.tower_top⟩
  have h2 : A.valuation (τ t - t) < 1 := h ⟨t, ht.tower_top⟩
  have h3 : A.valuation (τ s) = 1 := by
    rw [← hs1]; exact Valuation.map_eq_of_sub_lt _ (by rwa [hs1])
  have e1 : τ s * (τ x - x) = (τ t - t) - (τ s - s) * x := by rw [← e, map_mul]; ring
  have h4 : A.valuation (τ s * (τ x - x)) < 1 := by
    rw [e1]
    refine Valuation.map_sub_lt _ h2 ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) h1
  rwa [map_mul, h3, one_mul] at h4

open scoped Pointwise in
theorem exists_pow_cong {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {g : G F Ω} (hg : g ∈ Dec (F := F) A) (X : Finset (IntCl F Ω)) :
    ∃ i : ℕ, ∀ b ∈ X, A.valuation (g b - (b : Ω) ^ normV v ^ i) < 1 := by
  classical
  set Q := primeBelow (F := F) A with hQ
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  let : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  have : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  have : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  have hgQ : g ∈ MulAction.stabilizer (G F Ω) Q := by
    show g • Q = Q
    rw [hQ, ← primeBelow_smul, mem_Dec.1 hg]
  obtain ⟨i, hi⟩ := exists_pow_of_finite
    (Ideal.Quotient.stabilizerHom Q v.asIdeal (G F Ω) ⟨g, hgQ⟩) (X.image (Ideal.Quotient.mk Q))
  refine ⟨i, fun b hb => ?_⟩
  have h1 : Ideal.Quotient.mk Q (g • b) = _ := hi _ (Finset.mem_image_of_mem _ hb)
  have h2 : g • b - b ^ normV v ^ i ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, Fintype.card_eq_nat_card]
    exact sub_self _
  exact h2

theorem frob_pow_cong {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (hφ : IsFrob A q φ) (i : ℕ) :
    ActsAs A q (φ ^ i) i 0 := by
  induction i with
  | zero => simpa using actsAs_zero_iff.2 (Ine (F := F) A).one_mem
  | succ i ih => rw [pow_succ]; exact ih.mul (actsAs_one_iff.2 hφ)

theorem closure_frob_sup_Ine : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) → (Subgroup.zpowers φ ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A)).topologicalClosure = ⊤ := by
  intro F Ω _ _ _ _ _ A v hA φ hφ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  rw [eq_top_iff]
  rintro g -
  set S := (Subgroup.zpowers φ ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A)).topologicalClosure
    with hS
  have hS' : IsClosed (S : Set (Dec (F := F) A)) := Subgroup.isClosed_topologicalClosure _
  obtain ⟨s, hs, hs'⟩ := hS'.isCompact.inter_iInter_nonempty
    (fun b : IntCl F Ω => {s : Dec (F := F) A | A.valuation (g.1 b - s.1 b) < 1})
    (fun b => (isClosed_setOf_apply (F := F) (b : Ω)
      (fun t => A.valuation (g.1 b - t) < 1)).preimage continuous_subtype_val)
    (fun X => by
      obtain ⟨i, hi⟩ := exists_pow_cong hA g.2 X
      refine ⟨φ ^ i, Subgroup.le_topologicalClosure _
        (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers _) i)), ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro b hb
      have h1 := (frob_pow_cong hφ i).2 b (valuation_le_one_intCl A b)
      rw [pow_zero, pow_one] at h1
      exact cong_trans (hi b hb) (cong_symm h1))
  have h2 : (s⁻¹ * g).1 ∈ Ine (F := F) A := mem_Ine_of_integral (s⁻¹ * g).2 fun b => by
    rw [← valuation_apply_lt_one_iff s.2, map_sub, Subgroup.coe_mul, Subgroup.coe_inv,
      AlgEquiv.mul_apply, mul_inv_apply]
    exact Set.mem_iInter.1 hs' b
  have h3 := S.mul_mem hs (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right
    (Subgroup.mem_subgroupOf.2 h2)))
  rwa [mul_inv_cancel_left] at h3

theorem exists_degMod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) → (Subgroup.zpowers φ ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A)).topologicalClosure = ⊤) → ∀ M : ℕ, 0 < M → ∃ d : Dec (F := F) A →* Multiplicative (ZMod M), IsOpen (d.ker : Set (Dec (F := F) A)) ∧ (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → d σ = 1) ∧ ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) → d φ = Multiplicative.ofAdd 1 := by
  intro F Ω _ _ _ _ _ A v hA hd M hM
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero M := ⟨hM.ne'⟩
  have hq := one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, normV v ^ M = n + 1 := ⟨_, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hM.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  have hnv : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    have h1 : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    have h2 : ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA _).1 (by simpa using h)
    have h3 := v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h1 M hM) h2
    rw [← Nat.cast_pow, hn] at h3
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hζ1 : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hn0 hζ.pow_eq_one).le
  let θ : Dec (F := F) A →* (ZMod n)ˣ := (hζ.autToPow F).comp (Dec (F := F) A).subtype
  have hθ : ∀ (g : Dec (F := F) A) (k : ℕ), (θ g : ZMod n) = k ↔ g.1 ζ = ζ ^ k := fun g k => by
    have hu : IsPrimitiveRoot (hζ.isUnit hn0).unit n := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    rw [← hζ.autToPow_spec F g.1]
    change (θ g : ZMod n) = k ↔ ζ ^ (θ g : ZMod n).val = _
    conv_lhs => rw [← ZMod.natCast_zmod_val (θ g : ZMod n)]
    rw [ZMod.natCast_eq_natCast_iff]
    generalize (θ g : ZMod n).val = m
    conv_lhs => rw [hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
    simp
  have hθ' : ∀ (g : Dec (F := F) A) (k : ℕ), A.valuation (g.1 ζ - ζ ^ k) < 1 → (θ g : ZMod n) = k :=
    fun g k h => (hθ g k).2 (eq_of_pow_eq_one A hnv (by rw [← map_pow, hζ.pow_eq_one, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h)
  have hI : ∀ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A → θ σ = 1 := fun σ hσ =>
    Units.ext (by simpa using hθ' σ 1 (by simpa using hσ.2 ζ hζ1))
  have hF : ∀ φ : Dec (F := F) A, IsFrob A (normV v) φ.1 → (θ φ : ZMod n) = (normV v : ℕ) :=
    fun φ hφ => hθ' φ _ (hφ.2 ζ hζ1)
  have ho : IsOpen (θ.ker : Set (Dec (F := F) A)) := by
    have e : (θ.ker : Set (Dec (F := F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ζ = ζ} := by
      ext g
      have := hθ g 1
      rw [pow_one, Nat.cast_one] at this
      exact Units.ext_iff.trans this
    rw [e]
    exact (isOpen_setOf_apply (F := F) ζ (fun t => t = ζ)).preimage continuous_subtype_val
  obtain ⟨φ₁, hφ₀⟩ := exists_isFrob hA
  let φ₀ : Dec (F := F) A := ⟨φ₁, hφ₀.1⟩
  have h3 : θ φ₀ ^ M = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hF φ₀ hφ₀, ← Nat.cast_pow, hn]; simp)
  let ψ : Multiplicative (ZMod M) →* (ZMod n)ˣ :=
    MonoidHom.mk' (fun s => θ φ₀ ^ s.toAdd.val) fun s t => by
      rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ h3]
  have hψ1 : ψ (Multiplicative.ofAdd 1) = θ φ₀ := by
    change θ φ₀ ^ (1 : ZMod M).val = _
    rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ h3, pow_one]
  have hψ : Function.Injective ψ := (injective_iff_map_eq_one ψ).2 fun s hs => by
    have h1 : ((θ φ₀ ^ s.toAdd.val : (ZMod n)ˣ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      rw [Nat.cast_one]; exact congrArg Units.val hs
    rw [Units.val_pow_eq_pow_val, hF φ₀ hφ₀, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h1
    have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
    have h4 := pow_lt_pow_right₀ hq (ZMod.val_lt s.toAdd)
    have h5 := Nat.eq_zero_of_dvd_of_lt h2 (by
      have := Nat.one_le_pow s.toAdd.val (normV v) (by omega)
      omega)
    have h6 : s.toAdd.val = 0 := by
      by_contra h
      have := one_lt_pow₀ hq h
      omega
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h6)
  have hr : ∀ g, θ g ∈ ψ.range := by
    have h4 : ⊤ ≤ ψ.range.comap θ := by
      rw [← hd φ₀ hφ₀]
      refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 ⟨_, hψ1⟩)
        fun σ hσ => ⟨1, by rw [map_one, hI σ hσ]⟩) (Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono (fun σ hσ => ⟨1, by rw [map_one, hσ]⟩) ho))
    exact fun g => h4 (Subgroup.mem_top g)
  let d := (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp (θ.codRestrict _ hr)
  have hdψ : ∀ g, ψ (d g) = θ g := fun g => MonoidHom.apply_ofInjective_symm hψ _
  refine ⟨d, Subgroup.isOpen_mono (fun σ hσ => hψ ?_) ho, fun σ hσ => hψ ?_, fun φ hφ => hψ ?_⟩
  · rw [hdψ, map_one, hσ]
  · rw [hdψ, map_one, hI σ hσ]
  · rw [hdψ, hψ1]
    exact Units.ext ((hF φ hφ).trans (hF φ₀ hφ₀).symm)

theorem exists_openNormal_le {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {K : Subgroup Γ} {U : Subgroup K}
    (hU : IsOpen (U : Set K)) :
    ∃ H : Subgroup Γ, H.Normal ∧ IsOpen (H : Set Γ) ∧ ∀ σ : K, σ.1 ∈ H → σ ∈ U := by
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : Γ) ∈ V := by
    have : (1 : K) ∈ (U : Set K) := U.one_mem
    rw [← hVU] at this
    exact this
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨H.toSubgroup, H.isNormal', H.isOpen, fun σ hσ => ?_⟩
  have h2 : σ ∈ (U : Set K) := by
    rw [← hVU]
    exact hH hσ
  exact h2

theorem exists_coprime_pow_of_wild {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {H : Subgroup (G F Ω)} (hn : H.Normal)
    (ho : IsOpen (H : Set (G F Ω))) {σ : G F Ω} (hσ : σ ∈ Wild F A) :
    ∃ m : ℕ, m.Coprime l ∧ σ ^ m ∈ H := by
  have hlp : l.Prime := Fact.out
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have := Subgroup.quotient_finite_of_isOpen _ ho
  obtain ⟨d, hd, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := H)) σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' l hlp.ne_one
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hlp).2 hm).symm,
    GlobalTheory.mem_of_wild_of_pow_mem_open_normal F Ω A v hA H hn ho _ (l ^ a)
      (fun h => hl (v.isPrime.mem_of_pow_mem a (by simpa using h))) (pow_mem hσ m) ?_⟩
  rwa [← pow_mul, mul_comm]

theorem wild_mem_proKer {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {σ : Ine (F := F) A} (hσ : σ.1 ∈ Wild F A) :
    σ ∈ proKer l (Ine (F := F) A) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  rw [mem_proKer]
  rintro U hn ho ⟨n, hU⟩
  obtain ⟨H, hH, hHo, hHU⟩ := exists_openNormal_le ho
  obtain ⟨m, hm, h⟩ := exists_coprime_pow_of_wild hA hl hH hHo hσ
  have h1 : (QuotientGroup.mk σ : _ ⧸ U) ^ m = 1 := (QuotientGroup.eq_one_iff _).2 (hHU (σ ^ m) h)
  have h2 : (QuotientGroup.mk σ : _ ⧸ U) ^ l ^ n = 1 :=
    (QuotientGroup.eq_one_iff _).2 (hU ▸ U.pow_index_mem σ)
  exact (QuotientGroup.eq_one_iff _).1 ((pow_eq_one_iff_of_coprime (hm.pow_right n)).1 ⟨h1, h2⟩)

theorem continuous_toZModPow {l : ℕ} [Fact l.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) := by
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ?_
  rw [ContinuousAt, map_zero, nhds_discrete (ZMod (l ^ n)), Filter.tendsto_pure]
  have hl : (0 : ℝ) < (l : ℝ) ^ (-n : ℤ) :=
    zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow] at hx
  exact hx

theorem eq_one_iff_mem_ineKer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ t : Ine (F := F) A →* Multiplicative ℤ_[l], Continuous t → Function.Surjective t → ∀ σ : Ine (F := F) A, t σ = 1 ↔ (σ : G F Ω) ∈ ineKer F A l := by
  intro F Ω _ _ _ _ _ l _ A v hA hl t ht hs σ
  let θ : ∀ n, Ine (F := F) A →* Multiplicative (ZMod (l ^ n)) := fun n =>
    (AddMonoidHom.toMultiplicative (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom).comp t
  have hθ : ∀ n τ, θ n τ = 1 ↔ PadicInt.toZModPow n (t τ).toAdd = 0 := fun n τ => Iff.rfl
  have ho : ∀ n, IsOpen ((θ n).ker : Set (Ine (F := F) A)) := fun n =>
    (isOpen_discrete {0}).preimage ((continuous_toZModPow n).comp (continuous_toAdd.comp ht))
  have hsur : ∀ n, Function.Surjective (θ n) := fun n x => by
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) x.toAdd
    obtain ⟨τ, hτ⟩ := hs (Multiplicative.ofAdd y)
    exact ⟨τ, by simp [θ, hτ, hy]⟩
  have hidx : ∀ n, (θ n).ker.index = l ^ n := fun n => by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (hsur n), Subgroup.card_top]
    simp
  rw [coe_mem_ineKer]
  refine ⟨fun h => mem_proKer.2 ?_, fun h => Multiplicative.toAdd.injective
    (PadicInt.ext_of_toZModPow.mp fun n => ?_)⟩
  · rintro U hn hU ⟨n, hUn⟩
    obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt F Ω v A hA
    set g : Ine (F := F) A := ⟨γ, hγ.1⟩
    have hall : ∀ τ, τ ∈ Subgroup.zpowers g ⊔ (U ⊓ (θ n).ker) := fun τ =>
      GlobalTheory.TameCharUnique.mem_of_tameGen hγ _ (Subgroup.isClosed_of_isOpen _
        (Subgroup.isOpen_mono le_sup_right (hU.inter (ho n))))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (fun w hw => Subgroup.mem_sup_right <| Subgroup.mem_inf.2
          ⟨mem_proKer.1 (wild_mem_proKer hA hl hw) U hn hU ⟨n, hUn⟩,
            mem_proKer.1 (wild_mem_proKer hA hl hw) _ inferInstance (ho n) ⟨n, hidx n⟩⟩) τ
    have hgen : ∀ x, x ∈ Subgroup.zpowers (θ n g) := fun x => by
      obtain ⟨τ, rfl⟩ := hsur n x
      obtain ⟨_, ⟨k, rfl⟩, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hall τ)
      exact ⟨k, by rw [map_mul, map_zpow, hw.2, mul_one]⟩
    have hord : orderOf (θ n g) = l ^ n := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hgen]; simp
    obtain ⟨_, ⟨k, rfl⟩, w, hw, e⟩ := Subgroup.mem_sup_of_normal_right.1 (hall σ)
    have h1 : θ n σ = 1 := by rw [hθ, h]; simp
    rw [← e, map_mul, map_zpow, hw.2, mul_one, ← orderOf_dvd_iff_zpow_eq_one, hord] at h1
    obtain ⟨j, rfl⟩ := h1
    rw [← e]
    refine U.mul_mem ?_ hw.1
    dsimp only
    rw [zpow_mul, zpow_natCast, ← hUn]
    exact zpow_mem (U.pow_index_mem g) j
  · simpa using (hθ n σ).1 (mem_proKer.1 h _ inferInstance (ho n) ⟨n, hidx n⟩)

theorem exists_coprime_pow_of_mem_proKer {I C : Type} [Group I] [TopologicalSpace I]
    [IsTopologicalGroup I] [CommGroup C] [Finite C] {l : ℕ} [Fact l.Prime] (θ : I →* C)
    (ho : IsOpen (θ.ker : Set I)) {σ : I} (hσ : σ ∈ proKer l I) :
    ∃ m : ℕ, m.Coprime l ∧ θ σ ^ m = 1 := by
  have hlp : l.Prime := Fact.out
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := C)).ne' l hlp.ne_one
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hlp).2 hm).symm, ?_⟩
  refine mem_proKer.1 hσ ((powMonoidHom m).comp θ).ker inferInstance
    (Subgroup.isOpen_mono (fun τ hτ => ?_) ho) ?_
  · simp [MonoidHom.mem_ker.1 hτ]
  · rw [Subgroup.index_ker]
    refine IsPGroup.iff_card.1 ?_
    rintro ⟨_, τ, rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change (θ τ ^ m) ^ l ^ a = 1
    rw [← pow_mul, mul_comm, ← e, pow_card_eq_one']

theorem exists_coprime_pow_of_mem_ineKer {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {H : Subgroup (G F Ω)} (hn : H.Normal)
    (ho : IsOpen (H : Set (G F Ω))) {σ : G F Ω} (hσ : σ ∈ ineKer F A l) :
    ∃ m : ℕ, m.Coprime l ∧ σ ^ m ∈ H := by
  have := compactSpace_Ine (E := F) A
  obtain ⟨σ, hσ, rfl⟩ := hσ
  have : ((Wild F A).subgroupOf (Ine (F := F) A)).Normal :=
    ⟨fun w hw g => conj_mem_Wild (Ine_le_Dec A g.2) hw⟩
  let W := (Wild F A).subgroupOf (Ine (F := F) A) ⊔ H.subgroupOf (Ine (F := F) A)
  have hW : IsOpen (W : Set (Ine (F := F) A)) :=
    Subgroup.isOpen_mono le_sup_right (ho.preimage continuous_subtype_val)
  have := Subgroup.quotient_finite_of_isOpen _ hW
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt F Ω v A hA
  set g : Ine (F := F) A := ⟨γ, hγ.1⟩
  have : IsCyclic (Ine (F := F) A ⧸ W) := ⟨QuotientGroup.mk g, fun x => by
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
    exact GlobalTheory.TameCharUnique.mem_of_tameGen hγ
      ((Subgroup.zpowers (QuotientGroup.mk g)).comap (QuotientGroup.mk' W))
      (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (fun w hw => ⟨0, by
        simpa using ((QuotientGroup.eq_one_iff w).2 hw).symm⟩) hW))
      (Subgroup.mem_zpowers _) (fun w hw => ⟨0, by
        simpa using ((QuotientGroup.eq_one_iff (N := W) w).2 (Subgroup.mem_sup_left hw)).symm⟩) τ⟩
  let : CommGroup (Ine (F := F) A ⧸ W) := IsCyclic.commGroup
  obtain ⟨m, hm, h⟩ := exists_coprime_pow_of_mem_proKer (QuotientGroup.mk' W)
    (by rwa [QuotientGroup.ker_mk']) hσ
  have h1 : σ ^ m ∈ W := (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨w, hw, u, hu, e⟩ := Subgroup.mem_sup_of_normal_right.1 h1
  obtain ⟨m', hm', h'⟩ := exists_coprime_pow_of_wild hA hl hn ho hw
  refine ⟨m * m', Nat.Coprime.mul_left hm hm', (QuotientGroup.eq_one_iff _).1 ?_⟩
  have e' : (σ : G F Ω) ^ m = w * u := (congrArg Subtype.val e).symm
  rw [Subgroup.coe_subtype, pow_mul, e', QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff (N := H) (u : G F Ω)).2 hu, mul_one]
  exact (QuotientGroup.eq_one_iff _).2 h'

theorem index_coprime : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ U : Subgroup (ineKer F A l), U.Normal → IsOpen (U : Set (ineKer F A l)) → U.index.Coprime l := by
  intro F Ω _ _ _ _ _ l _ A v hA hl U hn hU
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨H, hH, hHo, hHU⟩ := exists_openNormal_le hU
  have := Subgroup.quotient_finite_of_isOpen _ hHo
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : U.FiniteIndex := Subgroup.finiteIndex_of_le (H := H.subgroupOf _) fun σ hσ => hHU σ hσ
  refine ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => ?_).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ineKer F A l ⧸ U) l h
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hm, h⟩ := exists_coprime_pow_of_mem_ineKer hA hl hH hHo σ.2
  have h1 : (QuotientGroup.mk σ : _ ⧸ U) ^ m = 1 := (QuotientGroup.eq_one_iff _).2 (hHU (σ ^ m) h)
  rw [← orderOf_dvd_iff_pow_eq_one, hx] at h1
  exact (Fact.out : l.Prime).ne_one (Nat.Coprime.eq_one_of_dvd hm.symm h1)

theorem kummer_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (a : Fˣ) (g σ : G F Ω) (hσ : cycZ F Ω l σ = 1) :
    kummer l a (g * σ * g⁻¹) = (cycZ F Ω l g : ℤ_[l]ˣ) * kummer l a σ := by
  have h0 := kummer_mul l a g g⁻¹
  rw [mul_inv_cancel, kummer_one] at h0
  rw [mul_assoc, kummer_mul, kummer_mul, hσ, Units.val_one, one_mul, mul_add, add_left_comm, ← h0,
    add_zero]

theorem mem_ineKer_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (σ : G F Ω) :
    σ ∈ ineKer F A l ↔ σ ∈ Ine (F := F) A ∧ kummer l (unifUnit v) σ = 0 := by
  obtain ⟨tc, ts⟩ := isTameChar_tameL hA hl
  have hk := eq_one_iff_mem_ineKer F Ω l A v hA hl _ tc ts
  exact ⟨fun h => ⟨ineKer_le_Ine A l h,
      congrArg Multiplicative.toAdd ((hk ⟨σ, ineKer_le_Ine A l h⟩).2 h)⟩,
      fun h => (hk ⟨σ, h.1⟩).1 (congrArg Multiplicative.ofAdd h.2)⟩

theorem tame_rel {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {φ γ : G F Ω} (hφ : IsFrob A (normV v) φ) (hγ : γ ∈ Ine (F := F) A) :
    (γ ^ normV v)⁻¹ * (φ * γ * φ⁻¹) ∈ ineKer F A l := by
  obtain ⟨tc, ts⟩ := isTameChar_tameL hA hl
  have h1 : φ * γ * φ⁻¹ ∈ Ine (F := F) A := conj_mem_Ine hφ.1 hγ
  have h2 : tameL hA hl (((⟨γ, hγ⟩ : Ine (F := F) A) ^ normV v)⁻¹ * ⟨_, h1⟩) = 1 := by
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one]
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_pow, tameL, toAdd_kummerChar, toAdd_kummerChar]
    dsimp only
    rw [kummer_conj _ _ _ (cycZ_of_mem_Ine hA hl hγ), cycZ_of_isFrob hl hA hφ, nsmul_eq_mul]
  have h3 := (eq_one_iff_mem_ineKer F Ω l A v hA hl _ tc ts _).1 h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using h3

theorem exists_hom {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {φ γ : Dec (F := F) A} (hφ : IsFrob A (normV v) (φ : G F Ω))
    (hγ : IsProGen F A l (γ : G F Ω)) {H : Type} [Group H] [Finite H] {a c : H} {k : ℕ}
    (hc : c ^ l ^ k = 1) (hac : a * c * a⁻¹ = c ^ normV v) :
    ∃ f : Dec (F := F) A →* H, IsOpen (f.ker : Set (Dec (F := F) A)) ∧
      (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ ineKer F A l → f σ = 1) ∧ f φ = a ∧ f γ = c := by
  have hlp : l.Prime := Fact.out
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨tc, ts⟩ := isTameChar_tameL hA hl
  have hg := isProGen_iff_isUnit F Ω l A _ tc ts (eq_one_iff_mem_ineKer F Ω l A v hA hl _ tc ts)
  have hd := closure_frob_sup_Ine F Ω A v hA
  have hJ := mem_ineKer_iff hA hl
  have hN : 0 < l ^ k := pow_pos hlp.pos k
  have : NeZero (l ^ k) := ⟨hN.ne'⟩
  obtain ⟨u, hu⟩ := (hg ⟨γ.1, hγ.1⟩).1 hγ
  change _ = kummer l (unifUnit v) γ.1 at hu
  let κ : Dec (F := F) A → ZMod (l ^ k) := fun g =>
    PadicInt.toZModPow k ((↑u⁻¹ : ℤ_[l]) * kummer l (unifUnit v) g.1)
  let χ : Dec (F := F) A →* (ZMod (l ^ k))ˣ := (cycMod F Ω l k).comp (Dec (F := F) A).subtype
  have hχ : ∀ g, (χ g : ZMod (l ^ k)) = PadicInt.toZModPow k (cycZ F Ω l g.1 : ℤ_[l]ˣ) :=
    fun _ => rfl
  have hκ : ∀ g h, κ (g * h) = κ g + (χ g : ZMod (l ^ k)) * κ h := fun g h => by
    simp only [κ, hχ, Subgroup.coe_mul, kummer_mul, ← map_mul, ← map_add]
    congr 1; ring
  have ho : IsOpen {g : Dec (F := F) A | κ g = 0} := by
    have e : {g : Dec (F := F) A | κ g = 0} = Subtype.val ⁻¹'
        {σ : G F Ω | σ (rootOf Ω l (unifUnit v : F) k) = rootOf Ω l (unifUnit v : F) k} := by
      ext g
      have := toZModPow_kummer_eq_iff l (unifUnit v) g.1 1 k
      rw [kummer_one, map_zero] at this
      simp only [κ, map_mul, Set.mem_ofPred_eq, Set.mem_preimage]
      rw [((Units.isUnit u⁻¹).map (PadicInt.toZModPow k)).mul_right_eq_zero]
      exact this
    rw [e]
    exact (isOpen_setOf_apply (F := F) _ (fun t => t = _)).preimage continuous_subtype_val
  obtain ⟨M, hM, h1, h2, h3⟩ : ∃ M : ℕ, 0 < M ∧ κ (φ ^ M) = 0 ∧ a ^ M = 1 ∧ χ φ ^ M = 1 := by
    set x := rootOf Ω l (unifUnit v : F) k
    have hs : IsOpen ((MulAction.stabilizer (G F Ω) x : Subgroup (G F Ω)) : Set (G F Ω)) :=
      isOpen_setOf_apply (F := F) x (fun t => t = x)
    have := Subgroup.quotient_finite_of_isOpen _ hs
    obtain ⟨m, hm, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := MulAction.stabilizer (G F Ω) x)) φ.1
    refine ⟨m * (orderOf a * orderOf (χ φ)), Nat.mul_pos hm (Nat.mul_pos (orderOf_pos _)
      (orderOf_pos _)), ?_, ?_, ?_⟩
    · have := (toZModPow_kummer_eq_iff l (unifUnit v) _ 1 k).2
        (pow_mem h (orderOf a * orderOf (χ φ)))
      rw [kummer_one, map_zero, ← pow_mul] at this
      simp only [κ, map_mul, Subgroup.coe_pow, this, mul_zero]
    · exact orderOf_dvd_iff_pow_eq_one.1 ((dvd_mul_right _ _).mul_left _)
    · exact orderOf_dvd_iff_pow_eq_one.1 ((dvd_mul_left _ _).mul_left _)
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨d, hdo, hdI, hdφ⟩ := exists_degMod F Ω A v hA hd M hM
  have hdχ : ∀ g, χ g = χ φ ^ (d g).toAdd.val := by
    have hp : ∀ s t : ZMod M, χ φ ^ (s + t).val = χ φ ^ s.val * χ φ ^ t.val := fun s t => by
      rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ h3]
    let ψ : Multiplicative (ZMod M) →* (ZMod (l ^ k))ˣ :=
      MonoidHom.mk' (fun s => χ φ ^ s.toAdd.val) fun s t => hp _ _
    have c1 : Continuous d := by
      refine continuous_of_continuousAt_one d ?_
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod M)), Filter.tendsto_pure]
      exact hdo.mem_nhds d.ker.one_mem
    have c2 : IsClosed ((χ.eqLocus (ψ.comp d) : Subgroup _) : Set (Dec (F := F) A)) := by
      have e : ((χ.eqLocus (ψ.comp d) : Subgroup _) : Set (Dec (F := F) A)) =
          {g | (χ g : ZMod (l ^ k)) = (ψ (d g) : ZMod (l ^ k))} := Set.ext fun g => Units.ext_iff
      rw [e]
      exact isClosed_eq ((continuous_cycMod l k).comp continuous_subtype_val)
        ((continuous_of_discreteTopology (f := fun s => (ψ s : ZMod (l ^ k)))).comp c1)
    have h4 : ⊤ ≤ χ.eqLocus (ψ.comp d) := by
      rw [← hd φ hφ]
      refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 ?_)
        fun σ hσ => ?_) c2
      · change χ φ = χ φ ^ (d φ).toAdd.val
        rw [hdφ φ hφ, toAdd_ofAdd, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ h3, pow_one]
      · change χ σ = ψ (d σ)
        rw [hdI σ hσ, map_one]
        exact Units.ext (by rw [hχ, cycZ_of_mem_Ine hA hl (σ := σ.1) hσ]; simp)
    exact fun g => h4 (Subgroup.mem_top g)
  obtain ⟨f, hf1, hf2⟩ := exists_hom_of_cocycle _ H (l ^ k) M (normV v) hN hM κ χ d φ a c hκ (hdφ φ hφ)
    (by rw [hχ, cycZ_of_isFrob hl hA hφ, map_natCast]) h1
    (fun g hg => by rw [hdχ g, hg]; simp) hc h2 hac
  refine ⟨f, Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, fun σ hσ => ?_, hf1, ?_⟩
  · have h0 : κ 1 = 0 := by simp [κ]
    filter_upwards [hdo.mem_nhds d.ker.one_mem, ho.mem_nhds h0] with g h5 h6
    change f g = 1
    rw [hf2 g h5, h6]; simp
  · rw [hf2 σ (hdI σ ((hJ _).1 hσ).1)]
    simp [κ, ((hJ _).1 hσ).2]
  · rw [hf2 γ (hdI γ hγ.1)]
    simp only [κ, ← hu, Units.inv_mul, map_one]
    rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ hc, pow_one]

theorem _root_.GlobalTheory.Published.TameQuotient_holds : GlobalTheory.Published.TameQuotient := by
  intro F Ω _ _ _ _ _ l _ A v hA hl
  have hlp : l.Prime := Fact.out
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨tc, ts⟩ := isTameChar_tameL hA hl
  have hk := eq_one_iff_mem_ineKer F Ω l A v hA hl _ tc ts
  have hg := isProGen_iff_isUnit F Ω l A _ tc ts hk
  have hd := closure_frob_sup_Ine F Ω A v hA
  have hJ := mem_ineKer_iff hA hl
  refine ⟨?_, ⟨fun σ hσ g => ?_⟩, index_coprime F Ω l A v hA hl, ⟨_, tc, ts, hk⟩, ?_, fun φ γ hφ hγ => ⟨?_, ?_, ?_⟩⟩
  · have e : (ineKer F A l : Set (G F Ω)) = (Ine (F := F) A : Set (G F Ω)) ∩
        {σ | kummer l (unifUnit v) σ = 0} := Set.ext hJ
    rw [e]
    exact (isClosed_Ine A).inter (isClosed_eq (continuous_kummer l _) continuous_const)
  · rw [Subgroup.mem_subgroupOf, hJ] at hσ ⊢
    refine ⟨conj_mem_Ine g.2 hσ.1, ?_⟩
    change kummer l _ (g.1 * σ.1 * g.1⁻¹) = 0
    rw [kummer_conj _ _ _ (cycZ_of_mem_Ine hA hl hσ.1), hσ.2, mul_zero]
  · obtain ⟨γ, hγ⟩ := ts (Multiplicative.ofAdd 1)
    exact ⟨γ, (hg γ).2 (by rw [hγ]; simp)⟩
  · rw [eq_top_iff, ← hd φ hφ]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ fun σ hσ => ?_)
      (Subgroup.isClosed_topologicalClosure _)
    · refine le_trans ?_ (Subgroup.le_topologicalClosure _)
      exact le_sup_of_le_left ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp)))
    · set S := (Subgroup.closure {φ, γ} ⊔
        (ineKer F A l).subgroupOf (Dec (F := F) A)).topologicalClosure with hS
      have hS' : IsClosed (S : Set (Dec (F := F) A)) := Subgroup.isClosed_topologicalClosure _
      have hc : IsClosed ((S.map (Dec (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
        (isClosed_Dec A).isClosedEmbedding_subtypeVal.isClosedMap _ hS'
      have h1 : Subgroup.zpowers (γ : G F Ω) ⊔ ineKer F A l ≤ S.map (Dec (F := F) A).subtype := by
        refine sup_le (Subgroup.zpowers_le.2 ⟨γ, Subgroup.le_topologicalClosure _
          (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))), rfl⟩) fun τ hτ => ?_
        exact ⟨⟨τ, Ine_le_Dec A (ineKer_le_Ine A l hτ)⟩,
          Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hτ), rfl⟩
      obtain ⟨τ, hτ, e⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
      exact (Subtype.ext e : τ = σ) ▸ hτ
  · simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using tame_rel hA hl hφ hγ.1
  · rintro H _ _ a c ⟨k, hc⟩ hac
    exact exists_hom hA hl hφ hγ hc hac

noncomputable section Symbol

set_option linter.unusedSectionVars false

theorem cup_product_class_eq_zero_iff {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
    [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
    [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho' : Representation R Γ M') (rhoP : Representation R Γ P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (x : Z1 rho) (y : Z1 rho') :
    cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 ↔
      ∃ c : Γ → P, Continuous c ∧
        ∀ g h, rhoP g (c h) - c (g * h) + c g = b (x.1 g) (rho' g (y.1 h)) := by
  change (Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc x y) : H2 rhoP) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, fun g k => congrFun h (g, k)⟩,
    fun ⟨c, hc, h⟩ => ⟨c, hc, funext fun p => h p.1 p.2⟩⟩

theorem eq_zero_of_cup_product_injective {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* Rˣ) (hχ : ∀ g, χ g = 1) (hc)
    (hinj : Function.Injective (cupH1H1TwistedDual χ (Representation.trivial R Γ R) (MonoidHom.id _) hc).flip)
    (a : Z1 (Representation.trivial R Γ R))
    (h : ∀ y : Z1 (Representation.trivial R Γ R), ∃ c : Γ → R, Continuous c ∧
      ∀ g k, c k - c (g * k) + c g = y.1 g * a.1 k) (g : Γ) : a.1 g = 0 := by
  let a' : Z1 ((Representation.trivial R Γ R).comp (MonoidHom.id _)) := ⟨a.1, a.2⟩
  have ha : (Submodule.Quotient.mk a' :
      H1 ((Representation.trivial R Γ R).comp (MonoidHom.id _))) = 0 := by
    refine hinj ?_
    rw [map_zero]
    refine LinearMap.ext fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hc, h5⟩ := h ⟨fun g => y.1 g 1, (continuous_of_discreteTopology
      (f := fun s : TDual R R => s 1)).comp y.2.1, fun g k => by
        dsimp only; rw [y.2.2 g k]; simp [hχ g]⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext ?_⟩)
    rintro ⟨g, k⟩
    change (χ g : R) * c k - c (g * k) + c g = y.1 g (a.1 k)
    rw [hχ, Units.val_one, one_mul, h5, mul_comm, ← smul_eq_mul]
    exact (LinearMap.map_smul (show R →ₗ[R] R from y.1 g) _ 1).symm.trans
      (by rw [smul_eq_mul, mul_one]; rfl)
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 ha)
  exact (hm g).trans (sub_self m)

theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (a + b), Nat.choose_succ_succ' b, ih]
    simp only [Nat.choose_one_right]
    ring

theorem choose_two_mod (N a : ℕ) : (((a % (2 * N)).choose 2 : ℕ) : ZMod N) = (a.choose 2 : ℕ) := by
  have h : ∀ j : ℕ, (((2 * N * j).choose 2 : ℕ) : ZMod N) = 0 := fun j => by
    rw [show 2 * N * j = N * j + N * j by ring, choose_two_add, Nat.choose_two_right, ← two_mul,
      Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd, mul_assoc N, mul_assoc N]
    simp
  conv_rhs => rw [← Nat.mod_add_div a (2 * N), choose_two_add]
  push_cast
  rw [h]
  simp

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}

theorem cycMod_eq_one (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hq : normV v ≡ 1 [MOD l ^ n]) (g : Dec (F := F) A) : cycMod F Ω l n g.1 = 1 := by
  obtain ⟨φ, hφ⟩ := exists_isFrob hA
  have h4 : ⊤ ≤ ((cycMod F Ω l n).comp (Dec (F := F) A).subtype).ker := by
    rw [← closure_frob_sup_Ine F Ω A v hA ⟨φ, hφ.1⟩ hφ]
    refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 (Units.ext ?_))
      fun σ hσ => Units.ext ?_) ?_
    · change PadicInt.toZModPow n ((cycZ F Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = 1
      rw [cycZ_of_isFrob hl hA hφ, map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 hq, Nat.cast_one]
    · change PadicInt.toZModPow n ((cycZ F Ω l σ.1 : ℤ_[l]ˣ) : ℤ_[l]) = 1
      rw [cycZ_of_mem_Ine hA hl (σ := σ.1) hσ]; simp
    · have e : (((cycMod F Ω l n).comp (Dec (F := F) A).subtype).ker : Set (Dec (F := F) A)) =
          {g | ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) = 1} :=
        Set.ext fun g => Units.ext_iff
      rw [e]
      exact isClosed_eq ((continuous_cycMod l n).comp continuous_subtype_val) continuous_const
  exact h4 (Subgroup.mem_top g)

omit [IsAlgClosure F Ω] [Fact l.Prime] in

def homOf (z : Z1 (trivDec F A l n)) : Dec (F := F) A →* Multiplicative (ZMod (l ^ n)) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => congrArg _ (z.2.2 g h)

omit [IsAlgClosure F Ω] in
theorem eq_zero_of_mem_ineKer (z : Z1 (trivDec F A l n)) {σ : Dec (F := F) A}
    (hσ : σ.1 ∈ ineKer F A l) : z.1 σ = 0 := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨m, hm, h⟩ := exists_coprime_pow_of_mem_proKer
    ((homOf z).comp (Subgroup.inclusion (Ine_le_Dec A)))
    ((isOpen_discrete {0}).preimage (z.2.1.comp (continuous_subtype_val.subtype_mk _)))
    (coe_mem_ineKer.1 (show ((⟨σ.1, ineKer_le_Ine A l hσ⟩ : Ine (F := F) A) : G F Ω) ∈ _ from hσ))
  have h1 : (m : ZMod (l ^ n)) * z.1 σ = 0 := by
    rw [← nsmul_eq_mul]; exact congrArg Multiplicative.toAdd h
  exact (((ZMod.isUnit_iff_coprime _ _).2 (hm.pow_right n)).mul_right_eq_zero).1 h1

theorem dvd_of_isProGen (z : Z1 (trivDec F A l n)) {γ σ : Dec (F := F) A}
    (hγ : IsProGen F A l γ.1) (hσ : σ.1 ∈ Ine (F := F) A) : z.1 γ ∣ z.1 σ := by
  let S : Subgroup (Dec (F := F) A) :=
    (AddSubgroup.toSubgroup (Ideal.span {z.1 γ}).toAddSubgroup).comap (homOf z)
  have hS : IsClosed (S : Set (Dec (F := F) A)) :=
    (isClosed_discrete (Ideal.span {z.1 γ} : Set (ZMod (l ^ n)))).preimage z.2.1
  have hc : IsClosed ((S.map (Dec (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
    (isClosed_Dec A).isClosedEmbedding_subtypeVal.isClosedMap _ hS
  have h1 : Subgroup.zpowers (γ : G F Ω) ⊔ ineKer F A l ≤ S.map (Dec (F := F) A).subtype := by
    refine sup_le (Subgroup.zpowers_le.2 ⟨γ, Ideal.mem_span_singleton_self _, rfl⟩) fun τ hτ => ?_
    refine ⟨⟨τ, Ine_le_Dec A (ineKer_le_Ine A l hτ)⟩, ?_, rfl⟩
    change z.1 _ ∈ Ideal.span {z.1 γ}
    rw [eq_zero_of_mem_ineKer z (σ := ⟨τ, _⟩) hτ]
    exact zero_mem _
  obtain ⟨τ, hτ, e⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
  obtain rfl : τ = σ := Subtype.ext e
  exact Ideal.mem_span_singleton.1 hτ

omit [Fact l.Prime] in
theorem eq_zero_of_unram (hA : IsPlaceOver A v) (z : Z1 (trivDec F A l n))
    (hz : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → z.1 g = 0) {φ : Dec (F := F) A}
    (hφ : IsFrob A (normV v) φ.1) (h : z.1 φ = 0) : z = 0 := by
  have h4 : ⊤ ≤ (homOf z).ker := by
    rw [← closure_frob_sup_Ine F Ω A v hA φ hφ]
    exact Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 h)
      fun σ hσ => hz σ hσ) ((isClosed_discrete {0}).preimage z.2.1)
  exact Subtype.ext (funext fun g => h4 (Subgroup.mem_top g))

theorem exists_unram (hA : IsPlaceOver A v) : ∃ χ : Z1 (trivDec F A l n),
    (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → χ.1 g = 0) ∧
    (∀ φ : Dec (F := F) A, IsFrob A (normV v) φ.1 → χ.1 φ = 1) ∧
    ∃ c : Dec (F := F) A → ZMod (l ^ n), Continuous c ∧
      ∀ g h, c h - c (g * h) + c g = χ.1 g * χ.1 h := by
  have hN : 0 < 2 * l ^ n := Nat.mul_pos two_pos (pow_pos (Fact.out : l.Prime).pos n)
  have : NeZero (2 * l ^ n) := ⟨hN.ne'⟩
  obtain ⟨d, ho, hI, hφ⟩ := exists_degMod F Ω A v hA (closure_frob_sup_Ine F Ω A v hA) _ hN
  have c1 : Continuous d := by
    refine continuous_of_continuousAt_one d ?_
    rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod (2 * l ^ n))), Filter.tendsto_pure]
    exact ho.mem_nhds d.ker.one_mem
  let p := ZMod.castHom (dvd_mul_left (l ^ n) 2) (ZMod (l ^ n))
  refine ⟨⟨fun g => p (d g).toAdd, (continuous_of_discreteTopology
      (f := fun s : Multiplicative (ZMod (2 * l ^ n)) => p s.toAdd)).comp c1, fun g h => by simp⟩,
    fun g hg => by simp [hI g hg], fun φ h => by simp [hφ φ h],
    fun g => -(((d g).toAdd.val.choose 2 : ℕ) : ZMod (l ^ n)), (continuous_of_discreteTopology
      (f := fun s : Multiplicative (ZMod (2 * l ^ n)) =>
        -((s.toAdd.val.choose 2 : ℕ) : ZMod (l ^ n)))).comp c1, fun g h => ?_⟩
  simp only [map_mul, toAdd_mul, ZMod.val_add, choose_two_mod, choose_two_add, p,
    ZMod.castHom_apply, ← ZMod.natCast_val]
  push_cast
  ring

omit [IsAlgClosure F Ω] in
theorem valuation_le_of_unif (hA : IsPlaceOver A v) {a b : 𝓞 F} (ha : a ∈ v.asIdeal)
    (hb : b ∈ v.asIdeal) (hb' : b ∉ v.asIdeal ^ 2) :
    A.valuation (algebraMap F Ω a) ≤ A.valuation (algebraMap F Ω b) := by
  have hint : ∀ c : 𝓞 F, A.valuation (algebraMap F Ω c) ≤ 1 := fun c =>
    (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A
      (c.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom))
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
  have h1 : ¬ I ≤ v.asIdeal := fun h => hb' (by
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.1 h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (hI ▸ Ideal.mul_mem_mul ha hs)
  have h2 : A.valuation (algebraMap F Ω s) = 1 :=
    le_antisymm (hint s) (not_lt.1 fun h => hs' ((hA s).1 h))
  have h3 := congrArg (fun c : 𝓞 F => A.valuation (algebraMap F Ω c)) ht
  simp only [map_mul, RingOfIntegers.coe_eq_algebraMap] at h3 h2 hint ⊢
  rw [h2, mul_one] at h3
  rw [h3]
  exact mul_le_of_le_one_right' (hint t)

theorem pow_val_inj {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) {a b : ℕ} :
    ζ ^ a = ζ ^ b ↔ (a : ZMod (l ^ n)) = b := by
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [ZMod.natCast_eq_natCast_iff, hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
  simp

omit [IsAlgClosure F Ω] in
theorem IsUnifRoot.ne_zero {x : Ω} (hx : IsUnifRoot v (l ^ n) x) : x ≠ 0 := by
  obtain ⟨ϖ, -, h2, h⟩ := hx
  rintro rfl
  rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero), eq_comm, map_eq_zero,
    RingOfIntegers.coe_eq_zero_iff] at h
  exact h2 (h ▸ zero_mem _)

theorem exponent_unique {ζ x y : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hx : x ≠ 0)
    {a b : ZMod (l ^ n)} (ha : y = ζ ^ a.val * x) (hb : y = ζ ^ b.val * x) : a = b := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  simpa using (pow_val_inj hζ).1 (mul_right_cancel₀ hx (ha.symm.trans hb))

theorem exists_kummer {ζ x : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hx : IsUnifRoot v (l ^ n) x) :
    ∃ κ : Z1 (muDec F A l n), ∀ g : Dec (F := F) A, g.1 x = ζ ^ (κ.1 g).val * x := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have h0 := hx.ne_zero
  obtain ⟨ϖ, -, -, h⟩ := hx
  have hex : ∀ y : Ω, ∃ c : ZMod (l ^ n), y ^ l ^ n = x ^ l ^ n → y = ζ ^ c.val * x := fun y => by
    by_cases hy : y ^ l ^ n = x ^ l ^ n
    · obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one (ξ := y / x)
        (by rw [div_pow, hy, div_self (pow_ne_zero _ h0)])
      exact ⟨i, fun _ => by rw [ZMod.val_cast_of_lt hi, e, div_mul_cancel₀ _ h0]⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose c hc using hex
  have hc' : ∀ g : G F Ω, g x = ζ ^ (c (g x)).val * x := fun g =>
    hc _ (by rw [← map_pow, h, AlgEquiv.commutes])
  refine ⟨⟨fun g => c (g.1 x), continuous_def.2 fun s _ => (isOpen_setOf_apply (F := F) x
    (fun t => c t ∈ s)).preimage continuous_subtype_val, fun g k => ?_⟩, fun g => hc' g.1⟩
  refine exponent_unique hζ h0 (hc' _) ?_
  have hg : g.1 ζ = ζ ^ (cycMod F Ω l n g.1 : ZMod (l ^ n)).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω g.1) ζ hζ.pow_eq_one
  rw [Subgroup.coe_mul, AlgEquiv.mul_apply]
  conv_lhs => rw [hc' k.1, map_mul, map_pow, hg, hc' g.1, ← pow_mul, ← mul_assoc, ← pow_add]
  congr 1
  rw [pow_val_inj hζ]
  simp [add_comm]

theorem exists_isUnit_kummer (hA : IsPlaceOver A v) {ζ x : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (hx : IsUnifRoot v (l ^ n) x) {κ : Dec (F := F) A → ZMod (l ^ n)}
    (hκ : ∀ g : Dec (F := F) A, g.1 x = ζ ^ (κ g).val * x) :
    ∃ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A ∧ IsUnit (κ σ) := by
  have hlp : l.Prime := Fact.out
  rcases n with _ | n
  · have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, one_mem _, isUnit_of_subsingleton _⟩
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  obtain ⟨ϖ, h1, h2, h⟩ := hx
  obtain ⟨σ, hσ, hne⟩ := GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne F Ω A v hA l hlp ϖ h1 h2
    (x ^ l ^ n) (by rw [← pow_mul, ← pow_succ, h])
  refine ⟨⟨σ, hσ.1⟩, hσ, ?_⟩
  rw [← ZMod.natCast_zmod_val (κ _), ZMod.isUnit_natCast_iff_not_dvd_pow hlp n.succ_pos]
  rintro ⟨j, hj⟩
  apply hne
  rw [map_pow, hκ ⟨σ, hσ.1⟩, hj, mul_pow, ← pow_mul, mul_right_comm, ← pow_succ', pow_mul,
    hζ.pow_eq_one, one_pow, one_mul]

theorem kummer_eq_on_Ine (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {ζ x x' : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ n)) (hx : IsUnifRoot v (l ^ n) x) (hx' : IsUnifRoot v (l ^ n) x')
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) {c c' : ZMod (l ^ n)} (h : σ x = ζ ^ c.val * x)
    (h' : σ x' = ζ ^ c'.val * x') : c = c' := by
  have hN : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN⟩
  have h0 := hx.ne_zero
  have h0' := hx'.ne_zero
  obtain ⟨a, a1, a2, ha⟩ := hx
  obtain ⟨b, b1, b2, hb⟩ := hx'
  have hv : A.valuation x = A.valuation x' := by
    refine (pow_left_inj₀ zero_le zero_le hN).1 ?_
    rw [← map_pow, ← map_pow, ha, hb]
    exact le_antisymm (valuation_le_of_unif hA a1 b1 b2) (valuation_le_of_unif hA b1 a1 a2)
  have hu : A.valuation (x / x') = 1 := by rw [map_div₀, hv, div_self (by simpa using h0')]
  have h1 := hσ.2 _ hu.le
  have hz : ζ ≠ 0 := hζ.ne_zero hN
  have e : σ (x / x') - x / x' = (ζ ^ c.val - ζ ^ c'.val) * (x / x') / ζ ^ c'.val := by
    rw [map_div₀, h, h']; field_simp
  rw [e, map_div₀, map_mul, hu, map_pow, valuation_eq_one_of_pow_eq_one A hN hζ.pow_eq_one,
    one_pow, div_one, mul_one] at h1
  have hp : ∀ k : ℕ, (ζ ^ k) ^ l ^ n = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  simpa using (pow_val_inj hζ).1
    (eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl hA n) (hp _) (hp _) h1)

omit [IsAlgClosure F Ω] in
theorem mk_eq_zero_of_cochain (f : Z2 (muDec F A l n)) (c : Dec (F := F) A → ZMod (l ^ n))
    (hc : Continuous c) (h : ∀ g k, muDec F A l n g (c k) - c (g * k) + c g = f.1 (g, k)) :
    (Submodule.Quotient.mk f : H2 (muDec F A l n)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext fun p => h p.1 p.2⟩)

section Trivial

variable (hμ : ∀ g : Dec (F := F) A, cycMod F Ω l n g.1 = 1)
include hμ

omit [IsAlgClosure F Ω] in
theorem muDec_apply (g : Dec (F := F) A) (s : ZMod (l ^ n)) : muDec F A l n g s = s := by
  simp [hμ g]

omit [IsAlgClosure F Ω] in

def toMu : Z1 (trivDec F A l n) ≃ₗ[ZMod (l ^ n)] Z1 (muDec F A l n) :=
  LinearEquiv.ofEq _ _ (Submodule.ext fun f => by
    simp only [mem_Z1_iff_cocycle, muDec_apply hμ, Representation.trivial_apply])

omit [IsAlgClosure F Ω] in
theorem cup_toMu_eq_zero (B : Z1 (trivDec F A l n) × Z1 (trivDec F A l n))
    (c : Dec (F := F) A → ZMod (l ^ n)) (hc : Continuous c)
    (h : ∀ g k, c k - c (g * k) + c g = B.1.1 g * B.2.1 k) :
    cupMu F A l n (Submodule.Quotient.mk B.1) (Submodule.Quotient.mk (toMu hμ B.2)) = 0 :=
  mk_eq_zero_of_cochain _ c hc fun g k => by
    rw [muDec_apply hμ, h, cupCocycleZ1Z1_apply, muDec_apply hμ]; rfl

omit [IsAlgClosure F Ω] in
theorem cup_anticomm (a b : Z1 (trivDec F A l n)) :
    cupMu F A l n (Submodule.Quotient.mk a) (Submodule.Quotient.mk (toMu hμ b)) =
      -cupMu F A l n (Submodule.Quotient.mk b) (Submodule.Quotient.mk (toMu hμ a)) := by
  rw [eq_neg_iff_add_eq_zero]
  refine ((Submodule.Quotient.mk_add _).symm.trans
    (mk_eq_zero_of_cochain _ (fun g => -(a.1 g * b.1 g)) (a.2.1.mul b.2.1).neg fun g k => ?_))
  have ha : a.1 (g * k) = a.1 g + a.1 k := a.2.2 g k
  have hb : b.1 (g * k) = b.1 g + b.1 k := b.2.2 g k
  rw [muDec_apply hμ, ha, hb, Submodule.coe_add, Pi.add_apply, cupCocycleZ1Z1_apply, cupCocycleZ1Z1_apply,
    muDec_apply hμ, muDec_apply hμ]
  change _ = a.1 g * b.1 k + b.1 g * a.1 k
  ring

def cupT : Z1 (trivDec F A l n) →ₗ[ZMod (l ^ n)] Z1 (trivDec F A l n) →ₗ[ZMod (l ^ n)]
    H2 (muDec F A l n) :=
  (cupMu F A l n).compl₁₂ (Submodule.mkQ _) ((Submodule.mkQ _).comp (toMu hμ).toLinearMap)

theorem cupT_apply (a b : Z1 (trivDec F A l n)) : cupT hμ a b =
    cupMu F A l n (Submodule.Quotient.mk a) (Submodule.Quotient.mk (toMu hμ b)) := rfl

theorem cupT_unram (hA : IsPlaceOver A v) {a b : Z1 (trivDec F A l n)}
    (ha : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → a.1 g = 0)
    (hb : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → b.1 g = 0) : cupT hμ a b = 0 := by
  obtain ⟨χ, h1, h2, c, hc, h3⟩ := exists_unram (l := l) (n := n) hA
  obtain ⟨φ, hφ⟩ := exists_isFrob hA
  have key : ∀ a : Z1 (trivDec F A l n), (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → a.1 g = 0) →
      a = a.1 ⟨φ, hφ.1⟩ • χ := fun a ha =>
    sub_eq_zero.1 (eq_zero_of_unram hA _ (fun g hg => by simp [ha g hg, h1 g hg])
      (φ := ⟨φ, hφ.1⟩) hφ (by simp [h2 ⟨φ, hφ.1⟩ hφ]))
  have h0 : cupT hμ χ χ = 0 := cup_toMu_eq_zero hμ (χ, χ) c hc h3
  rw [key a ha, key b hb]
  simp [h0]

theorem cupT_eq (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {κ : Z1 (trivDec F A l n)} (hκ : ∃ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A ∧ IsUnit (κ.1 σ))
    (z : Z1 (trivDec F A l n)) : ∃ b : ZMod (l ^ n),
      (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → z.1 g = b * κ.1 g) ∧
      ∀ y : Z1 (trivDec F A l n), (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → y.1 g = 0) →
        cupT hμ z y = -(b • cupT hμ y κ) := by
  obtain ⟨γ₁, hγ⟩ := (GlobalTheory.Published.TameQuotient_holds F Ω l A v hA hl).2.2.2.2.1
  let γ : Dec (F := F) A := ⟨γ₁, Ine_le_Dec A hγ.1⟩
  obtain ⟨σ, hσ, hu⟩ := hκ
  obtain ⟨b, hb⟩ := (isUnit_of_dvd_unit (dvd_of_isProGen κ (γ := γ) hγ hσ) hu).dvd (a := z.1 γ)
  have h1 : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → (z - b • κ).1 g = 0 := fun g hg => by
    refine zero_dvd_iff.1 ?_
    have := dvd_of_isProGen (z - b • κ) (γ := γ) hγ hg
    rwa [show (z - b • κ).1 γ = 0 by simp [hb, mul_comm]] at this
  refine ⟨b, fun g hg => by simpa [sub_eq_zero] using h1 g hg, fun y hy => ?_⟩
  have h2 := cupT_unram hμ hA h1 hy
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero, map_smul, LinearMap.smul_apply] at h2
  rw [h2, cupT_apply, cup_anticomm, ← cupT_apply, smul_neg]

end Trivial

theorem tame_symbol_formula (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hq : normV v ≡ 1 [MOD l ^ n]) {ζ x : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (hx : IsUnifRoot v (l ^ n) x) {γ : Dec (F := F) A} {c : ZMod (l ^ n)}
    (hγ : (γ : G F Ω) ∈ Ine (F := F) A) (hc : (γ : G F Ω) x = ζ ^ c.val * x) :
    (IsProGen F A l (γ : G F Ω) → IsUnit c) ∧
      ∀ inv : H2 (muDec F A l n) →ₗ[ZMod (l ^ n)] ZMod (l ^ n), IsInvariantMap A v ζ inv →
      ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
      ∀ (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)),
        (Submodule.Quotient.mk y : H1 (muDec F A l n)) ∈
          H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) →
        c * inv (cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y)) =
          -(z.1 γ * y.1 φ) := by
  have hμ := cycMod_eq_one hA hl hq
  obtain ⟨κ, hκ⟩ := exists_kummer (A := A) hζ hx
  obtain ⟨κ, rfl⟩ := (toMu hμ).surjective κ
  have hu := exists_isUnit_kummer hA hζ hx hκ
  obtain rfl : c = κ.1 γ := exponent_unique hζ hx.ne_zero hc (hκ γ)
  refine ⟨fun h => ?_, fun inv hinv φ hφ z y hy => ?_⟩
  · obtain ⟨σ, hσ, hu⟩ := hu
    exact isUnit_of_dvd_unit (dvd_of_isProGen κ h hσ) hu
  obtain ⟨y, rfl⟩ := (toMu hμ).surjective y
  have hy' : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → y.1 g = 0 := fun g hg => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
    exact (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (muDec_apply hμ g m))
  obtain ⟨b, h1, h2⟩ := cupT_eq hμ hA hl hu z
  rw [← cupT_apply, h2 y hy', map_neg, map_smul, cupT_apply, hinv x hx _ hκ y hy' φ hφ, h1 γ hγ]
  change _ = -(b * κ.1 γ * y.1 φ)
  rw [smul_eq_mul]
  ring

theorem exists_isInvariantMap (hD : LocalTateDuality) (hA : IsPlaceOver A v)
    (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (hq : normV v ≡ 1 [MOD l ^ n]) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    ∃ inv : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n),
      IsInvariantMap A v ζ inv.toLinearMap := by
  have hN : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have := Module.subsingleton (ZMod (l ^ 0)) (H2 (muDec F A l 0))
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ _ _ => Subsingleton.elim _ _⟩
  have hμ := cycMod_eq_one hA hl hq
  obtain ⟨⟨e⟩, -, -, ⟨hinj, -⟩, -⟩ := hD F Ω l n (ZMod (l ^ n)) A (trivDec F A l n) v hn hA
    continuous_snd
  obtain ⟨x₀, hx₀⟩ := exists_isUnifRoot (Ω := Ω) v (Nat.pos_of_ne_zero hN)
  obtain ⟨κ₀, hκ₀⟩ := exists_kummer (A := A) hζ hx₀
  obtain ⟨κ₀, rfl⟩ := (toMu hμ).surjective κ₀
  have hu := exists_isUnit_kummer hA hζ hx₀ hκ₀
  obtain ⟨χ₀, h1, h2, -⟩ := exists_unram (l := l) (n := n) hA
  have hw : IsUnit (e (cupT hμ χ₀ κ₀)) := by
    refine isUnit_iff_mem_nonZeroDivisors_of_finite.2 (mem_nonZeroDivisors_iff_right.2 fun r hr => ?_)
    have hr' : r • cupT hμ χ₀ κ₀ = 0 := e.injective (by rw [map_smul, map_zero]; exact hr)
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have h6 := eq_zero_of_cup_product_injective _ hμ _ hinj (r • χ₀) (fun y => by
      obtain ⟨b, -, h3⟩ := cupT_eq hμ hA hl hu y
      have h4 := h3 (r • χ₀) fun g hg => by simp [h1 g hg]
      rw [map_smul (cupT hμ), LinearMap.smul_apply, hr', smul_zero, neg_zero, cupT_apply, cupMu,
        cup_product_class_eq_zero_iff] at h4
      obtain ⟨c, hc, h5⟩ := h4
      refine ⟨c, hc, fun g k => ?_⟩
      have h7 := h5 g k
      rw [muDec_apply hμ, muDec_apply hμ] at h7
      exact h7) ⟨φ, hφ.1⟩
    simpa [h2 ⟨φ, hφ.1⟩ hφ] using h6
  obtain ⟨w, hw⟩ := hw
  refine ⟨e.trans (LinearEquiv.smulOfUnit w⁻¹), fun x hx κ hκ χ hχ φ hφ => ?_⟩
  obtain ⟨κ, rfl⟩ := (toMu hμ).surjective κ
  have h3 := cupT_unram hμ hA hχ (b := κ - κ₀) fun g hg => sub_eq_zero.2
    (kummer_eq_on_Ine hA hl hζ hx hx₀ hg (hκ g) (hκ₀ g))
  have h4 : χ = χ.1 φ • χ₀ := sub_eq_zero.1 (eq_zero_of_unram hA _
    (fun g hg => by simp [hχ g hg, h1 g hg]) hφ (by simp [h2 φ hφ]))
  rw [map_sub, sub_eq_zero] at h3
  rw [← cupT_apply, h3]
  conv_lhs => rw [h4, map_smul, LinearMap.smul_apply, map_smul]
  change χ.1 φ * ((↑w⁻¹ : ZMod (l ^ n)) * e (cupT hμ χ₀ κ₀)) = _
  rw [← hw, Units.inv_mul, mul_one]

theorem _root_.GlobalTheory.Published.TameSymbol_of_duality (hD : LocalTateDuality) : GlobalTheory.Published.TameSymbol :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hA hl hq _ hζ =>
    ⟨exists_isInvariantMap hD hA hl hq hζ, fun _ hx _ _ hγ hc =>
      tame_symbol_formula hA hl hq hζ hx hγ hc⟩

theorem _root_.GlobalTheory.Published.TameLocal_of_duality (hD : LocalTateDuality) : GlobalTheory.Published.TameLocal :=
  ⟨GlobalTheory.Published.TameQuotient_holds, GlobalTheory.Published.TameSymbol_of_duality hD⟩

end Symbol

end GlobalTheory.TameQuot
