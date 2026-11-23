import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace Formalism.BasicNotions.Examples₂.Tame

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)

def rat (σ : G E Ω) : Ωˣ →* Ωˣ := (Units.map (σ : Ω →* Ω)) / MonoidHom.id _

theorem rat_val (σ : G E Ω) (y : Ωˣ) : ((rat σ y : Ωˣ) : Ω) = σ y / y := by
  simp [rat]

theorem rat_mul (σ τ : G E Ω) (y : Ωˣ) : rat (σ * τ) y = rat σ (rat τ y) * rat τ y * rat σ y := by
  ext
  have := y.ne_zero
  have h2 : σ (y : Ω) ≠ 0 := (map_ne_zero σ).mpr this
  have h3 : τ (y : Ω) ≠ 0 := (map_ne_zero τ).mpr this
  simp only [Units.val_mul, rat_val, map_div₀, AlgEquiv.mul_apply]
  field_simp

theorem rat_princ {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (u : Ωˣ) (hu : A.valuation u = 1) :
    rat σ u ∈ A.principalUnitGroup := by
  rw [ValuationSubring.mem_principalUnitGroup_iff, rat_val, div_sub_one u.ne_zero, map_div₀, hu, div_one]
  exact hσ.2 _ hu.le

theorem rat_not_lt {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) (hy : y ≠ 0) (N : ℕ) (hN : 0 < N)
    (hfix : (σ ^ N) y = y) : ¬ A.valuation (σ y) < A.valuation y := by
  intro h
  have step : ∀ j : ℕ, A.valuation ((σ ^ j) (σ y)) < A.valuation ((σ ^ j) y) := fun j => by
    have h1 : A.valuation (σ y / y) < 1 := by
      rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr (by simpa using hy))]; exact h
    have h2 := (valuation_apply_lt_one_iff (pow_mem hσ j) (σ y / y)).mpr h1
    rwa [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr
      ((Valuation.ne_zero_iff _).mpr ((map_ne_zero (σ ^ j)).mpr hy)))] at h2
  have all : ∀ j : ℕ, A.valuation ((σ ^ (j + 1)) y) < A.valuation y := fun j => by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      refine lt_trans ?_ ih
      rw [pow_succ σ (j + 1), AlgEquiv.mul_apply]
      exact step (j + 1)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have := all j
  rw [hfix] at this
  exact lt_irrefl _ this

theorem val_eq {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) (hy : y ≠ 0) (N : ℕ) (hN : 0 < N)
    (hfix : ∀ z : ℤ, ∀ x, x = (σ ^ z) y → (σ ^ N) x = x) : A.valuation (σ y) = A.valuation y := by
  have h1 := rat_not_lt A hσ y hy N hN (hfix 0 y (by simp))
  have h2 := rat_not_lt A (inv_mem hσ) (σ y) ((map_ne_zero σ).mpr hy) N hN (by
    have := hfix 1 (σ y) (by simp)
    rw [inv_pow]
    conv_lhs => rw [← this]
    show ((σ ^ N)⁻¹ * σ ^ N) (σ y) = σ y
    rw [inv_mul_cancel]; rfl)
  have h3 : (σ⁻¹ : G E Ω) (σ y) = y := by
    show (σ⁻¹ * σ) y = y
    rw [inv_mul_cancel]; rfl
  rw [h3] at h2
  exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)

theorem val_nat_eq_one (p N : ℕ) (hp : A.valuation (p : Ω) < 1) (hc : N.Coprime p) :
    A.valuation (N : Ω) = 1 := by
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hN : A.valuation (N : Ω) ≤ 1 := by exact_mod_cast hle N
  refine le_antisymm hN (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have e : (a : Ω) * N + (b : Ω) * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * N + (b : Ω) * p) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hlt
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hp
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem exists_unif (L : Type) [Field L] [NumberField L] (i : L →+* Ω) (p : ℕ) (hp0 : p ≠ 0)
    (hp : A.valuation (p : Ω) < 1) :
    ∃ π : L, π ≠ 0 ∧ ∀ y : L, y ≠ 0 → ∃ n : ℤ, A.valuation (i (y / π ^ n)) = 1 := by
  have hint : ∀ x : 𝓞 L, i (x : L) ∈ A := fun x => by
    have h1 : IsIntegral ℤ (i (x : L)) := (RingOfIntegers.isIntegral_coe x).map i.toIntAlgHom
    have h2 : IsIntegral A (i (x : L)) := h1.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h2
    rw [← hy]; exact y.2
  let j : 𝓞 L →+* A := (i.comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap j
  have hP : ∀ x : 𝓞 L, x ∈ P ↔ A.valuation (i (x : L)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (j x)
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, fun hb => by
    have : (p : 𝓞 L) ∈ P := (hP _).mpr (by simpa using hp)
    rw [hb, Ideal.mem_bot] at this
    exact hp0 (by exact_mod_cast this)⟩
  have hunit : ∀ x : 𝓞 L, x ∉ P → A.valuation (i (x : L)) = 1 := fun x hx =>
    le_antisymm ((A.valuation_le_one_iff _).mpr (hint x)) (not_lt.mp fun h => hx ((hP x).mpr h))
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, hπ0, fun y hy => ⟨-WithZero.log (w.valuation L y), ?_⟩⟩
  have hv : w.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have h1 : w.valuation L (y / π ^ (-WithZero.log (w.valuation L y))) = 1 := by
    rw [map_div₀, map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  generalize y / π ^ (-WithZero.log (w.valuation L y)) = z at h1
  obtain ⟨a, b, hab⟩ := w.exists_primeCompl_mul_eq_of_integer z h1.le
  have hb : A.valuation (i ((b : 𝓞 L) : L)) = 1 := hunit _ b.2
  have ha : a ∉ P := by
    intro ha
    have h2 : w.valuation L (algebraMap (𝓞 L) L a) < 1 := (w.valuation_lt_one_iff_mem _).mpr ha
    have h3 : w.valuation L (algebraMap (𝓞 L) L b) = 1 := (w.valuation_eq_one_iff_notMem).mpr b.2
    rw [← hab, map_mul, h1, h3, mul_one] at h2
    exact lt_irrefl _ h2
  have := congrArg (fun t => A.valuation (i t)) hab
  simp only [map_mul] at this
  have hb' : A.valuation (i (algebraMap (𝓞 L) L b)) = 1 := hb
  rw [hb', mul_one] at this
  exact this.trans (hunit a ha)

variable [IsAlgClosure E Ω]

def Near {A' : Type} [Group A'] (φ : G E Ω →* A') (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → (∀ κ ∈ φ.ker, κ y = y) → A.valuation (σ y / y - 1) < 1

omit [NumberField E] [IsAlgClosure E Ω] in
theorem Near.congr {A' : Type} [Group A'] {φ : G E Ω →* A'} {σ σ' : G E Ω} (e : φ σ = φ σ')
    (h : Near A φ σ) : Near A φ σ' := fun y hy hf => by
  have : σ' y = σ y := by
    have h1 := hf (σ⁻¹ * σ') (by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel])
    have h2 : σ' = σ * (σ⁻¹ * σ') := by group
    rw [h2, AlgEquiv.mul_apply, h1]
  rw [this]; exact h y hy hf

theorem exists_gen (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) (A' : Type) [Group A'] [Finite A']
    (φ : G E Ω →* A') (ho : IsOpen (φ.ker : Set (G E Ω))) :
    ∃ γ ∈ Ine (F := E) A, ∀ σ ∈ Ine (F := E) A, ∃ n : ℤ, Near A φ ((γ ^ n)⁻¹ * σ) := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let L := IntermediateField.fixedField φ.ker
  have hL : L.fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, Subgroup.isClosed_of_isOpen _ ho⟩
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hL]; exact ho)
  have : NumberField L := NumberField.of_module_finite E L
  have hmem : ∀ x, x ∈ L ↔ ∀ κ ∈ φ.ker, κ x = x := fun x => IntermediateField.mem_fixedField_iff _ x
  have hstab : ∀ (σ : G E Ω), ∀ x ∈ L, σ x ∈ L := fun σ x hx => (hmem _).mpr fun κ hκ => by
    have h1 : σ⁻¹ * κ * σ ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hκ ⊢; simp [hκ]
    have h2 := (hmem x).mp hx _ h1
    have : (κ * σ) x = (σ * (σ⁻¹ * κ * σ)) x := by congr 1; group
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply σ, h2] at this
    exact this
  set N := Nat.card A' with hNdef
  have hN : 0 < N := Nat.card_pos
  have hpow : ∀ (σ : G E Ω), ∀ x ∈ L, (σ ^ N) x = x := fun σ x hx =>
    (hmem x).mp hx _ (by rw [MonoidHom.mem_ker, map_pow, hNdef, pow_card_eq_one'])
  obtain ⟨π, hπ0, hπ⟩ := exists_unif A L (algebraMap L Ω) p hp0 hp
  let u : Ωˣ := Units.mk0 (π : Ω) (by simpa using hπ0)
  have hu : ∀ σ ∈ Ine (F := E) A, rat σ u ∈ A.unitGroup := fun σ hσ => by
    rw [ValuationSubring.mem_unitGroup_iff, rat_val, map_div₀,
      val_eq A (Ine_le_Dec A hσ) _ u.ne_zero N hN (fun z x hx => hpow σ x (hx ▸ hstab _ _ π.2)),
      div_self (by simp)]
  have hker : ∀ x : A.unitGroup, A.unitGroupToResidueFieldUnits x = 1 ↔ (x : Ωˣ) ∈ A.principalUnitGroup :=
    fun x => by rw [← MonoidHom.mem_ker, A.ker_unitGroupToResidueFieldUnits]; rfl
  let θ : Ine (F := E) A →* (IsLocalRing.ResidueField A)ˣ := MonoidHom.mk'
    (fun σ => A.unitGroupToResidueFieldUnits ⟨rat σ.1 u, hu _ σ.2⟩) (fun σ τ => by
      have h1 := rat_princ A σ.2 (rat τ.1 u) ((A.mem_unitGroup_iff _).mp (hu _ τ.2))
      have h2 := (hker ⟨_, A.principal_units_le_units h1⟩).mpr h1
      have h3 : (⟨rat (σ * τ).1 u, hu _ (σ * τ).2⟩ : A.unitGroup) =
          ⟨_, A.principal_units_le_units h1⟩ * ⟨rat τ.1 u, hu _ τ.2⟩ * ⟨rat σ.1 u, hu _ σ.2⟩ :=
        Subtype.ext (rat_mul σ.1 τ.1 u)
      rw [h3, map_mul, map_mul, h2, one_mul, mul_comm])
  have near : ∀ σ : Ine (F := E) A, θ σ = 1 → ∀ y ∈ L, y ≠ 0 →
      A.valuation (σ.1 y / y - 1) < 1 := fun σ hσ y hy hy0 => by
    have h1 : rat σ.1 u ∈ A.principalUnitGroup := (hker _).mp hσ
    obtain ⟨n, hn⟩ := hπ ⟨y, hy⟩ (fun h => hy0 (congrArg Subtype.val h))
    let yu : Ωˣ := Units.mk0 y hy0
    have h2 := rat_princ A σ.2 (yu / u ^ n) (by simpa [yu, u] using hn)
    have h3 : rat σ.1 yu ∈ A.principalUnitGroup := by
      have := mul_mem h2 (zpow_mem h1 n)
      rwa [← map_zpow, ← map_mul, div_mul_cancel] at this
    rw [ValuationSubring.mem_principalUnitGroup_iff, rat_val] at h3
    exact h3
  have hfix : ∀ τ : Ine (F := E) A, τ.1 (u : Ω) = u → θ τ = 1 := fun τ hτ => by
    refine (hker _).mpr ?_
    have : rat τ.1 u = 1 := by
      ext
      rw [rat_val, hτ, div_self u.ne_zero]; rfl
    show rat τ.1 u ∈ _
    rw [this]; exact one_mem _
  clear_value θ
  have hθN : ∀ σ : Ine (F := E) A, θ σ ^ N = 1 := fun σ => by
    rw [← map_pow]
    apply hfix
    rw [SubgroupClass.coe_pow]
    exact hpow σ.1 _ π.2
  have : NeZero N := ⟨hN.ne'⟩
  have hle : θ.range ≤ rootsOfUnity N (IsLocalRing.ResidueField A) := by
    rintro _ ⟨σ, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (hθN σ)
  have : Finite θ.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have : IsCyclic θ.range := isCyclic_of_injective_ringHom
    ((Units.coeHom _).comp θ.range.subtype) (Units.val_injective.comp Subtype.val_injective)
  obtain ⟨⟨g, γ, rfl⟩, hg⟩ := IsCyclic.exists_generator (α := θ.range)
  refine ⟨γ.1, γ.2, fun σ hσ => ?_⟩
  obtain ⟨n, hn⟩ := hg ⟨θ ⟨σ, hσ⟩, ⟨_, rfl⟩⟩
  have hn' : θ γ ^ n = θ ⟨σ, hσ⟩ := congrArg Subtype.val hn
  refine ⟨n, fun y hy hf => ?_⟩
  have h := near ((γ ^ n)⁻¹ * ⟨σ, hσ⟩) (by rw [map_mul, map_inv, map_zpow, hn', inv_mul_cancel]) y
    ((hmem y).mpr hf) hy
  rw [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow] at h
  exact h

structure Test (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Type 1 where
  A' : Type
  [grp : Group A']
  [fin : Finite A']
  φ : G E Ω →* A'
  ho : IsOpen (φ.ker : Set (G E Ω))

attribute [instance] Test.grp Test.fin

def Test.prod {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (s t : Test E Ω) : Test E Ω where
  A' := s.A' × t.A'
  φ := s.φ.prod t.φ
  ho := by rw [MonoidHom.ker_prod]; exact s.ho.inter t.ho

omit [NumberField E] [IsAlgClosure E Ω] in
theorem near_left {s t : Test E Ω} {σ : G E Ω} (h : Near A (s.prod t).φ σ) : Near A s.φ σ :=
  fun y hy hf => h y hy fun κ hκ => hf κ (congrArg Prod.fst hκ)

omit [NumberField E] [IsAlgClosure E Ω] in
theorem near_right {s t : Test E Ω} {σ : G E Ω} (h : Near A (s.prod t).φ σ) : Near A t.φ σ :=
  fun y hy hf => h y hy fun κ hκ => hf κ (congrArg Prod.snd hκ)

omit [NumberField E] [IsAlgClosure E Ω] in
theorem closed_of_sat (t : Test E Ω) (X : Set (G E Ω))
    (h : ∀ σ σ', t.φ σ = t.φ σ' → σ ∈ X → σ' ∈ X) : IsClosed X := by
  let _ : TopologicalSpace t.A' := ⊥
  have : DiscreteTopology t.A' := ⟨rfl⟩
  have hc : Continuous t.φ := by
    refine continuous_of_continuousAt_one t.φ ?_
    rw [ContinuousAt, map_one, nhds_discrete t.A', Filter.tendsto_pure]
    exact t.ho.mem_nhds (one_mem t.φ.ker)
  have : X = t.φ ⁻¹' (t.φ '' X) :=
    Set.Subset.antisymm (Set.subset_preimage_image _ _) fun σ' ⟨σ, hσ, e⟩ => h σ σ' e hσ
  rw [this]
  exact (isClosed_discrete _).preimage hc

theorem exists_test (y : Ω) : ∃ t : Test E Ω, ∀ κ ∈ t.φ.ker, κ y = y := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let L := FiniteGaloisIntermediateField.adjoin E ({y} : Set Ω)
  have hk := IntermediateField.restrictNormalHom_ker L.toIntermediateField
  refine ⟨{ A' := L ≃ₐ[E] L, φ := AlgEquiv.restrictNormalHom L.toIntermediateField
            ho := by rw [hk]; exact L.toIntermediateField.fixingSubgroup_isOpen }, fun κ hκ => ?_⟩
  change κ ∈ (AlgEquiv.restrictNormalHom L.toIntermediateField).ker at hκ
  rw [hk, IntermediateField.mem_fixingSubgroup_iff] at hκ
  exact hκ y (FiniteGaloisIntermediateField.subset_adjoin E {y} rfl)

theorem exists_tameGen (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ γ : G E Ω, TameGenAt A γ := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have : Nonempty (Test E Ω) := ⟨(exists_test (E := E) (0 : Ω)).choose⟩
  let S : Test E Ω → Set (G E Ω) := fun t => (Ine (F := E) A : Set (G E Ω)) ∩
    {γ | ∀ σ ∈ Ine (F := E) A, ∃ n : ℤ, Near A t.φ ((γ ^ n)⁻¹ * σ)}
  have hcl : ∀ t, IsClosed (S t) := fun t => (isClosed_Ine (F := E) A).inter
    (closed_of_sat t _ fun γ γ' e h σ hσ => (h σ hσ).imp fun n hn =>
      hn.congr A (by simp only [map_mul, map_inv, map_zpow, e]))
  obtain ⟨γ, hγ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    (fun s t => ⟨s.prod t,
      fun γ h => ⟨h.1, fun σ hσ => (h.2 σ hσ).imp fun _ hn => near_left A hn⟩,
      fun γ h => ⟨h.1, fun σ hσ => (h.2 σ hσ).imp fun _ hn => near_right A hn⟩⟩)
    (fun t => exists_gen A p hp0 hp t.A' t.φ t.ho) (fun t => (hcl t).isCompact) hcl
  rw [Set.mem_iInter] at hγ
  refine ⟨γ, (hγ (Classical.arbitrary _)).1, fun σ hσ => ?_⟩
  set C := Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1})
  let U : Test E Ω → Set (G E Ω) := fun t => (C.topologicalClosure : Set (G E Ω)) ∩
    {τ | Near A t.φ (τ⁻¹ * σ)}
  have hU : ∀ t, IsClosed (U t) := fun t => C.isClosed_topologicalClosure.inter
    (closed_of_sat t _ fun τ τ' e h => Near.congr A (by simp only [map_mul, map_inv, e]) h)
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed U
    (fun s t => ⟨s.prod t, fun τ h => ⟨h.1, near_left A h.2⟩, fun τ h => ⟨h.1, near_right A h.2⟩⟩)
    (fun t => by
      obtain ⟨n, hn⟩ := (hγ t).2 σ hσ
      exact ⟨γ ^ n, C.le_topologicalClosure
        (zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) n), hn⟩)
    (fun t => (hU t).isCompact) hU
  rw [Set.mem_iInter] at hτ
  have hw : τ⁻¹ * σ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ fun y hy => by
    obtain ⟨t, ht⟩ := exists_test (E := E) y
    exact (hτ t).2 y hy ht)
  have := mul_mem (hτ (Classical.arbitrary _)).1 (C.le_topologicalClosure hw)
  rwa [mul_inv_cancel_left] at this

end Formalism.BasicNotions.Examples₂.Tame
