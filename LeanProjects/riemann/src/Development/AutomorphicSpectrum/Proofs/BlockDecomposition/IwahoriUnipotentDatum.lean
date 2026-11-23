import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlValuedDatum

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.IwGLV

namespace GlobalTheory.CompanionTheory.IwUnit

section Abstract

variable {G : Type*} [Group G]

theorem fac_unique {A B C P : Subgroup G} (hB : B ≤ P) (hC : C ≤ P) (hAP : A ⊓ P = ⊥) (hBC : B ⊓ C = ⊥)
    {a a' b b' c c' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (hc : c ∈ C)
    (hc' : c' ∈ C) (h : a * b * c = a' * b' * c') : a = a' ∧ b = b' ∧ c = c' := by
  have e1 : a'⁻¹ * a = b' * c' * c⁻¹ * b⁻¹ := by
    have : a = a' * b' * c' * c⁻¹ * b⁻¹ := by rw [← h]; group
    rw [this]; group
  have m1 : a'⁻¹ * a ∈ A ⊓ P := ⟨A.mul_mem (A.inv_mem ha') ha, by
    rw [e1]
    exact P.mul_mem (P.mul_mem (P.mul_mem (hB hb') (hC hc')) (P.inv_mem (hC hc))) (P.inv_mem (hB hb))⟩
  rw [hAP, Subgroup.mem_bot] at m1
  have haa : a = a' := (inv_mul_eq_one.1 m1).symm
  subst haa
  have h2 : b * c = b' * c' := by simpa [mul_assoc] using h
  have e2 : b'⁻¹ * b = c' * c⁻¹ := by
    have : b = b' * c' * c⁻¹ := by rw [← h2]; group
    rw [this]; group
  have m2 : b'⁻¹ * b ∈ B ⊓ C := ⟨B.mul_mem (B.inv_mem hb') hb, by
    rw [e2]; exact C.mul_mem hc' (C.inv_mem hc)⟩
  rw [hBC, Subgroup.mem_bot] at m2
  have hbb : b = b' := (inv_mul_eq_one.1 m2).symm
  subst hbb
  exact ⟨rfl, rfl, mul_left_cancel h2⟩

theorem fac_descent (θ : G →* G) {A B C P : Subgroup G} (hB : B ≤ P) (hC : C ≤ P) (hAP : A ⊓ P = ⊥)
    (hBC : B ⊓ C = ⊥) (tA : ∀ x ∈ A, θ x ∈ A) (tB : ∀ x ∈ B, θ x ∈ B) (tC : ∀ x ∈ C, θ x ∈ C)
    {a b c : G} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (h : θ (a * b * c) = a * b * c) :
    θ a = a ∧ θ b = b ∧ θ c = c :=
  fac_unique hB hC hAP hBC (tA _ ha) ha (tB _ hb) hb (tC _ hc) hc (by rwa [map_mul, map_mul] at h)

theorem norm_subgroupOf {H S : Subgroup G} {t : H} (h : (t : G) ∈ Subgroup.normalizer (S : Set G)) :
    t ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup H) : Set H) :=
  Subgroup.mem_normalizer_iff.2 fun x => by
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.1 h x

end Abstract

section Mat

variable {L : Type} [Field L] {n : ℕ}

def tau (σ : L →+* L) (M : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  fun i j => σ (M (Fin.rev j) (Fin.rev i))

theorem antiJ_self_rev (i : Fin n) : antiJ L n i (Fin.rev i) = 1 :=
  if_pos (by have := i.2; rw [Fin.val_rev]; omega)

theorem antiJ_rev_self (i : Fin n) : antiJ L n (Fin.rev i) i = 1 :=
  if_pos (by have := i.2; rw [Fin.val_rev]; omega)

theorem antiJ_ne {i k : Fin n} (h : k ≠ Fin.rev i) : antiJ L n i k = 0 :=
  if_neg fun e => h (Fin.ext (by have := i.2; rw [Fin.val_rev]; omega))

theorem antiJ_ne' {j k : Fin n} (h : k ≠ Fin.rev j) : antiJ L n k j = 0 :=
  if_neg fun e => h (Fin.ext (by have := j.2; rw [Fin.val_rev]; omega))

theorem antiJ_mul (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (antiJ L n * M) i j = M (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [antiJ_self_rev, one_mul]
  · intro k _ hk
    rw [antiJ_ne hk, zero_mul]
  · simp

theorem mul_antiJ (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (M * antiJ L n) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · rw [antiJ_rev_self, mul_one]
  · intro k _ hk
    rw [antiJ_ne' hk, mul_zero]
  · simp

theorem antiJ_mul_self : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [antiJ_rev_self, if_pos rfl]
  · rw [antiJ_ne (fun e => h (by simpa using e.symm)), if_neg h]

theorem tau_eq (σ : L →+* L) (M : Matrix (Fin n) (Fin n) L) :
    tau σ M = antiJ L n * cT σ M * antiJ L n := by
  ext i j
  rw [mul_antiJ, antiJ_mul]
  simp [tau, cT]

theorem tau_mul (σ : L →+* L) (M N : Matrix (Fin n) (Fin n) L) :
    tau σ (M * N) = tau σ N * tau σ M := by
  ext i j
  simp only [tau, Matrix.mul_apply, map_sum, map_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

theorem tau_one (σ : L →+* L) : tau σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [tau]
  · have : ¬ Fin.rev j = Fin.rev i := fun e => h (Fin.rev_injective e).symm
    simp [tau, Matrix.one_apply, this, h]

def theta (σ : L →+* L) : GL (Fin n) L →* GL (Fin n) L where
  toFun g := ⟨tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    tau σ (g : Matrix (Fin n) (Fin n) L),
    by rw [← tau_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, tau_one],
    by rw [← tau_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tau_one]⟩
  map_one' := Units.ext (by simp [tau_one])
  map_mul' a b := Units.ext (by simp [_root_.mul_inv_rev, tau_mul])

theorem theta_val (σ : L →+* L) (g : GL (Fin n) L) :
    ((theta σ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl

theorem mem_GU_iff [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {g : GL (Fin n) L} :
    g ∈ GU σ n ↔ theta σ g = g := by
  have hJ := antiJ_mul_self (L := L) (n := n)
  have key : g ∈ GU σ n ↔ tau σ (g : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    show cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n ↔ _
    rw [tau_eq]
    constructor
    · intro h
      rw [Matrix.mul_assoc (antiJ L n * _), Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (cT σ _), h, hJ]
    · intro h
      have := congrArg (antiJ L n * ·) h
      simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.mul_one] at this
      exact this
  rw [key]
  have h1 : tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tau σ (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← tau_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, tau_one]
  have h2 : tau σ (g : Matrix (Fin n) (Fin n) L) * tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← tau_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tau_one]
  constructor
  · intro h
    apply Units.ext
    rw [theta_val]
    calc tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        = tau σ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (tau σ (g : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L)) := by rw [h, Matrix.mul_one]
      _ = (g : Matrix (Fin n) (Fin n) L) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · intro h
    have : ((theta σ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = g := by rw [h]
    rw [theta_val] at this
    rw [this] at h2
    exact h2

theorem theta_up (σ : L →+* L) {g : GL (Fin n) L} (hg : g ∈ (upSub : Subgroup (GL (Fin n) L))) :
    theta σ g ∈ (upSub : Subgroup (GL (Fin n) L)) := by
  have h := mem_upSub.1 (upSub.inv_mem hg)
  refine mem_upSub.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [theta_val]
    show σ _ = 0
    rw [h.1 _ _ (Fin.rev_lt_rev.2 hij), map_zero]
  · rw [theta_val]
    show σ _ = 1
    rw [h.2, map_one]

theorem theta_low (σ : L →+* L) {g : GL (Fin n) L} (hg : g ∈ (lowSub : Subgroup (GL (Fin n) L))) :
    theta σ g ∈ (lowSub : Subgroup (GL (Fin n) L)) := by
  have h := mem_lowSub.1 (lowSub.inv_mem hg)
  refine mem_lowSub.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [theta_val]
    show σ _ = 0
    rw [h.1 _ _ (Fin.rev_lt_rev.2 hij), map_zero]
  · rw [theta_val]
    show σ _ = 1
    rw [h.2, map_one]

theorem theta_diag (σ : L →+* L) {g : GL (Fin n) L} (hg : g ∈ (diagSub : Subgroup (GL (Fin n) L))) :
    theta σ g ∈ (diagSub : Subgroup (GL (Fin n) L)) := by
  have h := mem_diagSub.1 (diagSub.inv_mem hg)
  refine mem_diagSub.2 fun i j hij => ?_
  rw [theta_val]
  show σ _ = 0
  rw [h _ _ (fun e => hij (Fin.rev_injective e).symm), map_zero]

theorem eq_one_of_entries {g : GL (Fin n) L}
    (h1 : ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) L) i j = 0)
    (h2 : ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1) : g = 1 := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h; simp [h2]
  · simp [h1 i j h, h]

theorem low_inf_bt : (lowSub : Subgroup (GL (Fin n) L)) ⊓ btSub (id : Fin n → Fin n) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun g hg => by
    obtain ⟨h1, h2⟩ := hg
    have h1' := mem_lowSub.1 h1
    refine eq_one_of_entries (fun i j hij => ?_) h1'.2
    rcases lt_or_gt_of_ne hij with h | h
    · exact h1'.1 i j h
    · exact h2 h

theorem up_inf_bt : (upSub : Subgroup (GL (Fin n) L)) ⊓ btSub (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun g hg => by
    obtain ⟨h1, h2⟩ := hg
    have h1' := mem_upSub.1 h1
    refine eq_one_of_entries (fun i j hij => ?_) h1'.2
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual j < OrderDual.toDual i from h)
    · exact h1'.1 i j h

theorem diag_inf_up : (diagSub : Subgroup (GL (Fin n) L)) ⊓ upSub = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun g hg =>
    eq_one_of_entries (mem_diagSub.1 hg.1) (mem_upSub.1 hg.2).2

theorem diag_inf_low : (diagSub : Subgroup (GL (Fin n) L)) ⊓ lowSub = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun g hg =>
    eq_one_of_entries (mem_diagSub.1 hg.1) (mem_lowSub.1 hg.2).2

end Mat

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem continuous_sigma {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)).2 fun γ _ =>
    ⟨γ, trivial, fun x hx => ?_⟩
  rwa [Set.mem_setOf_eq, show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

theorem isClosed_GU {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsClosed ((GU σ n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
  have hc : Continuous fun g : GL (Fin n) L => cT σ (g : Matrix (Fin n) (Fin n) L) := by
    unfold cT
    exact (Units.continuous_val.matrix_map (continuous_sigma hv)).matrix_transpose
  exact isClosed_eq ((hc.matrix_mul continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem isCompact_IwU [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact ((IwU σ n : Subgroup (GU σ n)) : Set (GU σ n)) := by
  rw [Subtype.isCompact_iff]
  have : ((↑) '' ((IwU σ n : Subgroup (GU σ n)) : Set (GU σ n)) : Set (GL (Fin n) L)) =
      ((IwGL L n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) ∩
        ((GU σ n : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.1 hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, Subgroup.mem_subgroupOf.2 h1, rfl⟩
  rw [this]
  exact (isCompact_IwGL h).inter_right (isClosed_GU h.2.1)

variable {ϖ : L} {σ : L →+* L}

theorem desc_low
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : GU σ n} (hx : x ∈ IwU σ n) :
    ∃ a ∈ IwU σ n ⊓ lowSub.subgroupOf (GU σ n), ∃ b ∈ IwU σ n ⊓ diagSub.subgroupOf (GU σ n),
      ∃ c ∈ IwU σ n ⊓ upSub.subgroupOf (GU σ n), x = a * b * c := by
  obtain ⟨a, ⟨haJ, haN⟩, b, ⟨hbJ, hbT⟩, c, ⟨hcJ, hcN⟩, e⟩ := fact_low hϖ (Subgroup.mem_subgroupOf.1 hx)
  have hx' : theta σ (a * b * c) = a * b * c := by
    rw [← e]; exact mem_GU_iff.1 x.2
  obtain ⟨ta, tb, tc⟩ := fac_descent (theta σ) (C := upSub) (B := diagSub) (A := lowSub)
    (P := btSub (id : Fin n → Fin n)) inf_le_left (fun _ hg => hg.1) low_inf_bt diag_inf_up
    (fun _ => theta_low σ) (fun _ => theta_diag σ) (fun _ => theta_up σ) haN hbT hcN hx'
  exact ⟨⟨a, mem_GU_iff.2 ta⟩, ⟨haJ, haN⟩, ⟨b, mem_GU_iff.2 tb⟩, ⟨hbJ, hbT⟩, ⟨c, mem_GU_iff.2 tc⟩,
    ⟨hcJ, hcN⟩, Subtype.ext e⟩

theorem desc_up
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : GU σ n} (hx : x ∈ IwU σ n) :
    ∃ c ∈ IwU σ n ⊓ upSub.subgroupOf (GU σ n), ∃ b ∈ IwU σ n ⊓ diagSub.subgroupOf (GU σ n),
      ∃ a ∈ IwU σ n ⊓ lowSub.subgroupOf (GU σ n), x = c * b * a := by
  obtain ⟨c, ⟨hcJ, hcN⟩, b, ⟨hbJ, hbT⟩, a, ⟨haJ, haN⟩, e⟩ := fact_up hϖ (Subgroup.mem_subgroupOf.1 hx)
  have hx' : theta σ (c * b * a) = c * b * a := by
    rw [← e]; exact mem_GU_iff.1 x.2
  obtain ⟨tc, tb, ta⟩ := fac_descent (theta σ) (C := lowSub) (B := diagSub) (A := upSub)
    (P := btSub (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)) inf_le_right (fun _ hg => hg.1) up_inf_bt
    diag_inf_low (fun _ => theta_up σ) (fun _ => theta_diag σ) (fun _ => theta_low σ) hcN hbT haN hx'
  exact ⟨⟨c, mem_GU_iff.2 tc⟩, ⟨hcJ, hcN⟩, ⟨b, mem_GU_iff.2 tb⟩, ⟨hbJ, hbT⟩, ⟨a, mem_GU_iff.2 ta⟩,
    ⟨haJ, haN⟩, Subtype.ext e⟩

end Val

theorem iwahoriU : PositivityTheory.SphericalProduct.IwahoriU := by
  intro L _ _ _ ϖ σ q h n
  have hϖ := h.2.2.2.1
  have cN : IsClosed ((upSub : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := isClosed_triSub _ _
  have cNm : IsClosed ((lowSub : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) := isClosed_triSub _ _
  have cT' : IsClosed ((diagSub : Subgroup (GL (Fin n) L)) : Set (GL (Fin n) L)) :=
    (isClosed_btSub _).inter (isClosed_btSub _)
  refine ⟨{ N := upSub.subgroupOf (GU σ n), Nm := lowSub.subgroupOf (GU σ n),
            T := diagSub.subgroupOf (GU σ n), J := IwU σ n
            isOpen_J := isOpen_IwGL.preimage continuous_subtype_val
            isCompact_J := isCompact_IwU h
            isClosed_N := cN.preimage continuous_subtype_val
            isClosed_Nm := cNm.preimage continuous_subtype_val
            isClosed_alt := cT'.preimage continuous_subtype_val
            norm_N := fun t ht => norm_subgroupOf (norm_tri _ (Subgroup.mem_subgroupOf.1 ht).1)
            norm_Nm := fun t ht => norm_subgroupOf (norm_tri _ (Subgroup.mem_subgroupOf.1 ht).2)
            fact_low := fun x hx => desc_low hϖ hx
            fact_up := fun x hx => desc_up hϖ hx },
    rfl, fun g => Subgroup.mem_subgroupOf.trans mem_upSub,
    fun g => Subgroup.mem_subgroupOf.trans mem_lowSub,
    fun g => Subgroup.mem_subgroupOf.trans mem_diagSub⟩

end GlobalTheory.CompanionTheory.IwUnit
