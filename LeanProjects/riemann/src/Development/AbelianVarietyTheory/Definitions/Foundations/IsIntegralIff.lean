import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HermitianLattices

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a + b) y = hf L H a y + hf L H b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H (c • a) y = c * hf L H a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a + b) = hf L H y a + hf L H y b := by
  simp [hf, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a - b) = hf L H y a - hf L H y b := by
  simp [hf, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H y (c • a) = L.cj c * hf L H y a := by
  unfold hf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hf_symm (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x y : Fin n → E) : hf L H y x = L.cj (hf L H x y) := by
  have hH : ∀ i j, L.cj (H j i) = H i j := fun i j => congrFun (congrFun h i) j
  unfold hf
  simp only [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_single (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hf L H (Pi.single i 1) (Pi.single j 1) = H i j := by
  simp [hf, Pi.single_apply, apply_ite]

theorem eich_isom (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x u : Fin n → E) (s : E) (hxx : hf L H x x = 0) (hux : hf L H u x = 0)
    (hs : s + L.cj s = hf L H u u) (v w : Fin n → E) :
    hf L H (eich L H x u s v) (eich L H x u s w) = hf L H v w := by
  have hxu : hf L H x u = 0 := by rw [hf_symm L h u x, hux, map_zero]
  have hxw : hf L H x w = L.cj (hf L H w x) := hf_symm L h w x
  have huw : hf L H u w = L.cj (hf L H w u) := hf_symm L h w u
  simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, hf_sub_right,
    hf_smul_right, hxx, hux, hxu, hxw, huw]
  linear_combination (-(hf L H v x * L.cj (hf L H w x))) * hs

theorem eich_inv (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x u : Fin n → E) (s : E) (hxx : hf L H x x = 0) (hux : hf L H u x = 0)
    (hs : s + L.cj s = hf L H u u) (v : Fin n → E) :
    eich L H x (-u) (L.cj s) (eich L H x u s v) = v := by
  have hxu : hf L H x u = 0 := by rw [hf_symm L h u x, hux, map_zero]
  have hneg : hf L H (eich L H x u s v) (-u) = -hf L H (eich L H x u s v) u := by
    simp [hf, map_neg, Finset.sum_neg_distrib]
  have h1 : hf L H (eich L H x u s v) x = hf L H v x := by
    simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hxx, hux]
    ring
  have h2 : hf L H (eich L H x u s v) u = hf L H v u - hf L H v x * hf L H u u := by
    simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hxu]
    ring
  have e : eich L H x (-u) (L.cj s) (eich L H x u s v) = eich L H x u s v +
      hf L H (eich L H x u s v) (-u) • x - hf L H (eich L H x u s v) x • (-u + L.cj s • x) := rfl
  rw [e, hneg, h1, h2]
  funext i
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (-(hf L H v x * x i)) * hs

theorem isHermND_one (L : LocE F E) (n : ℕ) : IsHermND L (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨?_, by simp⟩
  ext i j
  show L.cj ((1 : Matrix (Fin n) (Fin n) E) j i) = (1 : Matrix (Fin n) (Fin n) E) i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

def stdLat (L : LocE F E) (n : ℕ) : Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))

private theorem cj_mem_O_of_mem_O' (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

private theorem mem_stdLat_iff_forall_mem_O (L : LocE F E) (n : ℕ) (y : Fin n → E) :
    y ∈ stdLat L n ↔ ∀ i, y i ∈ L.O := by
  unfold stdLat
  constructor
  · intro hy i
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    | zero => simp
    | add x z _ _ hx hz => exact L.O.add_mem hx hz
    | smul a x _ hx => exact L.O.mul_mem a.2 hx
  · intro h
    have hy : y = ∑ i, (⟨y i, h i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSD_std (L : LocE F E) (n : ℕ) : IsSD L (1 : Matrix (Fin n) (Fin n) E) (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : Pi.single i (v i) = v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      by_cases h : j = i <;> simp [h]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (mem_stdLat_iff_forall_mem_O L n _).mpr fun j => by by_cases h : j = i <;> simp [h]
  · rw [mem_stdLat_iff_forall_mem_O]
    constructor
    · intro hy i
      have h1 := hy (Pi.single i 1) ((mem_stdLat_iff_forall_mem_O L n _).mpr fun j => by
        by_cases h : j = i <;> simp [h])
      have h2 : hf L 1 (Pi.single i 1) y = L.cj (y i) := by
        simp [hf, Pi.single_apply, Matrix.one_apply]
      rw [h2] at h1
      simpa [L.cj_cj] using cj_mem_O_of_mem_O' L h1
    · intro hy x hx
      rw [mem_stdLat_iff_forall_mem_O] at hx
      unfold hf
      refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
      refine L.O.mul_mem (L.O.mul_mem (hx i) ?_) (cj_mem_O_of_mem_O' L (hy j))
      by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem nontrivial (L : LocE F E) : Nontrivial E := by
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

theorem not_isLat_bot (L : LocE F E) (n : ℕ) : ¬ IsLat L (⊥ : Submodule L.O (Fin (n + 1) → E)) := by
  rintro ⟨-, h⟩
  have := nontrivial L
  simp at h

theorem isSD_zero (L : LocE F E) {n : ℕ} {Λ : Submodule L.O (Fin n → E)} (h : IsSD L 0 Λ) : Λ = ⊤ := by
  exact eq_top_iff.mpr fun y _ => (h.2 y).mp fun x _ => by simp [hf]

theorem unipOn_top_bot {n : ℕ} : unipOn (E := E) (n := n) ⊤ ⊥ = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr ?_
  refine LinearEquiv.ext fun v => ?_
  have h2 := hg.2 v Submodule.mem_top
  rw [Submodule.mem_bot, sub_eq_zero] at h2
  simpa using h2

theorem invVol_self {G : Type*} [Group G] (K : Subgroup G) : invVol K K = 1 := by
  simp [invVol, Subgroup.relIndex_self]

theorem invVol_of_le {G : Type*} [Group G] {K0 K : Subgroup G} (h : K ≤ K0) :
    invVol K0 K = K.relIndex K0 := by
  simp [invVol, Subgroup.relIndex_eq_one.mpr h]

theorem lead_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) : lead Z 0 = 1 := by
  unfold lead
  have : IsEmpty (Fin ((0 : Fin (N + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  exact Matrix.det_isEmpty

theorem lead_last {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) : lead Z (Fin.last N) = Z.det := rfl

theorem lead_one {N : ℕ} (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) E) :
    lead Z ⟨1, by omega⟩ = Z 0 0 := by
  rw [lead, Matrix.det_fin_one]
  rfl

theorem vE_zero (L : LocE F E) (ϖ : 𝒪[F]) : vE L ϖ 0 = 0 := by
  unfold vE
  have hS : {m : ℤ | ∃ y ∈ L.O, (0 : E) = algebraMap F E ((ϖ : F) ^ m) * y} = Set.univ :=
    Set.eq_univ_of_forall fun m => ⟨0, L.O.zero_mem, by simp⟩
  rw [hS]
  rw [csSup_of_not_bddAbove not_bddAbove_univ]
  exact Int.csSup_empty

theorem algebraMap_mem_iff (L : LocE F E) (a : F) : algebraMap F E a ∈ L.O ↔ a ∈ 𝒪[F] := by
  have := nontrivial L
  rw [L.O_def, isIntegral_algebraMap_iff (algebraMap F E).injective]
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))

theorem vE_pow (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (u : 𝒪[F]ˣ) (k : ℤ) :
    vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have := nontrivial L
  unfold vE
  apply IsGreatest.csSup_eq
  refine ⟨⟨algebraMap F E ((u : 𝒪[F]) : F), (algebraMap_mem_iff L _).mpr (u : 𝒪[F]).2, by
    rw [map_mul]⟩, ?_⟩
  rintro m ⟨y, hy, he⟩
  by_contra hlt
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = k + ((j + 1 : ℕ) : ℤ) := ⟨(m - k - 1).toNat, by omega⟩
  have h1 : algebraMap F E ((ϖ : F) ^ m)⁻¹ * algebraMap F E ((ϖ : F) ^ m) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), map_one]
  have hy' : y = algebraMap F E (((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F)) := by
    calc y = algebraMap F E ((ϖ : F) ^ m)⁻¹ * (algebraMap F E ((ϖ : F) ^ m) * y) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← he, ← map_mul]
          congr 1
          rw [hj, zpow_add₀ hϖ0, zpow_natCast]
          field_simp
  have hz : ((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F) ∈ 𝒪[F] :=
    (algebraMap_mem_iff L _).mp (hy' ▸ hy)
  have hu : ϖ ^ (j + 1) * (⟨_, hz⟩ : 𝒪[F]) = (u : 𝒪[F]) := by
    apply Subtype.ext
    push_cast
    field_simp
  have hunit : IsUnit (ϖ ^ (j + 1)) := isUnit_of_mul_isUnit_left (hu ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero j)).mp hunit)

theorem exists_char (a : F) (ha : a ∉ 𝒪[F]) :
    ∃ ψ : AddChar F ℂ, (∀ y ∈ 𝒪[F], ψ y = 1) ∧ ψ a ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    (A := F ⧸ (𝒪[F]).toAddSubgroup) (a := (a : F ⧸ (𝒪[F]).toAddSubgroup))
    (by rw [ne_eq, QuotientAddGroup.eq_zero_iff]; exact ha)
  let ι : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      intro q hq
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      change (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hx
      obtain ⟨k, hk⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
      refine ⟨k, ?_⟩
      have hk' : ((k : ℚ) : ℝ) = (q : ℝ) := by simpa using hk
      simpa using (Rat.cast_injective hk')
  refine ⟨{ toFun := fun x => ((AddCircle.toCircle (ι (c (x : F ⧸ (𝒪[F]).toAddSubgroup))) : Circle) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [AddCircle.toCircle_add] }, ?_, ?_⟩
  · intro y hy
    have hy0 : (y : F ⧸ (𝒪[F]).toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    simp [hy0]
  · intro h
    apply hc
    apply hι
    apply AddCircle.injective_toCircle one_ne_zero
    rw [map_zero, AddCircle.toCircle_zero]
    exact Circle.ext (by simpa using h)

theorem isIntegral_iff (a : F) : IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))

theorem nonempty_split [IsNonarchimedeanLocalField F] :
    ∃ L : LocE F (F × F), (∀ x, L.cj x = x.swap) ∧ L.O = (𝒪[F]).prod 𝒪[F] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have hϖ0 : (ϖ : F) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have hinv : (ϖ : F)⁻¹ ∉ 𝒪[F] := by
    intro h
    apply hϖ.not_isUnit
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext (by simp [hϖ0])⟩
  obtain ⟨ψ, hψo, hψ⟩ := exists_char _ hinv
  have hcont : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hO : (𝒪[F] : Set F) ∈ nhds (0 : F) :=
      (Valuation.isOpen_integer (v := ValuativeRel.valuation F)).mem_nhds (zero_mem _)
    have ht : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
      rw [← sub_self x]
      exact Filter.tendsto_id.sub tendsto_const_nhds
    have hev : ∀ᶠ y in nhds x, ψ x = ψ y := by
      filter_upwards [ht hO] with y hy
      have hy' : y = x + (y - x) := by ring
      rw [hy', AddChar.map_add_eq_mul, hψo _ hy, mul_one]
    exact continuousAt_const.congr hev
  have key : ∀ b : F, b ∉ 𝒪[F] → ∃ t ∈ 𝒪[F], b * t = (ϖ : F)⁻¹ := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hb (zero_mem _)
    have hlt : ValuativeRel.valuation F b⁻¹ < 1 :=
      (Valuation.one_lt_val_iff _ hb0).mp (not_le.mp fun h => hb h)
    have hbi : b⁻¹ ∈ 𝒪[F] := hlt.le
    have hnu : ¬ IsUnit (⟨b⁻¹, hbi⟩ : 𝒪[F]) := fun hu =>
      hlt.ne ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mp hu)
    have hmem : (⟨b⁻¹, hbi⟩ : 𝒪[F]) ∈ Ideal.span {ϖ} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hs' : (s : F) * ϖ = b⁻¹ := congrArg Subtype.val hs
    refine ⟨s, s.2, ?_⟩
    calc b * (s : F) = b * ((s : F) * ϖ) * (ϖ : F)⁻¹ := by field_simp
      _ = (ϖ : F)⁻¹ := by rw [hs', mul_inv_cancel₀ hb0, one_mul]
  let O : Subring (F × F) := (𝒪[F]).prod 𝒪[F]
  have memO : ∀ x : F × F, x ∈ O ↔ x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F] := fun x => Subring.mem_prod
  have comp : ∀ (p : 𝒪[F]), Irreducible p → ∀ a ra : F, a ∈ 𝒪[F] → ra ∈ 𝒪[F] →
      ra * p = a * a → ∃ s ∈ 𝒪[F], s * p = a := by
    intro p hp a ra ha hra h
    have hdvd : p ∣ (⟨a, ha⟩ : 𝒪[F]) * ⟨a, ha⟩ :=
      ⟨⟨ra, hra⟩, Subtype.ext (by push_cast; rw [← h, mul_comm])⟩
    obtain ⟨s, hs⟩ := (hp.prime.dvd_or_dvd hdvd).elim id id
    refine ⟨s, s.2, ?_⟩
    have hs' := congrArg Subtype.val hs
    push_cast at hs'
    rw [hs', mul_comm]
  let sw : (F × F) ≃ₐ[F] (F × F) :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  refine ⟨{
    cj := sw
    cj_cj := fun x => rfl
    cj_fix := fun x => by
      constructor
      · intro h
        have h2 : x.2 = x.1 := congrArg Prod.fst h
        exact ⟨x.1, Prod.ext rfl h2.symm⟩
      · rintro ⟨a, rfl⟩
        rfl
    free := inferInstance
    rank := by simp
    reduced := inferInstance
    top := inferInstance
    O := O
    O_def := fun x => by
      rw [memO, ← GlobalTheory.HL.Model.isIntegral_iff x.1, ← GlobalTheory.HL.Model.isIntegral_iff x.2]
      exact IsIntegral.pair_iff.symm
    unram := fun p hp x hx hxx => by
      rw [Submodule.mem_span_singleton] at hxx ⊢
      obtain ⟨r, hr⟩ := hxx
      have hr1 : r.1.1 * p = x.1 * x.1 := by
        have := congrArg Prod.fst hr
        simpa [Subring.smul_def] using this
      have hr2 : r.1.2 * p = x.2 * x.2 := by
        have := congrArg Prod.snd hr
        simpa [Subring.smul_def] using this
      obtain ⟨s1, hs1, e1⟩ := comp p hp x.1 r.1.1 ((memO x).mp hx).1 ((memO _).mp r.2).1 hr1
      obtain ⟨s2, hs2, e2⟩ := comp p hp x.2 r.1.2 ((memO x).mp hx).2 ((memO _).mp r.2).2 hr2
      refine ⟨⟨(s1, s2), (memO _).mpr ⟨hs1, hs2⟩⟩, Prod.ext ?_ ?_⟩
      · simpa [Subring.smul_def] using e1
      · simpa [Subring.smul_def] using e2
    psi0 := { toFun := fun x => ψ (x.1 + x.2)
              map_zero_eq_one' := by simp
              map_add_eq_mul' := fun x y => by
                simp only [Prod.fst_add, Prod.snd_add]
                rw [add_add_add_comm, AddChar.map_add_eq_mul] }
    local_additive_char_continuous := hcont.comp (continuous_fst.add continuous_snd)
    local_additive_char_conj := fun y => by
      show ψ (y.2 + y.1) = ψ (y.1 + y.2)
      rw [add_comm]
    additive_character_dual_ring := fun x => by
      constructor
      · intro h
        rw [memO]
        constructor
        · by_contra h1
          obtain ⟨t, ht, hbt⟩ := key _ h1
          have h2 := h (t, 0) ((memO _).mpr ⟨ht, zero_mem _⟩)
          change ψ ((x * (t, 0)).1 + (x * (t, 0)).2) = 1 at h2
          simp only [Prod.fst_mul, Prod.snd_mul, mul_zero, add_zero, hbt] at h2
          exact hψ h2
        · by_contra h1
          obtain ⟨t, ht, hbt⟩ := key _ h1
          have h2 := h (0, t) ((memO _).mpr ⟨zero_mem _, ht⟩)
          change ψ ((x * (0, t)).1 + (x * (0, t)).2) = 1 at h2
          simp only [Prod.fst_mul, Prod.snd_mul, mul_zero, zero_add, hbt] at h2
          exact hψ h2
      · intro hx y hy
        have hxy := (memO _).mp (O.mul_mem hx hy)
        exact hψo _ (add_mem hxy.1 hxy.2) }, fun x => rfl, rfl⟩

theorem exists_isSD [IsNonarchimedeanLocalField F] (n : ℕ) :
    ∃ (L : LocE F (F × F)) (H : Matrix (Fin n) (Fin n) (F × F)) (Λ : Submodule L.O (Fin n → F × F)),
      IsHermND L H ∧ IsSD L H Λ := by
  obtain ⟨L, -, -⟩ := nonempty_split (F := F)
  exact ⟨L, 1, stdLat L n, isHermND_one L n, isSD_std L n⟩

theorem resQ_eq [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) ∧ 2 ≤ resQ ϖ := by
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp h
  have e : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [← hm]
    rfl
  refine ⟨e, ?_⟩
  rw [e]
  exact Finite.one_lt_card

end GlobalTheory.HL.Model
