import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxTowerTwo

universe u u'

section Gen

variable {C₁ : Type u} [Category.{0} C₁] {C₂ : Type u'} [Category.{0} C₂]

theorem cx_D1_D0_eq_zero (K : Cx C₁) (g : K.M0.c0) : K.D1 (K.D0 g) = 0 := by
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · simp [Cx.D0, Cx.D1, Coef.map_comp, map_sub]
  · simp [Cx.D0, Cx.D1, Cx.diffZero_natural, map_sub]
  · simp [Cx.D0, Cx.D1, Cx.diffOne_diffZero]

theorem first_diagonal_phase_mem_unitary (K : Cx C₁) (c : K.T1) : K.D1 c ∈ K.Z2 := by
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · simp [Cx.D1, Coef.map_comp, map_sub, map_add]; abel
  · simp [Cx.D1, Coef.map_comp, map_sub, map_add, Cx.diffZero_natural]; abel
  · simp [Cx.D1, map_sub, Cx.diffOne_natural, Cx.diffOne_diffZero]
  · simp [Cx.D1, Cx.diffTwo_comp_diffOne]

variable {K : Cx C₁} {K' : Cx C₂} (m : CxMap K K')

theorem h1_mk (c : K.Z1) : m.h1 (QuotientAddGroup.mk c) = QuotientAddGroup.mk (m.z1 c) := rfl
theorem h2_mk (c : K.Z2) : m.h2 (QuotientAddGroup.mk c) = QuotientAddGroup.mk (m.z2 c) := rfl

theorem h1_mk_eq_zero_iff_exists_d0 {K : Cx C₁} (c : K.Z1) : (QuotientAddGroup.mk c : K.H1) = 0 ↔ ∃ w, K.D0 w = c := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem h2_mk_eq_zero_iff_exists_d1 {K : Cx C₁} (c : K.Z2) : (QuotientAddGroup.mk c : K.H2) = 0 ↔ ∃ w, K.D1 w = c := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem inj1 (h : Function.Injective m.h1) (x : K.T1) (hx : x ∈ K.Z1) (w : K'.M0.c0)
    (hw : m.p1 x = K'.D0 w) : ∃ v, K.D0 v = x := by
  have e : m.h1 (QuotientAddGroup.mk ⟨x, hx⟩) = m.h1 0 := by
    rw [map_zero, h1_mk, h1_mk_eq_zero_iff_exists_d0]; exact ⟨w, hw.symm⟩
  exact (h1_mk_eq_zero_iff_exists_d0 _).1 (h e)

theorem inj2 (h : Function.Injective m.h2) (x : K.T2) (hx : x ∈ K.Z2) (w : K'.T1)
    (hw : m.p2 x = K'.D1 w) : ∃ v, K.D1 v = x := by
  have e : m.h2 (QuotientAddGroup.mk ⟨x, hx⟩) = m.h2 0 := by
    rw [map_zero, h2_mk, h2_mk_eq_zero_iff_exists_d1]; exact ⟨w, hw.symm⟩
  exact (h2_mk_eq_zero_iff_exists_d1 _).1 (h e)

theorem surj1 (h : Function.Surjective m.h1) (y : K'.T1) (hy : y ∈ K'.Z1) :
    ∃ x ∈ K.Z1, ∃ w, y = m.p1 x + K'.D0 w := by
  obtain ⟨q, hq⟩ := h (QuotientAddGroup.mk ⟨y, hy⟩)
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [h1_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨x, hx, w, ?_⟩
  have e : K'.D0 w = -m.p1 x + y := hw
  rw [e]; abel

theorem surj2 (h : Function.Surjective m.h2) (y : K'.T2) (hy : y ∈ K'.Z2) :
    ∃ x ∈ K.Z2, ∃ w, y = m.p2 x + K'.D1 w := by
  obtain ⟨q, hq⟩ := h (QuotientAddGroup.mk ⟨y, hy⟩)
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [h2_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨x, hx, w, ?_⟩
  have e : K'.D1 w = -m.p2 x + y := hw
  rw [e]; abel

theorem h2_bijective_of_surj_of_inj_on_cocycles (hs : ∀ y ∈ K'.Z2, ∃ x ∈ K.Z2, ∃ w, y = m.p2 x + K'.D1 w)
    (hi : ∀ x ∈ K.Z2, ∀ w, m.p2 x = K'.D1 w → ∃ v, K.D1 v = x) : Function.Bijective m.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [h2_mk, h2_mk_eq_zero_iff_exists_d1] at hq
    obtain ⟨w, hw⟩ := hq
    exact (h2_mk_eq_zero_iff_exists_d1 _).2 (hi x hx w hw.symm)
  · intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, hx, w, hxw⟩ := hs y hy
    refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, ?_⟩
    rw [h2_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    show K'.D1 w = -m.p2 x + y
    rw [hxw]; abel

end Gen

section Lvl

variable {C : Type u} [Category.{0} C]

def lvl (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') : CxMap (K.res P'.ι) (K.res P.ι) where
  G := ObjectProperty.ιOfLE h
  a0 _ := AddMonoidHom.id _
  a1 _ := AddMonoidHom.id _
  a2 _ := AddMonoidHom.id _
  a3 _ := AddMonoidHom.id _
  compDegreeZero_natural _ _ := rfl
  compDegreeOne_natural _ _ := rfl
  compDegreeTwo_natural _ _ := rfl
  comp_commutes_diffZero _ _ := rfl
  comp_commutes_diffOne _ _ := rfl
  comp_commutes_diffTwo _ _ := rfl

theorem level_p0_surjective (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') :
    Function.Surjective (lvl K h).p0 := by
  classical
  intro g
  refine ⟨fun T ↦ if hT : P T.obj then g ⟨T.obj, hT⟩ else 0, ?_⟩
  funext T
  show (if hT : P T.obj then g ⟨T.obj, hT⟩ else 0) = g T
  rw [dif_pos T.property]

theorem level_p1_surjective (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') :
    Function.Surjective (lvl K h).p1 := by
  classical
  intro c
  refine ⟨(fun T T' φ ↦ if hT : P T.obj ∧ P T'.obj then
      c.1 ⟨T.obj, hT.1⟩ ⟨T'.obj, hT.2⟩ (ObjectProperty.homMk φ.hom) else 0,
    fun T ↦ if hT : P T.obj then c.2 ⟨T.obj, hT⟩ else 0), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_)
  · show (if hT : P T.obj ∧ P T'.obj then
      c.1 ⟨T.obj, hT.1⟩ ⟨T'.obj, hT.2⟩ (ObjectProperty.homMk φ.hom) else 0) = c.1 T T' φ
    rw [dif_pos ⟨T.property, T'.property⟩]; rfl
  · show (if hT : P T.obj then c.2 ⟨T.obj, hT⟩ else 0) = c.2 T
    rw [dif_pos T.property]

end Lvl

section Glue

variable {C : Type u} [Category.{0} C] {Q : ℕ → ObjectProperty C}

theorem ex2 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' : C) :
    ∃ n, Q n T ∧ Q n T' := by
  obtain ⟨a, ha⟩ := hex T
  obtain ⟨b, hb⟩ := hex T'
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_right _ _) hb⟩

theorem ex3 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' T'' : C) :
    ∃ n, Q n T ∧ Q n T' ∧ Q n T'' := by
  obtain ⟨a, ha, ha'⟩ := ex2 hQ hex T T'
  obtain ⟨b, hb⟩ := hex T''
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_left _ _) ha',
    hQ _ _ _ (le_max_right _ _) hb⟩

theorem ex4 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' T'' T''' : C) :
    ∃ n, Q n T ∧ Q n T' ∧ Q n T'' ∧ Q n T''' := by
  obtain ⟨a, ha, ha', ha''⟩ := ex3 hQ hex T T' T''
  obtain ⟨b, hb⟩ := hex T'''
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_left _ _) ha',
    hQ _ _ _ (le_max_left _ _) ha'', hQ _ _ _ (le_max_right _ _) hb⟩

variable (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (M : Coef C)

def glue0 (g : ∀ n, (M.res (Q n).ι).c0) : M.c0 := fun T ↦
  g (hex T).choose ⟨T, (hex T).choose_spec⟩

def glue1 (g : ∀ n, (M.res (Q n).ι).c1) : M.c1 := fun T T' φ ↦
  g (ex2 hQ hex T T').choose ⟨T, (ex2 hQ hex T T').choose_spec.1⟩
    ⟨T', (ex2 hQ hex T T').choose_spec.2⟩ (ObjectProperty.homMk φ)

def glue2 (g : ∀ n, (M.res (Q n).ι).c2) : M.c2 := fun T T' T'' φ ψ ↦
  g (ex3 hQ hex T T' T'').choose ⟨T, (ex3 hQ hex T T' T'').choose_spec.1⟩
    ⟨T', (ex3 hQ hex T T' T'').choose_spec.2.1⟩ ⟨T'', (ex3 hQ hex T T' T'').choose_spec.2.2⟩
    (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ)

include hQ in
theorem glueZeroCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c0)
    (hc : ∀ n (T : C) (h : Q n T) (k : Q (n + 1) T), g (n + 1) ⟨T, k⟩ = g n ⟨T, h⟩)
    (m : ℕ) (T : C) (h : Q m T) : glue0 hex M g T = g m ⟨T, h⟩ := by
  have mono : ∀ n m, n ≤ m → ∀ (T : C) (h : Q n T) (k : Q m T), g m ⟨T, k⟩ = g n ⟨T, h⟩ := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T h k
      rw [hc m T (hQ _ _ _ hnm h) k]
      exact ih T h _
  have hn := (hex T).choose_spec
  exact (mono _ (max (hex T).choose m) (le_max_left _ _) T hn (hQ _ _ _ (le_max_right _ _) h)).symm.trans
    (mono m _ (le_max_right _ _) T h _)

theorem glueOneCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c1)
    (hc : ∀ n (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (k : Q (n + 1) T) (k' : Q (n + 1) T'),
      g (n + 1) ⟨T, k⟩ ⟨T', k'⟩ (ObjectProperty.homMk φ) = g n ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ))
    (m : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q m T) (h' : Q m T') :
    glue1 hQ hex M g T T' φ = g m ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ) := by
  have mono : ∀ n m, n ≤ m → ∀ (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (k : Q m T) (k' : Q m T'),
      g m ⟨T, k⟩ ⟨T', k'⟩ (ObjectProperty.homMk φ) = g n ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T T' φ h h' k k'
      rw [hc m T T' φ (hQ _ _ _ hnm h) (hQ _ _ _ hnm h') k k']
      exact ih T T' φ h h' _ _
  have hn := (ex2 hQ hex T T').choose_spec
  exact (mono _ (max (ex2 hQ hex T T').choose m) (le_max_left _ _) T T' φ hn.1 hn.2
    (hQ _ _ _ (le_max_right _ _) h) (hQ _ _ _ (le_max_right _ _) h')).symm.trans
    (mono m _ (le_max_right _ _) T T' φ h h' _ _)

theorem glueTwoCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c2)
    (hc : ∀ n (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T') (h'' : Q n T'')
      (k : Q (n + 1) T) (k' : Q (n + 1) T') (k'' : Q (n + 1) T''),
      g (n + 1) ⟨T, k⟩ ⟨T', k'⟩ ⟨T'', k''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) =
        g n ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ))
    (m : ℕ) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q m T) (h' : Q m T') (h'' : Q m T'') :
    glue2 hQ hex M g T T' T'' φ ψ =
      g m ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) := by
  have mono : ∀ n m, n ≤ m → ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T')
      (h'' : Q n T'') (k : Q m T) (k' : Q m T') (k'' : Q m T''),
      g m ⟨T, k⟩ ⟨T', k'⟩ ⟨T'', k''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) =
        g n ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T T' T'' φ ψ h h' h'' k k' k''
      rw [hc m T T' T'' φ ψ (hQ _ _ _ hnm h) (hQ _ _ _ hnm h') (hQ _ _ _ hnm h'') k k' k'']
      exact ih T T' T'' φ ψ h h' h'' _ _ _
  have hn := (ex3 hQ hex T T' T'').choose_spec
  exact (mono _ (max (ex3 hQ hex T T' T'').choose m) (le_max_left _ _) T T' T'' φ ψ hn.1 hn.2.1 hn.2.2
    (hQ _ _ _ (le_max_right _ _) h) (hQ _ _ _ (le_max_right _ _) h')
    (hQ _ _ _ (le_max_right _ _) h'')).symm.trans
    (mono m _ (le_max_right _ _) T T' T'' φ ψ h h' h'' _ _ _)

end Glue

open ObjectProperty in

theorem tower_two : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C)
    (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) →
    (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U),
      ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h2 := by
  intro C _ D _ K P ℓ N₀ hP hPex hB
  let Q : ℕ → ObjectProperty C := fun n ↦ P (N₀ + n)
  have hQ : ∀ m n T, m ≤ n → Q m T → Q n T := fun m n T h ↦ hP _ _ T (by omega)
  have hQex : ∀ T, ∃ n, Q n T := fun T ↦
    let ⟨n, hn⟩ := hPex T; ⟨n, hP _ _ _ (by omega) hn⟩
  have hB' : ∀ n, ∃ h : ∀ U, Q n (ℓ.obj U), ((K.res (Q n).ι).resMap ((Q n).lift ℓ h)).Bij :=
    fun n ↦ hB _ (by omega)
  choose hl hbij using hB'
  let μ : ∀ n, CxMap (K.res (Q n).ι) (K.res ℓ) := fun n ↦ (K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))
  have hμ : ∀ n, (Function.Injective (μ n).h1 ∧ Function.Surjective (μ n).h1) ∧
      (Function.Injective (μ n).h2 ∧ Function.Surjective (μ n).h2) := fun n ↦ (hbij n).2
  let ρ : ∀ n, CxMap (K.res (Q (n + 1)).ι) (K.res (Q n).ι) := fun n ↦
    lvl K (P := Q n) (P' := Q (n + 1)) (fun T hT ↦ hQ n (n + 1) T (Nat.le_succ n) hT)
  have hμρ1 : ∀ n x, (μ n).p1 ((ρ n).p1 x) = (μ (n + 1)).p1 x := fun n x ↦ rfl
  have hμρ2 : ∀ n x, (μ n).p2 ((ρ n).p2 x) = (μ (n + 1)).p2 x := fun n x ↦ rfl
  have hS2 : ∀ n, ∀ b ∈ (K.res (Q n).ι).Z2, ∃ b' ∈ (K.res (Q (n + 1)).ι).Z2, ∃ a,
      b = (ρ n).p2 b' + (K.res (Q n).ι).D1 a := by
    intro n b hb
    obtain ⟨b', hb', w, hw⟩ := surj2 (μ (n + 1)) (hμ (n + 1)).2.2 ((μ n).p2 b) ((μ n).p2_mem_Z2_of_mem_Z2 hb)
    have hz : (μ n).p2 (b - (ρ n).p2 b') = (K.res ℓ).D1 w := by
      rw [map_sub, hμρ2, hw]; abel
    obtain ⟨v, hv⟩ := inj2 (μ n) (hμ n).2.1 _ (sub_mem hb ((ρ n).p2_mem_Z2_of_mem_Z2 hb')) w hz
    exact ⟨b', hb', v, by rw [hv]; abel⟩
  have hS1 : ∀ n (a : (K.res (Q n).ι).T1), (K.res (Q n).ι).D1 a = 0 → ∃ a' w,
      (K.res (Q (n + 1)).ι).D1 a' = 0 ∧ a = (ρ n).p1 a' + (K.res (Q n).ι).D0 w := by
    intro n a ha
    obtain ⟨a', ha', w, hw⟩ := surj1 (μ (n + 1)) (hμ (n + 1)).1.2 ((μ n).p1 a) ((μ n).z1 ⟨a, ha⟩).2
    have hz : (μ n).p1 (a - (ρ n).p1 a') = (K.res ℓ).D0 w := by
      rw [map_sub, hμρ1, hw]; abel
    have hmem : a - (ρ n).p1 a' ∈ (K.res (Q n).ι).Z1 := sub_mem ha ((ρ n).z1 ⟨a', ha'⟩).2
    obtain ⟨v, hv⟩ := inj1 (μ n) (hμ n).1.1 _ hmem w hz
    exact ⟨a', v, ha', by rw [hv]; abel⟩
  apply h2_bijective_of_surj_of_inj_on_cocycles (K.resMap ℓ)
  · intro y hy
    obtain ⟨x, hx, w, hw⟩ := surj2 (μ 0) (hμ 0).2.2 y hy
    obtain ⟨b, hb0, hbZ, hbc⟩ := GlobalTheory.T.tower_complex_lift_and_extension_lemmas.2 (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).T2) (fun n ↦ (K.res (Q n).ι).Z2) (fun n ↦ (K.res (Q n).ι).D1)
      (fun n ↦ (ρ n).p1) (fun n ↦ (ρ n).p2) (fun n x ↦ first_diagonal_phase_mem_unitary _ x) (fun n x ↦ (ρ n).pullback_secondDifferential x)
      (fun n ↦ level_p1_surjective K _) (fun n x hx ↦ (ρ n).p2_mem_Z2_of_mem_Z2 hx) hS2 x hx
    have hc2 := fun (n : ℕ) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T') (h'' : Q n T'') (_ : Q (n + 1) T) (_ : Q (n + 1) T') (_ : Q (n + 1) T'') ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.1 ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (homMk φ) (homMk ψ)) (hbc n)
    have hc1 := fun (n : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (_ : Q (n + 1) T) (_ : Q (n + 1) T') ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.2.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (hbc n)
    have hc0 := fun (n : ℕ) (T : C) (h : Q n T) (_ : Q (n + 1) T) ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.2.2 ⟨T, h⟩) (hbc n)
    have e2 := glueTwoCochain_apply_of_tower hQ hQex K.M0 (fun n ↦ (b n).1) hc2
    have e1 := glueOneCochain_apply_of_tower hQ hQex K.M1 (fun n ↦ (b n).2.1) hc1
    have e0 := glueZeroCochain_apply_of_tower hQ hQex K.M2 (fun n ↦ (b n).2.2) hc0
    refine ⟨(glue2 hQ hQex K.M0 (fun n ↦ (b n).1), glue1 hQ hQex K.M1 (fun n ↦ (b n).2.1),
      glue0 hQex K.M2 (fun n ↦ (b n).2.2)), ?_, w, ?_⟩
    · refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
      · obtain ⟨m, h1, h2, h3, h4⟩ := ex4 hQ hQex T T' T'' T'''
        dsimp only
        rw [e2 m T T' T'' φ ψ h1 h2 h3, e2 m T T'' T''' (φ ≫ ψ) χ h1 h3 h4, e2 m T T' T''' φ (ψ ≫ χ) h1 h2 h4,
          e2 m T' T'' T''' ψ χ h2 h3 h4]
        exact (hbZ m).1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ ⟨T''', h4⟩ (homMk φ) (homMk ψ) (homMk χ)
      · obtain ⟨m, h1, h2, h3⟩ := ex3 hQ hQex T T' T''
        dsimp only
        rw [e1 m T T'' (φ ≫ ψ) h1 h3, e1 m T T' φ h1 h2, e1 m T' T'' ψ h2 h3, e2 m T T' T'' φ ψ h1 h2 h3]
        exact (hbZ m).2.1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ (homMk φ) (homMk ψ)
      · obtain ⟨m, h1, h2⟩ := ex2 hQ hQex T T'
        dsimp only
        rw [e0 m T' h2, e0 m T h1, e1 m T T' φ h1 h2]
        exact (hbZ m).2.2.1 ⟨T, h1⟩ ⟨T', h2⟩ (homMk φ)
      · obtain ⟨m, h1⟩ := hQex T
        dsimp only
        rw [e0 m T h1]
        exact (hbZ m).2.2.2 ⟨T, h1⟩
    · have hp : (K.resMap ℓ).p2 (glue2 hQ hQex K.M0 (fun n ↦ (b n).1), glue1 hQ hQex K.M1 (fun n ↦ (b n).2.1),
          glue0 hQex K.M2 (fun n ↦ (b n).2.2)) = (μ 0).p2 (b 0) := by
        refine Prod.ext (funext fun U ↦ funext fun U' ↦ funext fun U'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
          (Prod.ext (funext fun U ↦ funext fun U' ↦ funext fun φ ↦ ?_) (funext fun U ↦ ?_))
        · exact e2 0 _ _ _ (ℓ.map φ) (ℓ.map ψ) (hl 0 U) (hl 0 U') (hl 0 U'')
        · exact e1 0 _ _ (ℓ.map φ) (hl 0 U) (hl 0 U')
        · exact e0 0 _ (hl 0 U)
      rw [hp, hb0]; exact hw
  · intro x hx w hw
    let bx : ∀ n, (K.res (Q n).ι).T2 := fun n ↦ (K.resMap (Q n).ι).p2 x
    have hbx : ∀ n, ∃ a, (K.res (Q n).ι).D1 a = bx n := fun n ↦
      inj2 (μ n) (hμ n).2.1 (bx n) ((K.resMap (Q n).ι).p2_mem_Z2_of_mem_Z2 hx) w hw
    obtain ⟨a, hac, had⟩ := GlobalTheory.T.tower_complex_lift_and_extension_lemmas.1 (fun n ↦ (K.res (Q n).ι).M0.c0) (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).T2) (fun n ↦ (K.res (Q n).ι).D0) (fun n ↦ (K.res (Q n).ι).D1)
      (fun n ↦ (ρ n).p0) (fun n ↦ (ρ n).p1) (fun n ↦ (ρ n).p2) (fun n x ↦ cx_D1_D0_eq_zero _ x)
      (fun n x ↦ (ρ n).pullback_firstDifferential x) (fun n x ↦ (ρ n).pullback_secondDifferential x) (fun n ↦ level_p0_surjective K _) hS1 bx
      (fun n ↦ rfl) (fun n ↦ hbx n)
    have hc1 := fun (n : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (_ : Q (n + 1) T) (_ : Q (n + 1) T') ↦
      congrArg (fun q : (K.res (Q n).ι).T1 ↦ q.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (hac n)
    have hc0 := fun (n : ℕ) (T : C) (h : Q n T) (_ : Q (n + 1) T) ↦
      congrArg (fun q : (K.res (Q n).ι).T1 ↦ q.2 ⟨T, h⟩) (hac n)
    have e1 := glueOneCochain_apply_of_tower hQ hQex K.M0 (fun n ↦ (a n).1) hc1
    have e0 := glueZeroCochain_apply_of_tower hQ hQex K.M1 (fun n ↦ (a n).2) hc0
    refine ⟨(glue1 hQ hQex K.M0 (fun n ↦ (a n).1), glue0 hQex K.M1 (fun n ↦ (a n).2)), ?_⟩
    refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
      (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
    · obtain ⟨m, h1, h2, h3⟩ := ex3 hQ hQex T T' T''
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e1 m T T' φ h1 h2, e1 m T T'' (φ ≫ ψ) h1 h3, e1 m T' T'' ψ h2 h3]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ (homMk φ) (homMk ψ)) (had m)
    · obtain ⟨m, h1, h2⟩ := ex2 hQ hQex T T'
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e0 m T' h2, e0 m T h1, e1 m T T' φ h1 h2]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.2.1 ⟨T, h1⟩ ⟨T', h2⟩ (homMk φ)) (had m)
    · obtain ⟨m, h1⟩ := hQex T
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e0 m T h1]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.2.2 ⟨T, h1⟩) (had m)

end GlobalTheory.CxTowerTwo
