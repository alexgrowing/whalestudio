import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.RgSplit

section Lat

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem lat_smul_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem lat_absorb {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {ι : Type} [Fintype ι] (v : ι → V) :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ i, c • v i ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  set C : ℝ := 1 + ∑ i, ∑ j, ‖b.repr (v i) j‖ with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ ∑ i, ∑ j, ‖b.repr (v i) j‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hC0 : 0 < C := by linarith
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt L (inv_pos.2 hC0)
  refine ⟨c, norm_pos_iff.1 hc0, hc.le.trans (inv_le_one_of_one_le₀ hC1), fun i => ?_⟩
  rw [hb]
  intro j
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr (v i) j‖ ≤ C := by
    have h2 : ‖b.repr (v i) j‖ ≤ ∑ j, ‖b.repr (v i) j‖ :=
      Finset.single_le_sum (f := fun j => ‖b.repr (v i) j‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)
    have h3 : ∑ j, ‖b.repr (v i) j‖ ≤ ∑ i, ∑ j, ‖b.repr (v i) j‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖b.repr (v i) j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  calc ‖c‖ * ‖b.repr (v i) j‖ ≤ C⁻¹ * C :=
        mul_le_mul hc.le h1 (norm_nonneg _) (inv_pos.2 hC0).le
    _ = 1 := inv_mul_cancel₀ hC0.ne'

theorem lat_bdd {V' : Type} [AddCommGroup V'] [Module L V'] {Λ : AddSubgroup V}
    {Λ₀ : AddSubgroup V'} (hΛ : IsLat L Λ) (hΛ₀ : IsLat L Λ₀) (P : V →ₗ[L] V') :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ x ∈ Λ, c • P x ∈ Λ₀ := by
  obtain ⟨m, b, hb⟩ := hΛ
  obtain ⟨c, hc0, hc1, hc⟩ := lat_absorb hΛ₀ (fun i => P (b i))
  refine ⟨c, hc0, hc1, fun x hx => ?_⟩
  have hx' := (hb x).1 hx
  have key : c • P x = ∑ i, b.repr x i • (c • P (b i)) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [key]
  exact AddSubgroup.sum_mem _ fun i _ => lat_smul_mem hΛ₀ (hx' i) (hc i)

variable [IsUltrametricDist L]

def latOf {m : ℕ} (b : Module.Basis (Fin m) L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' := fun {x y} hx hy i => by
    simp only [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {x} hx i => by simpa using hx i

theorem latOf_isLat {m : ℕ} (b : Module.Basis (Fin m) L V) : IsLat L (latOf b) :=
  ⟨m, b, fun _ => Iff.rfl⟩

def bigLat {V' : Type} [AddCommGroup V'] [Module L V'] (p q : V →ₗ[L] L) (P : V →ₗ[L] V')
    (N : AddSubgroup V') : AddSubgroup V where
  carrier := {x | ‖p x‖ ≤ 1 ∧ ‖q x‖ ≤ 1 ∧ P x ∈ N}
  add_mem' := fun {x y} hx hy => by
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx.1 hy.1)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx.2.1 hy.2.1)
    · rw [map_add]
      exact N.add_mem hx.2.2 hy.2.2
  zero_mem' := by simp [N.zero_mem]
  neg_mem' := fun {x} hx => by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hx.1
    · simpa using hx.2.1
    · rw [map_neg]
      exact N.neg_mem hx.2.2

end Lat

section Form

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

def hlin (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y

@[simp] theorem hlin_apply (hh : IsHerm s h) (x y : V) : hlin hh x y = h x y := rfl

def ca (hh : IsHerm s h) (δ : L) (f : V) : V →ₗ[L] L := (s δ)⁻¹ • hlin hh f

def cb (hh : IsHerm s h) (δ : L) (e : V) : V →ₗ[L] L := δ⁻¹ • hlin hh e

def pr (hh : IsHerm s h) (δ : L) (e f : V) : V →ₗ[L] V :=
  LinearMap.id - (ca hh δ f).smulRight e - (cb hh δ e).smulRight f

theorem ca_apply (hh : IsHerm s h) (δ : L) (f x : V) : ca hh δ f x = (s δ)⁻¹ * h f x := rfl

theorem cb_apply (hh : IsHerm s h) (δ : L) (e x : V) : cb hh δ e x = δ⁻¹ * h e x := rfl

theorem pr_apply (hh : IsHerm s h) (δ : L) (e f x : V) :
    pr hh δ e f x = x - ca hh δ f x • e - cb hh δ e x • f := by
  simp [pr]

theorem decomp (hh : IsHerm s h) (δ : L) (e f x : V) :
    x = ca hh δ f x • e + cb hh δ e x • f + pr hh δ e f x := by
  rw [pr_apply]; abel

variable {δ : L} {e f : V}

theorem h_fe (hh : IsHerm s h) (hef : h e f = δ) : h f e = s δ := by
  rw [hh.2.2.1 e f, hef]

theorem pr_orth (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (x : V) : h e (pr hh δ e f x) = 0 ∧ h f (pr hh δ e f x) = 0 := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hfe := h_fe hh hef
  constructor
  · change hlin hh e _ = 0
    rw [pr_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [hlin_apply, he, hef, cb_apply, smul_eq_mul]
    field_simp
    ring
  · change hlin hh f _ = 0
    rw [pr_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [hlin_apply, hf, hfe, ca_apply, smul_eq_mul]
    field_simp
    ring

theorem coef_eq (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    ca hh δ f (a • e + b • f + w) = a ∧ cb hh δ e (a • e + b • f + w) = b ∧
      pr hh δ e f (a • e + b • f + w) = w := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hfe := h_fe hh hef
  have h1 : ca hh δ f (a • e + b • f + w) = a := by
    rw [ca_apply, hh.1, hh.1, hh.2.1, hh.2.1, hf, hfe, hfw]
    field_simp
    simp
  have h2 : cb hh δ e (a • e + b • f + w) = b := by
    rw [cb_apply, hh.1, hh.1, hh.2.1, hh.2.1, he, hef, hew]
    field_simp
    simp
  refine ⟨h1, h2, ?_⟩
  rw [pr_apply, h1, h2]
  abel

theorem norm_form (hs : IsInv s) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    h (a • e + b • f + w) (a • e + b • f + w) = δ * (s a * b) + s (δ * (s a * b)) + h w w := by
  have hfe := h_fe hh hef
  have hwe : h w e = 0 := by rw [hh.2.2.1 e w, hew, map_zero]
  have hwf : h w f = 0 := by rw [hh.2.2.1 f w, hfw, map_zero]
  simp only [herm_add_left hh, hh.1, herm_smul_left hh, hh.2.1, he, hf, hef, hfe, hew, hfw, hwe,
    hwf, mul_zero, zero_add, add_zero, map_mul, hs.1]
  ring

end Form

section Main

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}

theorem coef_int (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hΛ : IsLat L Λ) (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ)
    {x : V} (hx : x ∈ Λ) :
    ‖ca hh δ f x‖ ≤ 1 ∧ ‖cb hh δ e x‖ ≤ 1 ∧ pr hh δ e f x ∈ Λ := by
  have hn : 0 < ‖δ‖ := norm_pos_iff.2 hδ
  have h1 : ‖ca hh δ f x‖ ≤ 1 := by
    rw [ca_apply, norm_mul, norm_inv, hs.2.1]
    exact inv_mul_le_one_of_le₀ (hpair f hfΛ x hx) hn.le
  have h2 : ‖cb hh δ e x‖ ≤ 1 := by
    rw [cb_apply, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hpair e heΛ x hx) hn.le
  refine ⟨h1, h2, ?_⟩
  rw [pr_apply]
  exact Λ.sub_mem (Λ.sub_mem hx (lat_smul_mem hΛ h1 heΛ)) (lat_smul_mem hΛ h2 hfΛ)

variable {U : Submodule L V}

def prU (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) : V →ₗ[L] U :=
  LinearMap.codRestrict U (pr hh δ e f) fun x => (hU _).2 (pr_orth hh hδ he hf hef x)

theorem herm_restrict (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) :
    IsHerm s (fun x y : U => h x y) := by
  refine ⟨fun x y z => hh.1 _ _ _, fun a x y => hh.2.1 a _ _, fun x y => hh.2.2.1 _ _,
    fun x hx => Subtype.ext (hh.2.2.2 _ fun y => ?_)⟩
  have hx' := (hU x).1 x.2
  have hxe : h x e = 0 := by rw [hh.2.2.1 e x, hx'.1, map_zero]
  have hxf : h x f = 0 := by rw [hh.2.2.1 f x, hx'.2, map_zero]
  have hxp : h x (pr hh δ e f y) = 0 := hx ⟨_, (hU _).2 (pr_orth hh hδ he hf hef y)⟩
  rw [decomp hh δ e f y, hh.1, hh.1, hh.2.1, hh.2.1, hxe, hxf, hxp]
  simp

theorem restrict_isLat (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V]
    (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) :
    IsLat L (Λ.comap U.subtype.toAddMonoidHom) := by
  have lat0 := latOf_isLat (Module.finBasis L U)
  obtain ⟨c, hc0, -, hc⟩ := lat_bdd hΛ lat0 (prU hh hδ he hf hef hU)
  refine hS L U _ _ c lat0 hc0 (fun x hx => ?_) (fun x => ?_) (fun a ha x hx => ?_)
  · have hx' := (hU x).1 x.2
    have hp : prU hh hδ he hf hef hU (x : V) = x := by
      apply Subtype.ext
      have := (coef_eq hh hδ he hf hef 0 0 hx'.1 hx'.2).2.2
      simpa [prU] using this
    have := hc x hx
    rwa [hp] at this
  · obtain ⟨a, ha0, -, ha⟩ := lat_absorb hΛ (fun _ : Unit => (x : V))
    exact ⟨a, ha0, ha ()⟩
  · exact lat_smul_mem hΛ ha hx

theorem restrict_isMax (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V] (hs : IsInv s)
    (hδ : IsDelta s δ) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsMax h Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) :
    IsMax (fun x y : U => h x y) (Λ.comap U.subtype.toAddMonoidHom) := by
  have hδ0 := hδ.1
  have hlatU := restrict_isLat hS hh hδ0 he hf hef hU hΛ.1
  refine ⟨hlatU, fun x hx => hΛ.2.1 _ hx, fun N hN hNint hle => ?_⟩
  set P := prU hh hδ0 he hf hef hU with hP
  have hPv : ∀ x, ((P x : U) : V) = pr hh δ e f x := fun _ => rfl
  set M := bigLat (ca hh δ f) (cb hh δ e) P N with hM
  have hΛM : Λ ≤ M := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := coef_int hs hδ0 hh hΛ.1 hpair heΛ hfΛ hx
    exact ⟨h1, h2, hle h3⟩
  obtain ⟨c, hc0, hc1, hc⟩ := lat_bdd hN hlatU (LinearMap.id : U →ₗ[L] U)
  have hMlat : IsLat L M := by
    refine hS L V Λ M c hΛ.1 hc0 (fun x hx => ?_) (fun x => ?_) (fun a ha x hx => ?_)
    · obtain ⟨h1, h2, h3⟩ := hx
      have h4 : c • pr hh δ e f x ∈ Λ := hc _ h3
      rw [decomp hh δ e f x, smul_add, smul_add]
      exact Λ.add_mem (Λ.add_mem (lat_smul_mem hΛ.1 hc1 (lat_smul_mem hΛ.1 h1 heΛ))
        (lat_smul_mem hΛ.1 hc1 (lat_smul_mem hΛ.1 h2 hfΛ))) h4
    · obtain ⟨a, ha0, -, ha⟩ := lat_absorb hΛ.1 (fun _ : Unit => x)
      exact ⟨a, ha0, hΛM (ha ())⟩
    · obtain ⟨h1, h2, h3⟩ := hx
      refine ⟨?_, ?_, ?_⟩
      · rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) h1
      · rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) h2
      · rw [map_smul]
        exact lat_smul_mem hN ha h3
  have hMint : ∀ x ∈ M, ‖h x x‖ ≤ 1 := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨o1, o2⟩ := pr_orth hh hδ0 he hf hef x
    have hq := norm_form hs hh he hf hef (ca hh δ f x) (cb hh δ e x) o1 o2
    rw [← decomp hh δ e f x] at hq
    rw [hq]
    have ht : ‖δ * (s (ca hh δ f x) * cb hh δ e x) + s (δ * (s (ca hh δ f x) * cb hh δ e x))‖ ≤ 1 :=
      ((hδ.2.1 δ).2 le_rfl) _ (by
        rw [norm_mul, hs.2.1]
        exact mul_le_one₀ h1 (norm_nonneg _) h2)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht (hNint _ h3))
  have hMeq : M = Λ := hΛ.2.2 M hMlat hMint hΛM
  refine le_antisymm (fun x hx => ?_) hle
  have hx' := (hU x).1 x.2
  obtain ⟨c1, c2, c3⟩ := coef_eq hh hδ0 he hf hef 0 0 hx'.1 hx'.2
  simp only [zero_smul, zero_add] at c1 c2 c3
  have hxM : (x : V) ∈ M := by
    refine ⟨by simp [c1], by simp [c2], ?_⟩
    have : P (x : V) = x := Subtype.ext c3
    rwa [this]
  rw [hMeq] at hxM
  exact hxM

theorem split_mem_iff (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) (he : h e e = 0)
    (hf : h f f = 0) (hef : h e f = δ) {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) (a b : L) {w : V}
    (hew : h e w = 0) (hfw : h f w = 0) :
    a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ w ∈ Λ := by
  constructor
  · intro hx
    obtain ⟨c1, c2, c3⟩ := coef_eq hh hδ he hf hef a b hew hfw
    have := coef_int hs hδ hh hΛ hpair heΛ hfΛ hx
    rwa [c1, c2, c3] at this
  · rintro ⟨h1, h2, h3⟩
    exact Λ.add_mem (Λ.add_mem (lat_smul_mem hΛ h1 heΛ) (lat_smul_mem hΛ h2 hfΛ)) h3

end Main

theorem stSplit : StSandwich → StPairing → StSplit := by
  intro hS hP L _ _ _ _ s hs δ hδ V _ _ _ h hh e f U he hf hef hU
  have hδ0 := hδ.1
  refine ⟨herm_restrict hh hδ0 he hf hef hU, fun x => ⟨_, _, _, (hU _).2
    (pr_orth hh hδ0 he hf hef x), decomp hh δ e f x⟩, ?_, fun Λ hΛ heΛ hfΛ => ?_⟩
  · rintro rfl
    exact hδ0 (hef ▸ ((hU f).1 Submodule.mem_top).1)
  · have hpair := (hP L s hs δ hδ V h hh Λ hΛ).1
    refine ⟨restrict_isMax hS hs hδ hh he hf hef hU hΛ hpair heΛ hfΛ, fun a b w hw => ?_⟩
    have hw' := (hU w).1 hw
    exact split_mem_iff hs hδ0 hh he hf hef hΛ.1 hpair heΛ hfΛ a b hw'.1 hw'.2

end GlobalTheory.CompanionTheory.RgSplit
