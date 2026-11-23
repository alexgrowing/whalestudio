import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z3

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0

section General

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def orth (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Submodule K V) : Submodule K V where
  carrier := {x | ∀ q ∈ P, h q x = 0}
  add_mem' := by
    intro x y hx hy q hq
    have hx' : ∀ q ∈ P, h q x = 0 := hx
    have hy' : ∀ q ∈ P, h q y = 0 := hy
    simp [hx' q hq, hy' q hq]
  zero_mem' := by
    intro q _
    simp
  smul_mem' := by
    intro c x hx q hq
    have hx' : ∀ q ∈ P, h q x = 0 := hx
    simp [hx' q hq]

theorem mem_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {x : V} :
    x ∈ orth h P ↔ ∀ q ∈ P, h q x = 0 := Iff.rfl

def Splits (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Submodule K V) (M : AddSubgroup V) : Prop :=
  ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ P ∧ w - w₁ ∈ orth h P

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}

theorem orth_symm (hs : h.IsSymm) {q x : V} (hq : q ∈ P) (hx : x ∈ orth h P) : h x q = 0 := by
  have e := hs.eq q x
  rw [mem_orth.mp hx q hq, map_zero] at e
  exact e.symm

theorem mem_res {W : Submodule K V} {M : AddSubgroup V} {x : W} :
    x ∈ M.comap W.subtype.toAddMonoidHom ↔ (x : V) ∈ M := Iff.rfl

theorem decomp {Q : Submodule K V} (hc : IsCompl P Q) (v : V) : ∃ a ∈ P, ∃ b ∈ Q, a + b = v :=
  Submodule.mem_sup.mp (by rw [hc.sup_eq_top]; trivial)

theorem isCompl_orth (hs : h.IsSymm) (hd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (hM : IsSelfDualMod S h M) (hsp : Splits h P M) : IsCompl P (orth h P) := by
  have hdec : ∀ v : V, ∃ a ∈ P, v - a ∈ orth h P := by
    intro v
    obtain ⟨t, ht0, htv⟩ := hM.span v
    obtain ⟨w₁, -, hw₁P, hw₁⟩ := hsp _ htv
    refine ⟨t⁻¹ • w₁, P.smul_mem _ hw₁P, ?_⟩
    have e : v - t⁻¹ • w₁ = t⁻¹ • (t • v - w₁) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e]
    exact (orth h P).smul_mem _ hw₁
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxP hxW
    apply hd
    intro y
    obtain ⟨a, haP, ha⟩ := hdec y
    have e1 : h x a = 0 := orth_symm hs haP hxW
    have e2 : h x (y - a) = 0 := mem_orth.mp ha x hxP
    rw [map_sub, e1, sub_zero] at e2
    exact e2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨a, haP, ha⟩ := hdec v
    have e : v = a + (v - a) := by abel
    rw [e]
    exact Submodule.add_mem_sup haP ha

theorem isSelfDualMod_res (hM : IsSelfDualMod S h M) (hsp : Splits h P M) :
    IsSelfDualMod S (h.domRestrict₁₂ (orth h P) (orth h P))
      (M.comap (orth h P).subtype.toAddMonoidHom) where
  smul_mem a ha m hm := by
    rw [mem_res, Submodule.coe_smul]
    exact hM.smul_mem a ha _ (mem_res.mp hm)
  int x hx y hy := by
    rw [LinearMap.domRestrict₁₂_apply]
    exact hM.int _ (mem_res.mp hx) _ (mem_res.mp hy)
  dual x hx := by
    rw [mem_res]
    apply hM.dual
    intro m hm
    obtain ⟨w₁, hw₁M, hw₁P, hw₁⟩ := hsp m hm
    have e : h m x = h w₁ x + h (m - w₁) x := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    have e1 : h w₁ x = 0 := mem_orth.mp x.2 w₁ hw₁P
    have e2 := hx ⟨m - w₁, hw₁⟩ (mem_res.mpr (M.sub_mem hm hw₁M))
    rw [LinearMap.domRestrict₁₂_apply] at e2
    rw [e, e1, zero_add]
    exact e2
  span x := by
    obtain ⟨t, ht0, htx⟩ := hM.span x
    exact ⟨t, ht0, mem_res.mpr (by rw [Submodule.coe_smul]; exact htx)⟩

theorem res_nondeg (hs : h.IsSymm) (hd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (hM : IsSelfDualMod S h M) (hsp : Splits h P M) :
    ∀ x : orth h P, (∀ y, h.domRestrict₁₂ (orth h P) (orth h P) x y = 0) → x = 0 := by
  intro x hx
  have hc := isCompl_orth hs hd hM hsp
  apply Subtype.ext
  rw [Submodule.coe_zero]
  apply hd
  intro y
  obtain ⟨a, haP, b, hbW, rfl⟩ := decomp hc y
  have e1 : h x a = 0 := orth_symm hs haP x.2
  have e2 := hx ⟨b, hbW⟩
  rw [LinearMap.domRestrict₁₂_apply] at e2
  rw [map_add, e1, zero_add]
  exact e2

theorem mem_iff_split {Q : Submodule K V} (hc : IsCompl P Q)
    (hsp : ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ P ∧ w - w₁ ∈ Q) (x : V) :
    x ∈ M ↔ (((Submodule.prodEquivOfIsCompl P Q hc).symm x).1 : V) ∈ M ∧
      (((Submodule.prodEquivOfIsCompl P Q hc).symm x).2 : V) ∈ M := by
  constructor
  · intro hx
    obtain ⟨w₁, hw₁M, hw₁P, hw₁⟩ := hsp x hx
    have e : (Submodule.prodEquivOfIsCompl P Q hc).symm x = (⟨w₁, hw₁P⟩, ⟨x - w₁, hw₁⟩) := by
      rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
      simp
    rw [e]
    exact ⟨hw₁M, M.sub_mem hx hw₁M⟩
  · rintro ⟨h1, h2⟩
    have e := (Submodule.prodEquivOfIsCompl P Q hc).apply_symm_apply x
    rw [Submodule.coe_prodEquivOfIsCompl'] at e
    rw [← e]
    exact M.add_mem h1 h2

theorem glue (hs : h.IsSymm) (hc : IsCompl P (orth h P))
    (hsp₁ : Splits h P M₁) (hsp₂ : Splits h P M₂) (hag : ∀ w ∈ P, w ∈ M₁ ↔ w ∈ M₂)
    (g' : orth h P ≃ₗ[K] orth h P) (hg'i : ∀ x y : orth h P, h (g' x) (g' y) = h x y)
    (hg'M : ∀ x : orth h P, (x : V) ∈ M₁ ↔ (g' x : V) ∈ M₂) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ w ∈ P, g w = w) ∧ (∀ x : orth h P, g x = g' x) ∧
      ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  set e := Submodule.prodEquivOfIsCompl P (orth h P) hc with he
  let g : V ≃ₗ[K] V := e.symm.trans (((LinearEquiv.refl K P).prodCongr g').trans e)
  have hgs : ∀ x, e.symm (g x) = ((e.symm x).1, g' (e.symm x).2) := by
    intro x
    simp [g, LinearEquiv.prodCongr_apply]
  have hgx : ∀ x, g x = ((e.symm x).1 : V) + (g' (e.symm x).2 : V) := by
    intro x
    have := e.apply_symm_apply (g x)
    rw [hgs x, he, Submodule.coe_prodEquivOfIsCompl'] at this
    exact this.symm
  have hx : ∀ x, x = ((e.symm x).1 : V) + ((e.symm x).2 : V) := by
    intro x
    have := e.apply_symm_apply x
    rw [he, Submodule.coe_prodEquivOfIsCompl'] at this
    exact this.symm
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y
    change h (g x) (g y) = h x y
    rw [hgx x, hgx y]
    conv_rhs => rw [hx x, hx y]
    have z1 : ∀ (c : P) (d : orth h P), h (c : V) (d : V) = 0 := fun c d => mem_orth.mp d.2 c c.2
    have z2 : ∀ (c : P) (d : orth h P), h (d : V) (c : V) = 0 := fun c d => orth_symm hs c.2 d.2
    simp only [map_add, LinearMap.add_apply, z1, z2, hg'i, add_zero, zero_add]
  · intro w hw
    have e1 : e.symm w = (⟨w, hw⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left P (orth h P) hc ⟨w, hw⟩
    rw [hgx w, e1]
    simp
  · intro x
    have e1 : e.symm x = (0, x) := Submodule.prodEquivOfIsCompl_symm_apply_right P (orth h P) hc x
    rw [hgx x, e1]
    simp
  · intro x
    rw [mem_iff_split hc hsp₁ x, mem_iff_split hc hsp₂ (g x), hgs x]
    exact and_congr (hag _ (e.symm x).1.2) (hg'M _)

theorem isSelfDualMod_comap (F : V ≃ₗ[K] V) (hF : ∀ x y, h (F x) (F y) = h x y)
    (hM : IsSelfDualMod S h M) : IsSelfDualMod S h (M.comap F.symm.toLinearMap.toAddMonoidHom) where
  smul_mem a ha m hm := by
    change F.symm (a • m) ∈ M
    rw [map_smul]
    exact hM.smul_mem a ha _ hm
  int x hx y hy := by
    have e := hF (F.symm x) (F.symm y)
    rw [F.apply_symm_apply, F.apply_symm_apply] at e
    rw [e]
    exact hM.int _ hx _ hy
  dual x hx := by
    change F.symm x ∈ M
    apply hM.dual
    intro m hm
    have e := hF m (F.symm x)
    rw [F.apply_symm_apply] at e
    rw [← e]
    apply hx
    change F.symm (F m) ∈ M
    rw [F.symm_apply_apply]
    exact hm
  span x := by
    obtain ⟨t, ht0, htx⟩ := hM.span (F.symm x)
    exact ⟨t, ht0, by change F.symm (t • x) ∈ M; rw [map_smul]; exact htx⟩

theorem orth_pair {z y x : V} (hz : h z x = 0) (hy : h y x = 0) :
    x ∈ orth h (Submodule.span K {z, y}) := by
  rw [mem_orth]
  intro q hq
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hq
  simp [hz, hy]

theorem hyz_one (hs : h.IsSymm) {z y : V} (hzy : h z y = 1) : h y z = 1 := by
  have e := hs.eq z y
  rw [hzy, map_one] at e
  exact e.symm

theorem splits_plane (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {z y : V} (hz : z ∈ M) (hy : y ∈ M)
    (hzy : h z y = 1) (hD : IsUnitIn S (1 - h z z * h y y)) :
    Splits h (Submodule.span K {z, y}) M := by
  intro w hw
  have hyz := hyz_one hs hzy
  have hAS : h z w ∈ S := hM.int _ hz _ hw
  have hBS : h y w ∈ S := hM.int _ hy _ hw
  have hnz : h z z ∈ S := hM.int _ hz _ hz
  have hb : h y y ∈ S := hM.int _ hy _ hy
  obtain ⟨β, hβ⟩ : ∃ β : K, β = (h z w - h z z * h y w) * (1 - h z z * h y y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : K, α = h y w - β * h y y := ⟨_, rfl⟩
  have hβS : β ∈ S := by
    rw [hβ]
    exact S.mul_mem (S.sub_mem hAS (S.mul_mem hnz hBS)) hD.2.2
  have hαS : α ∈ S := by
    rw [hα]
    exact S.sub_mem hBS (S.mul_mem hβS hb)
  have hβD : β * (1 - h z z * h y y) = h z w - h z z * h y w := by
    rw [hβ, mul_assoc, inv_mul_cancel₀ hD.1, mul_one]
  refine ⟨α • z + β • y, M.add_mem (hM.smul_mem _ hαS _ hz) (hM.smul_mem _ hβS _ hy),
    Submodule.mem_span_pair.mpr ⟨α, β, rfl⟩, orth_pair ?_ ?_⟩
  · have e : h z (w - (α • z + β • y)) = h z w - (α * h z z + β) := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul, hzy, mul_one]
    rw [e, hα]
    linear_combination (-1 : K) * hβD
  · have e : h y (w - (α • z + β • y)) = h y w - (α + β * h y y) := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul, hyz, mul_one]
    rw [e, hα]
    ring

theorem mem_plane (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {z y : V} (hz : z ∈ M) (hy : y ∈ M)
    (hzy : h z y = 1) (hD : IsUnitIn S (1 - h z z * h y y)) (α β : K) :
    α • z + β • y ∈ M ↔ α ∈ S ∧ β ∈ S := by
  have hyz := hyz_one hs hzy
  constructor
  · intro hw
    have hA := hM.int _ hz _ hw
    have hB := hM.int _ hy _ hw
    have hnz : h z z ∈ S := hM.int _ hz _ hz
    have hb : h y y ∈ S := hM.int _ hy _ hy
    have eA : h z (α • z + β • y) = α * h z z + β := by
      simp only [map_add, map_smul, smul_eq_mul, hzy, mul_one]
    have eB : h y (α • z + β • y) = α + β * h y y := by
      simp only [map_add, map_smul, smul_eq_mul, hyz, mul_one]
    rw [eA] at hA
    rw [eB] at hB
    have hβ : β = ((α * h z z + β) - h z z * (α + β * h y y)) * (1 - h z z * h y y)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hD.1]
      ring
    have hβS : β ∈ S := by
      rw [hβ]
      exact S.mul_mem (S.sub_mem hA (S.mul_mem hnz hB)) hD.2.2
    refine ⟨?_, hβS⟩
    have hα : α = (α + β * h y y) - β * h y y := by ring
    rw [hα]
    exact S.sub_mem hB (S.mul_mem hβS hb)
  · rintro ⟨hα, hβ⟩
    exact M.add_mem (hM.smul_mem _ hα _ hz) (hM.smul_mem _ hβ _ hy)

end General

section Fix

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem fix_of (h1 : SemiGenusLoc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (P : Submodule K V)
    {M₁ M₂ : AddSubgroup V} (hM₁ : IsSelfDualMod (locRing p) h M₁)
    (hM₂ : IsSelfDualMod (locRing p) h M₂)
    (hsp₁ : Splits h P M₁) (hsp₂ : Splits h P M₂) (hag : ∀ w ∈ P, w ∈ M₁ ↔ w ∈ M₂) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ w ∈ P, g w = w) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  have hc := isCompl_orth hs hd hM₁ hsp₁
  obtain ⟨g', hg'i, hg'M⟩ := h1 K (orth h P) (h.domRestrict₁₂ (orth h P) (orth h P)) hK
    (hs.domRestrict (orth h P)) (res_nondeg hs hd hM₁ hsp₁) p hp _ _
    (isSelfDualMod_res hM₁ hsp₁) (isSelfDualMod_res hM₂ hsp₂)
  obtain ⟨g, hg, hgP, -, hgM⟩ := glue hs hc hsp₁ hsp₂ hag g' (fun x y => hg'i x y)
    (fun x => hg'M x)
  exact ⟨g, hg, hgP, hgM⟩

end Fix

section Z

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem isUnitIn_one_sub {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a b : K}
    (ha : a ∈ locRing p) (has : star a = a) (hna : ¬ IsUnitIn (locRing p) a) (hb : b ∈ locRing p) :
    IsUnitIn (locRing p) (1 - a * b) := by
  rw [mem_locRing, mem_locR_iff hp] at ha hb
  obtain ⟨r, s, hs, rfl⟩ := ha
  obtain ⟨r', t, ht, rfl⟩ := hb
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have ht0 := algebraMap_ne_zero_of_mem_hcompl hp ht
  have hr : ¬ (r ∉ p ∧ conjO K r ∉ p) := by
    intro hr'
    apply hna
    rw [isUnitIn_div_iff hp r hs, mem_hcompl_iff hp, mem_conjIdeal_iff]
    exact hr'
  have hsc := (mem_hcompl_iff hp s).mp hs
  rw [mem_conjIdeal_iff] at hsc
  have e : star (algebraMap (𝓞 K) K r) * algebraMap (𝓞 K) K s =
      algebraMap (𝓞 K) K r * star (algebraMap (𝓞 K) K s) := by
    rw [star_div₀, div_eq_div_iff (star_ne_zero.mpr hs0) hs0] at has
    exact has
  have hrel : conjO K r * s = r * conjO K s := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (conjO K r * s) = algebraMap (𝓞 K) K (r * conjO K s)
    rw [map_mul, map_mul, algebraMap_conjO, algebraMap_conjO]
    exact e
  have hrp : r ∈ p ∧ conjO K r ∈ p := by
    by_cases h1 : r ∈ p
    · refine ⟨h1, ?_⟩
      have h3 : conjO K r * s ∈ p := by
        rw [hrel]
        exact p.mul_mem_right _ h1
      exact (hp.mem_or_mem h3).resolve_right hsc.1
    · have h2 : conjO K r ∈ p := by
        by_contra h2
        exact hr ⟨h1, h2⟩
      have h3 : r * conjO K s ∈ p := by
        rw [← hrel]
        exact p.mul_mem_right _ h2
      exact absurd ((hp.mem_or_mem h3).resolve_right hsc.2) h1
  have hst : s * t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hs ht
  have htc := (mem_hcompl_iff hp (s * t)).mp hst
  rw [mem_conjIdeal_iff] at htc
  have hnum : s * t - r * r' ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff]
    constructor
    · intro hm
      apply htc.1
      have e1 : s * t = (s * t - r * r') + r * r' := by ring
      rw [e1]
      exact p.add_mem hm (p.mul_mem_right r' hrp.1)
    · intro hm
      apply htc.2
      have e1 : conjO K (s * t) = conjO K (s * t - r * r') + conjO K r * conjO K r' := by
        rw [map_sub, map_mul (conjO K) r r']
        ring
      rw [e1]
      exact p.add_mem hm (p.mul_mem_right _ hrp.2)
  have key := (isUnitIn_div_iff hp _ hst).mpr hnum
  convert key using 1
  simp only [map_sub, map_mul]
  field_simp

theorem exists_dual_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {z : V}
    {M₁ : AddSubgroup V} (hM₁ : IsSelfDualMod (locRing p) h M₁) (hz₁ : z ∈ M₁)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hz0 : z ≠ 0) : ∃ y₁ ∈ M₁, h z y₁ = 1 := by
  have hS := isHermSemilocal_locRing hK hp
  let f : V →+ K :=
    { toFun := fun m => h m z
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hfA : ∀ a, a ∈ M₁.map f ↔ ∃ m ∈ M₁, h m z = a := fun a => AddSubgroup.mem_map
  have H1 : ∀ s ∈ locRing p, ∀ a ∈ M₁.map f, s * a ∈ M₁.map f := by
    intro s hs' a ha
    obtain ⟨m, hm, rfl⟩ := (hfA a).mp ha
    refine (hfA _).mpr ⟨star s • m, hM₁.smul_mem _ (hS.star_mem _ hs') _ hm, ?_⟩
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  have H2 : ∃ a ∈ M₁.map f, a ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x, h z x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz0 (hd z hcon)
    obtain ⟨t, ht0, htx⟩ := hM₁.span x
    refine ⟨h (t • x) z, (hfA _).mpr ⟨_, htx, rfl⟩, ?_⟩
    have e := hs.eq z x
    rw [starRingEnd_apply] at e
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← e, starRingEnd_apply]
    exact mul_ne_zero (star_ne_zero.mpr ht0) (star_ne_zero.mpr hx)
  have H3 : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ M₁.map f, t * a ∈ locRing p := by
    refine ⟨1, one_ne_zero, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := (hfA a).mp ha
    rw [one_mul]
    exact hM₁.int _ hm _ hz₁
  obtain ⟨α, hαA, hα0, hdiv⟩ := hS.principal (M₁.map f) H1 H2 H3
  obtain ⟨m₀, hm₀, rfl⟩ := (hfA α).mp hαA
  have hinv : (h m₀ z)⁻¹ ∈ locRing p := by
    apply hp₁
    apply hM₁.dual
    intro m hm
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hdiv _ ((hfA _).mpr ⟨m, hm, rfl⟩)
  refine ⟨(star (h m₀ z))⁻¹ • m₀, hM₁.smul_mem _ ?_ _ hm₀, ?_⟩
  · rw [← star_inv₀]
    exact hS.star_mem _ hinv
  · have e := hs.eq m₀ z
    rw [starRingEnd_apply] at e
    rw [map_smul, smul_eq_mul, ← e]
    exact inv_mul_cancel₀ (star_ne_zero.mpr hα0)

theorem zOnly (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (z : V)
    (M₁ M₂ : AddSubgroup V) (hM₁ : IsSelfDualMod (locRing p) h M₁)
    (hM₂ : IsSelfDualMod (locRing p) h M₂) (hz₁ : z ∈ M₁) (hz₂ : z ∈ M₂)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hp₂ : ∀ c : K, c • z ∈ M₂ → c ∈ locRing p) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g z = z ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  have hnzS : h z z ∈ locRing p := hM₁.int _ hz₁ _ hz₁
  have hnzs : star (h z z) = h z z := by
    have e := hs.eq z z
    rwa [starRingEnd_apply] at e
  by_cases hz0 : z = 0
  · obtain ⟨g, hg, hgM⟩ := h1 K V h hK hs hd p hp M₁ M₂ hM₁ hM₂
    exact ⟨g, hg, by rw [hz0, map_zero], hgM⟩
  by_cases hu : IsUnitIn (locRing p) (h z z)
  · have hsp : ∀ {M : AddSubgroup V}, IsSelfDualMod (locRing p) h M → z ∈ M →
        Splits h (Submodule.span K {z}) M := by
      intro M hM hzM w hw
      refine ⟨((h z z)⁻¹ * h z w) • z,
        hM.smul_mem _ ((locRing p).mul_mem hu.2.2 (hM.int _ hzM _ hw)) _ hzM,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z), ?_⟩
      rw [mem_orth]
      intro q hq
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hq
      have e : h z (w - ((h z z)⁻¹ * h z w) • z) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, mul_comm ((h z z)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ hu.1, mul_one, sub_self]
      rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
    obtain ⟨g, hg, hgP, hgM⟩ := fix_of h1 hK hs hd hp (Submodule.span K {z}) hM₁ hM₂
      (hsp hM₁ hz₁) (hsp hM₂ hz₂) (by
        intro w hw
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
        exact ⟨fun h' => hM₂.smul_mem _ (hp₁ d h') _ hz₂, fun h' => hM₁.smul_mem _ (hp₂ d h') _ hz₁⟩)
    exact ⟨g, hg, hgP z (Submodule.mem_span_singleton_self z), hgM⟩
  obtain ⟨y₁, hy₁M, hzy₁⟩ := exists_dual_one hK hs hd hp hM₁ hz₁ hp₁ hz0
  have hbS : h y₁ y₁ ∈ locRing p := hM₁.int _ hy₁M _ hy₁M
  have hbs : star (h y₁ y₁) = h y₁ y₁ := by
    have e := hs.eq y₁ y₁
    rwa [starRingEnd_apply] at e
  obtain ⟨y₂, hy₂M, hzy₂, hy₂y₂⟩ :=
    h2 K V h hK hs hd p hp M₂ z (h y₁ y₁) hM₂ hz₂ hp₂ hu hbS hbs ⟨y₁, hzy₁, rfl⟩
  have hD := isUnitIn_one_sub hp.isPrime hnzS hnzs hu hbS
  have hyz₁ := hyz_one hs hzy₁
  have hyz₂ := hyz_one hs hzy₂
  obtain ⟨c, hc⟩ : ∃ c : K, c = (1 - h z z * h y₁ y₁)⁻¹ := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : V, v = star c • z + star (-(c * h z z)) • y₁ := ⟨_, rfl⟩
  have hv : ∀ x, h v x = c * h z x - c * h z z * h y₁ x := by
    intro x
    rw [hvdef]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, star_star]
    ring
  have hvz : h v z = 0 := by
    rw [hv, hyz₁]
    ring
  have hvy : h v y₁ = 1 := by
    rw [hv, hzy₁]
    have e : c * 1 - c * h z z * h y₁ y₁ = c * (1 - h z z * h y₁ y₁) := by ring
    rw [e, hc, inv_mul_cancel₀ hD.1]
  obtain ⟨T, hTdef⟩ : ∃ T : V →ₗ[K] V, T = LinearMap.id + (h v).smulRight (y₂ - y₁) := ⟨_, rfl⟩
  have hT : ∀ α β : K, T (α • z + β • y₁) = α • z + β • y₂ := by
    intro α β
    have e : h v (α • z + β • y₁) = β := by
      rw [map_add, map_smul, map_smul, hvz, hvy]
      simp
    rw [hTdef, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, e, smul_sub]
    abel
  have hQ : ∀ x : Submodule.span K ({z, y₁} : Set V), ∃ α β : K, (x : V) = α • z + β • y₁ := by
    intro x
    obtain ⟨α, β, hx⟩ := Submodule.mem_span_pair.mp x.2
    exact ⟨α, β, hx.symm⟩
  have hstar : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [← starRingEnd_apply]
    exact hs.eq x y
  have hiso : ∀ x y : Submodule.span K ({z, y₁} : Set V),
      h ((T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) x)
        ((T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) y) = h x y := by
    intro x y
    obtain ⟨α, β, hx⟩ := hQ x
    obtain ⟨α', β', hy⟩ := hQ y
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hx, hy, hT]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hzy₁, hzy₂, hyz₁, hyz₂, hy₂y₂]
  have hinj : Function.Injective (T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx0
    obtain ⟨α, β, hx⟩ := hQ x
    rw [LinearMap.comp_apply, Submodule.subtype_apply, hx, hT] at hx0
    have e1 := congrArg (h z) hx0
    have e2 := congrArg (h y₂) hx0
    simp only [map_add, map_smul, smul_eq_mul, map_zero, hzy₂, hyz₂, hy₂y₂] at e1 e2
    have hβ : β * (1 - h z z * h y₁ y₁) = 0 := by linear_combination e1 - h z z * e2
    have hβ0 : β = 0 := (mul_eq_zero.mp hβ).resolve_right hD.1
    have hα0 : α = 0 := by
      rw [hβ0] at e2
      linear_combination e2
    apply Subtype.ext
    rw [hx, hα0, hβ0]
    simp
  obtain ⟨F, hFi, hFf⟩ := witt_extension_theorem K V h hstar hd _ _ hinj hiso
  have hzQ : z ∈ Submodule.span K ({z, y₁} : Set V) := Submodule.subset_span (by simp)
  have hyQ : y₁ ∈ Submodule.span K ({z, y₁} : Set V) := Submodule.subset_span (by simp)
  have hTz : T z = z := by simpa using hT 1 0
  have hTy : T y₁ = y₂ := by simpa using hT 0 1
  have hFz : F z = z := (hFf ⟨z, hzQ⟩).trans hTz
  have hFy : F y₁ = y₂ := (hFf ⟨y₁, hyQ⟩).trans hTy
  have hmem' : ∀ x, x ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom ↔ F.symm x ∈ M₁ :=
    fun x => Iff.rfl
  have hM₁' := isSelfDualMod_comap F hFi hM₁
  have hz' : z ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom := by
    rw [hmem', F.symm_apply_eq.mpr hFz.symm]
    exact hz₁
  have hy' : y₂ ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom := by
    rw [hmem', F.symm_apply_eq.mpr hFy.symm]
    exact hy₁M
  have hD₂ : IsUnitIn (locRing p) (1 - h z z * h y₂ y₂) := by
    rw [hy₂y₂]
    exact hD
  obtain ⟨g₂, hg₂, hg₂P, hg₂M⟩ := fix_of h1 hK hs hd hp (Submodule.span K {z, y₂}) hM₁' hM₂
    (splits_plane hs hM₁' hz' hy' hzy₂ hD₂) (splits_plane hs hM₂ hz₂ hy₂M hzy₂ hD₂) (by
      intro w hw
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [mem_plane hs hM₁' hz' hy' hzy₂ hD₂, mem_plane hs hM₂ hz₂ hy₂M hzy₂ hD₂])
  have hg₂' : ∀ x y, h (g₂ x) (g₂ y) = h x y := hg₂
  refine ⟨F.trans g₂, ?_, ?_, ?_⟩
  · intro x y
    change h (g₂ (F x)) (g₂ (F y)) = h x y
    rw [hg₂', hFi]
  · change g₂ (F z) = z
    rw [hFz, hg₂P z (Submodule.subset_span (by simp))]
  · intro x
    change x ∈ M₁ ↔ g₂ (F x) ∈ M₂
    rw [← hg₂M (F x), hmem', F.symm_apply_apply]

end Z

theorem semiGenusZLoc_of (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) : SemiGenusZLoc := by
  intro K _ _ _ V _ _ _ h hK hs hd p hp r s z M₁ M₂ hM₁ hM₂ hsz hag hsp₁ hsp₂ hz₁ hz₂ hp₁ hp₂
  have horth : ∀ x, (∀ a, h (s a) x = 0) → x ∈ orth h (Submodule.span K (Set.range s)) := by
    intro x hx
    rw [mem_orth]
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hx a
    | zero => simp
    | add y y' _ _ ihy ihy' => rw [map_add, LinearMap.add_apply, ihy, ihy', add_zero]
    | smul c y _ ihy => rw [map_smulₛₗ, LinearMap.smul_apply, ihy, smul_zero]
  have hspl : ∀ {M : AddSubgroup V}, (∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span K (Set.range s) ∧
      ∀ a, h (s a) (w - w₁) = 0) → Splits h (Submodule.span K (Set.range s)) M := by
    intro M hM w hw
    obtain ⟨w₁, hw₁M, hw₁U, hw₁⟩ := hM w hw
    exact ⟨w₁, hw₁M, hw₁U, horth _ hw₁⟩
  have hS₁ := hspl hsp₁
  have hS₂ := hspl hsp₂
  have hc := isCompl_orth hs hd hM₁ hS₁
  have hzW : z ∈ orth h (Submodule.span K (Set.range s)) := horth z hsz
  obtain ⟨g', hg'i, hg'z, hg'M⟩ := zOnly h1 h2 hK (hs.domRestrict _) (res_nondeg hs hd hM₁ hS₁) hp
    (⟨z, hzW⟩ : orth h (Submodule.span K (Set.range s))) _ _ (isSelfDualMod_res hM₁ hS₁)
    (isSelfDualMod_res hM₂ hS₂) hz₁ hz₂ (fun c hc' => hp₁ c hc') (fun c hc' => hp₂ c hc')
  obtain ⟨g, hg, hgU, hgW, hgM⟩ := glue hs hc hS₁ hS₂ hag g' (fun x y => hg'i x y) (fun x => hg'M x)
  refine ⟨g, hg, fun a => hgU _ (Submodule.subset_span ⟨a, rfl⟩), ?_, hgM⟩
  have e := hgW ⟨z, hzW⟩
  rw [hg'z] at e
  exact e

end Formalism.L2.SG.Pf.LatDictZ.Z3
