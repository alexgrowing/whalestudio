import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHCompEqSmul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls GlobalTheory.CompanionTheory.LsRho

namespace GlobalTheory.CompanionTheory.TowFlat

variable {W : Type} [CommRing W]

theorem mem_B_of_mk {L : Cx.{1} W} {n : ℕ} (z : L.Z n) (hz : (Submodule.Quotient.mk z : L.H n) = 0) :
    z.1 ∈ L.B n :=
  (Submodule.Quotient.mk_eq_zero ((L.B n).submoduleOf (L.Z n))).1 hz

theorem mk_of_mem_B {L : Cx.{1} W} {n : ℕ} (z : L.Z n) (h : z.1 ∈ L.B n) :
    (Submodule.Quotient.mk z : L.H n) = 0 :=
  (Submodule.Quotient.mk_eq_zero ((L.B n).submoduleOf (L.Z n))).2 h

theorem d_of_B {L : Cx.{1} W} {n : ℕ} {x : L.X n} (h : x ∈ L.B n) : L.d n x = 0 := by
  cases n with
  | zero =>
    have e : x = 0 := h
    rw [e, map_zero]
  | succ n =>
    obtain ⟨y, rfl⟩ := h
    exact L.dd n y

def Ses {A B C : Cx.{1} W} (f : Cx.Hom A B (RingHom.id W)) (g : Cx.Hom B C (RingHom.id W)) : Prop :=
  (∀ i, Function.Injective (f.f i)) ∧ (∀ i, Function.Surjective (g.f i)) ∧
    ∀ i x, g.f i x = 0 ↔ ∃ y, f.f i y = x

section Conn

variable {A B C : Cx.{1} W} {f : Cx.Hom A B (RingHom.id W)} {g : Cx.Hom B C (RingHom.id W)}

theorem lift_B (hS : Ses f g) {n : ℕ} {z : C.X n} (h : z ∈ C.B n) : ∃ b ∈ B.B n, g.f n b = z := by
  cases n with
  | zero =>
    have e : z = 0 := h
    exact ⟨0, Submodule.zero_mem _, by rw [e, map_zero]⟩
  | succ n =>
    obtain ⟨c, rfl⟩ := h
    obtain ⟨b, rfl⟩ := hS.2.1 n c
    exact ⟨B.d n b, ⟨b, rfl⟩, (g.comm n b).symm⟩

def Rel (f : Cx.Hom A B (RingHom.id W)) (g : Cx.Hom B C (RingHom.id W)) (j : ℕ) (x : C.H j) (v : A.H (j + 1)) : Prop :=
  ∃ (z : C.Z j) (β : B.X j) (w : A.Z (j + 1)), Submodule.Quotient.mk z = x ∧ Submodule.Quotient.mk w = v ∧
    g.f j β = z.1 ∧ f.f (j + 1) w.1 = B.d j β

theorem rel_total (hS : Ses f g) (j : ℕ) (x : C.H j) : ∃ v, Rel f g j x v := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨β, hβ⟩ := hS.2.1 j z.1
  have h0 : g.f (j + 1) (B.d j β) = 0 := by
    rw [← g.comm, hβ]
    exact z.2
  obtain ⟨w, hw⟩ := (hS.2.2 (j + 1) _).1 h0
  have hd : A.d (j + 1) w = 0 := by
    apply hS.1 (j + 2)
    rw [← f.comm, hw, B.dd, map_zero]
  exact ⟨_, z, β, ⟨w, hd⟩, rfl, rfl, hβ, hw⟩

theorem rel_add {j : ℕ} {x x' : C.H j} {v v' : A.H (j + 1)} (h : Rel f g j x v) (h' : Rel f g j x' v') :
    Rel f g j (x + x') (v + v') := by
  obtain ⟨z, β, w, rfl, rfl, h1, h2⟩ := h
  obtain ⟨z', β', w', rfl, rfl, h1', h2'⟩ := h'
  refine ⟨z + z', β + β', w + w', rfl, rfl, ?_, ?_⟩
  · rw [map_add, h1, h1']; rfl
  · change f.f (j + 1) (w.1 + w'.1) = _
    rw [map_add, map_add, h2, h2']

theorem rel_smul {j : ℕ} (s : W) {x : C.H j} {v : A.H (j + 1)} (h : Rel f g j x v) :
    Rel f g j (s • x) (s • v) := by
  obtain ⟨z, β, w, rfl, rfl, h1, h2⟩ := h
  refine ⟨s • z, s • β, s • w, rfl, rfl, ?_, ?_⟩
  · rw [map_smul, h1]; rfl
  · change f.f (j + 1) (s • w.1) = _
    simp only [map_smul, h2, RingHom.id_apply]

theorem rel_zero (hS : Ses f g) {j : ℕ} {v : A.H (j + 1)} (h : Rel f g j 0 v) : v = 0 := by
  obtain ⟨z, β, w, hz, rfl, h1, h2⟩ := h
  obtain ⟨b, hbB, hb⟩ := lift_B hS (mem_B_of_mk z hz)
  have h0 : g.f j (β - b) = 0 := by rw [map_sub, h1, hb, sub_self]
  obtain ⟨a, ha⟩ := (hS.2.2 j _).1 h0
  have e : w.1 = A.d j a := by
    apply hS.1 (j + 1)
    rw [h2, ← f.comm, ha, map_sub, d_of_B hbB, sub_zero]
  exact mk_of_mem_B w ⟨a, e.symm⟩

theorem rel_unique (hS : Ses f g) {j : ℕ} {x : C.H j} {v v' : A.H (j + 1)} (h : Rel f g j x v)
    (h' : Rel f g j x v') : v = v' := by
  have h2 := rel_add h (rel_smul (-1) h')
  rw [neg_one_smul, neg_one_smul, add_neg_cancel] at h2
  exact add_neg_eq_zero.1 (rel_zero hS h2)

def cn (hS : Ses f g) (j : ℕ) : C.H j →ₗ[W] A.H (j + 1) where
  toFun x := Classical.choose (rel_total hS j x)
  map_add' x y := rel_unique hS (Classical.choose_spec (rel_total hS j (x + y)))
    (rel_add (Classical.choose_spec (rel_total hS j x)) (Classical.choose_spec (rel_total hS j y)))
  map_smul' s x := rel_unique hS (Classical.choose_spec (rel_total hS j (s • x)))
    (rel_smul s (Classical.choose_spec (rel_total hS j x)))

theorem cn_rel (hS : Ses f g) (j : ℕ) (x : C.H j) : Rel f g j x (cn hS j x) :=
  Classical.choose_spec (rel_total hS j x)

theorem cn_eq (hS : Ses f g) {j : ℕ} {x : C.H j} {v : A.H (j + 1)} (h : Rel f g j x v) : cn hS j x = v :=
  rel_unique hS (cn_rel hS j x) h

theorem ex_mid (hS : Ses f g) (j : ℕ) (x : B.H j) (h : g.mapH j x = 0) : ∃ y, f.mapH j y = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hb : g.f j z.1 ∈ C.B j := mem_B_of_mk (g.mapZ j z) h
  obtain ⟨b, hbB, hbg⟩ := lift_B hS hb
  have h0 : g.f j (z.1 - b) = 0 := by rw [map_sub, hbg, sub_self]
  obtain ⟨a, ha⟩ := (hS.2.2 j _).1 h0
  have da : A.d j a = 0 := by
    apply hS.1 (j + 1)
    have hz : B.d j z.1 = 0 := z.2
    rw [map_zero, ← f.comm, ha, map_sub, d_of_B hbB, hz, sub_zero]
  refine ⟨Submodule.Quotient.mk ⟨a, da⟩, ?_⟩
  change Submodule.Quotient.mk (f.mapZ j ⟨a, da⟩) = Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq]
  change f.f j a - z.1 ∈ B.B j
  rw [ha, sub_sub_cancel_left]
  exact Submodule.neg_mem _ hbB

theorem ex_cn (hS : Ses f g) (j : ℕ) (x : C.H j) (h : cn hS j x = 0) : ∃ y, g.mapH j y = x := by
  obtain ⟨z, β, w, rfl, hw, h1, h2⟩ := cn_rel hS j x
  rw [h] at hw
  obtain ⟨a, ha⟩ := mem_B_of_mk w hw
  have hd : B.d j (β - f.f j a) = 0 := by
    rw [map_sub, f.comm, ha, h2, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨_, hd⟩, ?_⟩
  change Submodule.Quotient.mk (g.mapZ j ⟨_, hd⟩) = Submodule.Quotient.mk z
  congr 1
  refine Subtype.ext ?_
  change g.f j (β - f.f j a) = z.1
  rw [map_sub, h1, (hS.2.2 j _).2 ⟨a, rfl⟩, sub_zero]

theorem cn_nat {A' B' C' : Cx.{1} W} {f' : Cx.Hom A' B' (RingHom.id W)} {g' : Cx.Hom B' C' (RingHom.id W)}
    (hS : Ses f g) (hS' : Ses f' g') (α : Cx.Hom A A' (RingHom.id W)) (μ : Cx.Hom B B' (RingHom.id W))
    (γ : Cx.Hom C C' (RingHom.id W)) (j : ℕ)
    (hf : ∀ x, f'.f (j + 1) (α.f (j + 1) x) = μ.f (j + 1) (f.f (j + 1) x))
    (hg : ∀ x, g'.f j (μ.f j x) = γ.f j (g.f j x)) (x : C.H j) :
    cn hS' j (γ.mapH j x) = α.mapH (j + 1) (cn hS j x) := by
  obtain ⟨z, β, w, rfl, hw, h1, h2⟩ := cn_rel hS j x
  rw [← hw]
  refine cn_eq hS' ⟨γ.mapZ j z, μ.f j β, α.mapZ (j + 1) w, rfl, rfl, ?_, ?_⟩
  · change g'.f j (μ.f j β) = γ.f j z.1
    rw [hg, h1]
  · change f'.f (j + 1) (α.f (j + 1) w.1) = _
    rw [hf, h2, μ.comm]

end Conn

theorem mapH_bij {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (h : ∀ i, Function.Bijective (φ.f i))
    (j : ℕ) : Function.Bijective (φ.mapH j) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hb : φ.f j z.1 ∈ L.B j := mem_B_of_mk (φ.mapZ j z) hx
    refine mk_of_mem_B z ?_
    cases j with
    | zero =>
      have e : φ.f 0 z.1 = 0 := hb
      have e' : z.1 = 0 := (h 0).1 (by rw [e, map_zero])
      rw [e']
      exact Submodule.zero_mem _
    | succ j =>
      obtain ⟨y, hy⟩ := hb
      obtain ⟨y, rfl⟩ := (h j).2 y
      exact ⟨y, (h (j + 1)).1 (by rw [← φ.comm, hy])⟩
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy⟩ := (h j).2 z.1
    have hd : K.d j y = 0 := by
      apply (h (j + 1)).1
      have hz : L.d j z.1 = 0 := z.2
      rw [map_zero, ← φ.comm, hy, hz]
    refine ⟨Submodule.Quotient.mk ⟨y, hd⟩, ?_⟩
    change Submodule.Quotient.mk (φ.mapZ j ⟨y, hd⟩) = Submodule.Quotient.mk z
    congr 1
    exact Subtype.ext hy

theorem mem_lpow {l : ℕ} {M : Type 1} [AddCommGroup M] [Module W M] {n : ℕ} {x : M} :
    x ∈ lpow (W := W) l M n ↔ ∃ y : M, ((l : W) ^ n) • y = x := by
  simp [lpow, LinearMap.mem_range]

def mulc (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0) :
    Cx.Hom (quo l K a) K (RingHom.id W) where
  f i := Submodule.liftQ _ (((l : W) ^ (c - a)) • LinearMap.id) (by
    rintro _ ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add,
      Nat.sub_add_cancel h, hk])
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (K.d i).map_smul _ x

theorem mulc_mk (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0)
    (i : ℕ) (x : K.X i) : (mulc l K h hk).f i (Submodule.Quotient.mk x) = ((l : W) ^ (c - a)) • x := rfl

theorem ses_flat {l c : ℕ} {K : Cx.{1} W} (hK : FlatL l c K) {a b : ℕ} (hc : a + b = c) (h : a ≤ c)
    (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0) : Ses (mulc l K h hk) (prj l K b) := by
  have hb : c - a = b := by omega
  refine ⟨fun i => (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun i => Submodule.mkQ_surjective _,
    fun i x => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mulc_mk, hb] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hK i).2 a b hc x hx)
  · constructor
    · intro hx
      obtain ⟨y, rfl⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      exact ⟨Submodule.Quotient.mk y, by rw [mulc_mk, hb]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [mulc_mk, hb]
      exact (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨y, rfl⟩)

theorem ses_red {l e : ℕ} {L : Cx.{1} W} (hL : FlatL l e L) {a b c : ℕ} (hc : a + b = c) (he : c ≤ e)
    (ha : a ≤ c) (hb : b ≤ c) : Ses (nug l L ha) (redg l L hb) := by
  have hb' : c - a = b := by omega
  refine ⟨fun i => (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun i x => ?_, fun i x => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.Quotient.mk (((l : W) ^ (c - a)) • y) = (0 : (quo l L c).X i) := hx
    rw [hb'] at h1
    obtain ⟨t, ht⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
    have h2 : ((l : W) ^ b) • (y - ((l : W) ^ a) • t) = 0 := by
      rw [smul_sub, smul_smul, ← pow_add, Nat.add_comm b a, hc, ht, sub_self]
    obtain ⟨s, hs⟩ := mem_lpow.1 ((hL i).2 (e - b) b (by omega) _ h2)
    refine (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨((l : W) ^ (e - b - a)) • s + t, ?_⟩)
    rw [smul_add, smul_smul, ← pow_add, show a + (e - b - a) = e - b by omega, hs, sub_add_cancel]
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : Submodule.Quotient.mk t = (0 : (quo l L b).X i) := hx
      obtain ⟨s, rfl⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
      refine ⟨Submodule.Quotient.mk s, ?_⟩
      change Submodule.Quotient.mk (((l : W) ^ (c - a)) • s) = _
      rw [hb']
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have h1 : Submodule.Quotient.mk (((l : W) ^ (c - a)) • y) = (Submodule.Quotient.mk t : (quo l L c).X i) := hy
      rw [hb'] at h1
      rw [← h1]
      change Submodule.Quotient.mk (((l : W) ^ b) • y) = (0 : (quo l L b).X i)
      exact (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.TowFlat

end
