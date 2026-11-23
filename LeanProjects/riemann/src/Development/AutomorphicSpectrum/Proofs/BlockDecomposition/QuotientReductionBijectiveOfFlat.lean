import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

namespace GlobalTheory.CompanionTheory.QredFlat

variable {W : Type} [CommRing W]

theorem mem_lp {l : ℕ} {M : Type 1} [AddCommGroup M] [Module W M] {n : ℕ} {x : M} :
    x ∈ lpow (W := W) l M n ↔ ∃ y : M, ((l : W) ^ n) • y = x := Iff.rfl

theorem B_ker (D : Cx.{1} W) (n : ℕ) (v : D.X n) (hv : v ∈ D.B n) : D.d n v = 0 := by
  cases n with
  | zero =>
    have h : v = 0 := hv
    rw [h, map_zero]
  | succ n =>
    obtain ⟨g, rfl⟩ := hv
    exact D.dd n g

theorem exact_quo (D : Cx.{1} W) (l m : ℕ) (hF : FlatL l m D)
    (hE : ∀ n (x : D.X n), D.d n x = 0 → x ∈ D.B n) :
    ∀ n c, c ≤ m → ∀ x : D.X n, D.d n x ∈ lpow (W := W) l (D.X (n + 1)) c →
      ∃ u : D.X n, ∃ v ∈ D.B n, x = ((l : W) ^ c) • u + v := by
  have key : ∀ n c, c ≤ m → ∀ x : D.X n, D.d n x ∈ lpow (W := W) l (D.X (n + 1)) c →
      D.d n (((l : W) ^ (m - c)) • x) = 0 := by
    intro n c hc x hx
    obtain ⟨y, hy⟩ := mem_lp.1 hx
    rw [map_smul, ← hy, smul_smul, ← pow_add, Nat.sub_add_cancel hc]
    exact (hF (n + 1)).1 y
  intro n
  induction n with
  | zero =>
    intro c hc x hx
    have h0 : ((l : W) ^ (m - c)) • x = 0 := hE 0 _ (key 0 c hc x hx)
    obtain ⟨u, hu⟩ := mem_lp.1 ((hF 0).2 c (m - c) (by omega) x h0)
    exact ⟨u, 0, Submodule.zero_mem _, by rw [add_zero, hu]⟩
  | succ n ih =>
    intro c hc x hx
    obtain ⟨w, hw⟩ := hE (n + 1) _ (key (n + 1) c hc x hx)
    have hw' : D.d n w = ((l : W) ^ (m - c)) • x := hw
    obtain ⟨u, v, hv, e⟩ := ih (m - c) (Nat.sub_le _ _) w (by rw [hw']; exact mem_lp.2 ⟨x, rfl⟩)
    have hd : D.d n w = ((l : W) ^ (m - c)) • D.d n u := by
      rw [e, map_add, B_ker D n v hv, add_zero, map_smul]
    have h1 : ((l : W) ^ (m - c)) • (x - D.d n u) = 0 := by
      rw [smul_sub, ← hw', hd, sub_self]
    obtain ⟨t, ht⟩ := mem_lp.1 ((hF (n + 1)).2 c (m - c) (by omega) _ h1)
    exact ⟨t, D.d n u, ⟨u, rfl⟩, by rw [ht]; abel⟩

def Sh (L : Cx.{1} W) : ℕ → Type 1
  | 0 => PUnit
  | n + 1 => L.X n

instance instAC (L : Cx.{1} W) : ∀ n, AddCommGroup (Sh L n)
  | 0 => (inferInstance : AddCommGroup PUnit)
  | n + 1 => (inferInstance : AddCommGroup (L.X n))

instance instMod (L : Cx.{1} W) : ∀ n, Module W (Sh L n)
  | 0 => (PUnit.module : Module W PUnit.{2})
  | n + 1 => (inferInstance : Module W (L.X n))

def shD (L : Cx.{1} W) : ∀ n, Sh L n →ₗ[W] Sh L (n + 1)
  | 0 => 0
  | n + 1 => L.d n

def sdL (L : Cx.{1} W) (n : ℕ) : Sh L n →ₗ[W] L.X n := shD L n

theorem d_shD (L : Cx.{1} W) (n : ℕ) (y : Sh L n) : L.d n (shD L n y) = 0 := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact L.dd n y

theorem B_shD (L : Cx.{1} W) (n : ℕ) (y : L.X n) (hy : y ∈ L.B n) : ∃ t : Sh L n, sdL L n t = y := by
  cases n with
  | zero => exact ⟨PUnit.unit, (show y = 0 from hy).symm⟩
  | succ n =>
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩

def gf {K L : Cx.{1} W} (f : Cx.Hom K L (RingHom.id W)) (n : ℕ) : K.X n →ₗ[W] Sh L (n + 1) := f.f n

def cone {K L : Cx.{1} W} (f : Cx.Hom K L (RingHom.id W)) : Cx.{1} W where
  X n := K.X n × Sh L n
  d n := LinearMap.prod ((K.d n) ∘ₗ LinearMap.fst W _ _)
    (((gf f n) ∘ₗ LinearMap.fst W _ _) - (shD L n) ∘ₗ LinearMap.snd W _ _)
  dd n x := by
    refine Prod.ext (K.dd n x.1) ?_
    change gf f (n + 1) (K.d n x.1) - shD L (n + 1) (gf f n x.1 - shD L n x.2) = 0
    have e : shD L (n + 1) (gf f n x.1 - shD L n x.2) = gf f (n + 1) (K.d n x.1) := by
      have h1 : shD L (n + 1) (shD L n x.2) = 0 := d_shD L n x.2
      have h2 : shD L (n + 1) (gf f n x.1) = gf f (n + 1) (K.d n x.1) := f.comm n x.1
      rw [map_sub, h1, h2, sub_zero]
    rw [e, sub_self]

theorem shD_B (L : Cx.{1} W) (n : ℕ) (y : Sh L n) : sdL L n y ∈ L.B n := by
  cases n with
  | zero => exact Submodule.zero_mem _
  | succ n => exact ⟨y, rfl⟩

theorem cone_B_fst {K L : Cx.{1} W} (f : Cx.Hom K L (RingHom.id W)) (n : ℕ) (v : (cone f).X n)
    (hv : v ∈ (cone f).B n) : v.1 ∈ K.B n := by
  cases n with
  | zero =>
    have h : v = 0 := hv
    rw [h]
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨g, rfl⟩ := hv
    exact ⟨g.1, rfl⟩

theorem flat_sh {L : Cx.{1} W} {l m : ℕ} (hL : FlatL l m L) (n : ℕ) :
    (∀ y : Sh L n, ((l : W) ^ m) • y = 0) ∧
      ∀ a b, a + b = m → ∀ y : Sh L n, ((l : W) ^ b) • y = 0 → ∃ t : Sh L n, ((l : W) ^ a) • t = y := by
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ _ _ y _ => ⟨0, rfl⟩⟩
  | succ n => exact ⟨(hL n).1, fun a b h y hy => mem_lp.1 ((hL n).2 a b h y hy)⟩

theorem flat_cone {K L : Cx.{1} W} (f : Cx.Hom K L (RingHom.id W)) {l m : ℕ} (hK : FlatL l m K)
    (hL : FlatL l m L) : FlatL l m (cone f) := by
  intro i
  refine ⟨fun x => Prod.ext ((hK i).1 x.1) ((flat_sh hL i).1 x.2), fun a b h x hx => ?_⟩
  have h1 : ((l : W) ^ b) • x.1 = 0 := congrArg Prod.fst hx
  have h2 : ((l : W) ^ b) • x.2 = 0 := congrArg Prod.snd hx
  obtain ⟨s, hs⟩ := mem_lp.1 ((hK i).2 a b h _ h1)
  obtain ⟨t, ht⟩ := (flat_sh hL i).2 a b h _ h2
  exact mem_lp.2 ⟨(s, t), Prod.ext hs ht⟩

theorem cone_exact {K L : Cx.{1} W} (f : Cx.Hom K L (RingHom.id W))
    (hb : ∀ j, Function.Bijective (f.mapH j)) (n : ℕ) (x : (cone f).X n) (hx : (cone f).d n x = 0) :
    x ∈ (cone f).B n := by
  obtain ⟨x1, x2⟩ := x
  have h1 : K.d n x1 = 0 := congrArg Prod.fst hx
  have h2 : gf f n x1 - shD L n x2 = 0 := congrArg Prod.snd hx
  have h2' : f.f n x1 = sdL L n x2 := sub_eq_zero.1 h2
  have h3 : f.mapH n (K.cls x1 h1) = 0 := (Submodule.Quotient.mk_eq_zero ((L.B n).submoduleOf (L.Z n))).2 (by
    change f.f n x1 ∈ L.B n
    rw [h2']
    exact shD_B L n x2)
  have h4 : x1 ∈ K.B n :=
    (Submodule.Quotient.mk_eq_zero ((K.B n).submoduleOf (K.Z n))).1
      ((injective_iff_map_eq_zero _).1 (hb n).1 _ h3)
  cases n with
  | zero =>
    have h5 : x1 = 0 := h4
    exact Prod.ext h5 rfl
  | succ n =>
    change L.X n at x2
    obtain ⟨w, hw⟩ := h4
    have hw' : K.d n w = x1 := hw
    have h2'' : f.f (n + 1) x1 = L.d n x2 := h2'
    have h5 : L.d n (x2 - f.f n w) = 0 := by
      rw [map_sub, f.comm, hw', h2'', sub_self]
    obtain ⟨c, hc⟩ := (hb n).2 (L.cls _ h5)
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have h6 : f.f n z.1 - (x2 - f.f n w) ∈ L.B n :=
      (Submodule.Quotient.eq ((L.B n).submoduleOf (L.Z n))).1 hc
    obtain ⟨t, ht⟩ := B_shD L n _ h6
    refine ⟨(w + z.1, t), Prod.ext ?_ ?_⟩
    · change K.d n (w + z.1) = x1
      rw [map_add, hw', LinearMap.mem_ker.1 z.2, add_zero]
    · change f.f n (w + z.1) - sdL L n t = x2
      rw [ht, map_add]
      abel

section Main

variable {l : ℕ}

theorem prj_surj (L : Cx.{1} W) (n i : ℕ) : Function.Surjective ((prj l L n).f i) :=
  Submodule.mkQ_surjective _

theorem prj_zero (L : Cx.{1} W) (n i : ℕ) (x : L.X i) :
    (prj l L n).f i x = 0 ↔ x ∈ lpow (W := W) l (L.X i) n :=
  Submodule.Quotient.mk_eq_zero _

theorem redg_prj (L : Cx.{1} W) {b m : ℕ} (h : b ≤ m) (i : ℕ) (y : L.X i) :
    (redg l L h).f i ((prj l L m).f i y) = (prj l L b).f i y := rfl

theorem redg_surj (L : Cx.{1} W) {b m : ℕ} (h : b ≤ m) (i : ℕ) : Function.Surjective ((redg l L h).f i) := by
  intro z
  obtain ⟨y, rfl⟩ := prj_surj (l := l) L b i z
  exact ⟨(prj l L m).f i y, rfl⟩

theorem redg_zero (L : Cx.{1} W) {b m : ℕ} (h : b ≤ m) (i : ℕ) (w : (quo l L m).X i) :
    (redg l L h).f i w = 0 ↔ w ∈ lpow (W := W) l ((quo l L m).X i) b := by
  obtain ⟨y, rfl⟩ := prj_surj (l := l) L m i w
  constructor
  · intro hw
    obtain ⟨t, rfl⟩ := mem_lp.1 ((prj_zero L b i y).1 hw)
    exact mem_lp.2 ⟨(prj l L m).f i t, (map_smul _ _ _).symm⟩
  · intro hw
    obtain ⟨s, hs⟩ := mem_lp.1 hw
    obtain ⟨t, rfl⟩ := prj_surj (l := l) L m i s
    rw [← hs, map_smul, redg_prj, ← map_smul]
    exact (prj_zero L b i _).2 ⟨t, rfl⟩

theorem flat_quo {L : Cx.{1} W} {m : ℕ} (hL : FlatL l (m + 1) L) : FlatL l m (quo l L m) := by
  intro i
  refine ⟨fun x => ?_, fun a b h x hx => ?_⟩
  · obtain ⟨y, rfl⟩ := prj_surj (l := l) L m i x
    rw [← map_smul]
    exact (prj_zero L m i _).2 ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ := prj_surj (l := l) L m i x
    rw [← map_smul] at hx
    obtain ⟨t, ht⟩ := mem_lp.1 ((prj_zero L m i _).1 hx)
    have h1 : ((l : W) ^ b) • (y - ((l : W) ^ a) • t) = 0 := by
      rw [smul_sub, ← ht, smul_smul, ← pow_add, add_comm b a, h, sub_self]
    obtain ⟨s, hs⟩ := mem_lp.1 ((hL i).2 (a + 1) b (by omega) _ h1)
    refine mem_lp.2 ⟨(prj l L m).f i (t + (l : W) • s), ?_⟩
    rw [← map_smul]
    congr 1
    rw [smul_add, smul_smul, ← pow_succ, hs]
    abel

theorem prj_B (K : Cx.{1} W) (b j : ℕ) (v : K.X j) (hv : v ∈ K.B j) : (prj l K b).f j v ∈ (quo l K b).B j := by
  cases j with
  | zero =>
    have h : v = 0 := hv
    rw [h, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨g, rfl⟩ := hv
    exact ⟨(prj l K b).f j g, (prj l K b).comm j g⟩

theorem redg_B (L : Cx.{1} W) {b m : ℕ} (h : b ≤ m) (j : ℕ) (w : (quo l L m).X j)
    (hw : (redg l L h).f j w ∈ (quo l L b).B j) :
    ∃ t : Sh (quo l L m) j, ∃ s : (quo l L m).X j, ((l : W) ^ b) • s = w - sdL (quo l L m) j t := by
  cases j with
  | zero =>
    obtain ⟨s, hs⟩ := mem_lp.1 ((redg_zero L h 0 w).1 hw)
    exact ⟨PUnit.unit, s, by rw [hs]; exact (sub_zero w).symm⟩
  | succ j =>
    obtain ⟨g, hg⟩ := hw
    obtain ⟨g', rfl⟩ := redg_surj (l := l) L h j g
    have hg' : (quo l L b).d j ((redg l L h).f j g') = (redg l L h).f (j + 1) w := hg
    have h0 : (redg l L h).f (j + 1) (w - (quo l L m).d j g') = 0 := by
      rw [map_sub, ← (redg l L h).comm, hg', sub_self]
    obtain ⟨s, hs⟩ := mem_lp.1 ((redg_zero L h (j + 1) _).1 h0)
    exact ⟨g', s, hs⟩

theorem redg_shD (L : Cx.{1} W) {b m : ℕ} (h : b ≤ m) (j : ℕ) (t : Sh (quo l L m) j) :
    (redg l L h).f j (sdL (quo l L m) j t) ∈ (quo l L b).B j := by
  cases j with
  | zero =>
    have e : sdL (quo l L m) 0 t = 0 := rfl
    rw [e, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    exact ⟨(redg l L h).f j t, (redg l L h).comm j t⟩

end Main

theorem qred_bij : ∀ (W : Type) [CommRing W] (l : ℕ) (K L : Cx.{1} W) (m : ℕ)
    (f : Cx.Hom K (quo l L m) (RingHom.id W)), FlatL l m K → FlatL l (m + 1) L →
    (∀ j, Function.Bijective (f.mapH j)) →
    ∀ b (h : b ≤ m) j, Function.Bijective ((qred l f h).mapH j) := by
  intro W _ l K L m f hK hL hf b h j
  have E := exact_quo (cone f) l m (flat_cone f hK (flat_quo hL)) (cone_exact f hf)
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun u => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨x, hx⟩ := prj_surj (l := l) K b j z.1
    have hz : (quo l K b).d j z.1 = 0 := z.2
    have hdx : K.d j x ∈ lpow (W := W) l (K.X (j + 1)) b :=
      (prj_zero K b _ _).1 (by rw [← (prj l K b).comm, hx]; exact hz)
    have hB : (qred l f h).f j z.1 ∈ (quo l L b).B j :=
      (Submodule.Quotient.mk_eq_zero (((quo l L b).B j).submoduleOf ((quo l L b).Z j))).1 hu
    rw [← hx] at hB
    obtain ⟨t, s, hts⟩ := redg_B L h j (f.f j x) hB
    obtain ⟨p, hp⟩ := mem_lp.1 hdx
    have hdc : (cone f).d j (x, t) ∈ lpow (W := W) l ((cone f).X (j + 1)) b :=
      mem_lp.2 ⟨(p, s), Prod.ext hp hts⟩
    obtain ⟨u1, v, hv, e⟩ := E j b h (x, t) hdc
    have e1 : x = ((l : W) ^ b) • u1.1 + v.1 := congrArg Prod.fst e
    refine (Submodule.Quotient.mk_eq_zero (((quo l K b).B j).submoduleOf ((quo l K b).Z j))).2 ?_
    change z.1 ∈ (quo l K b).B j
    have e2 : z.1 = (prj l K b).f j v.1 := by
      have e3 : (prj l K b).f j (((l : W) ^ b) • u1.1) = 0 := (prj_zero K b j _).2 ⟨u1.1, rfl⟩
      rw [← hx, e1, map_add, e3, zero_add]
    rw [e2]
    exact prj_B K b j _ (cone_B_fst f j v hv)
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨w, hw⟩ := redg_surj (l := l) L h j z.1
    have hz : (quo l L b).d j z.1 = 0 := z.2
    have hdw : (quo l L m).d j w ∈ lpow (W := W) l ((quo l L m).X (j + 1)) b :=
      (redg_zero L h _ _).1 (by rw [← (redg l L h).comm, hw]; exact hz)
    obtain ⟨p, hp⟩ := mem_lp.1 hdw
    have hdc : (cone f).d (j + 1) ((0, w) : K.X (j + 1) × Sh (quo l L m) (j + 1)) ∈
        lpow (W := W) l ((cone f).X (j + 1 + 1)) b := by
      refine mem_lp.2 ⟨(0, -p), Prod.ext ?_ ?_⟩
      · change ((l : W) ^ b) • (0 : K.X (j + 1 + 1)) = K.d (j + 1) 0
        rw [smul_zero, map_zero]
      · change ((l : W) ^ b) • (-p) = (f.f (j + 1) 0) - (quo l L m).d j w
        rw [smul_neg, hp, map_zero, zero_sub]
    obtain ⟨⟨u1, u2⟩, v, ⟨⟨g1, g2⟩, rfl⟩, e⟩ := E (j + 1) b h (0, w) hdc
    change (quo l L m).X j at u2
    have e1 : 0 = ((l : W) ^ b) • u1 + K.d j g1 := congrArg Prod.fst e
    have e2 : w = ((l : W) ^ b) • u2 + (f.f j g1 - sdL (quo l L m) j g2) := congrArg Prod.snd e
    have hc : (quo l K b).d j ((prj l K b).f j g1) = 0 := by
      rw [(prj l K b).comm]
      exact (prj_zero K b _ _).2 ⟨-u1, by
        change ((l : W) ^ b) • (-u1) = K.d j g1
        rw [smul_neg]
        exact neg_eq_of_add_eq_zero_right e1.symm⟩
    refine ⟨(quo l K b).cls _ hc, (Submodule.Quotient.eq (((quo l L b).B j).submoduleOf ((quo l L b).Z j))).2 ?_⟩
    change (qred l f h).f j ((prj l K b).f j g1) - z.1 ∈ (quo l L b).B j
    have e3 : (qred l f h).f j ((prj l K b).f j g1) - z.1 = (redg l L h).f j (sdL (quo l L m) j g2) := by
      have e4 : (redg l L h).f j (((l : W) ^ b) • u2) = 0 := (redg_zero L h j _).2 ⟨u2, rfl⟩
      have e5 : (qred l f h).f j ((prj l K b).f j g1) = (redg l L h).f j (f.f j g1) := rfl
      rw [← hw, e2, map_add, e4, zero_add, map_sub, e5]
      abel
    rw [e3]
    exact redg_shD L h j g2

end GlobalTheory.CompanionTheory.QredFlat
