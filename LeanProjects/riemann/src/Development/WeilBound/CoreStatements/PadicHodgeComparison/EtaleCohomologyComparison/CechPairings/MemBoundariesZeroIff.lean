import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.CechClassBoundaries
variable {R : Type} [CommRing R]

theorem cls_eq {K : Cx.{w} R} {n : ℕ} (a b : K.X n) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb ↔ a - b ∈ K.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

theorem cls_eq_zero {K : Cx.{w} R} {n : ℕ} (a : K.X n) (ha : K.d n a = 0) :
    K.cls a ha = 0 ↔ a ∈ K.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem clsSurj {K : Cx.{w} R} {n : ℕ} (z : K.H n) : ∃ a ha, z = K.cls a ha := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨a, ha, rfl⟩

theorem cls_add {K : Cx.{w} R} {n : ℕ} (a b : K.X n) (ha : K.d n a = 0) (hb : K.d n b = 0) (h) :
    K.cls (a + b) h = K.cls a ha + K.cls b hb := rfl

theorem cls_sub {K : Cx.{w} R} {n : ℕ} (a b : K.X n) (ha : K.d n a = 0) (hb : K.d n b = 0) (h) :
    K.cls (a - b) h = K.cls a ha - K.cls b hb := rfl

theorem cls_smul {K : Cx.{w} R} {n : ℕ} (r : R) (a : K.X n) (ha : K.d n a = 0) (h) :
    K.cls (r • a) h = r • K.cls a ha := rfl

theorem cls_zero' {K : Cx.{w} R} {n : ℕ} (h) : K.cls (n := n) 0 h = 0 := rfl

theorem mem_boundaries_zero_iff {K : Cx.{w} R} (a : K.X 0) : a ∈ K.B 0 ↔ a = 0 := by
  show a ∈ (⊥ : Submodule R (K.X 0)) ↔ _
  exact Submodule.mem_bot R

theorem mem_Bs {K : Cx.{w} R} {n : ℕ} (a : K.X (n + 1)) : a ∈ K.B (n + 1) ↔ ∃ b, K.d n b = a := Iff.rfl

theorem class_zero_eq_zero_iff {K : Cx.{w} R} (a : K.X 0) (ha : K.d 0 a = 0) : K.cls a ha = 0 ↔ a = 0 := by
  rw [cls_eq_zero, mem_boundaries_zero_iff]

theorem mapH_cls' {R' : Type} [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) {n : ℕ} (a : K.X n) (ha : K.d n a = 0) (hb : L.d n (φ.f n a) = 0) :
    φ.mapH n (K.cls a ha) = L.cls (φ.f n a) hb := rfl

theorem cyc {R' : Type} [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) {n : ℕ} (a : K.X n) (ha : K.d n a = 0) : L.d n (φ.f n a) = 0 := by
  rw [φ.comm, ha, map_zero]

end CrystallineSemistableComparison.CechClassBoundaries
open CrystallineSemistableComparison.CechClassBoundaries

namespace CrystallineSemistableComparison.CechClassBoundaries
variable {R : Type} [CommRing R]

section LES
variable {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R}

theorem gf (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) {n : ℕ} (x : K.X n) : g.f n (f.f n x) = 0 :=
  (hfg n _).2 ⟨x, rfl⟩

theorem conn_ex (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) {n : ℕ} (y : L.X n) (hz : M.d n (g.f n y) = 0) :
    ∃ x : K.X (n + 1), f.f (n + 1) x = L.d n y :=
  (hfg (n + 1) _).1 (by rw [← g.comm, hz])

theorem conn_cyc (f : Cx.Hom K L (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) {n : ℕ}
    (y : L.X n) (x : K.X (n + 1)) (hx : f.f (n + 1) x = L.d n y) : K.d (n + 1) x = 0 := by
  apply hf (n + 2); rw [← f.comm, hx, L.dd, map_zero]

theorem conn_wd (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) {n : ℕ}
    (y y' : L.X n) (x x' : K.X (n + 1)) (hx : K.d (n + 1) x = 0) (hx' : K.d (n + 1) x' = 0)
    (e : g.f n y = g.f n y') (h : f.f (n + 1) x = L.d n y) (h' : f.f (n + 1) x' = L.d n y') :
    K.cls x hx = K.cls x' hx' := by
  rw [cls_eq, mem_Bs]
  obtain ⟨u, hu⟩ := (hfg n (y - y')).1 (by rw [map_sub, e, sub_self])
  refine ⟨u, hf (n + 1) ?_⟩
  rw [← f.comm, hu, map_sub, map_sub, h, h']

theorem lift_ex (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) (hg : ∀ n, Function.Surjective (g.f n)) {n : ℕ}
    (m : M.X n) (hm : M.d n m = 0) : ∃ y : L.X n, ∃ x : K.X (n + 1), g.f n y = m ∧ f.f (n + 1) x = L.d n y := by
  obtain ⟨y, rfl⟩ := hg n m
  obtain ⟨x, hx⟩ := conn_ex f g hfg y hm
  exact ⟨y, x, rfl, hx⟩

noncomputable def dfun (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) {n : ℕ} (m : M.X n) (hm : M.d n m = 0) : K.H (n + 1) :=
  K.cls (lift_ex f g hfg hg m hm).choose_spec.choose
    (conn_cyc f hf _ _ (lift_ex f g hfg hg m hm).choose_spec.choose_spec.2)

theorem dfun_spec (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) {n : ℕ} (m : M.X n) (hm : M.d n m = 0)
    (y : L.X n) (x : K.X (n + 1)) (hx : K.d (n + 1) x = 0) (hy : g.f n y = m) (h : f.f (n + 1) x = L.d n y) :
    dfun f g hf hfg hg m hm = K.cls x hx :=
  conn_wd f g hf hfg _ _ _ _ _ _ (by rw [(lift_ex f g hfg hg m hm).choose_spec.choose_spec.1, hy])
    (lift_ex f g hfg hg m hm).choose_spec.choose_spec.2 h

noncomputable def dZ (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (n : ℕ) : M.Z n →ₗ[R] K.H (n + 1) where
  toFun m := dfun f g hf hfg hg m.1 m.2
  map_add' m₁ m₂ := by
    obtain ⟨y₁, x₁, e₁, h₁⟩ := lift_ex f g hfg hg m₁.1 m₁.2
    obtain ⟨y₂, x₂, e₂, h₂⟩ := lift_ex f g hfg hg m₂.1 m₂.2
    have c₁ := conn_cyc f hf _ _ h₁
    have c₂ := conn_cyc f hf _ _ h₂
    rw [dfun_spec f g hf hfg hg _ _ y₁ x₁ c₁ e₁ h₁, dfun_spec f g hf hfg hg _ _ y₂ x₂ c₂ e₂ h₂,
      dfun_spec f g hf hfg hg _ _ (y₁ + y₂) (x₁ + x₂) (by rw [map_add, c₁, c₂, add_zero])
        (by rw [map_add, e₁, e₂]; rfl) (by rw [map_add, map_add, h₁, h₂])]
    rfl
  map_smul' r m := by
    obtain ⟨y, x, e, h⟩ := lift_ex f g hfg hg m.1 m.2
    have c := conn_cyc f hf _ _ h
    rw [dfun_spec f g hf hfg hg _ _ y x c e h,
      dfun_spec f g hf hfg hg _ _ (r • y) (r • x) (by rw [map_smul, c, smul_zero])
        (by rw [map_smul, e]; rfl) (by rw [map_smul, map_smul, h])]
    rfl

theorem dZ_B (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (n : ℕ) (m : M.Z n) (hm : m.1 ∈ M.B n) :
    dZ f g hf hfg hg n m = 0 := by
  show dfun f g hf hfg hg m.1 m.2 = 0
  cases n with
  | zero =>
    rw [mem_boundaries_zero_iff] at hm
    rw [dfun_spec f g hf hfg hg _ _ 0 0 (map_zero _) (by rw [map_zero, hm]) (by rw [map_zero, map_zero])]
    rfl
  | succ k =>
    obtain ⟨m₀, hm₀⟩ := (mem_Bs _).1 hm
    obtain ⟨y₀, rfl⟩ := hg k m₀
    rw [dfun_spec f g hf hfg hg _ _ (L.d k y₀) 0 (map_zero _) (by rw [← g.comm, hm₀]) (by rw [map_zero, L.dd])]
    rfl

noncomputable def dH (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (n : ℕ) : M.H n →ₗ[R] K.H (n + 1) :=
  Submodule.liftQ _ (dZ f g hf hfg hg n) (fun m hm => by
    rw [LinearMap.mem_ker]; exact dZ_B f g hf hfg hg n m hm)

theorem dH_char (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (n : ℕ) (y : L.X n) (x : K.X (n + 1)) (hz : M.d n (g.f n y) = 0)
    (hx : K.d (n + 1) x = 0) (h : f.f (n + 1) x = L.d n y) :
    dH f g hf hfg hg n (M.cls (g.f n y) hz) = K.cls x hx :=
  dfun_spec f g hf hfg hg _ hz y x hx rfl h

end LES

theorem pow3 {M : Type w} [AddCommGroup M] [Module R M] (s : R) (x : M) : s ^ 3 • x = s • s • s • x := by
  simp only [smul_smul, pow_succ, pow_zero, one_mul, mul_assoc]

theorem sqH {A : Cx.{w} R} {B : Cx.{w'} R} {C : Cx.{w''} R} {D : Cx.{t} R}
    (φ : Cx.Hom A B (RingHom.id R)) (ψ : Cx.Hom B D (RingHom.id R)) (φ' : Cx.Hom A C (RingHom.id R))
    (ψ' : Cx.Hom C D (RingHom.id R)) (h : ∀ n x, ψ.f n (φ.f n x) = ψ'.f n (φ'.f n x)) (n : ℕ) (z : A.H n) :
    ψ.mapH n (φ.mapH n z) = ψ'.mapH n (φ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := clsSurj z
  rw [mapH_cls' φ _ hx (cyc φ _ hx), mapH_cls' ψ _ _ (cyc ψ _ (cyc φ _ hx)),
    mapH_cls' φ' _ hx (cyc φ' _ hx), mapH_cls' ψ' _ _ (cyc ψ' _ (cyc φ' _ hx)), cls_eq, h, sub_self]
  exact zero_mem _

theorem dnat {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} {K' : Cx.{t} R} {L' : Cx.{t'} R} {M' : Cx.{u} R}
    (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R))
    (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n))
    (f' : Cx.Hom K' L' (RingHom.id R)) (g' : Cx.Hom L' M' (RingHom.id R))
    (a : Cx.Hom K K' (RingHom.id R)) (b : Cx.Hom L L' (RingHom.id R)) (c : Cx.Hom M M' (RingHom.id R))
    (hab : ∀ n x, b.f n (f.f n x) = f'.f n (a.f n x)) (hbc : ∀ n x, c.f n (g.f n x) = g'.f n (b.f n x))
    (δ : ∀ n, M.H n →ₗ[R] K.H (n + 1)) (δ' : ∀ n, M'.H n →ₗ[R] K'.H (n + 1))
    (hδ : ∀ n (y : L.X n) (x : K.X (n + 1)) (hz : M.d n (g.f n y) = 0) (hx : K.d (n + 1) x = 0),
      f.f (n + 1) x = L.d n y → δ n (M.cls (g.f n y) hz) = K.cls x hx)
    (hδ' : ∀ n (y : L'.X n) (x : K'.X (n + 1)) (hz : M'.d n (g'.f n y) = 0) (hx : K'.d (n + 1) x = 0),
      f'.f (n + 1) x = L'.d n y → δ' n (M'.cls (g'.f n y) hz) = K'.cls x hx)
    (n : ℕ) (w : M.H n) : δ' n (c.mapH n w) = a.mapH (n + 1) (δ n w) := by
  obtain ⟨m, hm, rfl⟩ := clsSurj w
  obtain ⟨y, rfl⟩ := hg n m
  obtain ⟨x, hx⟩ := conn_ex f g hfg y hm
  have hxc := conn_cyc f hf y x hx
  rw [hδ n y x hm hxc hx, mapH_cls' a _ hxc (cyc a _ hxc)]
  have h2 : M'.d n (g'.f n (b.f n y)) = 0 := by rw [← hbc]; exact cyc c _ hm
  have e1 : c.mapH n (M.cls (g.f n y) hm) = M'.cls (g'.f n (b.f n y)) h2 := by
    rw [mapH_cls' c _ hm (cyc c _ hm), cls_eq, hbc, sub_self]
    exact zero_mem _
  rw [e1]
  exact hδ' n (b.f n y) (a.f (n + 1) x) h2 _ (by rw [← hab, hx, b.comm])

theorem kill_iff {K : Cx.{w} R} (s : R) (n : ℕ) :
    ExactUpTo s (K.d n) (K.d (n + 1)) ↔ ∀ z : K.H (n + 1), s • z = 0 := by
  constructor
  · intro h z
    obtain ⟨y, hy, rfl⟩ := clsSurj z
    obtain ⟨x, hx⟩ := h y hy
    rw [← cls_smul (h := by rw [map_smul, hy, smul_zero]), cls_eq_zero, mem_Bs]
    exact ⟨x, hx⟩
  · intro h y hy
    have := h (K.cls y hy)
    rw [← cls_smul (h := by rw [map_smul, hy, smul_zero]), cls_eq_zero, mem_Bs] at this
    exact this

end CrystallineSemistableComparison.CechClassBoundaries

theorem CrystallineSemistableComparison.P.les : ∀ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) (hg : ∀ n, Function.Surjective (g.f n)), ∃ δ : ∀ n, M.H n →ₗ[R] K.H (n + 1), (∀ n (y : L.X n) (x : K.X (n + 1)) hz hx, f.f (n + 1) x = L.d n y → δ n (M.cls (g.f n y) hz) = K.cls x hx) ∧ Function.Injective (f.mapH 0) ∧ (∀ n, Function.Exact (f.mapH n) (g.mapH n)) ∧ (∀ n, Function.Exact (g.mapH n) (δ n)) ∧ ∀ n, Function.Exact (δ n) (f.mapH (n + 1)) := by
  intro R _ K L M f g hf hfg hg
  have char := dH_char f g hf hfg hg
  refine ⟨dH f g hf hfg hg, char, ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨a, ha, rfl⟩ := clsSurj z
    rw [mapH_cls' f _ ha (cyc f _ ha), class_zero_eq_zero_iff] at hz
    rw [class_zero_eq_zero_iff]
    exact hf 0 (by rw [hz, map_zero])
  · intro z
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := clsSurj z
      rw [mapH_cls' g _ hy (cyc g _ hy), cls_eq_zero] at h
      cases n with
      | zero =>
        rw [mem_boundaries_zero_iff] at h
        obtain ⟨x, rfl⟩ := (hfg 0 y).1 h
        have hxc : K.d 0 x = 0 := hf 1 (by rw [← f.comm, hy, map_zero])
        exact ⟨K.cls x hxc, rfl⟩
      | succ k =>
        obtain ⟨m₀, hm₀⟩ := (mem_Bs _).1 h
        obtain ⟨y₀, rfl⟩ := hg k m₀
        have e : g.f (k + 1) (y - L.d k y₀) = 0 := by rw [map_sub, ← g.comm, hm₀, sub_self]
        obtain ⟨x, hx⟩ := (hfg _ _).1 e
        have hxc : K.d (k + 1) x = 0 := hf _ (by rw [← f.comm, hx, map_sub, hy, L.dd, sub_self, map_zero])
        refine ⟨K.cls x hxc, ?_⟩
        rw [mapH_cls' f _ hxc (cyc f _ hxc), cls_eq, mem_Bs]
        exact ⟨-y₀, by rw [hx, map_neg]; abel⟩
    · rintro ⟨z', rfl⟩
      obtain ⟨x, hx, rfl⟩ := clsSurj z'
      rw [mapH_cls' f _ hx (cyc f _ hx), mapH_cls' g _ (cyc f _ hx) (cyc g _ (cyc f _ hx)), cls_eq_zero,
        gf f g hfg]
      exact zero_mem _
  · intro w
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := clsSurj w
      obtain ⟨y, rfl⟩ := hg n m
      obtain ⟨x, hx⟩ := conn_ex f g hfg y hm
      rw [char n y x hm (conn_cyc f hf y x hx) hx, cls_eq_zero, mem_Bs] at h
      obtain ⟨u, hu⟩ := h
      have hc : L.d n (y - f.f n u) = 0 := by rw [map_sub, f.comm, hu, hx, sub_self]
      refine ⟨L.cls _ hc, ?_⟩
      rw [mapH_cls' g _ hc (cyc g _ hc), cls_eq, map_sub, gf f g hfg, sub_zero, sub_self]
      exact zero_mem _
    · rintro ⟨z, rfl⟩
      obtain ⟨y, hy, rfl⟩ := clsSurj z
      rw [mapH_cls' g _ hy (cyc g _ hy), char n y 0 _ (map_zero _) (by rw [map_zero, hy])]
      rfl
  · intro k
    constructor
    · intro h
      obtain ⟨x, hx, rfl⟩ := clsSurj k
      rw [mapH_cls' f _ hx (cyc f _ hx), cls_eq_zero, mem_Bs] at h
      obtain ⟨y, hy⟩ := h
      have hz : M.d n (g.f n y) = 0 := by rw [g.comm, hy, gf f g hfg]
      exact ⟨M.cls _ hz, char n y x hz hx hy.symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨m, hm, rfl⟩ := clsSurj w
      obtain ⟨y, rfl⟩ := hg n m
      obtain ⟨x, hx⟩ := conn_ex f g hfg y hm
      have hxc := conn_cyc f hf y x hx
      rw [char n y x hm hxc hx, mapH_cls' f _ hxc (cyc f _ hxc), cls_eq_zero, mem_Bs]
      exact ⟨y, hx.symm⟩

theorem CrystallineSemistableComparison.P.five : ∀ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) (hg : ∀ n, Function.Surjective (g.f n)) {K' : Cx.{t} R} {L' : Cx.{t'} R} {M' : Cx.{u} R} (f' : Cx.Hom K' L' (RingHom.id R)) (g' : Cx.Hom L' M' (RingHom.id R)) (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n)) (hg' : ∀ n, Function.Surjective (g'.f n)) (a : Cx.Hom K K' (RingHom.id R)) (b : Cx.Hom L L' (RingHom.id R)) (c : Cx.Hom M M' (RingHom.id R)) (hab : ∀ n x, b.f n (f.f n x) = f'.f n (a.f n x)) (hbc : ∀ n x, c.f n (g.f n x) = g'.f n (b.f n x)) (s : R), ((∀ n, UpTo s (a.mapH n)) → (∀ n, UpTo s (c.mapH n)) → ∀ n, UpTo (s ^ 3) (b.mapH n)) ∧ ((∀ n, UpTo s (b.mapH n)) → (∀ n, UpTo s (c.mapH n)) → ∀ n, UpTo (s ^ 3) (a.mapH n)) ∧ ((∀ n, UpTo s (a.mapH n)) → (∀ n, UpTo s (b.mapH n)) → ∀ n, UpTo (s ^ 3) (c.mapH n)) := by
  intro R _ K L M f g hf hfg hg K' L' M' f' g' hf' hfg' hg' a b c hab hbc s
  obtain ⟨δ, hδ, i0, e1, e2, e3⟩ := CrystallineSemistableComparison.P.les f g hf hfg hg
  obtain ⟨δ', hδ', i0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have sq1 : ∀ n k, b.mapH n (f.mapH n k) = f'.mapH n (a.mapH n k) := sqH f b a f' hab
  have sq2 : ∀ n z, c.mapH n (g.mapH n z) = g'.mapH n (b.mapH n z) := sqH g c b g' hbc
  have sq3 : ∀ n w, δ' n (c.mapH n w) = a.mapH (n + 1) (δ n w) :=
    dnat f g hf hfg hg f' g' a b c hab hbc δ δ' hδ hδ'
  refine ⟨fun ha hc n => ⟨fun z hz => ?_, fun z' => ?_⟩, fun hb hc n => ⟨fun k hk => ?_, fun k' => ?_⟩,
    fun ha hb n => ⟨fun w hw => ?_, fun w' => ?_⟩⟩
  ·
    have h1 : c.mapH n (g.mapH n z) = 0 := by rw [sq2, hz, map_zero]
    have h2 := (hc n).1 _ h1
    rw [← map_smul (g.mapH n)] at h2
    obtain ⟨k, hk⟩ := (e1 n _).1 h2
    have h3 : f'.mapH n (a.mapH n k) = 0 := by rw [← sq1, hk, map_smul, hz, smul_zero]
    cases n with
    | zero =>
      have h4 : a.mapH 0 k = 0 := (injective_iff_map_eq_zero _).1 i0' _ h3
      have h5 := (ha 0).1 _ h4
      rw [pow3, ← hk, ← map_smul (f.mapH 0), ← map_smul (f.mapH 0), h5, smul_zero, map_zero]
    | succ j =>
      obtain ⟨w', hw'⟩ := (e3' j _).1 h3
      obtain ⟨w, hw⟩ := (hc j).2 w'
      have h6 : a.mapH (j + 1) (s • k - δ j w) = 0 := by
        rw [map_sub, map_smul, ← sq3, hw, map_smul, hw', sub_self]
      have h7 := (ha (j + 1)).1 _ h6
      rw [smul_sub, sub_eq_zero] at h7
      have h8 : f.mapH (j + 1) (δ j w) = 0 := (e3 j _).2 ⟨w, rfl⟩
      rw [pow3, ← hk, ← map_smul (f.mapH (j + 1)), ← map_smul (f.mapH (j + 1)), h7, map_smul, h8, smul_zero]
  ·
    obtain ⟨w, hw⟩ := (hc n).2 (g'.mapH n z')
    have h1 : a.mapH (n + 1) (δ n w) = 0 := by rw [← sq3, hw, map_smul, (e2' n _).2 ⟨z', rfl⟩, smul_zero]
    have h2 := (ha (n + 1)).1 _ h1
    rw [← map_smul (δ n)] at h2
    obtain ⟨z, hz⟩ := (e2 n _).1 h2
    have h3 : g'.mapH n (b.mapH n z - s ^ 2 • z') = 0 := by
      rw [map_sub, ← sq2, hz, map_smul, hw, map_smul, smul_smul, pow_two, sub_self]
    obtain ⟨k', hk'⟩ := (e1' n _).1 h3
    obtain ⟨k, hk⟩ := (ha n).2 k'
    refine ⟨s • z - f.mapH n k, ?_⟩
    rw [map_sub, map_smul, sq1, hk, map_smul, hk', smul_sub, sub_sub_cancel, smul_smul, ← pow_succ']
  ·
    have h1 : b.mapH n (f.mapH n k) = 0 := by rw [sq1, hk, map_zero]
    have h2 := (hb n).1 _ h1
    rw [← map_smul (f.mapH n)] at h2
    cases n with
    | zero =>
      have h3 : s • k = 0 := (injective_iff_map_eq_zero _).1 i0 _ h2
      rw [pow3, h3, smul_zero, smul_zero]
    | succ j =>
      obtain ⟨w, hw⟩ := (e3 j _).1 h2
      have h3 : δ' j (c.mapH j w) = 0 := by rw [sq3, hw, map_smul, hk, smul_zero]
      obtain ⟨z', hz'⟩ := (e2' j _).1 h3
      obtain ⟨z, hz⟩ := (hb j).2 z'
      have h4 : c.mapH j (g.mapH j z - s • w) = 0 := by
        rw [map_sub, sq2, hz, map_smul, hz', map_smul, sub_self]
      have h5 := (hc j).1 _ h4
      rw [smul_sub, sub_eq_zero] at h5
      rw [pow3, ← hw, ← map_smul (δ j), ← map_smul (δ j), ← h5, ← map_smul (g.mapH j), (e2 j _).2 ⟨_, rfl⟩]
  ·
    obtain ⟨z, hz⟩ := (hb n).2 (f'.mapH n k')
    have h1 : c.mapH n (g.mapH n z) = 0 := by
      rw [sq2, hz, map_smul, (e1' n _).2 ⟨k', rfl⟩, smul_zero]
    have h2 := (hc n).1 _ h1
    rw [← map_smul (g.mapH n)] at h2
    obtain ⟨k, hk⟩ := (e1 n _).1 h2
    have h3 : f'.mapH n (a.mapH n k - s ^ 2 • k') = 0 := by
      rw [map_sub, ← sq1, hk, map_smul, hz, map_smul, smul_smul, pow_two, sub_self]
    cases n with
    | zero =>
      have h4 := (injective_iff_map_eq_zero _).1 i0' _ h3
      rw [sub_eq_zero] at h4
      refine ⟨s • k, ?_⟩
      rw [map_smul, h4, smul_smul, ← pow_succ']
    | succ j =>
      obtain ⟨w', hw'⟩ := (e3' j _).1 h3
      obtain ⟨w, hw⟩ := (hc j).2 w'
      refine ⟨s • k - δ j w, ?_⟩
      rw [map_sub, map_smul, ← sq3, hw, map_smul, hw', smul_sub, sub_sub_cancel, smul_smul, ← pow_succ']
  ·
    have h1 : a.mapH (n + 1) (δ n w) = 0 := by rw [← sq3, hw, map_zero]
    have h2 := (ha (n + 1)).1 _ h1
    rw [← map_smul (δ n)] at h2
    obtain ⟨z, hz⟩ := (e2 n _).1 h2
    have h3 : g'.mapH n (b.mapH n z) = 0 := by rw [← sq2, hz, map_smul, hw, smul_zero]
    obtain ⟨k', hk'⟩ := (e1' n _).1 h3
    obtain ⟨k, hk⟩ := (ha n).2 k'
    have h4 : b.mapH n (s • z - f.mapH n k) = 0 := by
      rw [map_sub, map_smul, sq1, hk, map_smul, hk', sub_self]
    have h5 := (hb n).1 _ h4
    rw [smul_sub, sub_eq_zero] at h5
    rw [pow3, ← hz, ← map_smul (g.mapH n), ← map_smul (g.mapH n), h5, map_smul, (e1 n _).2 ⟨k, rfl⟩, smul_zero]
  ·
    obtain ⟨k, hk⟩ := (ha (n + 1)).2 (δ' n w')
    have h1 : b.mapH (n + 1) (f.mapH (n + 1) k) = 0 := by
      rw [sq1, hk, map_smul, (e3' n _).2 ⟨w', rfl⟩, smul_zero]
    have h2 := (hb (n + 1)).1 _ h1
    rw [← map_smul (f.mapH (n + 1))] at h2
    obtain ⟨w, hw⟩ := (e3 n _).1 h2
    have h3 : δ' n (c.mapH n w - s ^ 2 • w') = 0 := by
      rw [map_sub, sq3, hw, map_smul, hk, map_smul, smul_smul, pow_two, sub_self]
    obtain ⟨z', hz'⟩ := (e2' n _).1 h3
    obtain ⟨z, hz⟩ := (hb n).2 z'
    refine ⟨s • w - g.mapH n z, ?_⟩
    rw [map_sub, map_smul, sq2, hz, map_smul, hz', smul_sub, sub_sub_cancel, smul_smul, ← pow_succ']

theorem CrystallineSemistableComparison.P.res_2of3 : ∀ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (f : Cx.Hom K L (RingHom.id R)) (g : Cx.Hom L M (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n)) (hg : ∀ n, Function.Surjective (g.f n)) {A : Type t} {B : Type t'} {D : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module R A] [Module R B] [Module R D] (i : A →ₗ[R] B) (p : B →ₗ[R] D) (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p) (a : A →ₗ[R] K.X 0) (b : B →ₗ[R] L.X 0) (c : D →ₗ[R] M.X 0) (hab : ∀ x, b (i x) = f.f 0 (a x)) (hbc : ∀ x, c (p x) = g.f 0 (b x)) (hb : ∀ x, L.d 0 (b x) = 0) (s : R), (K.ResUpTo s a → M.ResUpTo s c → L.ResUpTo (s ^ 3) b) ∧ (L.ResUpTo s b → M.ResUpTo s c → K.ResUpTo (s ^ 3) a) ∧ (K.ResUpTo s a → L.ResUpTo s b → M.ResUpTo (s ^ 3) c) := by
  intro R _ K L M f g hf hfg hg A B D _ _ _ _ _ _ i p hi hip hp a b c hab hbc hb s
  obtain ⟨δ, hδ, i0, e1, e2, e3⟩ := CrystallineSemistableComparison.P.les f g hf hfg hg
  have ha0 : ∀ x, K.d 0 (a x) = 0 := fun x => hf 1 (by rw [map_zero, ← f.comm, ← hab, hb])
  have hc0 : ∀ x, M.d 0 (c x) = 0 := by
    intro x
    obtain ⟨x', rfl⟩ := hp x
    rw [hbc, g.comm, hb, map_zero]
  refine ⟨fun ⟨_, ka1, ka2, ka3⟩ ⟨_, mc1, mc2, mc3⟩ => ⟨hb, fun x hx => ?_, fun y hy => ?_, fun n => (kill_iff _ _).2 fun z => ?_⟩,
    fun ⟨_, lb1, lb2, lb3⟩ ⟨_, mc1, mc2, mc3⟩ => ⟨ha0, fun x hx => ?_, fun k hk => ?_, fun n => (kill_iff _ _).2 fun z => ?_⟩,
    fun ⟨_, ka1, ka2, ka3⟩ ⟨_, lb1, lb2, lb3⟩ => ⟨hc0, fun e he => ?_, fun m hm => ?_, fun n => (kill_iff _ _).2 fun w => ?_⟩⟩
  · have h1 : c (p x) = 0 := by rw [hbc, hx, map_zero]
    have h2 := mc1 _ h1
    rw [← map_smul p] at h2
    obtain ⟨y, hy⟩ := (hip _).1 h2
    have h3 : f.f 0 (a y) = 0 := by rw [← hab, hy, map_smul, hx, smul_zero]
    have h4 : a y = 0 := (injective_iff_map_eq_zero _).1 (hf 0) _ h3
    have h5 := ka1 _ h4
    rw [pow3, ← hy, ← map_smul i, h5, map_zero, smul_zero]
  · obtain ⟨e, he⟩ := mc2 (g.f 0 y) (cyc g _ hy)
    obtain ⟨x', rfl⟩ := hp e
    rw [hbc] at he
    obtain ⟨k, hk⟩ := (hfg 0 (s • y - b x')).1 (by rw [map_sub, map_smul, he, sub_self])
    have hkc : K.d 0 k = 0 := hf 1 (by rw [map_zero, ← f.comm, hk, map_sub, map_smul, hy, hb, smul_zero, sub_zero])
    obtain ⟨a0, ha0'⟩ := ka2 k hkc
    have e1 : b (i a0) = s • (s • y - b x') := by rw [hab, ha0', map_smul, hk]
    refine ⟨s • i a0 + s • s • x', ?_⟩
    simp only [map_add, map_smul]
    rw [e1, pow3, smul_sub, smul_sub, sub_add_cancel]
  · have hMk := (kill_iff _ _).1 (mc3 n) (g.mapH (n + 1) z)
    rw [← map_smul (g.mapH (n + 1))] at hMk
    obtain ⟨k, hk⟩ := (e1 (n + 1) _).1 hMk
    have h1 := (kill_iff _ _).1 (ka3 n) k
    rw [pow3, ← hk, ← map_smul (f.mapH (n + 1)), h1, map_zero, smul_zero]
  · have h1 : b (i x) = 0 := by rw [hab, hx, map_zero]
    have h2 := lb1 _ h1
    rw [← map_smul i] at h2
    have h3 : s • x = 0 := (injective_iff_map_eq_zero _).1 hi _ h2
    rw [pow3, h3, smul_zero, smul_zero]
  · obtain ⟨x, hx⟩ := lb2 (f.f 0 k) (cyc f _ hk)
    have h1 : c (p x) = 0 := by rw [hbc, hx, map_smul, gf f g hfg, smul_zero]
    have h2 := mc1 _ h1
    rw [← map_smul p] at h2
    obtain ⟨y, hy⟩ := (hip _).1 h2
    have e : f.f 0 (a y) = f.f 0 (s • s • k) := by
      rw [← hab, hy]
      simp only [map_smul, hx]
    refine ⟨s • y, ?_⟩
    rw [map_smul, hf 0 e, pow3]
  · have h1 := (kill_iff _ _).1 (lb3 n) (f.mapH (n + 1) z)
    rw [← map_smul (f.mapH (n + 1))] at h1
    obtain ⟨w, hw⟩ := (e3 n _).1 h1
    have h2 : δ n (s • w) = 0 := by
      cases n with
      | zero =>
        obtain ⟨m, hm, rfl⟩ := clsSurj w
        obtain ⟨e, he⟩ := mc2 m hm
        obtain ⟨x, rfl⟩ := hp e
        have hsm : M.d 0 (s • m) = 0 := by rw [map_smul, hm, smul_zero]
        rw [← cls_smul (h := hsm)]
        have e' : M.cls (s • m) hsm = M.cls (g.f 0 (b x)) (cyc g _ (hb x)) :=
          (cls_eq _ _ _ _).2 (by rw [← hbc, he, sub_self]; exact zero_mem _)
        rw [e', hδ 0 (b x) 0 _ (map_zero _) (by rw [map_zero, hb])]
        rfl
      | succ j =>
        rw [(kill_iff _ _).1 (mc3 j) w, map_zero]
    rw [pow3, ← hw, ← map_smul (δ n), h2, smul_zero]
  · obtain ⟨x, rfl⟩ := hp e
    rw [hbc] at he
    obtain ⟨k, hk⟩ := (hfg 0 _).1 he
    have hkc : K.d 0 k = 0 := hf 1 (by rw [map_zero, ← f.comm, hk, hb])
    obtain ⟨y, hy⟩ := ka2 k hkc
    have h1 : b (s • x - i y) = 0 := by rw [map_sub, map_smul, hab, hy, map_smul, hk, sub_self]
    have h2 := lb1 _ h1
    rw [smul_sub, sub_eq_zero] at h2
    rw [pow3, ← map_smul p, ← map_smul p, h2, map_smul, (hip _).2 ⟨y, rfl⟩, smul_zero, smul_zero]
  · have h1 := (kill_iff _ _).1 (ka3 0) (δ 0 (M.cls m hm))
    rw [← map_smul (δ 0)] at h1
    obtain ⟨z, hz⟩ := (e2 0 _).1 h1
    obtain ⟨y, hy, rfl⟩ := clsSurj z
    rw [mapH_cls' g _ hy (cyc g _ hy), ← cls_smul (h := by rw [map_smul, hm, smul_zero]), cls_eq, mem_boundaries_zero_iff,
      sub_eq_zero] at hz
    obtain ⟨x, hx⟩ := lb2 y hy
    refine ⟨s • p x, ?_⟩
    rw [map_smul, hbc, hx, map_smul, hz, pow3]
  · have h1 := (kill_iff _ _).1 (ka3 (n + 1)) (δ (n + 1) w)
    rw [← map_smul (δ (n + 1))] at h1
    obtain ⟨z, hz⟩ := (e2 (n + 1) _).1 h1
    have h2 := (kill_iff _ _).1 (lb3 n) z
    rw [pow3, ← hz, ← map_smul (g.mapH (n + 1)), h2, map_zero, smul_zero]

theorem CrystallineSemistableComparison.P.res_transfer : ∀ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) {M : Type w''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (s s' : R), (∀ n, UpTo s' (φ.mapH n)) → (K.ResUpTo s ε → L.ResUpTo (s * s') (φ.f 0 ∘ₗ ε)) ∧ ((∀ x, K.d 0 (ε x) = 0) → L.ResUpTo s (φ.f 0 ∘ₗ ε) → K.ResUpTo (s * s') ε) := by
  intro R _ K L φ M _ _ ε s s' hφ
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
    · simp only [LinearMap.comp_apply]; rw [φ.comm, h0, map_zero]
    · simp only [LinearMap.comp_apply] at hx
      have e1 : φ.mapH 0 (K.cls (ε x) (h0 x)) = 0 := by
        rw [mapH_cls' φ _ _ (cyc φ _ (h0 x)), class_zero_eq_zero_iff]; exact hx
      have e2 := (hφ 0).1 _ e1
      rw [← cls_smul (h := by rw [map_smul, h0, smul_zero]), class_zero_eq_zero_iff, ← map_smul] at e2
      rw [mul_smul]; exact h1 _ e2
    · obtain ⟨z, hz⟩ := (hφ 0).2 (L.cls y hy)
      obtain ⟨a, ha, rfl⟩ := clsSurj z
      rw [mapH_cls' φ _ _ (cyc φ _ ha), ← cls_smul (h := by rw [map_smul, hy, smul_zero])] at hz
      have e := (cls_eq _ _ _ _).mp hz
      rw [mem_boundaries_zero_iff, sub_eq_zero] at e
      obtain ⟨x, hx⟩ := h2 a ha
      refine ⟨x, ?_⟩
      simp only [LinearMap.comp_apply]
      rw [hx, map_smul, e, mul_smul]
    · obtain ⟨z, hz⟩ := (hφ (n + 1)).2 (L.cls y hy)
      obtain ⟨a, ha, rfl⟩ := clsSurj z
      rw [mapH_cls' φ _ _ (cyc φ _ ha), ← cls_smul (h := by rw [map_smul, hy, smul_zero])] at hz
      obtain ⟨v, hv⟩ := (mem_Bs _).mp ((cls_eq _ _ _ _).mp hz)
      obtain ⟨u, hu⟩ := h3 n a ha
      refine ⟨φ.f n u - s • v, ?_⟩
      rw [map_sub, map_smul, hv, φ.comm, hu, map_smul, smul_sub, mul_smul]
      abel
  · rintro hd0 ⟨h0, h1, h2, h3⟩
    refine ⟨hd0, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
    · have := h1 x (by simp only [LinearMap.comp_apply]; rw [hx, map_zero])
      rw [mul_comm, mul_smul, this, smul_zero]
    · obtain ⟨x, hx⟩ := h2 (φ.f 0 y) (cyc φ _ hy)
      simp only [LinearMap.comp_apply] at hx
      have hc : K.d 0 (ε x - s • y) = 0 := by rw [map_sub, map_smul, hd0, hy, smul_zero, sub_zero]
      have e1 : φ.mapH 0 (K.cls (ε x - s • y) hc) = 0 := by
        rw [mapH_cls' φ _ hc (cyc φ _ hc), class_zero_eq_zero_iff, map_sub, map_smul, hx, sub_self]
      have e2 := (hφ 0).1 _ e1
      rw [← cls_smul (h := by rw [map_smul, hc, smul_zero]), class_zero_eq_zero_iff, smul_sub, sub_eq_zero] at e2
      refine ⟨s' • x, ?_⟩
      rw [map_smul, e2, mul_comm, mul_smul]
    · obtain ⟨u, hu⟩ := h3 n (φ.f (n + 1) y) (cyc φ _ hy)
      have e1 : φ.mapH (n + 1) (K.cls (s • y) (by rw [map_smul, hy, smul_zero])) = 0 := by
        rw [mapH_cls' φ _ _ (cyc φ _ (by rw [map_smul, hy, smul_zero])), cls_eq_zero, mem_Bs, map_smul]
        exact ⟨u, hu⟩
      have e2 := (hφ (n + 1)).1 _ e1
      rw [← cls_smul (h := by rw [map_smul, map_smul, hy, smul_zero, smul_zero]), cls_eq_zero, mem_Bs] at e2
      obtain ⟨x, hx⟩ := e2
      refine ⟨x, ?_⟩
      rw [hx, mul_comm, mul_smul]

theorem CrystallineSemistableComparison.P.res_semilinear : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'} (φ : Cx.Hom K L σ) {M : Type w''} [AddCommGroup M] [Module R M] {M' : Type t} [AddCommGroup M'] [Module R' M'] (ε : M →ₗ[R] K.X 0) (ε' : M' →ₗ[R'] L.X 0) (a : M →ₛₗ[σ] M') (s : R), Function.Bijective a → (∀ n, Function.Bijective (φ.f n)) → (∀ x, φ.f 0 (ε x) = ε' (a x)) → (K.ResUpTo s ε ↔ L.ResUpTo (σ s) ε') := by
  intro R R' _ _ σ K L φ M _ _ M' _ _ ε ε' a s ha hφ hc
  have inj : ∀ n (x : K.X n), φ.f n x = 0 ↔ x = 0 := fun n x => map_eq_zero_iff _ (hφ n).1
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨fun x' => ?_, fun x' hx => ?_, fun y' hy => ?_, fun n y' hy => ?_⟩
    · obtain ⟨x, rfl⟩ := ha.2 x'
      rw [← hc, φ.comm, h0, map_zero]
    · obtain ⟨x, rfl⟩ := ha.2 x'
      rw [← hc, inj] at hx
      rw [← map_smulₛₗ, h1 x hx, map_zero]
    · obtain ⟨y, rfl⟩ := (hφ 0).2 y'
      rw [φ.comm, inj] at hy
      obtain ⟨x, hx⟩ := h2 y hy
      exact ⟨a x, by rw [← hc, hx, map_smulₛₗ]⟩
    · obtain ⟨y, rfl⟩ := (hφ (n + 1)).2 y'
      rw [φ.comm, inj] at hy
      obtain ⟨u, hu⟩ := h3 n y hy
      exact ⟨φ.f n u, by rw [φ.comm, hu, map_smulₛₗ]⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
    · rw [← inj, ← φ.comm, hc, h0]
    · have e : ε' (a x) = 0 := by rw [← hc, hx, map_zero]
      have e2 := h1 _ e
      rw [← map_smulₛₗ, map_eq_zero_iff _ ha.1] at e2
      exact e2
    · have hy' : L.d 0 (φ.f 0 y) = 0 := by rw [φ.comm, hy, map_zero]
      obtain ⟨x', hx'⟩ := h2 _ hy'
      obtain ⟨x, rfl⟩ := ha.2 x'
      refine ⟨x, (hφ 0).1 ?_⟩
      rw [hc, hx', map_smulₛₗ]
    · have hy' : L.d (n + 1) (φ.f (n + 1) y) = 0 := by rw [φ.comm, hy, map_zero]
      obtain ⟨u', hu'⟩ := h3 n _ hy'
      obtain ⟨u, rfl⟩ := (hφ n).2 u'
      refine ⟨u, (hφ (n + 1)).1 ?_⟩
      rw [← φ.comm, hu', map_smulₛₗ]

theorem CrystallineSemistableComparison.P.ses_cochains : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{w} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) → (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Function.Injective ((Mor.ofNatTrans α).hom.f n)) ∧ (∀ n, Function.Exact ((Mor.ofNatTrans α).hom.f n) ((Mor.ofNatTrans β).hom.f n)) ∧ ∀ n, Function.Surjective ((Mor.ofNatTrans β).hom.f n) := by
  intro R _ C _ F₁ F₂ F₃ α β hi he hs
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    exact hi _ (congrFun hxy s)
  · refine ⟨fun s => ((he _ (y s)).1 (congrFun hy s)).choose, ?_⟩
    funext s
    exact ((he _ (y s)).1 (congrFun hy s)).choose_spec
  · rintro ⟨x, rfl⟩
    funext s
    exact (he _ _).2 ⟨_, rfl⟩
  · exact ⟨fun s => (hs _ (y s)).choose, funext fun s => (hs _ (y s)).choose_spec⟩

theorem CrystallineSemistableComparison.P.ses_sub : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F : C ⥤ ModuleCat.{w} R} (S : SubF F), (∀ n, Function.Injective (S.inc.hom.f n)) ∧ (∀ n, Function.Exact (S.inc.hom.f n) (S.proj.hom.f n)) ∧ ∀ n, Function.Surjective (S.proj.hom.f n) := by
  intro R _ C _ F S
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    exact Subtype.val_injective (congrFun hxy s)
  · refine ⟨fun s => ⟨y s, (Submodule.Quotient.mk_eq_zero _).1 (congrFun hy s)⟩, ?_⟩
    funext s
    rfl
  · rintro ⟨x, rfl⟩
    funext s
    exact (Submodule.Quotient.mk_eq_zero _).2 (x _).2
  · exact ⟨fun s => (Submodule.Quotient.mk_surjective _ (y s)).choose,
      funext fun s => (Submodule.Quotient.mk_surjective _ (y s)).choose_spec⟩
