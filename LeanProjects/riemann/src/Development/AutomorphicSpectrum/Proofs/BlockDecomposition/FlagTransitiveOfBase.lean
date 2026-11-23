import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.Flag

open GlobalTheory.CompanionTheory.KFin

section Basic

variable {R : Type} [CommRing R] {c : R →+* R} {V : Type} [AddCommGroup V] [Module R V]
  {h : V → V → R}

theorem herm_zero_right (H : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := H.smul_right 0 x 0
  simpa using this

theorem herm_neg_right (H : IsHerm c h) (x y : V) : h x (-y) = - h x y := by
  have := H.smul_right (-1) x y
  simpa using this

theorem herm_sub_right (H : IsHerm c h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, H.add_right, herm_neg_right H, sub_eq_add_neg]

theorem herm_add_left (H : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [H.symm z (x + y), H.add_right, map_add, ← H.symm, ← H.symm]

theorem herm_smul_left (H : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [H.symm y (a • x), H.smul_right, map_mul, ← H.symm]

theorem herm_sub_left (H : IsHerm c h) (x y z : V) : h (x - y) z = h x z - h y z := by
  rw [H.symm z (x - y), herm_sub_right H, map_sub, ← H.symm, ← H.symm]

def linForm (H : IsHerm c h) (x : V) : V →ₗ[R] R where
  toFun := h x
  map_add' := H.add_right x
  map_smul' a y := by simp [H.smul_right]

@[simp] theorem linForm_apply (H : IsHerm c h) (x y : V) : linForm H x y = h x y := rfl

structure IsHyp (h : V → V → R) (x y : V) : Prop where
  xx : h x x = 0
  yy : h y y = 0
  xy : h x y = 1

def perp (H : IsHerm c h) (x y : V) : Submodule R V :=
  LinearMap.ker (linForm H x) ⊓ LinearMap.ker (linForm H y)

theorem mem_perp (H : IsHerm c h) {x y z : V} : z ∈ perp H x y ↔ h x z = 0 ∧ h y z = 0 := by
  simp [perp, LinearMap.mem_ker]

def projV (H : IsHerm c h) (x y : V) : V →ₗ[R] V :=
  LinearMap.id - (linForm H y).smulRight x - (linForm H x).smulRight y

theorem projV_apply (H : IsHerm c h) (x y z : V) :
    projV H x y z = z - h y z • x - h x z • y := by
  simp [projV]

def resForm (h : V → V → R) (W : Submodule R V) : W → W → R := fun a b => h a b

theorem isHerm_resForm (H : IsHerm c h) (W : Submodule R V) : IsHerm c (resForm h W) where
  add_right a b d := H.add_right _ _ _
  smul_right a b d := H.smul_right _ _ _
  symm a b := H.symm _ _

def resLat (𝔬 : Subring R) (W : Submodule R V) (L : Submodule 𝔬 V) : Submodule 𝔬 W :=
  L.comap (W.subtype.restrictScalars 𝔬)

def pullLat (𝔬 : Subring R) (p : V ≃ₗ[R] V) (L : Submodule 𝔬 V) : Submodule 𝔬 V :=
  L.comap (p.toLinearMap.restrictScalars 𝔬)

theorem mem_pullLat {𝔬 : Subring R} {p : V ≃ₗ[R] V} {L : Submodule 𝔬 V} {z : V} :
    z ∈ pullLat 𝔬 p L ↔ p z ∈ L := Iff.rfl

theorem IsHyp.yx (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) : h y x = 1 := by
  rw [H.symm x y, hy.xy, map_one]

theorem projV_mem (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) (z : V) :
    projV H x y z ∈ perp H x y := by
  rw [mem_perp, projV_apply, herm_sub_right H, herm_sub_right H, herm_sub_right H,
    herm_sub_right H, H.smul_right, H.smul_right,
    H.smul_right, H.smul_right, hy.xx, hy.yy, hy.xy, hy.yx H]
  constructor <;> ring

theorem decomp (H : IsHerm c h) (x y z : V) :
    z = h y z • x + h x z • y + projV H x y z := by
  rw [projV_apply]; abel

theorem herm_perp_left (H : IsHerm c h) {x y z : V} (hz : z ∈ perp H x y) (w : V) :
    h (projV H x y w) z = h w z := by
  have := (mem_perp H).1 hz
  rw [projV_apply, herm_sub_left H, herm_sub_left H, herm_smul_left H, herm_smul_left H,
    this.1, this.2]
  ring

theorem herm_perp_right (H : IsHerm c h) {x y z : V} (hz : z ∈ perp H x y) (w : V) :
    h z (projV H x y w) = h z w := by
  have := (mem_perp H).1 hz
  have h1 : h z x = 0 := by rw [H.symm x z, this.1, map_zero]
  have h2 : h z y = 0 := by rw [H.symm y z, this.2, map_zero]
  rw [projV_apply, herm_sub_right H, herm_sub_right H, H.smul_right, H.smul_right, h1, h2]
  ring

theorem herm_projV (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) (z w : V) :
    h (projV H x y z) (projV H x y w) = h z w - c (h y z) * h x w - c (h x z) * h y w := by
  rw [herm_perp_right H (projV_mem H hy z), projV_apply, herm_sub_left H, herm_sub_left H,
    herm_smul_left H, herm_smul_left H]

end Basic

section Lemmas
variable {R : Type} [CommRing R] {c : R →+* R} {𝔬 : Subring R} {V : Type} [AddCommGroup V] [Module R V]
  {h : V → V → R}

theorem herm_zero_left (H : IsHerm c h) (x : V) : h 0 x = 0 := by
  have := herm_smul_left H 0 0 x
  simpa using this

theorem smem {L : Submodule 𝔬 V} {a : R} {z : V} (ha : a ∈ 𝔬) (hz : z ∈ L) : a • z ∈ L :=
  L.smul_of_tower_mem (⟨a, ha⟩ : 𝔬) hz

theorem exists_denom (hR : IsHermRing c 𝔬) {L : Submodule 𝔬 V}
    (hs : Submodule.span R (L : Set V) = ⊤) (v : V) : ∃ s ∈ 𝔬, IsUnit s ∧ s • v ∈ L := by
  have hv : v ∈ Submodule.span R (L : Set V) := hs ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, 𝔬.one_mem, isUnit_one, by simpa using hv⟩
  | zero => exact ⟨1, 𝔬.one_mem, isUnit_one, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hv
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hw
    refine ⟨s * t, 𝔬.mul_mem hs₁ ht₁, hs₂.mul ht₂, ?_⟩
    have : (s * t) • (v + w) = t • (s • v) + s • (t • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [this]
    exact L.add_mem (smem ht₁ hs₃) (smem hs₁ ht₃)
  | smul a v _ hv =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hv
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hR.denom a
    refine ⟨t * s, 𝔬.mul_mem ht₁ hs₁, ht₂.mul hs₂, ?_⟩
    have : (t * s) • a • v = (t * a) • (s • v) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact smem ht₃ hs₃

theorem exists_primitive (hR : IsHermRing c 𝔬) (H : IsHerm c h) {L : Submodule 𝔬 V}
    (hL : IsLat 𝔬 L) {x₁ y₁ : V} (hxy : h x₁ y₁ = 1) :
    ∃ u : R, IsUnit u ∧ u • x₁ ∈ L ∧ ∀ a : R, a • (u • x₁) ∈ L → a ∈ 𝔬 := by
  have hyx : h y₁ x₁ = 1 := by rw [H.symm x₁ y₁, hxy, map_one]
  let I : Submodule 𝔬 R := L.comap ((LinearMap.toSpanSingleton R V x₁).restrictScalars 𝔬)
  have memI : ∀ a, a ∈ I ↔ a • x₁ ∈ L := fun a => Iff.rfl
  let J : Submodule 𝔬 R := L.map ((linForm H y₁).restrictScalars 𝔬)
  have hJ : J.FG := hL.1.map _
  have hIJ : I ≤ J := fun a ha => ⟨a • x₁, ha, by
    change h y₁ (a • x₁) = a
    rw [H.smul_right, hyx, mul_one]⟩
  have := hR.noeth
  have hN : IsNoetherian 𝔬 J := isNoetherian_of_fg_of_noetherian J hJ
  have hI : I.FG := (isNoetherian_submodule.1 hN) I hIJ
  obtain ⟨s, -, hs, hsL⟩ := exists_denom hR hL.2 x₁
  obtain ⟨u, hu, e⟩ := hR.principal I hI ⟨s, (memI s).2 hsL, hs⟩
  have huI : u ∈ I := e ▸ Submodule.mem_span_singleton_self u
  refine ⟨u, hu, huI, fun a ha => ?_⟩
  rw [smul_smul] at ha
  have : a * u ∈ I := ha
  rw [e, Submodule.mem_span_singleton] at this
  obtain ⟨b, hb⟩ := this
  have hb' : (b : R) * u = a * u := hb
  have := hu.mul_right_cancel hb'
  exact this ▸ b.2

theorem exists_partner (hR : IsHermRing c 𝔬) (H : IsHerm c h) {L : Submodule 𝔬 V}
    (hL : IsMaxEven c 𝔬 h L) {x₁ y₁ : V} (hxx : h x₁ x₁ = 0) (hxy : h x₁ y₁ = 1) :
    ∃ u : R, IsUnit u ∧ ∃ y ∈ L, u • x₁ ∈ L ∧ IsHyp h (u • x₁) y := by
  obtain ⟨u, hu, hxL, prim⟩ := exists_primitive hR H hL.1 hxy
  refine ⟨u, hu, ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, x = u • x₁ := ⟨_, rfl⟩
  rw [← hx] at hxL prim ⊢
  have hx0 : h x x = 0 := by
    rw [hx, herm_smul_left H, H.smul_right, hxx]; ring
  have hcu : IsUnit (c u) := hu.map c
  have hxy' : h x y₁ = c u := by rw [hx, herm_smul_left H, hxy, mul_one]
  let I : Submodule 𝔬 R := L.map ((linForm H x).restrictScalars 𝔬)
  have memI : ∀ l ∈ L, h x l ∈ I := fun l hl => ⟨l, hl, rfl⟩
  have hI : I.FG := hL.1.1.map _
  obtain ⟨s, -, hs, hsL⟩ := exists_denom hR hL.1.2 y₁
  have hsu : h x (s • y₁) = s * c u := by rw [H.smul_right, hxy']
  obtain ⟨e, he, eI⟩ := hR.principal I hI ⟨_, memI _ hsL, by rw [hsu]; exact hs.mul hcu⟩
  obtain ⟨f, hf⟩ := he.exists_left_inv
  have hxl : ∀ l ∈ L, ∃ b ∈ 𝔬, h x l = b * e := fun l hl => by
    have := memI l hl
    rw [eI, Submodule.mem_span_singleton] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, b.2, hb.symm⟩
  obtain ⟨w, hw⟩ : ∃ w, w = c f • x := ⟨_, rfl⟩
  have hinv := hR.invol
  have hwl : ∀ l ∈ L, h w l ∈ 𝔬 := fun l hl => by
    obtain ⟨b, hb, e1⟩ := hxl l hl
    have : h w l = b := by
      rw [hw, herm_smul_left H, hinv, e1]
      linear_combination b * hf
    exact this ▸ hb
  have hww : h w w = 0 := by
    rw [hw, herm_smul_left H, H.smul_right, hx0]; ring
  have hlw : ∀ l ∈ L, h l w ∈ 𝔬 := fun l hl => by
    rw [H.symm w l]; exact hR.conj_mem _ (hwl l hl)
  have key : IsEvenInt c 𝔬 h (L ⊔ Submodule.span 𝔬 {w}) := by
    have form : ∀ z ∈ L ⊔ Submodule.span 𝔬 {w}, ∃ l ∈ L, ∃ a ∈ 𝔬, z = l + a • w := fun z hz => by
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
      exact ⟨l, hl, a, a.2, rfl⟩
    refine ⟨fun z hz z' hz' => ?_, fun z hz => ?_⟩
    · obtain ⟨l, hl, a, ha, rfl⟩ := form z hz
      obtain ⟨l', hl', a', ha', rfl⟩ := form z' hz'
      simp only [herm_add_left H, H.add_right, herm_smul_left H, H.smul_right, hww, mul_zero,
        add_zero]
      exact 𝔬.add_mem (𝔬.add_mem (hL.2.1.1 l hl l' hl') (𝔬.mul_mem ha' (hlw l hl)))
        (𝔬.mul_mem (hR.conj_mem _ ha) (hwl l' hl'))
    · obtain ⟨l, hl, a, ha, rfl⟩ := form z hz
      obtain ⟨b, hb, e1⟩ := hL.2.1.2 l hl
      refine ⟨b + c a * h w l, 𝔬.add_mem hb (𝔬.mul_mem (hR.conj_mem _ ha) (hwl l hl)), ?_⟩
      simp only [herm_add_left H, H.add_right, herm_smul_left H, H.smul_right, hww, mul_zero,
        add_zero]
      rw [e1, map_add, map_mul, hinv, ← H.symm]
      ring
  have hwL : w ∈ L := hL.2.2 _ key le_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hcf : c f ∈ 𝔬 := prim _ (hw ▸ hwL)
  have hfo : f ∈ 𝔬 := by
    have := hR.conj_mem _ hcf
    rwa [hinv] at this
  have h1 : (1 : R) ∈ I := by
    rw [eI, Submodule.mem_span_singleton]
    exact ⟨⟨f, hfo⟩, hf⟩
  obtain ⟨l, hl, hl1⟩ := h1
  have hl1' : h x l = 1 := hl1
  have hlx : h l x = 1 := by rw [H.symm x l, hl1', map_one]
  obtain ⟨a, ha, e2⟩ := hL.2.1.2 l hl
  refine ⟨l - a • x, L.sub_mem hl (smem ha hxL), hxL, hx0, ?_, ?_⟩
  · simp only [herm_sub_left H, herm_sub_right H, herm_smul_left H, H.smul_right, hx0, hlx, hl1',
      e2]
    ring
  · rw [herm_sub_right H, H.smul_right, hx0, hl1']; ring

def projP (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) : V →ₗ[R] perp H x y :=
  (projV H x y).codRestrict _ (projV_mem H hy)

@[simp] theorem coe_projP (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) (z : V) :
    (projP H hy z : V) = projV H x y z := rfl

theorem projP_coe (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) (m : perp H x y) :
    projP H hy m = m := by
  apply Subtype.ext
  have := (mem_perp H).1 m.2
  rw [coe_projP, projV_apply, this.1, this.2]
  simp

theorem isPerfect_resForm (H : IsHerm c h) (P : IsPerfect h) {x y : V} (hy : IsHyp h x y) :
    IsPerfect (resForm h (perp H x y)) where
  nondeg m hm := by
    apply Subtype.ext
    refine P.nondeg _ fun w => ?_
    rw [← herm_perp_right H m.2 w]
    exact hm (projP H hy w)
  repr f := by
    obtain ⟨v, hv⟩ := P.repr (f ∘ₗ projP H hy)
    refine ⟨projP H hy v, fun m => ?_⟩
    change h (projV H x y v) m = _
    rw [herm_perp_left H m.2, hv]
    simp [projP_coe]

theorem isMaxEven_pullLat (H : IsHerm c h) {p : V ≃ₗ[R] V} (hp : ∀ a b, h (p a) (p b) = h a b)
    {L : Submodule 𝔬 V} (hL : IsMaxEven c 𝔬 h L) : IsMaxEven c 𝔬 h (pullLat 𝔬 p L) := by
  have hEq : pullLat 𝔬 p L = L.map (p.symm.toLinearMap.restrictScalars 𝔬) := by
    ext z
    rw [mem_pullLat]
    constructor
    · intro hz
      exact ⟨p z, hz, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      simpa using ht
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hEq]; exact hL.1.1.map _
  · rw [eq_top_iff]
    intro z _
    have h1 : p z ∈ Submodule.span R (L : Set V) := hL.1.2 ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := p.symm.toLinearMap) h1
    rw [Submodule.map_span] at h2
    have h3 : p.symm.toLinearMap '' (L : Set V) ⊆ (pullLat 𝔬 p L : Set V) := by
      rintro _ ⟨t, ht, rfl⟩
      change p (p.symm t) ∈ L
      simpa using ht
    have h4 := Submodule.span_mono h3 h2
    simpa using h4
  · intro s hs t ht
    rw [← hp]
    exact hL.2.1.1 _ hs _ ht
  · intro s hs
    rw [← hp]
    exact hL.2.1.2 _ hs
  · intro M hM hLM z hz
    have hs : ∀ a b, h (p.symm a) (p.symm b) = h a b := fun a b => by
      rw [← hp]; simp
    have hE : IsEvenInt c 𝔬 h (pullLat 𝔬 p.symm M) :=
      ⟨fun s hs' t ht' => by rw [← hs]; exact hM.1 _ hs' _ ht',
       fun s hs' => by rw [← hs]; exact hM.2 _ hs'⟩
    refine hL.2.2 _ hE (fun t ht => ?_) (?_ : p z ∈ pullLat 𝔬 p.symm M)
    · apply hLM
      rw [mem_pullLat]
      simpa using ht
    · rw [mem_pullLat]
      simpa using hz

theorem isMaxEven_resLat (hR : IsHermRing c 𝔬) (H : IsHerm c h) {x y : V} (hy : IsHyp h x y)
    {L : Submodule 𝔬 V} (hL : IsMaxEven c 𝔬 h L) (hx : x ∈ L) (hyL : y ∈ L) :
    IsMaxEven c 𝔬 (resForm h (perp H x y)) (resLat 𝔬 (perp H x y) L) := by
  have hprojL : ∀ z ∈ L, projV H x y z ∈ L := fun z hz => by
    rw [projV_apply]
    exact L.sub_mem (L.sub_mem hz (smem (hL.2.1.1 y hyL z hz) hx)) (smem (hL.2.1.1 x hx z hz) hyL)
  have hEq : resLat 𝔬 (perp H x y) L = L.map ((projP H hy).restrictScalars 𝔬) := by
    ext m
    constructor
    · intro hm
      exact ⟨m, hm, projP_coe H hy m⟩
    · rintro ⟨t, ht, rfl⟩
      exact hprojL t ht
  refine ⟨⟨?_, ?_⟩, ⟨fun s hs t ht => hL.2.1.1 _ hs _ ht, fun s hs => hL.2.1.2 _ hs⟩, ?_⟩
  · rw [hEq]; exact hL.1.1.map _
  · rw [eq_top_iff]
    intro m _
    have h1 : (m : V) ∈ Submodule.span R (L : Set V) := hL.1.2 ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := projP H hy) h1
    rw [Submodule.map_span, projP_coe] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact hprojL t ht
  · intro M hM hLM
    let L' : Submodule 𝔬 V :=
      { carrier := {z | h y z ∈ 𝔬 ∧ h x z ∈ 𝔬 ∧ projP H hy z ∈ M}
        add_mem' := fun {s t} hs ht => by
          refine ⟨?_, ?_, ?_⟩
          · rw [H.add_right]; exact 𝔬.add_mem hs.1 ht.1
          · rw [H.add_right]; exact 𝔬.add_mem hs.2.1 ht.2.1
          · rw [map_add]; exact M.add_mem hs.2.2 ht.2.2
        zero_mem' := by
          refine ⟨?_, ?_, ?_⟩
          · rw [herm_zero_right H]; exact 𝔬.zero_mem
          · rw [herm_zero_right H]; exact 𝔬.zero_mem
          · rw [map_zero]; exact M.zero_mem
        smul_mem' := fun a z hz => by
          have e : ∀ v, h v (a • z) = (a : R) * h v z := fun v => H.smul_right (a : R) v z
          refine ⟨?_, ?_, ?_⟩
          · rw [e]; exact 𝔬.mul_mem a.2 hz.1
          · rw [e]; exact 𝔬.mul_mem a.2 hz.2.1
          · have : projP H hy (a • z) = a • projP H hy z := (projP H hy).map_smul (a : R) z
            rw [this]
            exact M.smul_mem a hz.2.2 }
    have hform : ∀ z w, h z w = h (projV H x y z) (projV H x y w) + c (h y z) * h x w
        + c (h x z) * h y w := fun z w => by
      rw [herm_projV H hy]; ring
    have hE : IsEvenInt c 𝔬 h L' := by
      refine ⟨fun z hz w hw => ?_, fun z hz => ?_⟩
      · rw [hform]
        exact 𝔬.add_mem (𝔬.add_mem (hM.1 _ hz.2.2 _ hw.2.2)
          (𝔬.mul_mem (hR.conj_mem _ hz.1) hw.2.1)) (𝔬.mul_mem (hR.conj_mem _ hz.2.1) hw.1)
      · obtain ⟨a, ha, e⟩ := hM.2 _ hz.2.2
        have e' : h (projV H x y z) (projV H x y z) = a + c a := e
        refine ⟨a + c (h y z) * h x z, 𝔬.add_mem ha (𝔬.mul_mem (hR.conj_mem _ hz.1) hz.2.1), ?_⟩
        rw [hform, e', map_add, map_mul, hR.invol]
        ring
    have hLL' : L ≤ L' := fun z hz =>
      ⟨hL.2.1.1 y hyL z hz, hL.2.1.1 x hx z hz, hLM (hprojL z hz)⟩
    intro m hm
    have hp := (mem_perp H).1 m.2
    refine hL.2.2 _ hE hLL' (⟨?_, ?_, ?_⟩ : (m : V) ∈ L')
    · rw [hp.2]; exact 𝔬.zero_mem
    · rw [hp.1]; exact 𝔬.zero_mem
    · rw [projP_coe]; exact hm

theorem exists_glue (hR : IsHermRing c 𝔬) [Module.Finite R V] (H : IsHerm c h) (P : IsPerfect h) {x y x' y' : V}
    (hy : IsHyp h x y) (hy' : IsHyp h x' y') (ψ : perp H x y →ₗ[R] V)
    (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hψ' : ∀ a, ψ a ∈ perp H x' y') :
    ∃ p : V ≃ₗ[R] V, (∀ a b, h (p a) (p b) = h a b) ∧ p x = x' ∧ p y = y' ∧
      ∀ a : perp H x y, p a = ψ a := by
  let f : V →ₗ[R] V := (linForm H y).smulRight x' + (linForm H x).smulRight y' + ψ ∘ₗ projP H hy
  have fa : ∀ z, f z = h y z • x' + h x z • y' + ψ (projP H hy z) := fun z => by simp [f]
  have hR1 : ∀ s t, h x' (ψ s) = 0 ∧ h y' (ψ s) = 0 ∧ h (ψ t) x' = 0 ∧ h (ψ t) y' = 0 := fun s t => by
    have e1 := (mem_perp H).1 (hψ' s)
    have e2 := (mem_perp H).1 (hψ' t)
    refine ⟨e1.1, e1.2, ?_, ?_⟩
    · rw [H.symm x' (ψ t), e2.1, map_zero]
    · rw [H.symm y' (ψ t), e2.2, map_zero]
  have iso : ∀ a b, h (f a) (f b) = h a b := fun a b => by
    have e := hR1 (projP H hy b) (projP H hy a)
    have e3 : h (ψ (projP H hy a)) (ψ (projP H hy b)) = h (projV H x y a) (projV H x y b) := hψ _ _
    rw [herm_projV H hy] at e3
    rw [fa, fa]
    simp only [herm_add_left H, H.add_right, herm_smul_left H, H.smul_right, e.1, e.2.1, e.2.2.1,
      e.2.2.2, e3, hy'.xx, hy'.yy, hy'.xy, hy'.yx H]
    ring
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine P.nondeg z fun w => ?_
    rw [← iso, hz, herm_zero_left H]
  have := hR.artinian
  refine ⟨LinearEquiv.ofBijective f ⟨inj, IsArtinian.surjective_of_injective_endomorphism f inj⟩,
    iso, ?_, ?_, fun m => ?_⟩
  · have e : projP H hy x = 0 := by
      apply Subtype.ext
      rw [coe_projP, projV_apply, hy.xx, hy.yx H]; simp
    change f x = _
    rw [fa, e, hy.xx, hy.yx H]; simp
  · have e : projP H hy y = 0 := by
      apply Subtype.ext
      rw [coe_projP, projV_apply, hy.yy, hy.xy]; simp
    change f y = _
    rw [fa, e, hy.yy, hy.xy]; simp
  · change f m = _
    have hm := (mem_perp H).1 m.2
    rw [fa, projP_coe, hm.1, hm.2]; simp

end Lemmas

section Main
variable {R : Type} [CommRing R] {c : R →+* R} {𝔬 : Subring R} {V : Type} [AddCommGroup V] [Module R V]
  {h : V → V → R}

def Good (c : R →+* R) (𝔬 : Subring R) {V : Type} [AddCommGroup V] [Module R V] (h : V → V → R) : Prop :=
  ∀ (r : ℕ) (x y : Fin r → V), IsFrame h x y → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L' ∧
        ∀ j, p (x j) ∈ Submodule.span R (x '' {i | i ≤ j})

theorem mem_iff_of_hyp (H : IsHerm c h) {x y : V} {L : Submodule 𝔬 V} (hE : IsEvenInt c 𝔬 h L)
    (hx : x ∈ L) (hy : y ∈ L) (z : V) :
    z ∈ L ↔ h y z ∈ 𝔬 ∧ h x z ∈ 𝔬 ∧ projV H x y z ∈ L := by
  constructor
  · intro hz
    have h1 := hE.1 y hy z hz
    have h2 := hE.1 x hx z hz
    refine ⟨h1, h2, ?_⟩
    rw [projV_apply]
    exact L.sub_mem (L.sub_mem hz (L.smul_of_tower_mem (⟨_, h1⟩ : 𝔬) hx))
      (L.smul_of_tower_mem (⟨_, h2⟩ : 𝔬) hy)
  · rintro ⟨h1, h2, h3⟩
    rw [decomp H x y z]
    exact L.add_mem (L.add_mem (L.smul_of_tower_mem (⟨_, h1⟩ : 𝔬) hx)
      (L.smul_of_tower_mem (⟨_, h2⟩ : 𝔬) hy)) h3

theorem mem_iff_lift (H : IsHerm c h) {a b : V} (hyp : IsHyp h a b) {L L₂ : Submodule 𝔬 V}
    (hE : IsEvenInt c 𝔬 h L) (hE₂ : IsEvenInt c 𝔬 h L₂) (ha : a ∈ L) (hb : b ∈ L)
    (ha₂ : a ∈ L₂) (hb₂ : b ∈ L₂) (q : V ≃ₗ[R] V) (hq : ∀ s t, h (q s) (q t) = h s t)
    (hqa : q a = a) (hqb : q b = b)
    (hp : ∀ m : perp H a b, (m : V) ∈ L ↔ q m ∈ L₂) (z : V) : z ∈ L ↔ q z ∈ L₂ := by
  have e1 : h a (q z) = h a z := by
    conv_lhs => rw [← hqa]
    exact hq _ _
  have e2 : h b (q z) = h b z := by
    conv_lhs => rw [← hqb]
    exact hq _ _
  have e3 : projV H a b (q z) = q (projV H a b z) := by
    rw [projV_apply, projV_apply, e1, e2, map_sub, map_sub, map_smul, map_smul, hqa, hqb]
  rw [mem_iff_of_hyp H hE ha hb, mem_iff_of_hyp H hE₂ ha₂ hb₂, e1, e2, e3,
    hp ⟨_, projV_mem H hyp z⟩]

theorem flag_step (hR : IsHermRing c 𝔬) [Module.Finite R V] (H : IsHerm c h) (P : IsPerfect h)
    (ih : ∀ x y, IsHyp h x y → Good c 𝔬 (resForm h (perp H x y)))
    {r : ℕ} (x y : Fin (r + 1) → V) (hf : IsFrame h x y) {L L' : Submodule 𝔬 V}
    (hL : IsMaxEven c 𝔬 h L) (hL' : IsMaxEven c 𝔬 h L') :
    ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L' ∧
        ∀ j, p (x j) ∈ Submodule.span R (x '' {i | i ≤ j}) := by
  have hxx0 : h (x 0) (x 0) = 0 := hf.xx 0 0
  have hxy0 : h (x 0) (y 0) = 1 := by simpa using hf.xy 0 0
  obtain ⟨u, hu, b, hbL, haL, hyp⟩ := exists_partner hR H hL hxx0 hxy0
  obtain ⟨u', hu', b', hbL', haL', hyp'⟩ := exists_partner hR H hL' hxx0 hxy0
  obtain ⟨a, ha⟩ : ∃ a, a = u • x 0 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = u' • x 0 := ⟨_, rfl⟩
  rw [← ha] at haL hyp
  rw [← ha'] at haL' hyp'

  have aperp : ∀ z, h (x 0) z = 0 → h a z = 0 := fun z hz => by
    rw [ha, herm_smul_left H, hz, mul_zero]
  have a'perp : ∀ z, h a z = 0 → h a' z = 0 := fun z hz => by
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : x 0 = v • a := by rw [ha, smul_smul, hv, one_smul]
    rw [ha', herm_smul_left H, this, herm_smul_left H, hz]; ring

  let ψ : perp H a b →ₗ[R] V :=
    (perp H a b).subtype - ((linForm H b') ∘ₗ (perp H a b).subtype).smulRight a'
  have ψa : ∀ m : perp H a b, ψ m = (m : V) - h b' m • a' := fun m => by simp [ψ]
  have mpa : ∀ m : perp H a b, h a' m = 0 := fun m => a'perp _ ((mem_perp H).1 m.2).1
  have hψ : ∀ s t, h (ψ s) (ψ t) = h s t := fun s t => by
    have : h s a' = 0 := by rw [H.symm a' s, mpa, map_zero]
    rw [ψa, ψa, herm_sub_left H, herm_sub_right H, herm_sub_right H, herm_smul_left H,
      herm_smul_left H, H.smul_right, H.smul_right, mpa, this, hyp'.xx]
    ring
  have hψ' : ∀ s, ψ s ∈ perp H a' b' := fun s => by
    rw [mem_perp H, ψa, herm_sub_right H, herm_sub_right H, H.smul_right, H.smul_right, mpa,
      hyp'.xx, hyp'.yx H]
    constructor <;> ring
  obtain ⟨T, hT, hTa, hTb, hTz⟩ := exists_glue hR H P hyp hyp' ψ hψ hψ'
  have hL₂ := isMaxEven_pullLat H hT hL'
  have ha₂ : a ∈ pullLat 𝔬 T L' := by rw [mem_pullLat, hTa]; exact haL'
  have hb₂ : b ∈ pullLat 𝔬 T L' := by rw [mem_pullLat, hTb]; exact hbL'

  have hax : ∀ j : Fin r, h a (x j.succ) = 0 := fun j => aperp _ (hf.xx _ _)
  have hay : ∀ j : Fin r, h a (y j.succ) = 0 := fun j => aperp _ (by
    rw [hf.xy, if_neg (Fin.succ_ne_zero j).symm])
  let w : Fin r → perp H a b := fun j => ⟨projV H a b (x j.succ), projV_mem H hyp _⟩
  let v : Fin r → perp H a b := fun j => ⟨projV H a b (y j.succ), projV_mem H hyp _⟩
  have fr : IsFrame (resForm h (perp H a b)) w v := {
    xx := fun i j => by
      change h (projV H a b _) (projV H a b _) = 0
      rw [herm_projV H hyp, hax, hax, hf.xx]; simp
    yy := fun i j => by
      change h (projV H a b _) (projV H a b _) = 0
      rw [herm_projV H hyp, hay, hay, hf.yy]; simp
    xy := fun i j => by
      change h (projV H a b _) (projV H a b _) = _
      rw [herm_projV H hyp, hax, hay, hf.xy]
      simp [Fin.succ_inj] }
  obtain ⟨p₂, ⟨hp₂, hmem⟩, hflag⟩ := ih a b hyp r w v fr _ _
    (isMaxEven_resLat hR H hyp hL haL hbL) (isMaxEven_resLat hR H hyp hL₂ ha₂ hb₂)
  obtain ⟨q, hq, hqa, hqb, hqz⟩ := exists_glue hR H P hyp hyp
    ((perp H a b).subtype ∘ₗ p₂.toLinearMap) (fun s t => hp₂ s t)
    (fun s => (p₂ s).2)
  have flagMono : ∀ {i j : Fin (r + 1)}, i ≤ j → Submodule.span R (x '' {k | k ≤ i}) ≤
      Submodule.span R (x '' {k | k ≤ j}) := fun hij =>
    Submodule.span_mono (Set.image_mono fun _ hk => le_trans hk hij)
  have xF : ∀ {i j : Fin (r + 1)}, i ≤ j → x i ∈ Submodule.span R (x '' {k | k ≤ j}) :=
    fun hij => Submodule.subset_span ⟨_, hij, rfl⟩
  have aF : ∀ j : Fin (r + 1), a ∈ Submodule.span R (x '' {k | k ≤ j}) := fun j => by
    rw [ha]; exact Submodule.smul_mem _ _ (xF (Fin.zero_le j))
  have a'F : ∀ j : Fin (r + 1), a' ∈ Submodule.span R (x '' {k | k ≤ j}) := fun j => by
    rw [ha']; exact Submodule.smul_mem _ _ (xF (Fin.zero_le j))
  have projF : ∀ j : Fin r, projV H a b (x j.succ) = x j.succ - h b (x j.succ) • a := fun j => by
    rw [projV_apply, hax]; simp
  have wF : ∀ (i : Fin r) (j : Fin r), i ≤ j →
      ((w i : perp H a b) : V) ∈ Submodule.span R (x '' {k | k ≤ j.succ}) := fun i j hij => by
    change projV H a b (x i.succ) ∈ _
    rw [projF]
    exact Submodule.sub_mem _ (xF (Fin.succ_le_succ_iff.2 hij)) (Submodule.smul_mem _ _ (aF _))
  have TF : ∀ i : Fin (r + 1), T (x i) ∈ Submodule.span R (x '' {k | k ≤ i}) := fun i => by
    induction i using Fin.cases with
    | zero =>
      obtain ⟨v', hv⟩ := hu.exists_left_inv
      have : x 0 = v' • a := by rw [ha, smul_smul, hv, one_smul]
      rw [this, map_smul, hTa]
      exact Submodule.smul_mem _ _ (a'F _)
    | succ j =>
      have e := decomp H a b (x j.succ)
      rw [e, map_add, map_add, map_smul, map_smul, hTa, hTb, hax, zero_smul, add_zero]
      obtain ⟨m, hm⟩ : ∃ m : perp H a b, (m : V) = projV H a b (x j.succ) :=
        ⟨⟨_, projV_mem H hyp _⟩, rfl⟩
      have hmF : (m : V) ∈ Submodule.span R (x '' {k | k ≤ j.succ}) := by
        rw [hm, projF]
        exact Submodule.sub_mem _ (xF le_rfl) (Submodule.smul_mem _ _ (aF _))
      rw [← hm, hTz, ψa]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (a'F _))
        (Submodule.sub_mem _ hmF (Submodule.smul_mem _ _ (a'F _)))
  have qF : ∀ i : Fin (r + 1), q (x i) ∈ Submodule.span R (x '' {k | k ≤ i}) := fun i => by
    induction i using Fin.cases with
    | zero =>
      obtain ⟨v', hv⟩ := hu.exists_left_inv
      have : x 0 = v' • a := by rw [ha, smul_smul, hv, one_smul]
      rw [this, map_smul, hqa]
      exact Submodule.smul_mem _ _ (aF _)
    | succ j =>
      have e := decomp H a b (x j.succ)
      rw [e, map_add, map_add, map_smul, map_smul, hqa, hqb, hax, zero_smul, add_zero]
      have := hqz ⟨_, projV_mem H hyp (x j.succ)⟩
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (aF _)) ?_
      rw [this]
      change ((p₂ (w j) : perp H a b) : V) ∈ _
      have hle : Submodule.span R (w '' {i | i ≤ j}) ≤
          (Submodule.span R (x '' {k | k ≤ j.succ})).comap (perp H a b).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        exact wF i j hi
      exact hle (hflag j)
  refine ⟨q.trans T, ⟨fun s t => ?_, fun z => ?_⟩, fun j => ?_⟩
  · change h (T (q s)) (T (q t)) = _
    rw [hT, hq]
  · change z ∈ L ↔ T (q z) ∈ L'
    rw [← mem_pullLat (p := T)]
    refine mem_iff_lift H hyp hL.2.1 hL₂.2.1 haL hbL ha₂ hb₂ q hq hqa hqb (fun m => ?_) z
    rw [hqz]
    exact hmem m
  · change T (q (x j)) ∈ _
    have : Submodule.span R (x '' {k | k ≤ j}) ≤
        (Submodule.span R (x '' {k | k ≤ j})).comap T.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact flagMono hi (TF i)
    exact this (qF j)

theorem perp_ne_top (hR : IsHermRing c 𝔬) (H : IsHerm c h) {x y : V} (hy : IsHyp h x y) :
    perp H x y ≠ ⊤ := by
  intro e
  have : y ∈ perp H x y := e ▸ Submodule.mem_top
  have h1 := ((mem_perp H).1 this).1
  rw [hy.xy] at h1
  have := hR.nontrivial
  exact one_ne_zero h1

theorem good_all (hR : IsHermRing c 𝔬) (hB : HasBase c 𝔬) (k : ℕ∞) :
    ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
      Module.length R V = k → Good c 𝔬 h := by
  induction k using WellFoundedLT.induction with
  | ind k IH =>
    intro V _ _ _ h H P hk
    have := hR.artinian
    have hperp : ∀ x y, IsHyp h x y → Good c 𝔬 (resForm h (perp H x y)) := fun x y hy =>
      IH _ (hk ▸ Submodule.length_lt (perp_ne_top hR H hy)) _ _ (isHerm_resForm H _)
        (isPerfect_resForm H P hy) rfl
    intro r
    cases r with
    | succ r =>
      intro x y hf L L' hL hL'
      exact flag_step hR H P hperp x y hf hL hL'
    | zero =>
      intro x y hf L L' hL hL'
      by_cases hn : ∀ s t, h s s = 0 → h s t ≠ 1
      · obtain ⟨p, hp⟩ := hB V h H P hn L L' hL hL'
        exact ⟨p, hp, fun j => j.elim0⟩
      · push_neg at hn
        obtain ⟨s, t, hs, hst⟩ := hn
        obtain ⟨two, htwo⟩ := hR.two.exists_left_inv
        have hc2 : c two = two := by
          have : c two * 2 = 1 := by
            have := congrArg c htwo
            rw [map_mul, map_one, map_ofNat] at this
            exact this
          calc c two = c two * (2 * two) := by rw [mul_comm 2 two, htwo, mul_one]
            _ = (c two * 2) * two := by ring
            _ = two := by rw [this, one_mul]
        have hts : h t s = 1 := by rw [H.symm s t, hst, map_one]
        have hct : c (h t t) = h t t := (H.symm t t).symm
        let t' := t - (two * h t t) • s
        have f1 : IsFrame h (fun _ : Fin 1 => s) (fun _ => t') := {
          xx := fun _ _ => hs
          yy := fun _ _ => by
            simp only [t']
            rw [herm_sub_left H, herm_sub_right H, herm_sub_right H, herm_smul_left H,
              herm_smul_left H, H.smul_right, H.smul_right, hs, hst, hts, map_mul, hc2, hct]
            linear_combination (- h t t) * htwo
          xy := fun i j => by
            have : i = j := Subsingleton.elim _ _
            simp only [t', this, if_true]
            rw [herm_sub_right H, H.smul_right, hs, hst]; ring }
        obtain ⟨p, hp, -⟩ := flag_step hR H P hperp _ _ f1 hL hL'
        exact ⟨p, hp, fun j => j.elim0⟩

theorem flagTransitive : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → HasBase c 𝔬 →
    FlagTransitive c 𝔬 := by
  intro R _ c 𝔬 hR hB V _ _ _ h H P r x y hf L L' hL hL'
  exact good_all hR hB _ V h H P rfl r x y hf L L' hL hL'

end Main

end GlobalTheory.CompanionTheory.KFin.Flag

end
