import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans

set_option autoImplicit false

noncomputable section

open CategoryTheory DividedPowers

namespace GlobalTheory.LogCris

structure Base : Type 1 where

  R : Type
  [ring : CommRing R]

  I : Ideal R

  γ : DividedPowers I

  t : R

  p : ℕ

attribute [instance] Base.ring

structure LogFun (k : Type) [CommRing k] (τ : k) : Type 1 where

  ι : Type
  [fin : Fintype ι]

  A : Type

  Pt : CommRingCat.{0} ⥤ Type

  str : ∀ {B : CommRingCat.{0}}, Pt.obj B → (k →+* B)
  str_map : ∀ {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : Pt.obj B), str (Pt.map φ y) = φ.hom.comp (str y)

  In : A → ∀ {B : CommRingCat.{0}}, Pt.obj B → Prop
  in_map : ∀ {α} {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : Pt.obj B}, In α y → In α (Pt.map φ y)

  f : A → ι → ∀ {B : CommRingCat.{0}}, Pt.obj B → B
  f_map : ∀ {α} (i) {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : Pt.obj B}, In α y → f α i (Pt.map φ y) = φ.hom (f α i y)

  g : A → A → ι → ∀ {B : CommRingCat.{0}}, Pt.obj B → Bˣ
  g_map : ∀ {α β} (i) {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : Pt.obj B}, In α y → In β y →
    g α β i (Pt.map φ y) = Units.map φ.hom.toMonoidHom (g α β i y)
  f_eq : ∀ {α β} (i) {B : CommRingCat.{0}} {y : Pt.obj B}, In α y → In β y → f α i y = g α β i y * f β i y
  g_self : ∀ {α} (i) {B : CommRingCat.{0}} {y : Pt.obj B}, In α y → g α α i y = 1
  g_comp : ∀ {α β γ} (i) {B : CommRingCat.{0}} {y : Pt.obj B}, In α y → In β y → In γ y →
    g α β i y * g β γ i y = g α γ i y
  prod_f : ∀ {α} {B : CommRingCat.{0}} {y : Pt.obj B}, In α y → ∏ i, f α i y = str y τ
  prod_g : ∀ {α β} {B : CommRingCat.{0}} {y : Pt.obj B}, In α y → In β y → ∏ i, g α β i y = 1

attribute [instance] LogFun.fin

def LogFun.Covers {k : Type} [CommRing k] {τ : k} (L : LogFun k τ) : Prop :=
  ∀ (B : CommRingCat.{0}) (y : L.Pt.obj B), ∃ (s : Finset B), Ideal.span (s : Set B) = ⊤ ∧
    ∀ g ∈ s, ∃ α, L.In α (L.Pt.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) y)

abbrev Base.Fun (b : Base) : Type 1 := LogFun (b.R ⧸ b.I) (Ideal.Quotient.mk _ b.t)

variable {b : Base} (L : b.Fun)

structure Thick : Type 1 where

  B : Type
  [ring : CommRing B]

  i : b.R →+* B

  J : Ideal B

  δ : DividedPowers J
  adm : (b.p ≠ 0 → IsNilpotent (b.p : B)) ∧ (b.p = 0 → IsNilpotent J)
  compat : IsDPMorphism b.γ δ i

  α : L.A

  y : L.Pt.obj (CommRingCat.of (B ⧸ J))
  inα : L.In α y
  w : ∀ r, L.str y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk J (i r)

  x : L.ι → B

  v : L.ι → (B ⧸ J)ˣ

  s : Bˣ
  hx : ∀ j, Ideal.Quotient.mk J (x j) = v j * L.f α j y
  hs : ∏ j, x j = s * i b.t
  hv : Units.map (Ideal.Quotient.mk J).toMonoidHom s = ∏ j, v j

attribute [instance] Thick.ring

namespace Thick

variable {L}

@[ext] structure Hom (T T' : Thick L) where

  φ : T.B →+* T'.B

  u : L.ι → T'.Bˣ
  comm : ∀ r, φ (T.i r) = T'.i r
  dp : IsDPMorphism T.δ T'.δ φ
  hle : T.J ≤ T'.J.comap φ
  pt : L.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y
  hx : ∀ j, T'.x j = u j * φ (T.x j)
  hs : T'.s = (∏ j, u j) * Units.map φ.toMonoidHom T.s
  hv : ∀ j, T'.v j * L.g T'.α T.α j T'.y =
    Units.map (Ideal.Quotient.mk T'.J).toMonoidHom (u j) * Units.map (Ideal.quotientMap T'.J φ hle).toMonoidHom (T.v j)

theorem le_id (T : Thick L) : T.J ≤ T.J.comap (RingHom.id T.B) := fun _ h => h

theorem le_comp {T T' T'' : Thick L} (f : Hom T T') (g : Hom T' T'') : T.J ≤ T''.J.comap (g.φ.comp f.φ) :=
  fun _ h => g.hle (f.hle h)

theorem qmap_id (T : Thick L) (h) : Ideal.quotientMap T.J (RingHom.id T.B) h = RingHom.id _ := by
  ext; rfl

theorem qmap_comp {T T' T'' : Thick L} (f : Hom T T') (g : Hom T' T'') (h) :
    Ideal.quotientMap T''.J (g.φ.comp f.φ) h =
      (Ideal.quotientMap T''.J g.φ g.hle).comp (Ideal.quotientMap T'.J f.φ f.hle) := by
  ext; rfl

def Hom.id (T : Thick L) : Hom T T where
  φ := RingHom.id _
  u _ := 1
  comm _ := rfl
  dp := (DPMorphism.id T.δ).isDPMorphism
  hle := le_id T
  pt := by rw [qmap_id, CommRingCat.ofHom_id, L.Pt.map_id]; rfl
  hx _ := by simp
  hs := by ext; simp
  hv j := by rw [L.g_self j T.inα, qmap_id]; ext; simp

def Hom.comp {T T' T'' : Thick L} (f : Hom T T') (g : Hom T' T'') : Hom T T'' where
  φ := g.φ.comp f.φ
  u j := g.u j * Units.map g.φ.toMonoidHom (f.u j)
  comm r := by rw [RingHom.comp_apply, f.comm, g.comm]
  dp := IsDPMorphism.comp _ g.dp f.dp
  hle := le_comp f g
  pt := by
    rw [qmap_comp, CommRingCat.ofHom_comp, L.Pt.map_comp, ← g.pt, ← f.pt]; rfl
  hx j := by rw [g.hx, f.hx]; simp [mul_assoc]
  hs := by
    rw [g.hs, f.hs, Finset.prod_mul_distrib, map_mul, map_prod, mul_assoc]; rfl
  hv j := by
    have h1 : L.In T.α T'.y := f.pt ▸ L.in_map _ T.inα
    have h2 : L.In T'.α T''.y := g.pt ▸ L.in_map _ T'.inα
    have h3 : L.In T.α T''.y := g.pt ▸ L.in_map _ h1
    have e := L.g_map j (CommRingCat.ofHom (Ideal.quotientMap T''.J g.φ g.hle)) T'.inα h1
    rw [g.pt] at e
    have e2 := congrArg (Units.map (Ideal.quotientMap T''.J g.φ g.hle).toMonoidHom) (f.hv j)
    rw [map_mul, map_mul] at e2
    rw [← L.g_comp j T''.inα h2 h3, ← mul_assoc, g.hv, e, mul_assoc]
    erw [e2]
    rw [qmap_comp, map_mul, mul_assoc]
    rfl

instance : Category (Thick L) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext rfl (funext fun j => by simp [Hom.comp, Hom.id])
  comp_id f := Hom.ext rfl (funext fun j => by ext; simp [Hom.comp, Hom.id])
  assoc f g h := Hom.ext rfl (funext fun j => by ext; simp [Hom.comp, mul_assoc])

def pdPow (T : Thick L) (r : ℕ) : Ideal T.B :=
  Ideal.span {z | ∃ l : List (ℕ × T.B), (∀ q ∈ l, q.2 ∈ T.J) ∧ r ≤ (l.map Prod.fst).sum ∧
    z = (l.map fun q => T.δ.dpow q.1 q.2).prod}

theorem i_mem (T : Thick L) {x : b.R} (hx : x ∈ b.I) : T.i x ∈ T.J :=
  T.compat.1 (Ideal.mem_map_of_mem T.i hx)

theorem dpow_i (T : Thick L) (n : ℕ) {x : b.R} (hx : x ∈ b.I) : T.δ.dpow n (T.i x) = T.i (b.γ.dpow n x) :=
  T.compat.2 x hx

theorem pdPow_zero (T : Thick L) : T.pdPow 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem pdPow_anti (T : Thick L) {r r' : ℕ} (h : r ≤ r') : T.pdPow r' ≤ T.pdPow r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem J_le_pdPow_one (T : Thick L) : T.J ≤ T.pdPow 1 := by
  intro x hx
  refine Ideal.subset_span ⟨[(1, x)], by simpa using hx, by simp, ?_⟩
  simp [T.δ.dpow_one hx]

end Thick

def O : Thick L ⥤ ModuleCat.{0} b.R where
  obj T := letI := T.i.toAlgebra; ModuleCat.of b.R T.B
  map {T T'} f :=
    letI := T.i.toAlgebra; letI := T'.i.toAlgebra
    ModuleCat.ofHom
      { toFun := f.φ
        map_add' := map_add _
        map_smul' := fun r z => by
          change f.φ (T.i r * z) = T'.i r * f.φ z
          rw [map_mul, f.comm] }
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev H (n : ℕ) : Type 1 := CatH.H (O L) n

def Fil (n r : ℕ) : Set (H L n) :=
  {c | ∃ z : LinearMap.ker (CatH.d (O L) n), Submodule.Quotient.mk z = c ∧
    ∀ s, (show (s.obj (Fin.last n)).B from z.1 s) ∈ (s.obj (Fin.last n)).pdPow r}

theorem fil_zero (n : ℕ) : Fil L n 0 = Set.univ := by
  ext c
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z, rfl, fun s => by rw [Thick.pdPow_zero]; trivial⟩

theorem fil_anti (n : ℕ) {r r' : ℕ} (h : r ≤ r') : Fil L n r' ⊆ Fil L n r :=
  fun _ ⟨z, hz, hs⟩ => ⟨z, hz, fun s => Thick.pdPow_anti _ h (hs s)⟩

structure Mor {b b' : Base} (L : b.Fun) (L' : b'.Fun) (σ : b.R →+* b'.R) where
  hp : b.p = b'.p
  hI : IsDPMorphism b.γ b'.γ σ

  a : b'.Rˣ
  ha : (a : b'.R) - 1 ∈ b'.I

  m : ℕ
  ht : σ b.t = a * b'.t ^ m

  e : L.ι → L'.ι → ℕ
  he : ∀ j, ∑ i, e i j = m

  c : L'.A → L.A

  pt : L'.Pt ⟶ L.Pt
  str : ∀ {B : CommRingCat.{0}} (y : L'.Pt.obj B) (r : b.R),
    L.str (pt.app B y) (Ideal.Quotient.mk _ r) = L'.str y (Ideal.Quotient.mk _ (σ r))
  inc : ∀ {β} {B : CommRingCat.{0}} {y : L'.Pt.obj B}, L'.In β y → L.In (c β) (pt.app B y)

  w : L'.A → L.ι → ∀ {B : CommRingCat.{0}}, L'.Pt.obj B → Bˣ
  w_map : ∀ {β} (i) {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : L'.Pt.obj B}, L'.In β y →
    w β i (L'.Pt.map φ y) = Units.map φ.hom.toMonoidHom (w β i y)
  hf : ∀ {β} (i) {B : CommRingCat.{0}} {y : L'.Pt.obj B}, L'.In β y →
    ∏ j, L'.f β j y ^ e i j = w β i y * L.f (c β) i (pt.app B y)
  hg : ∀ {β γ} (i) {B : CommRingCat.{0}} {y : L'.Pt.obj B}, L'.In β y → L'.In γ y →
    w β i y * L.g (c β) (c γ) i (pt.app B y) = (∏ j, L'.g β γ j y ^ e i j) * w γ i y
  hw : ∀ {β} {B : CommRingCat.{0}} {y : L'.Pt.obj B}, L'.In β y → ∏ i, w β i y = 1

namespace Mor

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : Mor L L' σ)

theorem prod_pow {M : Type} [CommMonoid M] (z : L'.ι → M) : ∏ i, ∏ j, z j ^ m.e i j = (∏ j, z j) ^ m.m := by
  rw [Finset.prod_comm, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => by rw [Finset.prod_pow_eq_pow_sum, m.he]

def obj (T : Thick L') : Thick L where
  B := T.B
  i := T.i.comp σ
  J := T.J
  δ := T.δ
  adm := m.hp ▸ T.adm
  compat := IsDPMorphism.comp T.δ T.compat m.hI
  α := m.c T.α
  y := m.pt.app _ T.y
  inα := m.inc T.inα
  w r := by rw [m.str, T.w]; rfl
  x i := ∏ j, T.x j ^ m.e i j
  v i := (∏ j, T.v j ^ m.e i j) * m.w T.α i T.y
  s := T.s ^ m.m * (Units.map T.i.toMonoidHom m.a)⁻¹
  hx i := by
    rw [map_prod, Units.val_mul, mul_assoc]
    erw [← m.hf i T.inα]
    rw [Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [map_pow, T.hx, mul_pow, Units.val_pow_eq_pow_val]
  hs := by
    rw [m.prod_pow, T.hs, RingHom.comp_apply, m.ht, map_mul, map_pow, mul_pow, Units.val_mul, mul_assoc]
    congr 1
    exact ((Units.map T.i.toMonoidHom m.a).inv_mul_cancel_left _).symm
  hv := by
    have h : Units.map (Ideal.Quotient.mk T.J).toMonoidHom (Units.map T.i.toMonoidHom m.a) = 1 := by
      ext
      have := T.compat.1 (Ideal.mem_map_of_mem T.i m.ha)
      rw [map_sub, map_one] at this
      exact Ideal.Quotient.eq.2 this
    rw [map_mul, map_inv, h, inv_one, mul_one, map_pow, T.hv, Finset.prod_mul_distrib, m.prod_pow]
    erw [m.hw T.inα]
    rw [mul_one]

def map {T T' : Thick L'} (f : T ⟶ T') : m.obj T ⟶ m.obj T' where
  φ := f.φ
  u i := ∏ j, f.u j ^ m.e i j
  comm r := f.comm _
  dp := f.dp
  hle := f.hle
  pt := by
    have := f.pt
    change L.Pt.map _ (m.pt.app _ T.y) = m.pt.app _ T'.y
    rw [← this]
    exact (ConcreteCategory.congr_hom (m.pt.naturality _) T.y).symm
  hx i := by
    change ∏ j, T'.x j ^ m.e i j = ((∏ j, f.u j ^ m.e i j : T'.Bˣ) : T'.B) * f.φ (∏ j, T.x j ^ m.e i j)
    rw [map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [f.hx, mul_pow, map_pow, Units.val_pow_eq_pow_val]
  hs := by
    change T'.s ^ m.m * (Units.map T'.i.toMonoidHom m.a)⁻¹ =
      (∏ i, ∏ j, f.u j ^ m.e i j) * Units.map f.φ.toMonoidHom (T.s ^ m.m * (Units.map T.i.toMonoidHom m.a)⁻¹)
    have h : Units.map f.φ.toMonoidHom (Units.map T.i.toMonoidHom m.a) = Units.map T'.i.toMonoidHom m.a :=
      Units.ext (f.comm _)
    rw [m.prod_pow, f.hs, map_mul, map_inv, h, map_pow, mul_pow, mul_assoc]
  hv i := by
    have h1 : L'.In T.α T'.y := f.pt ▸ L'.in_map _ T.inα
    have e := m.w_map i (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) T.inα
    rw [f.pt] at e
    change (∏ j, T'.v j ^ m.e i j) * m.w T'.α i T'.y * L.g (m.c T'.α) (m.c T.α) i (m.pt.app _ T'.y) =
      Units.map (Ideal.Quotient.mk T'.J).toMonoidHom (∏ j, f.u j ^ m.e i j) *
        Units.map (Ideal.quotientMap T'.J f.φ f.hle).toMonoidHom ((∏ j, T.v j ^ m.e i j) * m.w T.α i T.y)
    rw [mul_assoc]
    erw [m.hg i T'.inα h1, e]
    rw [← mul_assoc, map_mul, ← mul_assoc, map_prod, map_prod]
    congr 1
    erw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by
      rw [map_pow, map_pow, ← mul_pow]
      erw [← mul_pow, f.hv j]

def functor : Thick L' ⥤ Thick L where
  obj := m.obj
  map := m.map
  map_id T := Thick.Hom.ext rfl (funext fun i => by
    change ∏ j, (1 : T.Bˣ) ^ m.e i j = 1
    simp)
  map_comp {T T' T''} f g := Thick.Hom.ext rfl (funext fun i => by
    change ∏ j, (g.u j * Units.map g.φ.toMonoidHom (f.u j)) ^ m.e i j =
      (∏ j, g.u j ^ m.e i j) * Units.map g.φ.toMonoidHom (∏ j, f.u j ^ m.e i j)
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow, map_pow])

def pull (n : ℕ) : H L n →ₛₗ[σ] H L' n :=
  CatH.Mor.pull (F := O L) (F' := O L')
    { G := m.functor
      τ := fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      nat := fun _ _ => rfl } n

open Classical in

def id (L : b.Fun) : Mor L L (RingHom.id b.R) where
  hp := rfl
  hI := ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
  a := 1
  ha := by simp
  m := 1
  ht := by simp
  e i j := if i = j then 1 else 0
  he j := by simp
  c α := α
  pt := 𝟙 L.Pt
  str _ _ := rfl
  inc h := h
  w _ _ _ _ := 1
  w_map _ _ _ _ _ _ := by simp
  hf i _ _ _ := by simp [pow_ite]
  hg i _ _ _ _ := by simp [pow_ite]
  hw _ := by simp

end Mor

namespace Ex

theorem isDPMorphism_bot {A B : Type} [CommRing A] [DecidableEq A] [CommRing B] {J : Ideal B} (δ : DividedPowers J)
    (f : A →+* B) : IsDPMorphism (dividedPowersBot A) δ f := by
  rw [isDPMorphism_iff]
  refine ⟨by rw [Ideal.map_bot]; exact bot_le, fun n hn a ha => ?_⟩
  rw [Ideal.mem_bot.1 ha, map_zero, δ.dpow_eval_zero hn, (dividedPowersBot A).dpow_eval_zero hn, map_zero]

abbrev base : Base where
  R := ℚ
  I := ⊥
  γ := dividedPowersBot ℚ
  t := 0
  p := 0

abbrev nodePt (k : Type) [CommRing k] (τ : k) : CommRingCat.{0} ⥤ Type where
  obj B := {q : (k →+* B) × B × B // q.2.1 * q.2.2 = q.1 τ}
  map φ := TypeCat.ofHom fun q => ⟨(φ.hom.comp q.1.1, φ.hom q.1.2.1, φ.hom q.1.2.2), by
    simp only [RingHom.comp_apply, ← map_mul, q.2]⟩
  map_id _ := by ext q <;> rfl
  map_comp _ _ := by ext q <;> rfl

abbrev node (k : Type) [CommRing k] (τ : k) : LogFun k τ where
  ι := Fin 2
  A := Unit
  Pt := nodePt k τ
  str y := y.1.1
  str_map _ _ := rfl
  In _ _ _ := True
  in_map _ _ _ := trivial
  f _ i _ y := ![y.1.2.1, y.1.2.2] i
  f_map i _ _ φ y _ := by fin_cases i <;> rfl
  g _ _ _ _ _ := 1
  g_map _ _ _ _ _ _ _ := by simp
  f_eq _ _ _ _ _ := by simp
  g_self _ _ _ _ := rfl
  g_comp _ _ _ _ _ _ := by simp
  prod_f {_ _ y} _ := by simpa [Fin.prod_univ_two] using y.2
  prod_g _ _ := by simp

theorem node_covers (k : Type) [CommRing k] (τ : k) : (node k τ).Covers :=
  fun _ _ => ⟨{1}, by simp, fun _ _ => ⟨(), trivial⟩⟩

abbrev nodeL : base.Fun := node _ _

abbrev D := DualNumber ℚ

abbrev J : Ideal D := Ideal.span {DualNumber.eps}

theorem J_sq : J ^ 2 = 0 := by
  rw [Ideal.span_singleton_pow, pow_two, DualNumber.eps_mul_eps, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

open Classical in

def δJ : DividedPowers J := RatAlgebra.dividedPowers J

def T : Thick nodeL where
  B := D
  i := algebraMap ℚ D
  J := J
  δ := δJ
  adm := ⟨fun h => absurd rfl h, fun _ => ⟨2, J_sq⟩⟩
  compat := isDPMorphism_bot _ _
  α := ()
  y := ⟨(Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp (algebraMap ℚ D)) (fun a ha => by
      rw [(Submodule.mem_bot _).1 ha, map_zero]), Ideal.Quotient.mk J DualNumber.eps,
      Ideal.Quotient.mk J DualNumber.eps), by
    change _ = Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (0 : ℚ))
    rw [Ideal.Quotient.lift_mk, ← map_mul, DualNumber.eps_mul_eps]; simp⟩
  inα := trivial
  w r := Ideal.Quotient.lift_mk _ _ _
  x := ![DualNumber.eps, DualNumber.eps]
  v _ := 1
  s := 1
  hx j := by fin_cases j <;> simp [nodeL, node, nodePt]
  hs := by simp [Fin.prod_univ_two, DualNumber.eps_mul_eps, base]
  hv := by simp

theorem T_J_ne_bot : T.J ≠ ⊥ := by
  intro h
  have : (DualNumber.eps : D) ∈ (⊥ : Ideal D) := h ▸ Ideal.subset_span rfl
  have h0 : (DualNumber.eps : D) = 0 := (Submodule.mem_bot _).1 this
  simpa using congrArg TrivSqZeroExt.snd h0

def sq : Mor nodeL nodeL (RingHom.id ℚ) where
  hp := rfl
  hI := isDPMorphism_bot _ _
  a := 1
  ha := by simp
  m := 2
  ht := by simp [base]
  e i j := if i = j then 2 else 0
  he j := by simp
  c := fun α => α
  pt := { app := fun B => TypeCat.ofHom fun y => ⟨(y.1.1, y.1.2.1 ^ 2, y.1.2.2 ^ 2), by
            rw [← mul_pow, y.2]; simp⟩
          naturality := fun _ _ φ => by
            ext y <;> first | rfl | exact (map_pow (CommRingCat.Hom.hom φ) _ 2).symm }
  str _ _ := rfl
  inc _ := trivial
  w _ _ _ _ := 1
  w_map _ _ _ _ _ _ := by simp
  hf i _ _ _ := by fin_cases i <;> simp [Fin.prod_univ_two, nodeL, node, nodePt]
  hg _ _ _ := by simp
  hw _ := by simp

example : Nonempty (Thick nodeL) := ⟨T⟩

example : (sq.functor.obj T).x 0 = 0 := by
  show ∏ j, T.x j ^ sq.e 0 j = 0
  rw [Fin.prod_univ_two]
  simp [sq, pow_two]
  exact DualNumber.eps_mul_eps

example : ((Mor.id nodeL).functor.obj T).B = D := rfl

end Ex

end GlobalTheory.LogCris
