import Mathlib

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Loop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

abbrev Form (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V]
    [Module E V] : Type := V →ₗ[E] V →ₛₗ[starRingEnd E] E

def IsHerm (h : Form E V) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ ∀ x, (∀ y, h x y = 0) → x = 0

def InO (c a : E) : Prop := ∃ b : 𝓞 E, a = c * (b : E)

def HasSig (h : Form E V) (p q : ℕ) : Prop :=
  Module.finrank E V = p + q ∧ ∀ φ : E →+* ℂ, ∃ A B : Submodule E V,
    Module.finrank E A = p ∧ Module.finrank E B = q ∧
    (∀ x ∈ A, x ≠ 0 → 0 < (φ (h x x)).re) ∧ ∀ x ∈ B, x ≠ 0 → (φ (h x x)).re < 0

def PosOn (h : Form E V) (A : Submodule E V) : Prop :=
  ∀ φ : E →+* ℂ, ∀ x ∈ A, x ≠ 0 → 0 < (φ (h x x)).re

def NondegOn (h : Form E V) (A : Submodule E V) : Prop :=
  ∀ x ∈ A, (∀ y ∈ A, h x y = 0) → x = 0

def perp (h : Form E V) (A : Submodule E V) : Submodule E V where
  carrier := {x | ∀ a ∈ A, h x a = 0}
  add_mem' := fun hx hy a ha => by simp [hx a ha, hy a ha]
  zero_mem' := fun a _ => by simp
  smul_mem' := fun c x hx a ha => by simp [hx a ha]

def spanE (M : Submodule (𝓞 E) V) : Submodule E V := Submodule.span E (M : Set V)

def dual (h : Form E V) (M : Submodule (𝓞 E) V) : AddSubgroup V where
  carrier := {x | x ∈ spanE M ∧ ∀ m ∈ M, InO 1 (h x m)}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun m hm => by
    obtain ⟨a, ha⟩ := hx.2 m hm
    obtain ⟨b, hb⟩ := hy.2 m hm
    exact ⟨a + b, by simp [ha, hb]⟩⟩
  zero_mem' := ⟨zero_mem _, fun m _ => ⟨0, by simp⟩⟩
  neg_mem' := fun {x} hx => ⟨neg_mem hx.1, fun m hm => by
    obtain ⟨a, ha⟩ := hx.2 m hm
    exact ⟨-a, by simp [ha]⟩⟩

def gidx (A B : AddSubgroup V) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

def ldet (h : Form E V) (M : Submodule (𝓞 E) V) : ℝ := Real.sqrt (gidx (dual h M) M.toAddSubgroup)

def idx (A B : Submodule (𝓞 E) V) : ℕ := B.toAddSubgroup.relIndex A.toAddSubgroup

def SelfDual (h : Form E V) (Λ : Submodule (𝓞 E) V) : Prop :=
  Λ.FG ∧ spanE Λ = ⊤ ∧ dual h Λ = Λ.toAddSubgroup

variable [IsScalarTower (𝓞 E) E V]

def cut (Λ : Submodule (𝓞 E) V) (A : Submodule E V) : Submodule (𝓞 E) V :=
  Λ ⊓ A.restrictScalars (𝓞 E)

def mulN (g : ℕ) (Λ : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def projAlong (M : Submodule (𝓞 E) V) (A B : Submodule E V) : Submodule (𝓞 E) V :=
  (M ⊔ A.restrictScalars (𝓞 E)) ⊓ B.restrictScalars (𝓞 E)

structure Flag (h : Form E V) (Λ : Submodule (𝓞 E) V) (r T : ℕ) where
  e : Fin r → V
  z : V
  indep : LinearIndependent E e
  iso : ∀ a b, h (e a) (e b) = 0
  orth : ∀ a, h z (e a) = 0
  mem : z ∈ Λ
  norm : h z z = -(T : E)

namespace Flag

variable {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' : ℕ}

def X (F : Flag h Λ r T) : Submodule E V := Submodule.span E (Set.range F.e)

def Xp (F : Flag h Λ r T) : Submodule E V := F.X ⊔ Submodule.span E {F.z}

def U (F : Flag h Λ r T) : Submodule (𝓞 E) V := cut Λ F.X ⊔ Submodule.span (𝓞 E) {F.z}

def f (F : Flag h Λ r T) : Fin (r + 1) → V := Fin.snoc (α := fun _ => V) F.e F.z

def cong (F : Flag h Λ r T) (g : ℕ) : Submodule (𝓞 E) V := cut Λ F.X ⊔ mulN g Λ

def Zhat (F : Flag h Λ r T) (F' : Flag h Λ r T') : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => h (F'.f b) (F.f a)

def Dtop (F : Flag h Λ r T) (F' : Flag h Λ r T') : E := (F.Zhat F').det

def Dr (F : Flag h Λ r T) (F' : Flag h Λ r T') : E :=
  ((F.Zhat F').submatrix Fin.castSucc Fin.castSucc).det

def G (F : Flag h Λ r T) (F' : Flag h Λ r T') : E :=
  F.Dtop F' * star (F.Dtop F') - (T : E) * T' * (F.Dr F' * star (F.Dr F'))

def Gv (F : Flag h Λ r T) (F' : Flag h Λ r T') (w : InfinitePlace E) : ℝ :=
  w (F.Dtop F') ^ 2 - (T : ℝ) * T' * w (F.Dr F') ^ 2

def invSh (F : Flag h Λ r T) (F' : Flag h Λ r T') (w : InfinitePlace E) : ℝ :=
  Real.sqrt ((T : ℝ) * T') * w (F.Dr F') / Real.sqrt (F.Gv F' w)

def chSh (F : Flag h Λ r T) (F' : Flag h Λ r T') (w : InfinitePlace E) : ℝ :=
  w (F.Dtop F') / Real.sqrt (F.Gv F' w)

def admitted (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Prop :=
  F'.cong g = F.cong g ∧ F'.z - F.z ∈ F.cong g

def UE (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule E V := F.Xp ⊔ F'.Xp

def Transv (F : Flag h Λ r T) (F' : Flag h Λ r T') : Prop :=
  Module.finrank E (F.UE F') = 2 * r + 2 ∧ NondegOn h (F.UE F')

def IsTerm (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Prop := F.admitted F' g ∧ F.Transv F'

def UU (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule (𝓞 E) V := F.U ⊔ F'.U

def H (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule E V := perp h (F.UE F')

def Th (F : Flag h Λ r T) (F' : Flag h Λ r T') : Submodule (𝓞 E) V := cut Λ (F.H F')

def cardB (F : Flag h Λ r T) (F' : Flag h Λ r T') : ℕ := idx (cut Λ (F.UE F')) (F.UU F')

def cardGB (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : ℕ :=
  idx (mulN g (cut Λ (F.UE F')) ⊔ F.UU F') (F.UU F')

def La (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Submodule (𝓞 E) V where
  carrier := {x | x ∈ F.H F' ∧ ∃ a ∈ F.X, ∃ a' ∈ F'.X, x + a ∈ Λ ∧ x + a' ∈ Λ ∧ a' - a ∈ F.cong g}
  add_mem' := by
    rintro x y ⟨hx, a, ha, a', ha', h1, h2, h3⟩ ⟨hy, b, hb, b', hb', k1, k2, k3⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_, ?_⟩
    · have := add_mem h1 k1
      rwa [add_add_add_comm] at this
    · have := add_mem h2 k2
      rwa [add_add_add_comm] at this
    · have := add_mem h3 k3
      rwa [← add_sub_add_comm] at this
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, a, ha, a', ha', h1, h2, h3⟩
    refine ⟨Submodule.smul_of_tower_mem _ c hx, c • a, Submodule.smul_of_tower_mem _ c ha, c • a',
      Submodule.smul_of_tower_mem _ c ha', ?_, ?_, ?_⟩
    · rw [← smul_add]; exact Λ.smul_mem c h1
    · rw [← smul_add]; exact Λ.smul_mem c h2
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h3

def ix (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : ℕ := idx (F.La F' g) (F.Th F')

def G0 (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : ℝ :=
  ldet h (F.UU F') / (g : ℝ) ^ (Module.finrank ℚ E * (r + 1))

def Generic (F : Flag h Λ r T) (F' : Flag h Λ r T') (g : ℕ) : Prop :=
  ∀ x ∈ cut Λ (F.UE F'), ∃ v ∈ F.UU F', ∃ u ∈ F.U, ∃ u' ∈ F'.U, ∃ y ∈ Λ,
    u' - u = (g : E) • y ∧ x = v + y

def Sg (F : Flag h Λ r T) (F' : Flag h Λ r T') (y y' : V) (α α' : E) : Prop :=
  y ∈ F.UE F' ⊓ perp h F.Xp ∧ y' ∈ F.UE F' ⊓ perp h F'.Xp ∧
    y - y' - α • F.z - α' • F'.z ∈ F.X ⊔ F'.X

end Flag

structure Pair {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' : ℕ} (g : ℕ) (F : Flag h Λ r T)
    (F' F'' : Flag h Λ r T') where
  β : V →ₗ[E] V
  term' : F.IsTerm F' g
  term'' : F.IsTerm F'' g
  mapX : F'.X.map β = F''.X
  mapPerp : (perp h F'.X).map β = perp h F''.X
  isom : ∀ x ∈ perp h F'.X, ∀ y ∈ perp h F'.X, h (β x) (β y) = h x y
  mapL : ∀ x ∈ perp h F'.X, (∃ a ∈ F'.X, x + a ∈ Λ) ↔ ∃ a ∈ F''.X, β x + a ∈ Λ
  mapz : β F'.z - F''.z ∈ F''.X
  compat : ∀ l ∈ Λ, l ∈ perp h F'.X → ∀ a ∈ F''.X, β l + a ∈ Λ → β l + a - l ∈ F.cong g

namespace Pair

variable {h : Form E V} {Λ : Submodule (𝓞 E) V} {r T T' g : ℕ} {F : Flag h Λ r T}
  {F' F'' : Flag h Λ r T'}

def Th (P : Pair g F F' F'') : Submodule E V :=
  F.H F' ⊓ (((F.H F'').comap (LinearMap.snd E V V) ⊓
    F.X.comap (LinearMap.fst E V V - LinearMap.snd E V V) ⊓
    F''.X.comap (P.β ∘ₗ LinearMap.fst E V V - LinearMap.snd E V V)).map (LinearMap.fst E V V))

def Th2 (P : Pair g F F' F'') : Submodule E V := F.H F'' ⊓ (P.Th ⊔ F.X)

def M (P : Pair g F F' F'') : Submodule (𝓞 E) V := cut (F.La F' g) P.Th

def b (P : Pair g F F' F'') (x y : V) : E := h x y - h (P.β x) y

def s0 (P : Pair g F F' F'') (k : ℕ) : ℕ := k - Module.finrank E P.Th

def BNondeg (P : Pair g F F' F'') : Prop :=
  ∀ x ∈ F.H F', (∀ y ∈ F.H F'', P.b x y = 0) → x ∈ P.Th

def Psi (P : Pair g F F' F'') : Submodule (𝓞 E) V :=
  projAlong (F.La F' g) P.Th (F.H F' ⊓ perp h P.Th)

def Psi2 (P : Pair g F F' F'') : Submodule (𝓞 E) V :=
  projAlong (F.La F'' g) P.Th2 (F.H F'' ⊓ perp h P.Th2)

def Ga (P : Pair g F F' F'') (α α' δ δ' : E) : Prop :=
  ∃ y y' w w', F.Sg F' y y' α α' ∧ F.Sg F'' w w' δ δ' ∧ w - y ∈ F.X ∧ w' - P.β y' ∈ F''.X

def Scalar (P : Pair g F F' F'') : Prop := ∀ α α', P.Ga α α' α α'

end Pair

def HidaSetting (h : Form E V) (Λ : Submodule (𝓞 E) V) (k r g T T' : ℕ) : Prop :=
  IsHerm h ∧ HasSig h (k + r) (r + 1) ∧ SelfDual h Λ ∧ 2 ≤ k ∧ 2 ≤ g ∧ 1 ≤ T ∧ 1 ≤ T' ∧
    Nat.Coprime g (T * T')

end GlobalTheory.CompanionTheory.Loop
