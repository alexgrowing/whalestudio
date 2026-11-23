import Mathlib

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Ord

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def ordPart (U : Module.End R M) : Submodule R M := ⨅ n : ℕ, LinearMap.range (U ^ n)

theorem mem_ordPart {U : Module.End R M} {x : M} : x ∈ ordPart U ↔ ∀ n : ℕ, ∃ y, (U ^ n) y = x := by
  simp [ordPart, Submodule.mem_iInf]

theorem map_mem_smul_top {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (J : Ideal R)
    {x : M} (hx : x ∈ (J • ⊤ : Submodule R M)) : f x ∈ (J • ⊤ : Submodule R N) := by
  have h1 := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

def nilPart (I : Ideal R) (U : Module.End R M) : Submodule R M where
  carrier := {x | ∀ k : ℕ, ∃ n : ℕ, (U ^ n) x ∈ (I ^ k • ⊤ : Submodule R M)}
  zero_mem' := fun k => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨n, hn⟩ := hx k
    obtain ⟨m, hm⟩ := hy k
    refine ⟨n + m, ?_⟩
    rw [map_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hn
    · rw [pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hm
  smul_mem' := by
    intro c x hx k
    obtain ⟨n, hn⟩ := hx k
    exact ⟨n, by rw [map_smul]; exact Submodule.smul_mem _ _ hn⟩

structure IsOrdProj (I : Ideal R) (U e : Module.End R M) : Prop where
  idem : IsIdempotentElem e
  comm : Commute U e
  bij : Set.BijOn U (LinearMap.range e) (LinearMap.range e)
  nil : ∀ k : ℕ, ∃ n : ℕ, ∀ x, (U ^ n) (x - e x) ∈ (I ^ k • ⊤ : Submodule R M)

def IsFactLim (I : Ideal R) (U e : Module.End R M) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ x, (U ^ j.factorial) x - e x ∈ (I ^ k • ⊤ : Submodule R M)

open Classical in

noncomputable def ordProj (I : Ideal R) (U : Module.End R M) : Module.End R M :=
  if h : ∃ e, IsOrdProj I U e then h.choose else 0

theorem isOrdProj_ordProj {I : Ideal R} {U : Module.End R M} (h : ∃ e, IsOrdProj I U e) :
    IsOrdProj I U (ordProj I U) := by
  unfold ordProj
  rw [dif_pos h]
  exact h.choose_spec

variable (M) in

structure OrdAdm (I : Ideal R) : Prop where
  complete : IsAdicComplete I M
  finLen : ∀ k : ℕ, IsFiniteLength R (M ⧸ (I ^ k • ⊤ : Submodule R M))

theorem IsOrdProj.mono {I J : Ideal R} (hIJ : I ≤ J) {U e : Module.End R M} (h : IsOrdProj I U e) :
    IsOrdProj J U e :=
  ⟨h.idem, h.comm, h.bij, fun k => (h.nil k).imp fun _ hn x =>
    Submodule.smul_mono (Ideal.pow_right_mono hIJ k) le_rfl (hn x)⟩

end Ord

section Map

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
  {M : Type*} [AddCommGroup M] [Module A M]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

theorem pow_intertwine {U : Module.End A M} {U' : Module.End A' M'} {f : M →ₗ[A] M'}
    (h : ∀ x, f (U x) = U' (f x)) (n : ℕ) (x : M) : f ((U ^ n) x) = (U' ^ n) (f x) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

theorem map_mem_ordPart {U : Module.End A M} {U' : Module.End A' M'} {f : M →ₗ[A] M'}
    (h : ∀ x, f (U x) = U' (f x)) {x : M} (hx : x ∈ ordPart U) : f x ∈ ordPart U' := by
  refine mem_ordPart.2 fun n => ?_
  obtain ⟨y, rfl⟩ := mem_ordPart.1 hx n
  exact ⟨f y, (pow_intertwine h n y).symm⟩

def ordMap {U : Module.End A M} {U' : Module.End A' M'} (f : M →ₗ[A] M')
    (h : ∀ x, f (U x) = U' (f x)) : ordPart U →ₗ[A] ordPart U' where
  toFun x := ⟨f x, map_mem_ordPart h x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

@[simp] theorem coe_ordMap {U : Module.End A M} {U' : Module.End A' M'} (f : M →ₗ[A] M')
    (h : ∀ x, f (U x) = U' (f x)) (x : ordPart U) : (ordMap f h x : M') = f x := rfl

def ordEnd {U : Module.End A M} (V : Module.End A M) (h : Commute V U) : Module.End A (ordPart U) :=
  ordMap (A' := A) V fun x => LinearMap.congr_fun h.eq x

@[simp] theorem coe_ordEnd {U : Module.End A M} (V : Module.End A M) (h : Commute V U)
    (x : ordPart U) : (ordEnd V h x : M) = V x := rfl

end Map

section Lim

variable {R : Type*} [CommRing R] {P : ℕ → Type*} [∀ b, AddCommGroup (P b)] [∀ b, Module R (P b)]
  {Q : ℕ → Type*} [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)]

def towerLim (t : ∀ b, P (b + 1) →ₗ[R] P b) : Submodule R (∀ b, P b) where
  carrier := {x | ∀ b, t b (x (b + 1)) = x b}
  zero_mem' := fun b => by simp
  add_mem' := fun hx hy b => by simp [hx b, hy b]
  smul_mem' := fun c x hx b => by simp [hx b]

def towerProj (t : ∀ b, P (b + 1) →ₗ[R] P b) (b : ℕ) : towerLim t →ₗ[R] P b :=
  (LinearMap.proj b).comp (towerLim t).subtype

@[simp] theorem towerProj_apply (t : ∀ b, P (b + 1) →ₗ[R] P b) (b : ℕ) (x : towerLim t) :
    towerProj t b x = x.1 b := rfl

def towerLift (t : ∀ b, P (b + 1) →ₗ[R] P b) {X : Type*} [AddCommGroup X] [Module R X]
    (f : ∀ b, X →ₗ[R] P b) (h : ∀ b x, t b (f (b + 1) x) = f b x) : X →ₗ[R] towerLim t :=
  LinearMap.codRestrict _ (LinearMap.pi f) fun x b => h b x

@[simp] theorem towerProj_towerLift (t : ∀ b, P (b + 1) →ₗ[R] P b) {X : Type*} [AddCommGroup X]
    [Module R X] (f : ∀ b, X →ₗ[R] P b) (h : ∀ b x, t b (f (b + 1) x) = f b x) (b : ℕ) (x : X) :
    towerProj t b (towerLift t f h x) = f b x := rfl

def towerMap (t : ∀ b, P (b + 1) →ₗ[R] P b) (s : ∀ b, Q (b + 1) →ₗ[R] Q b) (f : ∀ b, P b →ₗ[R] Q b)
    (h : ∀ b x, s b (f (b + 1) x) = f b (t b x)) : towerLim t →ₗ[R] towerLim s :=
  towerLift s (fun b => (f b).comp (towerProj t b)) fun b x => by
    simp only [LinearMap.comp_apply, towerProj_apply, h, x.2 b]

@[simp] theorem towerProj_towerMap (t : ∀ b, P (b + 1) →ₗ[R] P b) (s : ∀ b, Q (b + 1) →ₗ[R] Q b)
    (f : ∀ b, P b →ₗ[R] Q b) (h : ∀ b x, s b (f (b + 1) x) = f b (t b x)) (b : ℕ) (x : towerLim t) :
    towerProj s b (towerMap t s f h x) = f b (towerProj t b x) := rfl

structure IsTowerComplete (I : ℕ → Ideal R) : Prop where
  anti : Antitone I
  sep : ⨅ b, I b = ⊥
  lim : ∀ a : ℕ → R, (∀ b, a (b + 1) - a b ∈ I b) → ∃ L : R, ∀ b, L - a b ∈ I b

end Lim

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
