import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory
open GlobalTheory.CatH (face toLast)

universe w w' w'' v u v' u' v'' u''

namespace CrystallineSemistableComparison

section UpTo
variable {R : Type} [CommRing R] {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

def InjUpTo (s : R) (f : M →ₗ[R] N) : Prop := ∀ x : M, f x = 0 → s • x = 0

def SurjUpTo (s : R) (f : M →ₗ[R] N) : Prop := ∀ y : N, ∃ x : M, f x = s • y

def UpTo (s : R) (f : M →ₗ[R] N) : Prop := InjUpTo s f ∧ SurjUpTo s f

def Almost (I : Ideal R) (f : M →ₗ[R] N) : Prop := ∀ s ∈ I, UpTo s f

def ExactUpTo {P : Type w''} [AddCommGroup P] [Module R P] (s : R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Prop :=
  ∀ y, g y = 0 → ∃ x, f x = s • y

def Killed (s : R) (M : Type w) [AddCommGroup M] [Module R M] : Prop := ∀ x : M, s • x = 0
end UpTo

structure Cx (R : Type) [CommRing R] : Type (w + 1) where

  X : ℕ → Type w
  [instAddCommGroup : ∀ n, AddCommGroup (X n)]
  [instModule : ∀ n, Module R (X n)]

  d : ∀ n, X n →ₗ[R] X (n + 1)

  dd : ∀ n (x : X n), d (n + 1) (d n x) = 0

attribute [instance] Cx.instAddCommGroup Cx.instModule

universe w₁ w₂ w₃

namespace Cx

variable {R : Type} [CommRing R] (C : Cx.{w} R)

def B : (n : ℕ) → Submodule R (C.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (C.d n)

abbrev Z (n : ℕ) : Submodule R (C.X n) := LinearMap.ker (C.d n)

abbrev H (n : ℕ) : Type w := C.Z n ⧸ (C.B n).comap (C.Z n).subtype

def cls {n : ℕ} (x : C.X n) (hx : C.d n x = 0) : C.H n := Submodule.Quotient.mk ⟨x, hx⟩

variable {C}

@[simp] theorem mem_B_zero {x : C.X 0} : x ∈ C.B 0 ↔ x = 0 := Submodule.mem_bot R

theorem mem_B_succ {n : ℕ} {x : C.X (n + 1)} : x ∈ C.B (n + 1) ↔ ∃ y, C.d n y = x :=
  LinearMap.mem_range

theorem d_mem_B (n : ℕ) (y : C.X n) : C.d n y ∈ C.B (n + 1) := mem_B_succ.2 ⟨y, rfl⟩

@[ext]
structure Hom {R S : Type} [CommRing R] [CommRing S] (C : Cx.{w₁} R) (D : Cx.{w₂} S)
    (σ : R →+* S) where

  f : ∀ n, C.X n →ₛₗ[σ] D.X n

  comm : ∀ n (x : C.X n), D.d n (f n x) = f (n + 1) (C.d n x)

namespace Hom

variable {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  {C₁ : Cx.{w₁} R₁} {C₂ : Cx.{w₂} R₂} {C₃ : Cx.{w₃} R₃}
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable (C) in

def id : Hom C C (RingHom.id R) where
  f _ := LinearMap.id
  comm _ _ := rfl

def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (F : Hom C₁ C₂ σ₁₂) (G : Hom C₂ C₃ σ₂₃) :
    Hom C₁ C₃ σ₁₃ where
  f n := (G.f n).comp (F.f n)
  comm n x := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [G.comm, F.comm]

variable (F : Hom C₁ C₂ σ₁₂)

theorem d_f_eq_zero {n : ℕ} {x : C₁.X n} (hx : C₁.d n x = 0) : C₂.d n (F.f n x) = 0 := by
  rw [F.comm, hx, map_zero]

theorem map_mem_B {n : ℕ} {x : C₁.X n} (hx : x ∈ C₁.B n) : F.f n x ∈ C₂.B n := by
  cases n with
  | zero => rw [mem_B_zero.1 hx, map_zero]; exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨y, rfl⟩ := mem_B_succ.1 hx
    exact mem_B_succ.2 ⟨F.f n y, F.comm n y⟩

def mapZ (n : ℕ) : C₁.Z n →ₛₗ[σ₁₂] C₂.Z n where
  toFun z := ⟨F.f n z.1, F.d_f_eq_zero z.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smulₛₗ _ _ _)

theorem mapZ_le (n : ℕ) :
    (C₁.B n).comap (C₁.Z n).subtype ≤ ((C₂.B n).comap (C₂.Z n).subtype).comap (F.mapZ n) :=
  fun _ hz => F.map_mem_B hz

def mapH (n : ℕ) : C₁.H n →ₛₗ[σ₁₂] C₂.H n :=
  Submodule.mapQ _ _ (F.mapZ n) (F.mapZ_le n)

end Hom

def ResUpTo {M : Type w'} [AddCommGroup M] [Module R M] (K : Cx.{w} R) (s : R) (ε : M →ₗ[R] K.X 0) : Prop :=
  (∀ x, K.d 0 (ε x) = 0) ∧ InjUpTo s ε ∧ ExactUpTo s ε (K.d 0) ∧ ∀ n, ExactUpTo s (K.d n) (K.d (n + 1))

end Cx

namespace CH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

abbrev Cn (n : ℕ) : Type (max u v w) := ∀ s : ComposableArrows C n, F.obj (s.obj (Fin.last n))

def d (n : ℕ) : Cn F n →ₗ[R] Cn F (n + 1) where
  toFun f s := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def term {p n : ℕ} (s : ComposableArrows C n) (f : Cn F p) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : F.obj (s.obj (Fin.last n)) :=
  (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (f (hg.functor ⋙ s))

theorem term_congr {p n : ℕ} (s : ComposableArrows C n) (f : Cn F p) {g g' : Fin (p + 1) → Fin (n + 1)}
    (hg : Monotone g) (hg' : Monotone g') (h : g = g') : term F s f g hg = term F s f g' hg' := by
  subst h; rfl

theorem term_add {p n : ℕ} (s : ComposableArrows C n) (f f' : Cn F p) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : term F s (f + f') g hg = term F s f g hg + term F s f' g hg := map_add _ _ _

theorem term_smul {p n : ℕ} (s : ComposableArrows C n) (r : R) (f : Cn F p) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : term F s (r • f) g hg = r • term F s f g hg := map_smul _ _ _

theorem term_face {p n : ℕ} (s : ComposableArrows C (n + 1)) (f : Cn F p) (j : Fin (n + 2)) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : (F.map (toLast j s)).hom (term F (face j s) f g hg) =
      term F s f (j.succAbove ∘ g) ((Fin.strictMono_succAbove j).monotone.comp hg) := by
  have e : (face j s).map (homOfLE (Fin.le_last (g (Fin.last p)))) ≫ toLast j s =
      s.map (homOfLE (Fin.le_last (j.succAbove (g (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  unfold term
  rw [← ModuleCat.comp_apply, ← F.map_comp, e]
  rfl

theorem d_d (n : ℕ) (f : Cn F n) : d F (n + 1) (d F n f) = 0 := by
  funext s
  change ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • (F.map (toLast j s)).hom
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • term F (face j s) f i.succAbove (Fin.strictMono_succAbove i).monotone) = 0
  simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul, term_face]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    have e : ((j.succAbove i).succAbove ∘ (i.predAbove j).succAbove) = j.succAbove ∘ i.succAbove :=
      funext fun t => Fin.succAbove_succAbove_succAbove_predAbove j i t
    rw [term_congr F s f _ ((Fin.strictMono_succAbove j).monotone.comp (Fin.strictMono_succAbove i).monotone) e,
      GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

abbrev cx : Cx.{max u v w} R where
  X := Cn F
  d := d F
  dd := d_d F

abbrev H (n : ℕ) : Type (max u v w) := (cx F).H n

def aug {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T) : M →ₗ[R] Cn F 0 :=
  LinearMap.pi fun s => e _

variable {F} {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

structure Mor (F : C ⥤ ModuleCat.{w} R) (F' : C' ⥤ ModuleCat.{w'} R') (σ : R →+* R') where
  G : C' ⥤ C
  τ : ∀ T : C', F.obj (G.obj T) →ₛₗ[σ] F'.obj T
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : F.obj (G.obj T)), τ T' ((F.map (G.map φ)).hom x) = (F'.map φ).hom (τ T x)

namespace Mor

def id (F : C ⥤ ModuleCat.{w} R) : Mor F F (RingHom.id R) where
  G := 𝟭 C
  τ _ := LinearMap.id
  nat _ _ := rfl

def restrict (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) : Mor F (G ⋙ F) (RingHom.id R) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

def ofNatTrans {F₁ : C ⥤ ModuleCat.{w} R} (α : F ⟶ F₁) : Mor F F₁ (RingHom.id R) where
  G := 𝟭 C
  τ T := (α.app T).hom
  nat φ x := by
    change ((F.map φ ≫ α.app _).hom) x = ((α.app _ ≫ F₁.map φ).hom) x
    rw [α.naturality]

def comp {R'' : Type} [CommRing R''] {C'' : Type u''} [Category.{v''} C''] {F'' : C'' ⥤ ModuleCat.{w''} R''}
    {σ' : R' →+* R''} {σ'' : R →+* R''} [RingHomCompTriple σ σ' σ''] (m : Mor F F' σ) (m' : Mor F' F'' σ') : Mor F F'' σ'' where
  G := m'.G ⋙ m.G
  τ T := (m'.τ T).comp (m.τ (m'.G.obj T))
  nat φ x := by
    change m'.τ _ (m.τ _ ((F.map (m.G.map (m'.G.map φ))).hom x)) = _
    rw [m.nat, m'.nat]; rfl

variable (m : Mor F F' σ)

def pullC (n : ℕ) : Cn F n →ₛₗ[σ] Cn F' n where
  toFun f s := m.τ _ (f (s ⋙ m.G))
  map_add' f g := funext fun s => map_add (m.τ _) _ _
  map_smul' r f := funext fun s => LinearMap.map_smulₛₗ (m.τ _) _ _

theorem d_pullC (n : ℕ) (f : Cn F n) : d F' n (m.pullC n f) = m.pullC (n + 1) (d F n f) := by
  funext s
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F'.map (toLast i s)).hom (m.τ _ (f (face i s ⋙ m.G))) =
    m.τ _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (m.G.map (toLast i s))).hom (f (face i s ⋙ m.G)))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, m.nat]

def hom : Cx.Hom (cx F) (cx F') σ := ⟨m.pullC, m.d_pullC⟩

def pull (n : ℕ) : H F n →ₛₗ[σ] H F' n := m.hom.mapH n

end Mor

def Mor.ofBlk {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} (m : GlobalTheory.CatH.Mor F F' σ) : Mor F F' σ := ⟨m.G, m.τ, m.nat⟩

theorem H_eq_blk (F : C ⥤ ModuleCat.{0} R) (n : ℕ) : H F n = GlobalTheory.CatH.H F n := rfl

theorem pull_ofBlk {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} (m : GlobalTheory.CatH.Mor F F' σ) (n : ℕ)
    (x : GlobalTheory.CatH.H F n) : (Mor.ofBlk m).pull n x = m.pull n x := rfl

structure SubF (F : C ⥤ ModuleCat.{w} R) where
  S : ∀ T : C, Submodule R (F.obj T)
  map_mem : ∀ {T T' : C} (φ : T ⟶ T') {x : F.obj T}, x ∈ S T → (F.map φ).hom x ∈ S T'

def SubF.fn (S : SubF F) : C ⥤ ModuleCat.{w} R where
  obj T := ModuleCat.of R (S.S T)
  map φ := ModuleCat.ofHom ((F.map φ).hom.restrict fun _ hx => S.map_mem φ hx)
  map_id T := by ext x; simp [LinearMap.restrict_apply]
  map_comp φ ψ := by ext x; simp [LinearMap.restrict_apply]

def SubF.inc (S : SubF F) : Mor S.fn F (RingHom.id R) where
  G := 𝟭 C
  τ T := (S.S T).subtype
  nat _ _ := rfl

def SubF.quot (S : SubF F) : C ⥤ ModuleCat.{w} R where
  obj T := ModuleCat.of R (F.obj T ⧸ S.S T)
  map φ := ModuleCat.ofHom (Submodule.mapQ _ _ (F.map φ).hom fun _ hx => S.map_mem φ hx)
  map_id T := by ext x; simp
  map_comp φ ψ := by ext x; simp

def SubF.proj (S : SubF F) : Mor F S.quot (RingHom.id R) where
  G := 𝟭 C
  τ T := (S.S T).mkQ
  nat _ _ := rfl

def SubF.img (S : SubF F) (n : ℕ) : Submodule R (H F n) := LinearMap.range (S.inc.pull n)

structure Pairing (F₁ : C ⥤ ModuleCat.{w} R) (F₂ : C ⥤ ModuleCat.{w'} R) (F₃ : C ⥤ ModuleCat.{w''} R) where
  μ : ∀ T : C, F₁.obj T →ₗ[R] F₂.obj T →ₗ[R] F₃.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (x : F₁.obj T) (y : F₂.obj T),
    μ T' ((F₁.map φ).hom x) ((F₂.map φ).hom y) = (F₃.map φ).hom (μ T x y)

def front {p q n : ℕ} (h : p + q = n) (i : Fin (p + 1)) : Fin (n + 1) := ⟨i, by omega⟩

def back {p q n : ℕ} (h : p + q = n) (i : Fin (q + 1)) : Fin (n + 1) := ⟨p + i, by omega⟩

theorem front_mono {p q n : ℕ} (h : p + q = n) : Monotone (front h) := fun _ _ hab => hab

theorem back_mono {p q n : ℕ} (h : p + q = n) : Monotone (back h) := fun _ _ hab => Nat.add_le_add_left hab p

namespace Pairing

variable {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃)

def cupC {p q n : ℕ} (h : p + q = n) : Cn F₁ p →ₗ[R] Cn F₂ q →ₗ[R] Cn F₃ n :=
  LinearMap.mk₂ R (fun f g s => P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)))
    (fun f f' g => funext fun s => by simp [term_add])
    (fun r f g => funext fun s => by simp [term_smul])
    (fun f g g' => funext fun s => by simp [term_add])
    (fun r f g => funext fun s => by simp [term_smul])

open Classical in

def cup {p q n : ℕ} (h : p + q = n) (x : H F₁ p) (y : H F₂ q) : H F₃ n :=
  if hz : d F₃ n (P.cupC h (Quotient.out x).1 (Quotient.out y).1) = 0 then (cx F₃).cls _ hz else 0

end Pairing

def modF (A : C ⥤ CommAlgCat.{w} R) : C ⥤ ModuleCat.{w} R where
  obj T := ModuleCat.of R (A.obj T)
  map φ := ModuleCat.ofHom (A.map φ).hom.toLinearMap
  map_id T := by ext x; simp
  map_comp φ ψ := by ext x; simp

def mulP (A : C ⥤ CommAlgCat.{w} R) : Pairing (modF A) (modF A) (modF A) where
  μ T := LinearMap.mul R (A.obj T)
  nat {T _} φ (x y : A.obj T) := (map_mul (A.map φ).hom x y).symm

def oneH (A : C ⥤ CommAlgCat.{w} R) : H (modF A) 0 :=
  (cx (modF A)).cls (fun s => (1 : A.obj (s.obj (Fin.last 0)))) (by
    funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom 1 = (0 : A.obj _)
    rw [Fin.sum_univ_two, map_one, map_one]
    simp)

end CH

structure Sys (R : Type) [CommRing R] : Type (w + 1) where
  M : ℕ → Type w
  [ab : ∀ n, AddCommGroup (M n)]
  [md : ∀ n, Module R (M n)]
  r : ∀ n, M (n + 1) →ₗ[R] M n

attribute [instance] Sys.ab Sys.md

def Sys.lim {R : Type} [CommRing R] (S : Sys.{w} R) : Submodule R (∀ n, S.M n) where
  carrier := {x | ∀ n, S.r n (x (n + 1)) = x n}
  add_mem' ha hb n := by rw [Pi.add_apply, map_add, ha n, hb n]; rfl
  zero_mem' n := map_zero _
  smul_mem' c x hx n := by rw [Pi.smul_apply, map_smul, hx n]; rfl

structure Sys.Hom {R R' : Type} [CommRing R] [CommRing R'] (S : Sys.{w} R) (S' : Sys.{w'} R') (σ : R →+* R') where
  f : ∀ n, S.M n →ₛₗ[σ] S'.M n
  comm : ∀ n x, S'.r n (f (n + 1) x) = f n (S.r n x)

def Sys.Hom.lim {R R' : Type} [CommRing R] [CommRing R'] {S : Sys.{w} R} {S' : Sys.{w'} R'} {σ : R →+* R'}
    (φ : Sys.Hom S S' σ) : S.lim →ₛₗ[σ] S'.lim where
  toFun x := ⟨fun n => φ.f n (x.1 n), fun n => by rw [φ.comm, x.2 n]⟩
  map_add' x y := Subtype.ext (funext fun n => map_add (φ.f n) _ _)
  map_smul' c x := Subtype.ext (funext fun n => LinearMap.map_smulₛₗ (φ.f n) _ _)

def CH.towerH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : ℕ → (C ⥤ ModuleCat.{w} R))
    (r : ∀ n, F (n + 1) ⟶ F n) (j : ℕ) : Sys.{max u v w} R where
  M n := CH.H (F n) j
  r n := (CH.Mor.ofNatTrans (r n)).pull j

end CrystallineSemistableComparison
