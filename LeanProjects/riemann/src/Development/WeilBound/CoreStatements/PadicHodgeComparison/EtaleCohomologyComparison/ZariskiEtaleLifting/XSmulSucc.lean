import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial

universe w w' v u v' u'

namespace CrystallineSemistableComparison.B

open CH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

def IsoLe {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (s : R) (n : ℕ) (m : Mor F F' (RingHom.id R)) : Prop :=
  ∀ j ≤ n, UpTo s (m.pull j)

def RI (s : R) (n : ℕ) (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) : Prop := IsoLe s n (Mor.restrict F G)

def unAug (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (T : C) :
    F.obj T →ₗ[R] Cn (StructuredArrow.proj T G ⋙ G ⋙ F) 0 :=
  aug (StructuredArrow.proj T G ⋙ G ⋙ F) fun x => (F.map x.hom).hom

def Desc (s : R) (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) : Prop :=
  ∀ T : C, (cx (StructuredArrow.proj T G ⋙ G ⋙ F)).ResUpTo s (unAug F G T)

def Acyc1 {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (s : R)
    (a : M →ₗ[R] N) (g : N →ₗ[R] N) : Prop :=
  InjUpTo s a ∧ (∀ x, g x = x → ∃ m, a m = s • x) ∧ ∀ x, ∃ y, g y - y = s • x

structure Flt (F : C ⥤ ModuleCat.{w} R) where
  S : ℕ → SubF F
  μ : R
  mul : ∀ r T x, x ∈ (S r).S T → μ • x ∈ (S (r + 1)).S T

namespace Flt

variable {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F)

def Pr (T : C) : Type w := ∀ r, (Φ.S r).S T

instance (T : C) : AddCommGroup (Φ.Pr T) := inferInstanceAs (AddCommGroup (∀ r, (Φ.S r).S T))

def sh (T : C) : Module.End ℤ (Φ.Pr T) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x r => match r with
        | 0 => 0
        | r + 1 => ⟨Φ.μ • (x r).1, Φ.mul r T _ (x r).2⟩
      map_zero' := funext fun r => by
        cases r
        · rfl
        · exact Subtype.ext (smul_zero _)
      map_add' := fun x y => funext fun r => by
        cases r
        · exact (add_zero _).symm
        · exact Subtype.ext (smul_add _ _ _) }

instance (T : C) : Module ℤ[X] (Φ.Pr T) := Module.compHom _ (aeval (Φ.sh T)).toRingHom

theorem smul_def (T : C) (p : ℤ[X]) (x : Φ.Pr T) : p • x = aeval (Φ.sh T) p x := rfl

theorem X_smul (T : C) (x : Φ.Pr T) : (X : ℤ[X]) • x = Φ.sh T x := by rw [smul_def, aeval_X]

theorem X_smul_zero (T : C) (x : Φ.Pr T) : ((X : ℤ[X]) • x) 0 = 0 := by rw [X_smul]; rfl

theorem X_smul_succ (T : C) (x : Φ.Pr T) (r : ℕ) : (((X : ℤ[X]) • x) (r + 1)).1 = Φ.μ • (x r).1 := by rw [X_smul]; rfl

def lin {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module ℤ[X] M] [Module ℤ[X] N] (f : M →+ N)
    (h : ∀ x, f ((X : ℤ[X]) • x) = (X : ℤ[X]) • f x) : M →ₗ[ℤ[X]] N where
  toFun := f
  map_add' := map_add f
  map_smul' p x := by
    induction p using Polynomial.induction_on generalizing x with
    | C a => rw [RingHom.id_apply, eq_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
    | add p q hp hq => rw [RingHom.id_apply, add_smul, map_add, add_smul, hp, hq]; rfl
    | monomial n a ih =>
      rw [RingHom.id_apply, pow_succ, ← mul_assoc, mul_smul _ X x, mul_smul _ X (f x), ih, h]; rfl

def prMap {T T' : C} (φ : T ⟶ T') : Φ.Pr T →ₗ[ℤ[X]] Φ.Pr T' :=
  lin { toFun := fun x r => ⟨(F.map φ).hom (x r).1, (Φ.S r).map_mem φ (x r).2⟩
        map_zero' := funext fun r => Subtype.ext (map_zero _)
        map_add' := fun x y => funext fun r => Subtype.ext (map_add _ _ _) } fun x => by
    rw [X_smul, X_smul]
    funext r
    cases r
    · exact Subtype.ext (map_zero _)
    · exact Subtype.ext (map_smul _ _ _)

theorem prMap_apply {T T' : C} (φ : T ⟶ T') (x : Φ.Pr T) (r : ℕ) : (Φ.prMap φ x r).1 = (F.map φ).hom (x r).1 := rfl

def rees : C ⥤ ModuleCat.{w} ℤ[X] where
  obj T := ModuleCat.of _ (Φ.Pr T)
  map φ := ModuleCat.ofHom (Φ.prMap φ)
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun r => Subtype.ext (by
    change (F.map (𝟙 T)).hom (x r).1 = (x r).1
    rw [F.map_id]; rfl))
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun r => Subtype.ext (by
    change (F.map (φ ≫ ψ)).hom (x r).1 = (F.map ψ).hom ((F.map φ).hom (x r).1)
    rw [F.map_comp]; rfl))

def comap (G : C' ⥤ C) : Flt (G ⋙ F) where
  S r := ⟨fun T => (Φ.S r).S (G.obj T), fun φ _ hx => (Φ.S r).map_mem (G.map φ) hx⟩
  μ := Φ.μ
  mul r T := Φ.mul r (G.obj T)

theorem comap_rees (G : C' ⥤ C) : (Φ.comap G).rees = G ⋙ Φ.rees := rfl

theorem comap_fn (G : C' ⥤ C) (r : ℕ) : ((Φ.comap G).S r).fn = G ⋙ (Φ.S r).fn := rfl

def FAcyc {T T' : C} (i : T ⟶ T') (g : T' ⟶ T') : Prop :=
  Function.Injective (F.map i).hom ∧
  (∀ r, ∀ x ∈ (Φ.S r).S T', (F.map g).hom x = x → ∃ m ∈ (Φ.S (r + 1)).S T, (F.map i).hom m = Φ.μ • x) ∧
  ∀ r, ∀ x ∈ (Φ.S r).S T', ∃ y ∈ (Φ.S (r + 1)).S T', (F.map g).hom y - y = Φ.μ • x

end Flt

abbrev Gam (d : ℕ) : Type := Multiplicative (Fin d → ℕ)

def gen {d : ℕ} (k : Fin d) : Gam d := Multiplicative.ofAdd (Pi.single k 1)

structure UF (C : Type u) [Category.{v} C] where
  U : C → Type
  [grp : ∀ T, CommGroup (U T)]
  map : ∀ {T T' : C}, (T ⟶ T') → (U T →* U T')
  map_id : ∀ T x, map (𝟙 T) x = x
  map_comp : ∀ {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') x, map (φ ≫ ψ) x = map ψ (map φ x)
  q : ∀ T, U T
  map_q : ∀ {T T' : C} (φ : T ⟶ T'), map φ (q T) = q T'

attribute [instance] UF.grp

variable {C₀ : Type u'} [Category.{v'} C₀]

structure Act (j : C₀ ⥤ C) (U : UF C) (d : ℕ) (D : C) where
  act : ∀ {T : C}, (Fin d → U.U T) → (D ⟶ T) → (D ⟶ T)
  act_one : ∀ {T : C} (c : D ⟶ T), act 1 c = c
  act_mul : ∀ {T : C} (a b : Fin d → U.U T) (c : D ⟶ T), act (a * b) c = act a (act b c)
  act_comp : ∀ {T T' : C} (a : Fin d → U.U T) (c : D ⟶ T) (φ : T ⟶ T'),
    act a c ≫ φ = act (fun k => U.map φ (a k)) (c ≫ φ)
  ne : ∀ t : C₀, Nonempty (D ⟶ j.obj t)
  trans : ∀ (t : C₀) (c c' : D ⟶ j.obj t), ∃! a, act a c = c'

def Act.γ {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D : C} (A : Act j U d D) : Gam d →* End D where
  toFun a := A.act (fun k => U.q D ^ (Multiplicative.toAdd a k)) (𝟙 D)
  map_one' := by
    have : (fun k => U.q D ^ (Multiplicative.toAdd (1 : Gam d) k)) = 1 := funext fun k => pow_zero _
    rw [this, A.act_one]; rfl
  map_mul' a b := by
    change _ = A.act _ (𝟙 D) ≫ A.act _ (𝟙 D)
    rw [A.act_comp, Category.id_comp, ← A.act_mul]
    congr 1
    funext k
    rw [Pi.mul_apply, map_pow, U.map_q, ← pow_add, toAdd_mul, Pi.add_apply, add_comm]

def Act.ι {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D : C} (A : Act j U d D) : SingleObj (Gam d) ⥤ C := SingleObj.functor A.γ

structure Line (j : C₀ ⥤ C) (U : UF C) where
  Ξ : C ⥤ C
  i : 𝟭 C ⟶ Ξ
  η : ∀ T, U.U (Ξ.obj T)
  map_η : ∀ {T T' : C} (φ : T ⟶ T'), U.map (Ξ.map φ) (η T) = η T'
  γ : Ξ ⟶ Ξ
  iγ : i ≫ γ = i
  γη : ∀ T, U.map (γ.app T) (η T) = U.q _ * η T
  univ : ∀ (T : C) (t : C₀) (φ : T ⟶ j.obj t) (a : U.U (j.obj t)),
    ∃! ψ : Ξ.obj T ⟶ j.obj t, i.app T ≫ ψ = φ ∧ U.map ψ (η T) = a

structure NI {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) where
  ρ : N ⟶ M
  π : Fin d → (N ⟶ N)
  αρ : α ≫ ρ = 𝟙 M
  sum : ρ ≫ α + ∑ k, π k = 𝟙 N
  απ : ∀ k, α ≫ π k = 0
  idem : ∀ k, π k ≫ π k = π k
  orth : ∀ k k', k ≠ k' → π k ≫ π k' = 0
  surj : ∀ k (x : N.obj (SingleObj.star _)), ((π k).app _).hom x = x →
    ∃ y, ((π k).app _).hom y = y ∧ (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y = s • x
  inj : ∀ k (x : N.obj (SingleObj.star _)), ((π k).app _).hom x = x →
    (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom x = x → s • x = 0

def eqv {M : Type} [Monoid M] {D D' : C} (γ : M →* End D) (γ' : M →* End D') (θ : D ⟶ D')
    (h : ∀ a, (γ a : D ⟶ D) ≫ θ = θ ≫ (γ' a : D' ⟶ D')) : SingleObj.functor γ ⟶ SingleObj.functor γ' where
  app _ := θ
  naturality _ _ a := h a

structure Onto {C₁ : Type u'} [Category.{v'} C₁] (ι : C₁ ⥤ C) (Q : C → Prop) : Prop where
  full : ι.Full
  faithful : ι.Faithful
  mem : ∀ T, Q (ι.obj T)
  ess : ∀ T, Q T → ∃ T₁, Nonempty (ι.obj T₁ ≅ T)

structure LocMod (F : C ⥤ ModuleCat.{w} R) {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S) where
  Λ : Type
  [ring : CommRing Λ]
  f : Fin m → Λ
  span : Ideal.span (Set.range f) = ⊤
  ρ₀ : Λ →+* Module.End R (F.obj T')
  ρ : ∀ S, Λ →+* Module.End R (F.obj (Lc S))
  lam_ρ : ∀ S a x, (F.map (lam S)).hom (ρ₀ a x) = ρ S a ((F.map (lam S)).hom x)
  tr_ρ : ∀ S S' (t : Lc S ⟶ Lc S'), lam S ≫ t = lam S' → ∀ a x, (F.map t).hom (ρ S a x) = ρ S' a ((F.map t).hom x)
  unit : ∀ S, ∀ k ∈ S, Function.Bijective (ρ S (f k))
  surj : ∀ S y, ∃ (n : ℕ) (x : F.obj T'), ρ S ((∏ k ∈ S, f k) ^ n) y = (F.map (lam S)).hom x
  ker : ∀ S x, (F.map (lam S)).hom x = 0 → ∃ n : ℕ, ρ₀ ((∏ k ∈ S, f k) ^ n) x = 0

def ZarCov (F : C ⥤ ModuleCat.{w} R) (Q : C → Prop) : Prop :=
  (∀ ⦃T T' : C⦄, (T ⟶ T') → Q T → Q T') ∧
  ∀ T : C, ∃ (m : ℕ) (V : Fin m → ∀ ⦃T'' : C⦄, (T ⟶ T'') → Prop),
    (∀ k ⦃T₁ T₂ : C⦄ (ψ : T ⟶ T₁) (χ : T₁ ⟶ T₂), V k ψ → V k (ψ ≫ χ)) ∧
    (∀ k ⦃T₁ : C⦄ (ψ : T ⟶ T₁), V k ψ → Q T₁) ∧
    ∀ (T' : C) (φ : T ⟶ T'), ∃ (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S),
      (∀ S, ∀ k ∈ S, V k (φ ≫ lam S)) ∧
      (∀ S (T'' : C) (ψ : T' ⟶ T''), (∀ k ∈ S, V k (φ ≫ ψ)) → ∃! χ : Lc S ⟶ T'', lam S ≫ χ = ψ) ∧
      Nonempty (LocMod F T' Lc lam)

end CrystallineSemistableComparison.B
