import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Cris

open CatCoh

section Nil

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}

def IsNilDP (δ : DividedPowers J) : Prop :=
  ∃ N : ℕ, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ (l.map Prod.fst).sum →
    (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0

private theorem prod_dpow_mem_and_eq_zero_of_sq_zero (δ : DividedPowers J) (h2 : ∀ a ∈ J, ∀ b ∈ J, a * b = 0)
    (h : ∀ n, 2 ≤ n → ∀ a ∈ J, δ.dpow n a = 0) (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) :
    (1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J) ∧
      (2 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0) := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨k, a⟩ := p
    have ha : a ∈ J := hl (k, a) (by simp)
    have ht := ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simpa [δ.dpow_zero ha] using ht
      · rw [δ.dpow_one ha]
        exact ⟨fun _ ↦ J.mul_mem_right _ ha, fun hs ↦ h2 _ ha _ (ht.1 (by omega))⟩
    · simp [h k hk a ha]

theorem isDPNilpotent_of_sq (δ : DividedPowers J) (h2 : ∀ a ∈ J, ∀ b ∈ J, a * b = 0)
    (h : ∀ n, 2 ≤ n → ∀ a ∈ J, δ.dpow n a = 0) : IsNilDP δ := by
  refine ⟨2, fun l hl hs ↦ (prod_dpow_mem_and_eq_zero_of_sq_zero δ h2 h l hl).2 hs⟩

theorem isDPNilpotent_bot (B : Type) [CommRing B] : IsNilDP (dividedPowersBot B) :=
  isDPNilpotent_of_sq _ (fun a ha b _ ↦ by rw [Ideal.mem_bot.1 ha, zero_mul])
    (fun n hn a _ ↦ by
      classical
      rw [dividedPowersBot_dpow_eq, if_neg fun h' ↦ absurd h'.2 (by omega)])

theorem IsNilDP.exists_dpow_eq_zero {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a, δ.dpow n a = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn a ↦ ?_⟩
  by_cases ha : a ∈ J
  · simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  · exact δ.dpow_null ha

theorem isDPMorphism_of_eq_bot (δ : DividedPowers J) (hJ : J = ⊥) (δ' : DividedPowers J')
    (f : B →+* B') : IsDPMorphism δ δ' f := by
  subst hJ
  refine ⟨by simp, ?_⟩
  intro n a ha
  rw [Ideal.mem_bot.1 ha, map_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [δ.dpow_zero (Ideal.zero_mem _), δ'.dpow_zero J'.zero_mem, map_one]
  · rw [δ.dpow_eval_zero hn, δ'.dpow_eval_zero hn, map_zero]

open Classical in

def divided₂ (h : J ^ 2 = 0) : DividedPowers J := OfSquareZero.dividedPowers h

theorem squareZeroDividedPowers_dpow (h : J ^ 2 = 0) {n : ℕ} (hn : 2 ≤ n) (a : B) : (divided₂ h).dpow n a = 0 := by
  classical
  exact OfSquareZero.dpow_of_two_le h hn a

theorem isDPNilpotent_squareZero (h : J ^ 2 = 0) : IsNilDP (divided₂ h) :=
  isDPNilpotent_of_sq _ (fun a ha b hb ↦ by
      have hab := Ideal.mul_mem_mul ha hb
      rwa [← pow_two, h, Ideal.zero_eq_bot, Ideal.mem_bot] at hab)
    (fun n hn a _ ↦ squareZeroDividedPowers_dpow h hn a)

theorem isDPMorphism_sqDP (h : J ^ 2 = 0) (h' : J' ^ 2 = 0) (f : B →+* B') (hf : ∀ a ∈ J, f a ∈ J') :
    IsDPMorphism (divided₂ h) (divided₂ h') f := by
  refine ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ hf a ha, ?_⟩
  intro n a ha
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [(divided₂ h').dpow_zero (hf a ha), (divided₂ h).dpow_zero ha, map_one]
    · rw [(divided₂ h').dpow_one (hf a ha), (divided₂ h).dpow_one ha]
  · rw [squareZeroDividedPowers_dpow h' hn, squareZeroDividedPowers_dpow h hn, map_zero]

def dpExp (δ : DividedPowers J) (a : B) : B := ∑ᶠ n : ℕ, δ.dpow n a

theorem dpExp_zero (δ : DividedPowers J) : dpExp δ 0 = 1 := by
  rw [dpExp, finsum_eq_single (fun n ↦ δ.dpow n 0) 0 fun n hn ↦ δ.dpow_eval_zero hn,
    δ.dpow_zero J.zero_mem]

theorem dpExp_sqDP (h : J ^ 2 = 0) {a : B} (ha : a ∈ J) : dpExp (divided₂ h) a = 1 + a := by
  rw [dpExp, finsum_eq_sum_of_support_subset (fun n ↦ (divided₂ h).dpow n a) (s := Finset.range 2)
    fun n hn ↦ ?_]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, (divided₂ h).dpow_zero ha,
      (divided₂ h).dpow_one ha]
  · rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hn (squareZeroDividedPowers_dpow h (by omega) a)

end Nil

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}

structure Thick (γ : DividedPowers I) (s : X ⟶ Sp R) : Type 1 where

  B : Type
  [ring : CommRing B]
  [alg : Algebra R B]

  J : Ideal B

  δ : DividedPowers J
  nil : IsNilDP δ
  dp : IsDPMorphism γ δ (algebraMap R B)

  B₀ : Type
  [ring₀ : CommRing B₀]

  π : B →+* B₀
  surj : Function.Surjective π
  ker : ∀ b, π b = 0 ↔ b ∈ J

  x : Sp B₀ ⟶ X
  w : x ≫ s = spMap (π.comp (algebraMap R B))

attribute [instance] Thick.ring Thick.alg Thick.ring₀

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  exact Spec.map_id (CommRingCat.of A)

namespace Thick

variable {γ : DividedPowers I} {s : X ⟶ Sp R}

structure Hom (T T' : Thick γ s) where

  φ : T.B →ₐ[R] T'.B

  φ₀ : T.B₀ →+* T'.B₀
  comm : ∀ b, φ₀ (T.π b) = T'.π (φ b)
  dp : IsDPMorphism T.δ T'.δ (φ : T.B →+* T'.B)
  pt : spMap φ₀ ≫ T.x = T'.x

theorem Hom.ext' {T T' : Thick γ s} {f g : Hom T T'} (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

instance : Category (Thick γ s) where
  Hom := Hom
  id T := ⟨AlgHom.id R _, RingHom.id _, fun _ ↦ rfl, (DPMorphism.id T.δ).isDPMorphism, by
    rw [spMap_id, Category.id_comp]⟩
  comp f g := ⟨g.φ.comp f.φ, g.φ₀.comp f.φ₀, fun b ↦ by simp [f.comm, g.comm],
    IsDPMorphism.comp _ g.dp f.dp, by rw [spMap_comp, Category.assoc, f.pt, g.pt]⟩

@[ext] theorem hom_ext {T T' : Thick γ s} {f g : T ⟶ T'} (h : ∀ b, f.φ b = g.φ b) : f = g := Hom.ext' (AlgHom.ext h)

@[simp] theorem comp_φ {T T' T'' : Thick γ s} (f : T ⟶ T') (g : T' ⟶ T'') (b : T.B) :
    (f ≫ g).φ b = g.φ (f.φ b) := rfl

@[simp] theorem id_φ (T : Thick γ s) (b : T.B) : Hom.φ (𝟙 T) b = b := rfl

theorem Hom.mem {T T' : Thick γ s} (f : T ⟶ T') {b : T.B} (hb : b ∈ T.J) : f.φ b ∈ T'.J := f.dp.1 (Ideal.mem_map_of_mem _ hb)

end Thick

@[reducible] def O (γ : DividedPowers I) (s : X ⟶ Sp R) : Thick γ s ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R T.B
  map f := CommAlgCat.ofHom f.φ

theorem mp_O {γ : DividedPowers I} {s : X ⟶ Sp R} {T T' : Thick γ s} (f : T ⟶ T') :
    mp (O γ s) f = f.φ := rfl

def ev {γ : DividedPowers I} {s : X ⟶ Sp R} (f : Z1 (O γ s)) {T T' : Thick γ s} (φ : T ⟶ T') : T'.B :=
  f.1 T T' φ

theorem ev_comp {γ : DividedPowers I} {s : X ⟶ Sp R} (f : Z1 (O γ s)) {T T' T'' : Thick γ s}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') : ev f (φ ≫ ψ) = ψ.φ (ev f φ) + ev f ψ := Z1.comp f φ ψ

theorem ev_sq {γ : DividedPowers I} {s : X ⟶ Sp R} (f : Z1 (O γ s)) {T₁ T₂ T₃ T₄ : Thick γ s}
    (a : T₁ ⟶ T₂) (p : T₂ ⟶ T₄) (q : T₁ ⟶ T₃) (b : T₃ ⟶ T₄) (h : ∀ c, p.φ (a.φ c) = b.φ (q.φ c)) :
    p.φ (ev f a) + ev f p = b.φ (ev f q) + ev f b := by
  have e : a ≫ p = q ≫ b := Thick.hom_ext fun c ↦ h c
  rw [← ev_comp, ← ev_comp, e]

abbrev H1 (γ : DividedPowers I) (s : X ⟶ Sp R) : Type 1 := CatCoh.H1 (O γ s)

abbrev H2 (γ : DividedPowers I) (s : X ⟶ Sp R) : Type 1 := CatCoh.H2 (O γ s)

section Pull

variable {γ : DividedPowers I} {γ' : DividedPowers I'} {γ'' : DividedPowers I''}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''}

structure IsMor (γ : DividedPowers I) (s : X ⟶ Sp R) (γ' : DividedPowers I') (s' : X' ⟶ Sp R')
    (σ : R →+* R') (φ : X' ⟶ X) : Prop where
  dp : IsDPMorphism γ γ' σ
  w : φ ≫ s = s' ≫ spMap σ

theorem IsMor.id (γ : DividedPowers I) (s : X ⟶ Sp R) : IsMor γ s γ s (RingHom.id R) (𝟙 X) :=
  ⟨(DPMorphism.id γ).isDPMorphism, by rw [spMap_id, Category.id_comp, Category.comp_id]⟩

theorem IsMor.of_over (γ : DividedPowers I) {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    (h : φ ≫ s = s') : IsMor γ s γ s' (RingHom.id R) φ :=
  ⟨(DPMorphism.id γ).isDPMorphism, by rw [spMap_id, Category.comp_id, h]⟩

theorem IsMor.comp {σ : R →+* R'} {φ : X' ⟶ X} {τ : R' →+* R''} {ψ : X'' ⟶ X'}
    (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ) :
    IsMor γ s γ'' s'' (τ.comp σ) (ψ ≫ φ) :=
  ⟨IsDPMorphism.comp _ h'.dp h.dp, by
    rw [Category.assoc, h.w, ← Category.assoc, h'.w, Category.assoc, spMap_comp]⟩

variable {σ : R →+* R'} {φ : X' ⟶ X}

def IsMor.obj (h : IsMor γ s γ' s' σ φ) (T : Thick γ' s') : Thick γ s where
  B := T.B
  alg := ((algebraMap R' T.B).comp σ).toAlgebra
  J := T.J
  δ := T.δ
  nil := T.nil
  dp := IsDPMorphism.comp _ T.dp h.dp
  B₀ := T.B₀
  π := T.π
  surj := T.surj
  ker := T.ker
  x := T.x ≫ φ
  w := by
    rw [Category.assoc, h.w, ← Category.assoc, T.w, ← spMap_comp]

def IsMor.functor (h : IsMor γ s γ' s' σ φ) : Thick γ' s' ⥤ Thick γ s where
  obj := h.obj
  map {T T'} f :=
    { φ := { (f.φ : T.B →+* T'.B) with commutes' := fun r ↦ f.φ.commutes (σ r) }
      φ₀ := f.φ₀
      comm := f.comm
      dp := f.dp
      pt := by
        change spMap f.φ₀ ≫ T.x ≫ φ = T'.x ≫ φ
        rw [← Category.assoc, f.pt] }

def IsMor.coef (h : IsMor γ s γ' s' σ φ) : CoefMap σ (O γ s) (O γ' s') where
  G := h.functor
  α T := RingHom.id T.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.B) (σ r) b).symm

def IsMor.pull1 (h : IsMor γ s γ' s' σ φ) : H1 γ s →ₛₗ[σ] H1 γ' s' := h.coef.pull1

def IsMor.pull2 (h : IsMor γ s γ' s' σ φ) : H2 γ s →ₛₗ[σ] H2 γ' s' := h.coef.pull2

theorem IsMor.pullCohomologyTwo_cup (h : IsMor γ s γ' s' σ φ) (a b : H1 γ s) :
    h.pull2 (cup _ a b) = cup _ (h.pull1 a) (h.pull1 b) := h.coef.pullCohomologyTwo_cup a b

def IsMor.idTrans (h : IsMor γ s γ s (RingHom.id R) (𝟙 X)) : h.functor ⟶ 𝟭 _ where
  app T :=
    { φ := { RingHom.id T.B with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id T.δ).isDPMorphism
      pt := by
        change spMap (RingHom.id T.B₀) ≫ T.x = T.x ≫ 𝟙 X
        rw [spMap_id]; simp }

theorem IsMor.pullCohomologyOne_id (h : IsMor γ s γ s (RingHom.id R) (𝟙 X)) (c : H1 γ s) : h.pull1 c = c :=
  (h.coef.pullCohomologyOne_eq_of_natTrans (CoefMap.id _) h.idTrans (fun _ _ ↦ rfl) c).trans
    (CoefMap.pullCohomologyOne_id c)

theorem IsMor.pullCohomologyTwo_id (h : IsMor γ s γ s (RingHom.id R) (𝟙 X)) (c : H2 γ s) : h.pull2 c = c :=
  (h.coef.pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) h.idTrans (fun _ _ ↦ rfl) c).trans
    (CoefMap.pullCohomologyTwo_id c)

variable {τ : R' →+* R''} {ψ : X'' ⟶ X'} {ρ : R →+* R''} {χ : X'' ⟶ X}

def IsMor.compTrans (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ)
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) :
    h'.functor ⋙ h.functor ⟶ h''.functor where
  app T :=
    { φ := { RingHom.id T.B with commutes' := fun r ↦ congrArg (algebraMap R'' T.B) (e r) }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id T.δ).isDPMorphism
      pt := by
        change spMap (RingHom.id T.B₀) ≫ (T.x ≫ ψ) ≫ φ = T.x ≫ χ
        rw [spMap_id, ← e']; simp }

theorem IsMor.pullback1_comp (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ)
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H1 γ s) :
    h'.pull1 (h.pull1 c) = h''.pull1 c :=
  (h.coef.pullCohomologyOne_comp h'.coef c).symm.trans
    ((h.coef.comp h'.coef).pullCohomologyOne_eq_of_natTrans h''.coef (h.compTrans h' h'' e e')
      (fun _ _ ↦ rfl) c)

theorem IsMor.pullback2_comp (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ)
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H2 γ s) :
    h'.pull2 (h.pull2 c) = h''.pull2 c :=
  (h.coef.pullCohomologyTwo_comp h'.coef c).symm.trans
    ((h.coef.comp h'.coef).pullCohomologyTwo_eq_of_natTrans h''.coef (h.compTrans h' h'' e e')
      (fun _ _ ↦ rfl) c)

end Pull

section Hodge

abbrev dp0 (R : Type) [CommRing R] : DividedPowers (⊥ : Ideal R) := dividedPowersBot R

abbrev FirstDeRham (s : X ⟶ Sp R) : Type 1 := H1 (dp0 R) s

abbrev SecondDeRham (s : X ⟶ Sp R) : Type 1 := H2 (dp0 R) s

theorem IsMor.of_dividedPowersZeroIdeal {s : X ⟶ Sp R} (γ' : DividedPowers I') {s' : X' ⟶ Sp R'} {σ : R →+* R'}
    {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) : IsMor (dp0 R) s γ' s' σ φ := ⟨isDPMorphism_of_eq_bot _ rfl _ _, h⟩

variable {s : X ⟶ Sp R}

@[reducible] def Thick.triv (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) : Thick (dp0 R) s where
  B := B
  J := ⊥
  δ := dp0 B
  nil := isDPNilpotent_bot B
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := B
  π := RingHom.id B
  surj := Function.surjective_id
  ker := fun _ ↦ Ideal.mem_bot.symm
  x := x
  w := hx

def Thick.trivHom {B : Type} [CommRing B] [Algebra R B] {x : Sp B ⟶ X}
    {hx : x ≫ s = spMap (algebraMap R B)} {T : Thick (dp0 R) s} (φ : B →ₐ[R] T.B)
    (h : spMap (T.π.comp (φ : B →+* T.B)) ≫ x = T.x) : Thick.triv B x hx ⟶ T where
  φ := φ
  φ₀ := T.π.comp (φ : B →+* T.B)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := h

def IsTriv (s : X ⟶ Sp R) : ObjectProperty (Thick (dp0 R) s) := fun T ↦ T.J = ⊥

abbrev FirstCohomStructureSheaf (s : X ⟶ Sp R) : Type 1 := CatCoh.H1 ((IsTriv s).ι ⋙ O (dp0 R) s)

def toH1O (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] FirstCohomStructureSheaf s := (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull1

def F1 (s : X ⟶ Sp R) : Submodule R (FirstDeRham s) := LinearMap.ker (toH1O s)

def Form (s : X ⟶ Sp R) : Submodule R (Z1 (O (dp0 R) s)) where
  carrier := {f | ∀ ⦃T T' : Thick (dp0 R) s⦄ (φ : T ⟶ T'), T.J = ⊥ → T'.J = ⊥ → f.1 T T' φ = 0}
  add_mem' {f g} hf hg T T' φ h h' := by simp [hf φ h h', hg φ h h']
  zero_mem' T T' φ _ _ := rfl
  smul_mem' r f hf T T' φ h h' := by simp [hf φ h h']

theorem Form.ev_sq (f : Form s) {T₁ T₂ T₃ T₄ : Thick (dp0 R) s}
    (a : T₁ ⟶ T₂) (p : T₂ ⟶ T₄) (q : T₁ ⟶ T₃) (b : T₃ ⟶ T₄) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (h : ∀ c, p.φ (a.φ c) = b.φ (q.φ c)) : ev f.1 p = b.φ (ev f.1 q) + ev f.1 b := by
  have h0 : ev f.1 a = 0 := f.2 a h₁ h₂
  have e := GlobalTheory.Cris.ev_sq f.1 a p q b h
  rwa [h0, map_zero, zero_add] at e

def Form.cl (s : X ⟶ Sp R) : Form s →ₗ[R] FirstDeRham s := H1.mk _ ∘ₗ (Form s).subtype

theorem hodgeFiltration_eq_range (s : X ⟶ Sp R) : F1 s = LinearMap.range (Form.cl s) := by
  apply le_antisymm
  · intro c hc
    rw [F1, LinearMap.mem_ker] at hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [toH1O, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    classical
    obtain ⟨g', hg'⟩ : ∃ g' : C0 (O (dp0 R) s), ∀ (T : Thick (dp0 R) s) (hT : T.J = ⊥), g' T = g ⟨T, hT⟩ :=
      ⟨fun T ↦ if hT : T.J = ⊥ then g ⟨T, hT⟩ else 0, fun T hT ↦ dif_pos hT⟩
    have key : ∀ ⦃T T' : Thick (dp0 R) s⦄ (φ : T ⟶ T') (hT : T.J = ⊥) (hT' : T'.J = ⊥),
        f.1 T T' φ = g' T' - mp (O (dp0 R) s) φ (g' T) := by
      intro T T' φ hT hT'
      have e := congrFun (congrFun (congrFun hg ⟨T, hT⟩) ⟨T', hT'⟩) (ObjectProperty.homMk φ)
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      rw [hg' T hT, hg' T' hT']
      exact e.symm
    refine LinearMap.mem_range.2 ⟨⟨f - ⟨d0 _ g', commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g'⟩, fun T T' φ hT hT' ↦ ?_⟩, ?_⟩
    · show f.1 T T' φ - d0 _ g' T T' φ = 0
      rw [amitsur_d0_apply, key φ hT hT', sub_self]
    · show H1.mk _ (f - ⟨d0 _ g', commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g'⟩) = H1.mk _ f
      exact H1.mk_eq_mk.2 ⟨-g', by rw [map_neg, Submodule.coe_sub, sub_sub_cancel_left]⟩
  · rintro _ ⟨f, rfl⟩
    rw [F1, LinearMap.mem_ker, toH1O]
    show (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull1 (H1.mk _ f.1) = 0
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (f.2 φ.hom T.2 T'.2).symm

def IsMor.pullForm {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) : Form s →ₛₗ[σ] Form s' :=
  (h.coef.pullbackOneCocycle.domRestrict (Form s)).codRestrict (Form s') fun f _ _ ψ hT hT' ↦
    f.2 (h.functor.map ψ) hT hT'

theorem IsMor.cl_pullForm {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (f : Form s) :
    Form.cl s' (h.pullForm f) = h.pull1 (Form.cl s f) := rfl

theorem IsMor.pullback1_mem_hodgeFiltration {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) {c : FirstDeRham s} (hc : c ∈ F1 s) : h.pull1 c ∈ F1 s' := by
  rw [hodgeFiltration_eq_range] at hc ⊢
  obtain ⟨f, rfl⟩ := hc
  exact ⟨h.pullForm f, h.cl_pullForm f⟩

end Hodge

structure SqExt (R : Type) [CommRing R] : Type 1 where

  C : Type

  B : Type
  [ringC : CommRing C]
  [ringB : CommRing B]
  [algC : Algebra R C]
  [algB : Algebra R B]

  π : C →ₐ[R] B

  i : B →ₐ[R] C
  π_i : ∀ b, π (i b) = b
  sq : RingHom.ker (π : C →+* B) ^ 2 = 0

attribute [instance] SqExt.ringC SqExt.ringB SqExt.algC SqExt.algB

namespace SqExt

@[reducible] def ofModule (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] : SqExt R where
  C := TrivSqZeroExt B M
  B := B
  π := TrivSqZeroExt.fstHom R B M
  i := TrivSqZeroExt.inlAlgHom R B M
  π_i _ := rfl
  sq := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']

abbrev dual (R : Type) [CommRing R] : SqExt R := ofModule R R R

variable {s : X ⟶ Sp R} (E E' : SqExt R)

@[reducible] def thick (x : Sp E.B ⟶ X) (hx : x ≫ s = spMap (algebraMap R E.B)) :
    Thick (dp0 R) s where
  B := E.C
  J := RingHom.ker (E.π : E.C →+* E.B)
  δ := divided₂ E.sq
  nil := isDPNilpotent_squareZero _
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := E.B
  π := E.π
  surj := fun b ↦ ⟨E.i b, E.π_i b⟩
  ker := fun _ ↦ Iff.rfl
  x := x
  w := hx.trans (congrArg spMap E.π.comp_algebraMap.symm)

theorem red_w {y : Sp E.C ⟶ X} (hy : y ≫ s = spMap (algebraMap R E.C)) :
    (spMap (E.π : E.C →+* E.B) ≫ y) ≫ s = spMap (algebraMap R E.B) := by
  rw [Category.assoc, hy, ← spMap_comp, E.π.comp_algebraMap]

def secHom {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B)) (j : E.B →ₐ[R] E.C)
    (hj : ∀ b, E.π (j b) = b) : Thick.triv E.B x hx ⟶ E.thick x hx :=
  Thick.trivHom j (by
    have : (E.π : E.C →+* E.B).comp (j : E.B →+* E.C) = RingHom.id _ := RingHom.ext hj
    change spMap ((E.π : E.C →+* E.B).comp (j : E.B →+* E.C)) ≫ x = x
    rw [this, spMap_id, Category.id_comp])

def idHom {y : Sp E.C ⟶ X} (hy : y ≫ s = spMap (algebraMap R E.C)) :
    Thick.triv E.C y hy ⟶ E.thick _ (E.red_w hy) :=
  Thick.trivHom (AlgHom.id R _) rfl

def val (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) : Z1 (O (dp0 R) s) →ₗ[R] E.C where
  toFun f := ev f (E.secHom (E.red_w hy) E.i E.π_i) - ev f (E.idHom hy)
  map_add' f g := add_sub_add_comm (α := E.C) _ _ _ _
  map_smul' r f := (smul_sub r (_ : E.C) _).symm

theorem val_apply (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) :
    E.val y hy f = ev f (E.secHom (E.red_w hy) E.i E.π_i) - ev f (E.idHom hy) := rfl

theorem tangentValue_coboundary (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (g : C0 (O (dp0 R) s)) :
    E.val y hy ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ =
      (g (Thick.triv E.C y hy) : E.C) - E.i (g (Thick.triv E.B _ (E.red_w hy))) := by
  rw [val_apply]
  change d0 _ g _ _ (E.secHom (E.red_w hy) E.i E.π_i) - d0 _ g _ _ (E.idHom hy) = _
  rw [amitsur_d0_apply, amitsur_d0_apply, mp_O, mp_O]
  exact sub_sub_sub_cancel_left _ _ _

def thickHom (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B) (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B)) {x' : Sp E'.B ⟶ X}
    (hx' : x' ≫ s = spMap (algebraMap R E'.B)) (e : spMap (φ₀ : E.B →+* E'.B) ≫ x = x') :
    E.thick x hx ⟶ E'.thick x' hx' where
  φ := φ
  φ₀ := φ₀
  comm := hπ
  dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha ↦ by
    have ha' : E.π a = 0 := ha
    change E'.π (φ a) = 0
    rw [← hπ, ha', map_zero]
  pt := e

theorem val_map (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B) (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Form s) :
    E'.val y' hy' f.1 = φ (E.val y hy f.1) := by
  have hc : (φ₀ : E.B →+* E'.B).comp (E.π : E.C →+* E.B) =
      (E'.π : E'.C →+* E'.B).comp (φ : E.C →+* E'.C) := RingHom.ext hπ
  have ex : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← Category.assoc, ← spMap_comp, hc, spMap_comp, Category.assoc, e]
  have s1 := Form.ev_sq f
    (Thick.trivHom (x := spMap (E.π : E.C →+* E.B) ≫ y) (hx := E.red_w hy)
      (T := Thick.triv E'.B _ (E'.red_w hy')) φ₀ (by rw [RingHom.id_comp]; exact ex))
    (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    (E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') ex) rfl rfl (fun c ↦ (hi c).symm)
  have s2 := Form.ev_sq f
    (Thick.trivHom (x := y) (hx := hy) (T := Thick.triv E'.C y' hy') φ
      (by rw [RingHom.id_comp]; exact e))
    (E'.idHom hy') (E.idHom hy)
    (E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') ex) rfl rfl (fun c ↦ rfl)
  rw [val_apply, val_apply, s1, s2, map_sub]
  exact add_sub_add_right_eq_sub _ _ _

theorem val_pull {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : IsMor (dp0 R) s (dp0 R) s' (RingHom.id R) φ)
    (y : Sp E.C ⟶ X') (hy : y ≫ s' = spMap (algebraMap R E.C))
    (hy' : (y ≫ φ) ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.val y hy (h.pullForm f).1 = E.val (y ≫ φ) hy' f.1 := by
  let θ : h.functor.obj (E.thick (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy)) ⟶
      E.thick (spMap (E.π : E.C →+* E.B) ≫ y ≫ φ) (E.red_w hy') :=
    { φ := { RingHom.id E.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.B) ≫ (spMap (E.π : E.C →+* E.B) ≫ y) ≫ φ =
          spMap (E.π : E.C →+* E.B) ≫ y ≫ φ
        rw [spMap_id, Category.id_comp, Category.assoc] }
  let θB : h.functor.obj (Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy)) ⟶
      Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y ≫ φ) (E.red_w hy') :=
    { φ := { RingHom.id E.B with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.B) ≫ (spMap (E.π : E.C →+* E.B) ≫ y) ≫ φ =
          spMap (E.π : E.C →+* E.B) ≫ y ≫ φ
        rw [spMap_id, Category.id_comp, Category.assoc] }
  let θC : h.functor.obj (Thick.triv E.C y hy) ⟶ Thick.triv E.C (y ≫ φ) hy' :=
    { φ := { RingHom.id E.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.C) ≫ y ≫ φ = y ≫ φ
        rw [spMap_id, Category.id_comp] }
  have s1 := Form.ev_sq f θB (E.secHom (E.red_w hy') E.i E.π_i)
    (h.functor.map (E.secHom (E.red_w hy) E.i E.π_i)) θ rfl rfl (fun _ ↦ rfl)
  have s2 := Form.ev_sq f θC (E.idHom hy') (h.functor.map (E.idHom hy)) θ rfl rfl (fun _ ↦ rfl)
  have l1 : ev (h.pullForm f).1 (E.secHom (E.red_w hy) E.i E.π_i) =
      ev f.1 (h.functor.map (E.secHom (E.red_w hy) E.i E.π_i)) := rfl
  have l2 : ev (h.pullForm f).1 (E.idHom hy) = ev f.1 (h.functor.map (E.idHom hy)) := rfl
  rw [val_apply, val_apply, l1, l2, s1, s2]
  exact (add_sub_add_right_eq_sub _ _ _).symm

@[reducible] def self (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : SqExt R where
  C := B
  B := B
  π := AlgHom.id R B
  i := AlgHom.id R B
  π_i _ := rfl
  sq := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (fun _ _ h ↦ h)]
    simp

theorem val_self {B : Type} [CommRing B] [Algebra R B] (y : Sp B ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R B)) (f : Form s) : (self R B).val y hy f.1 = 0 := by
  have hk : RingHom.ker ((self R B).π : B →+* B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h ↦ h
  have k1 : ev f.1 ((self R B).secHom ((self R B).red_w hy) (self R B).i (self R B).π_i) = 0 :=
    f.2 _ rfl hk
  have k2 : ev f.1 ((self R B).idHom hy) = 0 := f.2 _ rfl hk
  rw [val_apply, k1, k2, sub_zero]

theorem π_val (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.π (E.val y hy f.1) = 0 := by
  let ρ : E.thick (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy) ⟶
      Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy) :=
    { φ := E.π
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2
          ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_bot.2 (RingHom.mem_ker.1 ha)
        · rw [RingHom.mem_ker.1 ha, (dp0 E.B).dpow_eval_zero hn]
          rcases Nat.lt_or_ge n 2 with h2 | h2
          · obtain rfl : n = 1 := by omega
            rw [(divided₂ E.sq).dpow_one ha, RingHom.mem_ker.1 ha]
          · rw [squareZeroDividedPowers_dpow E.sq h2, map_zero]
      pt := by
        change spMap (RingHom.id E.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
          spMap (E.π : E.C →+* E.B) ≫ y
        rw [spMap_id, Category.id_comp] }
  have k1 : ev f.1 (E.secHom (E.red_w hy) E.i E.π_i ≫ ρ) = 0 :=
    f.2 (E.secHom (E.red_w hy) E.i E.π_i ≫ ρ) rfl rfl
  have k2 : ev f.1 (E.idHom hy ≫ ρ) = 0 := f.2 (E.idHom hy ≫ ρ) rfl rfl
  rw [ev_comp] at k1 k2
  rw [val_apply, map_sub]
  exact sub_eq_zero.2 (add_right_cancel (k1.trans k2.symm))

theorem val_const (x : Sp E.B ⟶ X) (hx : x ≫ s = spMap (algebraMap R E.B)) (y : Sp E.C ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R E.C)) (e : spMap (E.i : E.B →+* E.C) ≫ x = y) (f : Form s) :
    E.val y hy f.1 = 0 := by
  subst e
  have hpi : (E.π : E.C →+* E.B).comp (E.i : E.B →+* E.C) = RingHom.id E.B := RingHom.ext E.π_i
  let lam : Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ spMap (E.i : E.B →+* E.C) ≫ x)
      (E.red_w hy) ⟶ Thick.triv E.C (spMap (E.i : E.B →+* E.C) ≫ x) hy :=
    Thick.trivHom E.i (by
      change spMap ((RingHom.id E.C).comp (E.i : E.B →+* E.C)) ≫ spMap (E.π : E.C →+* E.B) ≫
          spMap (E.i : E.B →+* E.C) ≫ x = spMap (E.i : E.B →+* E.C) ≫ x
      rw [RingHom.id_comp, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← spMap_comp, hpi,
        spMap_id, Category.id_comp])
  have k : E.secHom (E.red_w hy) E.i E.π_i = lam ≫ E.idHom hy := Thick.hom_ext fun _ ↦ rfl
  rw [val_apply, k, ev_comp, show ev f.1 lam = 0 from f.2 lam rfl rfl, map_zero, zero_add,
    sub_self]

end SqExt

end GlobalTheory.Cris
