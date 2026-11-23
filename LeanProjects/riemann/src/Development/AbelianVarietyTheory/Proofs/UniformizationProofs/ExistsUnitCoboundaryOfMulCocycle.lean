import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums

set_option autoImplicit false

open AddMonoidAlgebra

namespace GlobalTheory.MulCocycle

theorem finsupp_homotopy {X : Type*} [Zero X] {N : Type*} [AddCommGroup N] (f : X × X →₀ N)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) (q : X × X) :
    (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) =
      (f - (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
        g.mapDomain (fun y => (y, (0 : X)))) : X × X →₀ N) q := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  obtain rfl : g = s f := Finsupp.ext hg
  clear hg
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← sub_eq_zero] at hf hg ⊢
    rw [← add_zero (0 : N)]
    nth_rewrite 1 [← hf]
    rw [← hg]; abel
  | single p m =>
    obtain ⟨y, z⟩ := p
    by_cases h : y = 0
    · subst h
      have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
        ext x; simp [hs, Finsupp.single_apply]
      simp [this, Finsupp.single_apply]
      abel
    · have : s (Finsupp.single (y, z) m) = 0 := by
        ext x; simp [hs, h]
      simp [this, Finsupp.single_apply, h]

variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

theorem mem_map_algebraMap_iff (J : Ideal B) (b : B[X]) :
    b ∈ J.map (algebraMap B B[X]) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb
    have hb' : b ∈ J • (⊤ : Submodule B B[X]) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    refine Submodule.smul_induction_on hb' (p := fun b => ∀ x, b.coeff x ∈ J) ?_ ?_
    · intro r hr m _ x
      simpa using J.mul_mem_right _ hr
    · intro m m' h h' x
      simpa using J.add_mem (h x) (h' x)
  · intro h
    rw [← AddMonoidAlgebra.sum_coeff_single b]
    refine Ideal.sum_mem _ fun x _ => ?_
    have : single x (b.coeff x) = single x 1 * algebraMap B B[X] (b.coeff x) := by
      simp [AddMonoidAlgebra.single_mul_single]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h x))

theorem algHom_mem_map {C C' : Type*} [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    {J : Ideal B} (φ : C →ₐ[B] C') {a : C} (ha : a ∈ J.map (algebraMap B C)) :
    φ a ∈ J.map (algebraMap B C') := by
  have := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem mul_mem_map_sq {C : Type*} [CommRing C] [Algebra B C] {J : Ideal B} {a b : C}
    (ha : a ∈ J.map (algebraMap B C)) (hb : b ∈ J.map (algebraMap B C)) :
    a * b ∈ (J ^ 2).map (algebraMap B C) := by
  rw [Ideal.map_pow, pow_two]
  exact Ideal.mul_mem_mul ha hb

theorem exists_unit_of_faces {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [Algebra B R₁] [Algebra B R₂] [Algebra B R₃]
    (e₀ e₁ e₂ : R₁ →ₐ[B] R₂) (d₀ d₁ d₂ d₃ : R₂ →ₐ[B] R₃)
    (h₁ : ∀ w, d₁ (e₁ w) = d₂ (e₁ w)) (h₂ : ∀ w, d₁ (e₂ w) = d₃ (e₁ w))
    (h₃ : ∀ w, d₁ (e₀ w) = d₀ (e₀ w)) (h₄ : ∀ w, d₃ (e₂ w) = d₂ (e₂ w))
    (h₅ : ∀ w, d₃ (e₀ w) = d₀ (e₂ w)) (h₆ : ∀ w, d₂ (e₀ w) = d₀ (e₁ w))
    (H : ∀ (K L : Ideal B) (φ : R₂), φ ∈ K.map (algebraMap B R₂) →
      d₀ φ - d₁ φ + d₂ φ - d₃ φ ∈ L.map (algebraMap B R₃) →
      ∃ ψ ∈ K.map (algebraMap B R₁), φ - (e₀ ψ - e₁ ψ + e₂ ψ) ∈ L.map (algebraMap B R₂))
    (n : ℕ) : ∀ (K : Ideal B), K ^ 2 ^ n = ⊥ → ∀ f : R₂, f - 1 ∈ K.map (algebraMap B R₂) →
      d₁ f * d₃ f = d₂ f * d₀ f →
      ∃ g : R₁ˣ, g.val - 1 ∈ K.map (algebraMap B R₁) ∧ f * e₁ g.val = e₂ g.val * e₀ g.val := by
  induction n with
  | zero =>
    intro K hK f hf _
    rw [pow_zero, pow_one] at hK
    rw [hK, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at hf
    exact ⟨1, by simp, by simp [hf]⟩
  | succ n ih =>
    intro K hK f hf hc
    obtain ⟨φ, rfl⟩ : ∃ φ, f = 1 + φ := ⟨f - 1, by ring⟩
    rw [add_sub_cancel_left] at hf
    have hc' := hc
    simp only [map_add, map_one] at hc'
    obtain ⟨ψ, hψ, e⟩ := H K (K ^ 2) φ hf (by
      have : d₀ φ - d₁ φ + d₂ φ - d₃ φ = d₁ φ * d₃ φ - d₂ φ * d₀ φ := by
        linear_combination -hc'
      rw [this]
      exact sub_mem (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf))
        (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf)))
    have hn : IsNilpotent ψ := ⟨2 ^ (n + 1), by
      have := Ideal.pow_mem_pow hψ (2 ^ (n + 1))
      rwa [← Ideal.map_pow, hK, Ideal.map_bot, Ideal.mem_bot] at this⟩
    obtain ⟨u, hu⟩ := hn.isUnit_one_add
    have huv : u.val * (u⁻¹).val = 1 := u.mul_inv
    generalize (u⁻¹).val = v at huv
    have k (e : R₁ →ₐ[B] R₂) : e u.val * e v = 1 := by rw [← map_mul, huv, map_one]
    have k' (d : R₂ →ₐ[B] R₃) (e : R₁ →ₐ[B] R₂) : d (e u.val) * d (e v) = 1 := by
      rw [← map_mul, k, map_one]
    obtain ⟨g, hg, hg'⟩ := ih (K ^ 2) (by rw [← pow_mul, ← pow_succ', hK])
      ((1 + φ) * e₁ u.val * e₂ v * e₀ v) (by
        have : (1 + φ) * e₁ u.val * e₂ v * e₀ v - 1 =
            ((φ - (e₀ ψ - e₁ ψ + e₂ ψ)) + φ * e₁ ψ - e₂ ψ * e₀ ψ) * (e₂ v * e₀ v) := by
          have k₀ := k e₀
          have k₂ := k e₂
          rw [hu] at k₀ k₂ ⊢
          simp only [map_add, map_one] at k₀ k₂ ⊢
          linear_combination ((1 + e₀ ψ) * e₀ v) * k₂ + k₀
        rw [this]
        exact Ideal.mul_mem_right _ _ (sub_mem (add_mem e
          (mul_mem_map_sq hf (algHom_mem_map _ hψ)))
          (mul_mem_map_sq (algHom_mem_map _ hψ) (algHom_mem_map _ hψ)))) (by
        have k₁ := k' d₃ e₁
        have k₂ := k' d₀ e₁
        generalize 1 + φ = f at hc
        simp only [map_mul, h₁, h₂, h₃, h₄, h₅, h₆]
        linear_combination
          (d₂ (e₁ u.val) * d₂ (e₂ v) * d₀ (e₂ v) * d₀ (e₀ v)) *
            (d₁ f * d₃ f * k₁ - d₂ f * d₀ f * k₂ + hc))
    refine ⟨u * g, ?_, ?_⟩
    · have : (u * g).val - 1 = u.val * (g.val - 1) + ψ := by
        rw [Units.val_mul, hu]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _
        (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hg)) hψ
    · have k₀ := k e₀
      have k₂ := k e₂
      simp only [Units.val_mul, map_mul]
      linear_combination (e₂ u.val * e₀ u.val) * hg' -
        ((1 + φ) * e₁ u.val * e₁ g.val) * (e₀ u.val * e₀ v * k₂ + k₀)

end GlobalTheory.MulCocycle

namespace GlobalTheory

open MulCocycle

theorem exists_unit_coboundary_of_mul_cocycle (B : Type) [CommRing B] (I : Ideal B)
    (hI : IsNilpotent I) (X : Type) [AddCommGroup X] (f : AddMonoidAlgebra B (X × X))
    (hf : ∀ p, (f - 1).coeff p ∈ I)
    (hc : AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) f =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) f) :
    ∃ g : (AddMonoidAlgebra B X)ˣ, (∀ x, (g.val - 1).coeff x ∈ I) ∧
      f * AddMonoidAlgebra.mapDomain (fun x : X => (x, x)) g.val =
        AddMonoidAlgebra.mapDomain (fun x : X => (x, (0 : X))) g.val *
          AddMonoidAlgebra.mapDomain (fun x : X => ((0 : X), x)) g.val := by
  obtain ⟨n, hn⟩ := hI
  have hn' : I ^ 2 ^ n = ⊥ :=
    le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le).trans hn.le)
  have key : ∀ (a a' : X →+ X × X) (b b' : X × X →+ X × X × X), (∀ x, b (a x) = b' (a' x)) →
      ∀ w : B[X], mapDomainAlgHom B B b (mapDomainAlgHom B B a w) =
        mapDomainAlgHom B B b' (mapDomainAlgHom B B a' w) := by
    intro a a' b b' h w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single x r => simp [h]
  obtain ⟨g, hg, hg'⟩ := exists_unit_of_faces (B := B)
    (mapDomainAlgHom B B (AddMonoidHom.inr X X))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)))
    (mapDomainAlgHom B B (AddMonoidHom.inl X X))
    (mapDomainAlgHom B B (AddMonoidHom.inr X (X × X)))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod
      ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prodMap (AddMonoidHom.inl X X)))
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (fun K L φ hφ hd => by
      rw [mem_map_algebraMap_iff] at hφ hd
      refine ⟨ofCoeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn), (mem_map_algebraMap_iff _ _).2 fun x => hφ (0, x),
        (mem_map_algebraMap_iff _ _).2 fun q => ?_⟩
      have := finsupp_homotopy φ.coeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn) (fun _ => rfl) q
      exact (congrArg (· ∈ L) this).mp (hd (0, q)))
    n I hn' f ((mem_map_algebraMap_iff _ _).2 hf) hc
  exact ⟨g, (mem_map_algebraMap_iff _ _).1 hg, hg'⟩

end GlobalTheory
