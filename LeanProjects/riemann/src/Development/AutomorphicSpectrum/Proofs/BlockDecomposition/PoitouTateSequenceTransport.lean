import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge

namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer

section Ladder

variable {R : Type*} [CommRing R]

theorem exact_transfer {A A' B B' C C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
    (a : A' ≃ₗ[R] A) (b : B' ≃ₗ[R] B) (c : C' ≃ₗ[R] C)
    {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'} {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h1 : ∀ x, f (a x) = b (f' x)) (h2 : ∀ y, g (b y) = c (g' y))
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  obtain ⟨y', rfl⟩ := b.surjective y
  rw [h2, LinearEquiv.map_eq_zero_iff, h y']
  constructor
  · rintro ⟨x', rfl⟩
    exact ⟨a x', h1 x'⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := a.surjective x
    exact ⟨x', b.injective (by rw [← h1, hx])⟩

theorem nine_ladder {X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 X0' X1' X2' Y0' Y1' Y2' W0' W1' W2' : Type*}
    [AddCommGroup X0] [Module R X0] [AddCommGroup X1] [Module R X1]
    [AddCommGroup X2] [Module R X2] [AddCommGroup Y0] [Module R Y0]
    [AddCommGroup Y1] [Module R Y1] [AddCommGroup Y2] [Module R Y2]
    [AddCommGroup W0] [Module R W0] [AddCommGroup W1] [Module R W1]
    [AddCommGroup W2] [Module R W2]
    [AddCommGroup X0'] [Module R X0'] [AddCommGroup X1'] [Module R X1']
    [AddCommGroup X2'] [Module R X2'] [AddCommGroup Y0'] [Module R Y0']
    [AddCommGroup Y1'] [Module R Y1'] [AddCommGroup Y2'] [Module R Y2']
    [AddCommGroup W0'] [Module R W0'] [AddCommGroup W1'] [Module R W1']
    [AddCommGroup W2'] [Module R W2']
    (a0 : X0' ≃ₗ[R] X0) (a1 : X1' ≃ₗ[R] X1) (a2 : X2' ≃ₗ[R] X2)
    (p0 : Y0' ≃ₗ[R] Y0) (p1 : Y1' ≃ₗ[R] Y1) (p2 : Y2' ≃ₗ[R] Y2)
    (w0 : W0' ≃ₗ[R] W0) (w1 : W1' ≃ₗ[R] W1) (w2 : W2' ≃ₗ[R] W2)
    {g0 : X0 →ₗ[R] Y0} {g1 : X1 →ₗ[R] Y1} {g2 : X2 →ₗ[R] Y2}
    {t0 : Y0 →ₗ[R] W0} {t1 : Y1 →ₗ[R] W1} {t2 : Y2 →ₗ[R] W2}
    {g0' : X0' →ₗ[R] Y0'} {g1' : X1' →ₗ[R] Y1'} {g2' : X2' →ₗ[R] Y2'}
    {t0' : Y0' →ₗ[R] W0'} {t1' : Y1' →ₗ[R] W1'} {t2' : Y2' →ₗ[R] W2'}
    (hg0 : ∀ x, g0 (a0 x) = p0 (g0' x)) (hg1 : ∀ x, g1 (a1 x) = p1 (g1' x))
    (hg2 : ∀ x, g2 (a2 x) = p2 (g2' x))
    (ht0 : ∀ y, t0 (p0 y) = w0 (t0' y)) (ht1 : ∀ y, t1 (p1 y) = w1 (t1' y))
    (ht2 : ∀ y, t2 (p2 y) = w2 (t2' y))
    (h : ∃ (d1' : W0' →ₗ[R] X1') (d2' : W1' →ₗ[R] X2'),
      Function.Injective g0' ∧ Function.Exact g0' t0' ∧ Function.Exact t0' d1' ∧
      Function.Exact d1' g1' ∧ Function.Exact g1' t1' ∧ Function.Exact t1' d2' ∧
      Function.Exact d2' g2' ∧ Function.Exact g2' t2' ∧ Function.Surjective t2') :
    ∃ (d1 : W0 →ₗ[R] X1) (d2 : W1 →ₗ[R] X2),
      Function.Injective g0 ∧ Function.Exact g0 t0 ∧ Function.Exact t0 d1 ∧
      Function.Exact d1 g1 ∧ Function.Exact g1 t1 ∧ Function.Exact t1 d2 ∧
      Function.Exact d2 g2 ∧ Function.Exact g2 t2 ∧ Function.Surjective t2 := by
  obtain ⟨d1', d2', i0, e1, e2, e3, e4, e5, e6, e7, s8⟩ := h
  have hd1 : ∀ y, (a1.toLinearMap ∘ₗ d1' ∘ₗ w0.symm.toLinearMap) (w0 y) = a1 (d1' y) := by
    intro y; simp
  have hd2 : ∀ y, (a2.toLinearMap ∘ₗ d2' ∘ₗ w1.symm.toLinearMap) (w1 y) = a2 (d2' y) := by
    intro y; simp
  refine ⟨a1.toLinearMap ∘ₗ d1' ∘ₗ w0.symm.toLinearMap,
    a2.toLinearMap ∘ₗ d2' ∘ₗ w1.symm.toLinearMap, ?_, exact_transfer a0 p0 w0 hg0 ht0 e1,
    exact_transfer p0 w0 a1 ht0 hd1 e2, exact_transfer w0 a1 p1 hd1 hg1 e3,
    exact_transfer a1 p1 w1 hg1 ht1 e4, exact_transfer p1 w1 a2 ht1 hd2 e5,
    exact_transfer w1 a2 p2 hd2 hg2 e6, exact_transfer a2 p2 w2 hg2 ht2 e7, ?_⟩
  · intro x y hxy
    obtain ⟨x', rfl⟩ := a0.surjective x
    obtain ⟨y', rfl⟩ := a0.surjective y
    rw [hg0, hg0] at hxy
    rw [i0 (p0.injective hxy)]
  · intro w
    obtain ⟨y', hy⟩ := s8 (w2.symm w)
    exact ⟨p2 y', by rw [ht2, hy]; simp⟩

def piE {I I' : Type*} {A : I' → Type*} {B : I → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (eI : I ≃ I') (e : ∀ i, A (eI i) ≃ₗ[R] B i) : (∀ i', A i') ≃ₗ[R] ∀ i, B i :=
  (LinearEquiv.piCongrLeft R A eI).symm ≪≫ₗ LinearEquiv.piCongrRight e

@[simp] theorem piE_apply {I I' : Type*} {A : I' → Type*} {B : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (eI : I ≃ I') (e : ∀ i, A (eI i) ≃ₗ[R] B i) (x : ∀ i', A i') (i : I) :
    piE eI e x i = e i (x (eI i)) := rfl

end Ladder

section Main

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type}
  [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I]
  [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
  (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
  (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) (hχ : ∀ g, χ' (eG g) = χ g)
  (hc : ∀ g m, ρ' (eG g) m = ρ g m)
  (hd : ∀ g f, twDual χ' ρ' (eG g) f = twDual χ ρ g f)
  (hl : ∀ i d m, (ρ'.comp (φ' (eI i))) (eD i d) m = (ρ.comp (φ i)) d m)

include hχ hc in

theorem twDual_transfer : ∀ g f, twDual χ' ρ' (eG g) f = twDual χ ρ g f := by
  intro g f
  ext m
  rw [twDual_apply, twDual_apply, hχ, ← map_inv eG, hc]

include hD hc in

theorem loc_transfer :
    ∀ i d m, (ρ'.comp (φ' (eI i))) (eD i d) m = (ρ.comp (φ i)) d m := by
  intro i d m
  simp only [MonoidHom.comp_apply, hD, hc]

def P0 : (∀ i', H0 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  piE eI fun i => equivH0OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)

def P1 : (∀ i', H1 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  piE eI fun i => equivH1OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)

def P2 : (∀ i', H2 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  piE eI fun i => equivH2OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)

theorem local_degree_zero_square (x : H0 ρ') :
    gloc0 φ ρ (equivH0OfIso eG ρ' ρ hc x) = P0 φ φ' ρ ρ' eI eD hl (gloc0 φ' ρ' x) := by
  funext i
  exact Subtype.ext rfl

include hD in
theorem local_degree_one_square (x : H1 ρ') :
    gloc1 φ hφ ρ (equivH1OfIso eG ρ' ρ hc x) = P1 φ φ' ρ ρ' eI eD hl (gloc1 φ' hφ' ρ' x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    funext i
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d)) = f.1 (φ' (eI i) (eD i d))
    rw [hD]

include hD in
theorem local_degree_two_square (x : H2 ρ') :
    gloc2 φ hφ ρ (equivH2OfIso eG ρ' ρ hc x) = P2 φ φ' ρ ρ' eI eD hl (gloc2 φ' hφ' ρ' x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    funext i
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d.1), eG (φ i d.2)) = f.1 (φ' (eI i) (eD i d.1), φ' (eI i) (eD i d.2))
    rw [hD, hD]

variable (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
  (hj : ∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
    (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
      j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z))

include hD hj in
theorem trace_pairing_degree_zero_square (x : ∀ i', H0 (ρ'.comp (φ' i'))) (y : H2 (twDual χ' ρ')) :
    gtr0 φ hφ χ j ρ (P0 φ φ' ρ ρ' eI eD hl x) (equivH2OfIso eG _ _ hd y) =
      gtr0 φ' hφ' χ' j' ρ' x y := by
  simp only [gtr0, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply]
  rw [← Equiv.sum_comp eI]
  refine Finset.sum_congr rfl fun i _ => ?_
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    refine (hj i _ _ fun g h => ?_).symm
    show evalPair (x (eI i)).1 (z.1 (φ' (eI i) (eD i g), φ' (eI i) (eD i h))) =
      evalPair (x (eI i)).1 (z.1 (eG (φ i g), eG (φ i h)))
    rw [hD, hD]

include hj in
theorem trace_pairing_degree_two_square (x : ∀ i', H2 (ρ'.comp (φ' i'))) (y : H0 (twDual χ' ρ')) :
    gtr2 φ χ j ρ (P2 φ φ' ρ ρ' eI eD hl x) (equivH0OfIso eG _ _ hd y) =
      gtr2 φ' χ' j' ρ' x y := by
  simp only [gtr2, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply]
  rw [← Equiv.sum_comp eI]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show P2 φ φ' ρ ρ' eI eD hl x i =
    equivH2OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i) (x (eI i)) from rfl]
  generalize x (eI i) = u
  induction u using Submodule.Quotient.induction_on with
  | H w =>
    exact (hj i _ _ fun g h => rfl).symm

include hD hc hj in
theorem trace_pairing_degree_one_square (hρ : ContAction ρ) (hρ' : ContAction ρ')
    (x : ∀ i', H1 (ρ'.comp (φ' i'))) (y : H1 (twDual χ' ρ')) :
    gtr1 φ hφ χ j ρ hρ (P1 φ φ' ρ ρ' eI eD hl x) (equivH1OfIso eG _ _ hd y) =
      gtr1 φ' hφ' χ' j' ρ' hρ' x y := by
  simp only [gtr1, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply, LinearMap.flip_apply]
  rw [← Equiv.sum_comp eI]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show P1 φ φ' ρ ρ' eI eD hl x i =
    equivH1OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i) (x (eI i)) from rfl]
  generalize x (eI i) = u
  induction y using Submodule.Quotient.induction_on with
  | H a =>
    induction u using Submodule.Quotient.induction_on with
    | H b =>
      refine (hj i _ _ fun g h => ?_).symm
      show (a.1 (φ' (eI i) (eD i g))) (ρ' (φ' (eI i) (eD i g)) (b.1 (eD i h))) =
        (a.1 (eG (φ i g))) (ρ (φ i g) (b.1 (eD i h)))
      rw [hD, hc]

end Main

theorem nineG_of_iso {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type}
    [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
    (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)) :
    (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) →
    (∀ g m, ρ' (eG g) m = ρ g m) →
    ∀ (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
      (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
      (hρ : ContAction ρ) (hρ' : ContAction ρ'),
      (∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
        (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
          j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z)) →
      NineG φ' hφ' χ' j' ρ' hρ' → NineG φ hφ χ j ρ hρ := by
  intro hD hχ hc j j' hρ hρ' hj hN
  have hd := twDual_transfer χ χ' ρ ρ' eG hχ hc
  have hl := loc_transfer φ φ' ρ ρ' eG eI eD hD hc
  unfold NineG at hN ⊢
  have dual_sq : ∀ {A A' : Type} [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
      {Y Y' : Type} [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R Y']
      (β : A' ≃ₗ[R] A) (p : Y' ≃ₗ[R] Y) (t : Y →ₗ[R] Module.Dual R A)
      (t' : Y' →ₗ[R] Module.Dual R A') (_ : ∀ x y, t (p x) (β y) = t' x y) (x : Y'),
      t (p x) = β.symm.dualMap (t' x) := by
    intro A A' _ _ _ _ Y Y' _ _ _ _ β p t t' h x
    refine LinearMap.ext fun y => ?_
    obtain ⟨y', rfl⟩ := β.surjective y
    simp [LinearEquiv.dualMap_apply, h]
  exact nine_ladder (equivH0OfIso eG ρ' ρ hc) (equivH1OfIso eG ρ' ρ hc) (equivH2OfIso eG ρ' ρ hc)
    (P0 φ φ' ρ ρ' eI eD hl) (P1 φ φ' ρ ρ' eI eD hl) (P2 φ φ' ρ ρ' eI eD hl)
    (equivH2OfIso eG _ _ hd).symm.dualMap (equivH1OfIso eG _ _ hd).symm.dualMap (equivH0OfIso eG _ _ hd).symm.dualMap
    (local_degree_zero_square φ φ' ρ ρ' eG eI eD hc hl) (local_degree_one_square φ hφ φ' hφ' ρ ρ' eG eI eD hD hc hl)
    (local_degree_two_square φ hφ φ' hφ' ρ ρ' eG eI eD hD hc hl)
    (dual_sq _ _ _ _ (trace_pairing_degree_zero_square φ hφ φ' hφ' χ χ' ρ ρ' eG eI eD hD hd hl j j' hj))
    (dual_sq _ _ _ _ (trace_pairing_degree_one_square φ hφ φ' hφ' χ χ' ρ ρ' eG eI eD hD hc hd hl j j' hj hρ hρ'))
    (dual_sq _ _ _ _ (trace_pairing_degree_two_square φ φ' χ χ' ρ ρ' eG eI eD hd hl j j' hj)) hN

end GlobalTheory.CompanionTheory.PTIso.NineTransfer
