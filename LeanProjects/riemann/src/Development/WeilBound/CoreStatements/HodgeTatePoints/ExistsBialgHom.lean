import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twpol

open Coalgebra WithConv

section Level

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A]
  {J : Type} (x : J → A →ₐ[O] O)

abbrev fm (a : J) : CartierDual O A := toConv (x a).toLinearMap

theorem sep_two (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g) (s t : A ⊗[O] A)
    (h : ∀ a b, CartierDual.pair O A A (fm x a ⊗ₜ fm x b) s = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) t) :
    s = t := by
  have hr : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      φ (TensorProduct.rid O A (LinearMap.lTensor A ψ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [mul_comm]
  have hl : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      ψ (TensorProduct.lid O A (LinearMap.rTensor A φ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
  refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
  rw [← hl, ← hl]
  refine congrArg _ (sep _ _ fun b => ?_)
  refine (hl φ (fm x b) s).trans (Eq.trans ?_ (hl φ (fm x b) t).symm)
  rw [← hr, ← hr]
  refine congrArg _ (sep _ _ fun a => ?_)
  exact (hr (fm x a) (fm x b) s).trans ((h a b).trans (hr (fm x a) (fm x b) t).symm)

theorem exists_bialgHom [AddCommGroup J] (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g)
    (h0 : fm x 0 = 1) (hadd : ∀ a b, fm x (a + b) = fm x a * fm x b)
    (l : CartierDual O A →ₗ[O] A) (u : J → A) (hl : ∀ a φ, x a (l φ) = φ (u a))
    (hu0 : ∀ b, x b (u 0) = 1) (hu0' : ∀ a, x 0 (u a) = 1)
    (hua : ∀ a a' b, x b (u (a + a')) = x b (u a) * x b (u a'))
    (hub : ∀ a b b', x (b + b') (u a) = x b (u a) * x b' (u a)) :
    ∃ lam : CartierDual O A →ₐc[O] A, ∀ φ, lam φ = l φ := by
  have hx0 : ∀ f, x 0 f = counit (R := O) f := fun f => congrArg (fun φ : CartierDual O A => φ f) h0
  have hxa : ∀ a b f, x (a + b) f = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) (comul f) := fun a b f =>
    (congrArg (fun φ : CartierDual O A => φ f) (hadd a b)).trans (CartierDual.mul_apply _ _ _)
  have hone : u 0 = 1 := sep _ _ fun b => by rw [hu0, map_one]
  have hmul : ∀ a a', u (a + a') = u a * u a' := fun a a' => sep _ _ fun b => by rw [hua, map_mul]
  have hco : ∀ a, comul (R := O) (u a) = u a ⊗ₜ u a := fun a => sep_two x sep _ _ fun b b' => by
    rw [← hxa, hub, CartierDual.pair_tmul_tmul]; rfl
  let F : CartierDual O A →ₐ[O] A := AlgHom.ofLinearMap l
    (sep _ _ fun a => by rw [hl, map_one, CartierDual.one_apply, ← hx0, hu0'])
    (fun φ ψ => sep _ _ fun a => by
      rw [map_mul (x a), hl, hl, hl, CartierDual.mul_apply, hco, CartierDual.pair_tmul_tmul])
  have hF : ∀ φ, F φ = l φ := fun _ => rfl
  refine ⟨BialgHom.ofAlgHom F (AlgHom.ext fun φ => ?_) (AlgHom.ext fun φ => ?_), fun φ => rfl⟩
  · change counit (R := O) (l φ) = counit (R := O) φ
    rw [← hx0, hl, hone, CartierDual.counit_apply]
  · change Algebra.TensorProduct.map F F (comul (R := O) φ) = comul (R := O) (l φ)
    refine sep_two x sep _ _ fun a b => ?_
    rw [← hxa, hl, hmul, ← CartierDual.pair_comul_tmul]
    generalize comul (R := O) φ = s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul φ ψ =>
      rw [Algebra.TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, ← hl, ← hl]
      rfl

end Level

theorem exists_linear {O A T J : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O (T → O))
    (e : A ≃ₐ[O] S) (q : J → T) (x : J → A →ₐ[O] O) (hx : ∀ a f, x a f = (e f).1 (q a))
    (s : T × T → O) (hs : s ∈ Submodule.span O {g | ∃ a ∈ S, ∃ b ∈ S, g = fun z : T × T => a z.1 * b z.2}) :
    ∃ (l : CartierDual O A →ₗ[O] A) (u : J → A),
      (∀ a φ, x a (l φ) = φ (u a)) ∧ ∀ a b, x b (u a) = s (q a, q b) := by
  induction hs using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, g, hg, rfl⟩ := hg
    refine ⟨(CartierDual.evalAt O A (e.symm ⟨g, hg⟩)).smulRight (e.symm ⟨f, hf⟩),
      fun a => f (q a) • e.symm ⟨g, hg⟩, fun a φ => ?_, fun a b => ?_⟩
    · rw [LinearMap.smulRight_apply, map_smul, map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul,
        mul_comm]
      rfl
    · rw [map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul]
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨l, u, h1, h2⟩ := hs
    obtain ⟨l', u', h1', h2'⟩ := ht
    exact ⟨l + l', u + u', by simp [h1, h1'], by simp [h2, h2']⟩
  | smul c s _ hs =>
    obtain ⟨l, u, h1, h2⟩ := hs
    exact ⟨c • l, c • u, by simp [h1], by simp [h2]⟩

theorem tower_pol : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := exists_linear (X.A n) (e n) (lev p n) (fun a => (τ a).pt n)
      (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end PositivityTheory.HtPt.Twpol
