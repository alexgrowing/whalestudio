import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationExtensionOfAffine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DerFieldExt

theorem cover' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) :
    W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) (s t : Γ(X, W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k s = resG X k t) : s = t :=
  X.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
    W (fun i => homOfLE i.2) (cover' X hW h) s t (fun i => e i.1 i.2)

theorem exists_field : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U),
    (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) →
    ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  intro X W₀ hW d₀ hadd hmul
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(X, X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG X (X.basicOpen_le f) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    obtain ⟨δ, h1, h2, h3⟩ := GlobalTheory.LocDerExt.der_exists f (RingHom.id _)
      (fun a => resG X (X.basicOpen_le f) (d₀ a)) (fun a b => by simp only [hadd, map_add])
      (fun a b => by simp only [hmul, map_add, map_mul, RingHom.id_apply]; rfl)
    exact ⟨δ, h1, fun a b => by simpa using h2 a b, h3⟩
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG X k (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine GlobalTheory.LocDerExt.der_unique f (resG X k)
      (fun s => resG X k (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add, map_mul]
    · simp only [δmul, map_mul]
    · change resG X k (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [GlobalTheory.LocDerExt.res_res X, δres, δres, GlobalTheory.LocDerExt.res_res X]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(X, W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      W (fun i => homOfLE i.2) (cover' X hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen (i.1 * j.1) := e.ge
        have e' : resG X ki (δ i.1 (resG X i.2 s)) = resG X kj (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X]
        have e'' := congrArg (resG X k) e'
        rw [GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep' X hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (GlobalTheory.LocDerExt.res_res X h' k _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), GlobalTheory.LocDerExt.res_res X]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep' X hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.DerFieldExt
