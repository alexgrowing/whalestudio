import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
noncomputable section

namespace GlobalTheory.TInj

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F]
    (z : (TF (R := V) F).left) {k₁ k₂ : Fˣ}
    (h : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₁) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₂)) : k₁ = k₂ := by
  have e : unitOn k₁ = unitOn k₂ := unit_ext fun x _ => by
    have : x = z := Subsingleton.elim (α := PrimeSpectrum F) x z
    rw [this]; exact h
  revert e
  apply Units.map_injective
  intro x y h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h
  simpa using this

theorem cancel_four {G : Type} [CommGroup G] {V₁ V₂ K₁ K₂ L₁ L₂ U τ : G} (h₁ : V₁ = K₁ * (L₁ * τ))
    (h₂ : V₂ = K₂ * (L₂ * τ)) (h₃ : V₂ = V₁ * U) (h₄ : L₂ = L₁ * U) : K₁ = K₂ := by
  rw [h₄, h₃, h₁] at h₂
  have e : K₁ * (L₁ * U * τ) = K₂ * (L₁ * U * τ) := by rw [← h₂]; ac_rfl
  exact mul_right_cancel e

theorem coords_eq_of_match : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hn hε hD₁ hD₂ hF₁ hF₂ hs₁ hs₂ hM he hb H
  obtain ⟨ε₀, hε₀⟩ := hε
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  let f : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have key : ∀ c a : Fin T.r → ℤ, ∏ i, f (s₁ i) ^ ε i c a = ∏ i, f (s₂ i) ^ ε i c a := by
    intro c a
    obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hD₂ F n hn p' p₂ (by
      rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
    rw [hg] at hA
    have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
    obtain ⟨u, hun⟩ := hu (e₂.symm c)
    obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
    obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
    let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
    obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
    have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
    have a₃ := hA.2 (e₂.symm c) u hun z J hJ
    have a₄ := GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
      (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
    rw [← hA.1] at a₄
    rw [hχ] at a₁
    have hk : k₁ = k₂ := by
      apply gm_unitOn_inj z
      exact cancel_four a₁ a₂ a₃ a₄
    have := congrArg Units.val hk
    rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
    exact this
  simp only [hε₀] at key
  have hx := GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq F T.r I ε₀ (fun i => f (s₁ i)) (fun i => f (s₂ i))
    (fun i => (map_ne_zero_iff f hf).2 (hs₁ i)) (fun i => (map_ne_zero_iff f hf).2 (hs₂ i)) (fun a b => key a b)
  funext i
  exact hf (congrFun hx i)

end GlobalTheory.TInj
