import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.ExistsCoverPowerReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.RootFrame

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

private theorem expo_single_eq (a a' : ℕ → Bool) (R : Option ℝ) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (n : ℤ) :
    expo Dw (Finsupp.single (a, R, st) n) = expo Dw (Finsupp.single (a', R, st) n) := by
  funext x
  unfold expo
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

private theorem expo_root_eq (a a' : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) :
    expo Dw (rootSym Dw a R τ i) = expo Dw (rootSym Dw a' R τ i) := by
  unfold rootSym
  split_ifs <;> exact expo_single_eq _ _ _ _ _

private theorem lgOf_single_eq (a a' : ℕ → Bool) (R : Option ℝ) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (n : ℤ)
    (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt C.Y) (h : a (resP v) = a' (resP v)) :
    lgOf C (Finsupp.single (a, R, st) n) v ε y = lgOf C (Finsupp.single (a', R, st) n) v ε y := by
  unfold lgOf
  rw [expo_single_eq a a']
  split_ifs with hp
  · dsimp only
    rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    dsimp only
    rw [h]
  · rfl

private theorem lgOf_root_eq (a a' : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt C.Y) (h : a (resP v) = a' (resP v)) :
    lgOf C (rootSym Dw a R τ i) v ε y = lgOf C (rootSym Dw a' R τ i) v ε y := by
  unfold rootSym
  split_ifs <;> exact lgOf_single_eq C _ _ _ _ _ v ε y h

private theorem root_support (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) (s : Sym E)
    (hs : s ∈ (rootSym Dw a R τ i).support) : s.1 = a := by
  unfold rootSym at hs
  split_ifs at hs <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hs)]

end SlopeTestRemainingChoices

theorem UpperTheory.flag_component_true_model :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (ε : F ≃+* c.F) (C : FlagCpt Z ε) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (M : GlobalTheory.TrueGeo.Model C.Y) (ρ' : M.X ⟶ Z.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X → M.j ≫ ρ' = C.π ≫ genι Z → ∀ (τ : E →+* ℂ) (a : ℕ → Bool) (R : Option ℝ) (p N : ℕ), ∃ V₀ : Cover C.Y, ∀ (V : Cover C.Y) (b : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G), V.j ≫ b = g ≫ V₀.j → g ≫ V₀.π = V.π → ∀ i : Fin N, PowRead V p (genAt (divOf C (expo Dw (rootSym Dw a R τ i)))) (lgOf C (rootSym Dw a R τ i)) := by
  intro E _ _ _ H Dw l Xo c Z F _ _ ε C _ hX M ρ' hM hρ τ a R p N
  let a' : ℕ → Bool := fun q => a p && decide (q = p)
  have ha' : {q | a' q = true}.Finite :=
    (Set.finite_singleton p).subset fun q hq => by
      have hq' : (a p && decide (q = p)) = true := hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
      exact hq'.2
  obtain ⟨V₀, hV⟩ := UpperTheory.exists_cover_power_readings F C.Y N (fun i => divOf C (expo Dw (rootSym Dw a' R τ i)))
    (fun i => lgOf C (rootSym Dw a' R τ i)) fun i =>
      fromModel_lgOf C GlobalTheory.ShFam.Pad.HTBound.htBound hX M ρ' hM hρ _ fun s hs => by
        rw [root_support a' R τ i s hs]
        exact ha'
  refine ⟨V₀, fun V b g h₁ h₂ i => ?_⟩
  obtain ⟨m, hm, h⟩ := hV V b g h₁ h₂ p i
  rw [expo_root_eq a a']
  refine ⟨m, hm, fun x hx => ?_⟩
  obtain ⟨U, r, hU, h₃, h₄⟩ := h x hx
  refine ⟨U, r, hU, h₃, fun v e y z yt ht hy => ?_⟩
  rw [lgOf_root_eq C a a' R τ i v e y (by rw [ht.1]; simp [a'])]
  exact h₄ v e y z yt ht hy
