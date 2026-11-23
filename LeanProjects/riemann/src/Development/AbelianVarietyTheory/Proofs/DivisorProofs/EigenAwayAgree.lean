import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepInlEqInr

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj IsDedekindDomain

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp_eq {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isTanAtG_bc {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T)
    {x : Sp S ⟶ X} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  have e₁ : (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e₂ : (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
    RingHom.ext fun z => by simp [dualMap]
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, ← Category.assoc, spMap_comp_eq, e₁, ← spMap_comp_eq, Category.assoc]
  · rw [← Category.assoc, spMap_comp_eq, e₂, ← spMap_comp_eq, Category.assoc, hv.2]
    let p : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x := Over.homMk (spMap ψ) rfl
    rw [← MonObj.comp_one p]
    rfl

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem lnStep_frame {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (ψ : R →+* C) (p : ℕ) (hp : p.Prime)
    (hpC : ‖(p : C)‖ < 1) (hpd : ¬ p ∣ (NumberField.discr E).natAbs) (b : Bool) (k : ℕ)
    (z : Letter Dw) (hk : (letters Dw)[k]? = some z) :
    lnStep Z.t (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p b (.inr k) =
      lnStep Z.t (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p b (.inl (z.1, (z.2 : ℕ))) := by
  refine (GlobalTheory.UnramLine.lnStep_inl_eq_inr Z.t (spMap ψ ≫ x) _ p hp hpC hpd
    (fun τ => (ψ.comp φ).comp (embF c τ)) ?_ (fun τ i => isTanAtG_bc Z.t ψ (f.tan τ i)) ?_ b k z hk).symm
  · intro τ τ' h
    ext a
    have h₁ : (ψ.comp φ) (embF c τ a) = (ψ.comp φ) (embF c τ' a) := congrArg (fun g : E →+* C => g a) h
    exact congrArg Subtype.val ((ψ.comp φ).injective h₁)
  · intro τ i a
    rw [Category.assoc, f.eig τ i a, ← Category.assoc, spMap_comp_eq, dualMap_comp_epsMul, ← spMap_comp_eq,
      Category.assoc]
    rfl

theorem norm_p_lt_one_padicComplex (p : ℕ) (hp : Fact p.Prime) : ‖(p : ℂ_[p])‖ < 1 := by
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem sum_single_one {α : Type} (s : α) (g : α → ℝ) :
    (Finsupp.single s (1 : ℤ)).sum (fun a n => (n : ℝ) * g a) = g s := by
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem expo_inr_eq_inl (a : ℕ → Bool) (R : Option ℝ) (k : ℕ) (z : Letter Dw) (hk : (letters Dw)[k]? = some z) :
    expo Dw (Finsupp.single ((a, R, .inr k) : Sym E) 1) =
      expo Dw (Finsupp.single ((a, R, .inl (z.1, (z.2 : ℕ))) : Sym E) 1) := by
  funext x
  have h₁ : letterOf Dw (.inr k) = some z := hk
  have h₂ : letterOf Dw (.inl (z.1, (z.2 : ℕ))) = some z := dif_pos z.2.isLt
  rw [expo_single, expo_single]
  dsimp only
  rw [h₁, h₂]

theorem lgOf_inr_eq_inl {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : ℕ → Bool)
    (R : Option ℝ) (k : ℕ) (z : Letter Dw) (hk : (letters Dw)[k]? = some z) (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt Y.Y) (hv : ¬ resP v ∣ (NumberField.discr E).natAbs) :
    lgOf Y (Finsupp.single (a, R, .inr k) 1) v ε y =
      lgOf Y (Finsupp.single (a, R, .inl (z.1, (z.2 : ℕ))) 1) v ε y := by
  unfold lgOf
  split_ifs with hp
  · dsimp only
    rw [expo_inr_eq_inl a R k z hk, sum_single_one, sum_single_one]
    dsimp only
    rw [lnStep_frame _ _ _ hp (norm_p_lt_one_padicComplex _ _) hv _ k z hk]
  · rfl

end General

theorem awayAgree : ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ) (c : O.s.Comp),
    GlobalTheory.EigWhole.AwayAgree O T R c :=
  fun _ O _ T R c k z hk v ε y hv => lgOf_inr_eq_inl (O.Φ.C c) (ArIn.ind T) (some R) k z hk v ε y hv

end GlobalTheory.EigWhole

end
