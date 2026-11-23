import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianModelProperOverThetaSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledLatticeEquivOfCommonFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LatCmp

theorem act_unit {Y : Type} [AddCommGroup Y] (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

theorem exists_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b) :
    ∃ κ : Y ≃ₗ[ℤ] Y', ∀ v : Fin 8 → Y, θ v = fun a => κ (v a) := by
  let κ0 : Y →+ Y' := (Pi.evalAddMonoidHom (fun _ : Fin 8 => Y') 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => Y) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ h v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  refine ⟨(AddEquiv.ofBijective κ0 ⟨inj, surj⟩).toIntLinearEquiv, fun v => ?_⟩
  funext a
  exact hθ v a

end GlobalTheory.Poinc.LatCmp

theorem GlobalTheory.Poinc.lattice_equiv_of_same_centre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c c' : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ κ : c.T.D.toPre.X ≃ₗ[ℤ] c'.T.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (fun u => κ (μ u)) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε p _ z₁ c c' yy yy' h h'
  obtain ⟨Y, U₀, EE, FinalForm, q, hov, hee, hq, hpt, hcon, hlift⟩ := GlobalTheory.T.exists_semiabelianModel_proper_over_thetaSetup g n F W Z i X₁ hg hn ho hi he ht hp
  obtain ⟨y, hy⟩ := hlift p z₁ c
  obtain ⟨y', hy'⟩ := hlift p z₁ c'
  obtain ⟨θ, hl, hE⟩ := GlobalTheory.T.exists_labelled_lattice_equiv_of_common_fibre g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε Y U₀ EE FinalForm q hov hee hq hpt p z₁ (hcon z₁) c c' y y' hy hy' yy yy' h h'
  obtain ⟨κ, hκ⟩ := GlobalTheory.Poinc.LatCmp.exists_diag θ hE
  refine ⟨κ, fun a μ hμ => ?_⟩
  rw [hl a μ hμ, hκ]
