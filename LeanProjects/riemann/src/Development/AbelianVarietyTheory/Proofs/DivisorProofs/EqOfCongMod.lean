import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LabUniq

section Lin
variable {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem eq_of_congMod (x y : M) (h : ∀ m : ℕ, 1 ≤ m → CongMod m x y) : x = y := by
  let b := Module.Free.chooseBasis ℤ M
  rw [← sub_eq_zero]
  apply b.repr.injective
  ext k
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (b.repr (x - y) k).natAbs + 1 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := h N (by omega)
  have hxy : x - y = N • w := by rw [hw]; abel
  have h2 : b.repr (x - y) k = (N : ℤ) * b.repr w k := by
    rw [hxy, map_nsmul]; simp [nsmul_eq_mul]
  refine Int.eq_zero_of_abs_lt_dvd ⟨_, h2⟩ ?_
  rw [Int.abs_eq_natAbs]; omega

end Lin

section Diag
variable {Y : Type} [AddCommGroup Y]

theorem act_unit (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y))
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

end Diag

theorem qW_single {Y : Type} [AddCommGroup Y] (W : Matrix (Fin 8) (Fin 8) ℤ) (β : LinearMap.BilinForm ℤ Y) (y : Y) :
    qW W β (Pi.single 0 y) = W 0 0 * β y y := by
  unfold qW
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ κ : c.T.D.toPre.X ≃+ c.T.D.toPre.X, (∀ a b, c.T.β (κ a) (κ b) = c.T.β a b) ∧ ∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (fun a => κ (μ a)) := by
  intro g n F W Z i X ε hdiag p _ z c yy yy' h1 h2
  obtain ⟨θ, hq, hl, hE⟩ := GlobalTheory.T.exists_qW_automorphism_eighthPower_lattice_labels g n F W Z i X ε hdiag p z c yy yy' h1 h2
  have hc : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b :=
    fun E v => eq_of_congMod _ _ fun m hm => hE m hm E v
  let κ0 : c.T.D.toPre.X →+ c.T.D.toPre.X :=
    (Pi.evalAddMonoidHom (fun _ : Fin 8 => c.T.D.toPre.X) 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => c.T.D.toPre.X) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ hc v a
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
  let κ := AddEquiv.ofBijective κ0 ⟨inj, surj⟩
  have hκ : ∀ x, κ x = κ0 x := fun x => rfl
  have hd : ∀ x, c.T.β (κ0 x) (κ0 x) = c.T.β x x := by
    intro x
    have := hq (Pi.single 0 x)
    rw [hsingle, qW_single, qW_single] at this
    exact mul_left_cancel₀ (X.diag_pos 0).ne' this
  refine ⟨κ, ?_, ?_⟩
  · intro a b
    rw [hκ, hκ]
    have hab := hd (a + b)
    simp only [map_add, LinearMap.map_add₂, LinearMap.add_apply] at hab
    have s1 := c.T.symm (κ0 a) (κ0 b)
    have s2 := c.T.symm a b
    have ha := hd a
    have hb := hd b
    linarith
  · intro x μ h
    rw [hl x μ h]
    congr 1
    funext a
    exact hθ μ a

end GlobalTheory.Poinc.LabUniq
