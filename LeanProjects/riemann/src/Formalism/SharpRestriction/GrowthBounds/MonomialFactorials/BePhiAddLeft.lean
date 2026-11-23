import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

def OrthLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
      (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
      n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestSymm : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
      ∀ v ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
        bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 u v =
          bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 v u

def RestLjjFin : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2).FG ∧
    ∃ W : Submodule ℚ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      FiniteDimensional ℚ_[X.p] W ∧ ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2, u ∈ W

section Lin

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem bePhi_add_left (j : Fin G.T.t → ℕ) (jp : ℕ) (u u' v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (u + u') v = bePhi p (r := r) G j jp u v + bePhi p (r := r) G j jp u' v := by
  have hs := bePhi_sum_left p (r := r) G j jp (Finset.univ : Finset (Fin 2)) ![u, u'] v
  simpa [Fin.sum_univ_two] using hs

end Lin

variable {C0 CE1 CE2 X}

theorem restOrth_of (CM : ℝ) (hp2 : X.p ≠ 2) (hO : OrthLat) (hS : RestSymm C0 CE1 CE2 X)
    (hF : RestLjjFin C0 CE1 CE2 X) : RestOrth C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  obtain ⟨hfg, W, hW, hLW⟩ := hF dl hdl aTop ha x hx
  exact hO X.p _ _ _ W _ hp2 hW hLW hfg
    (fun c u v => bePhi_smul_left _ _ _ _ c u v)
    (fun u u' v => bePhi_add_left _ _ _ _ u u' v)
    (hS dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
