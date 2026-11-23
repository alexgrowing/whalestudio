import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def phisB (j : Fin G.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (List.finRange G.T.t).foldr (fun i acc =>
    Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
      (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i) ∘ₗ acc) LinearMap.id

theorem phiAll_eq (j : Fin G.T.t → ℕ) (jp : ℕ) :
    G.phiAll p (r := r) j jp =
      Formalism.GM.tiePhi (fun c => Sum.inl (Fin.castSucc G.uPos, c)) (fun c => Formalism.GM.M.xiVar N r G.T.t c)
        (G.LL.deg G.uPos - jp) (G.B - jp) G.zPlus ∘ₗ phisB p (r := r) G j jp := rfl

def bePhi (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) : ℚ_[p] :=
  Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p])

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusA (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
              (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ ≤
      bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ * dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2.2)

def RestRankL : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤ rL C0 CE1 CE2 X aTop x.1 x.2

def RestPlusB (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (∑ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (X.winA.card : ℝ) *
        ((Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
            (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) +
          5 / X.L.Y * (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ))

variable {C0 CE1 CE2 X}

theorem restPlus_of (CM : ℝ) (hY : 0 < X.L.Y) (hA : RestPlusA C0 CE1 CE2 X CM) (hR : RestRankL C0 CE1 CE2 X)
    (hB : RestPlusB C0 CE1 CE2 X CM) : RestPlus C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  have hA' := hA dl hdl aTop haTop x hx
  have hR' := hR dl hdl aTop haTop x hx
  refine (hB dl hdl aTop haTop x hx).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (by exact_mod_cast hA') ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hR') (div_nonneg (by norm_num) hY.le)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
