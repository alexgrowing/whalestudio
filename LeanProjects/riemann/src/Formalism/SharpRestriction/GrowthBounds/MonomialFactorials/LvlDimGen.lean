import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiRenameMon
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiSmulRight
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SumFinrankLeOfIndep

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def preF (j : Fin G.T.t → ℕ) (jp : ℕ) : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp *
    (∏ i, X (Formalism.GM.M.scalZ N r G.T.t (Fin.castSucc i)) ^ G.T.z i) * X (Formalism.GM.M.scalZ N r G.T.t (Fin.last G.T.t)) ^ G.zPlus

theorem lvlDim_gen (j : Fin G.T.t → ℕ) (jp : ℕ) (hpre : preF (p := p) (r := r) G j jp ≠ 0)
    (hden : ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr)
    (hfd : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)))
    (hM : ∀ β ∈ xiMons (r := r) G (G.B - jp), ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0)
    (hxi : ∀ β ∈ xiMons (r := r) G (G.B - jp), (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t (G.B - jp)) :
    dimY p (r := r) G j jp * dXi r (G.B - jp) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) :=
    Formalism.CountingSumsFrames.pol_finiteDimensional (p := p) (G.lettersAt j jp)
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le (inf_le_left)
  let b := Module.finBasis ℚ_[p] Yq
  choose c hc0 hcY using fun a => hden (b a) (b a).2
  have hc0' : ∀ a, (c a : ℚ_[p]) ≠ 0 := fun a h => hc0 a (PadicInt.coe_eq_zero.1 h)
  let w : Fin (Module.finrank ℚ_[p] Yq) → ℚ_[p]ˣ := fun a => Units.mk0 _ (hc0' a)
  have hb0 : LinearIndependent ℚ_[p] (fun a => ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    b.linearIndependent.map' Yq.subtype (Submodule.ker_subtype _)
  have hb' : LinearIndependent ℚ_[p] (fun a => (c a : ℚ_[p]) • ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    hb0.units_smul w
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext (Fin.castSucc_injective _ h.1) h.2
  have hli := li_mul_left (preF (p := p) (r := r) G j jp) hpre _
    (li_rename_mon (Formalism.GM.M.chainEmb N r G.T.t) hinj (xiMons (r := r) G (G.B - jp)) hM _ hb')
  have hmem : ∀ q : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)),
      preF (p := p) (r := r) G j jp * (rename (Formalism.GM.M.chainEmb N r G.T.t)
        ((c q.2 : ℚ_[p]) • ((b q.2 : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) * monomial (q.1 : _ →₀ ℕ) 1) ∈
        G.gens p (r := r) j jp := by
    intro q
    refine ⟨_, hcY q.2, monomial (q.1 : _ →₀ ℕ) 1, hxi _ q.1.2, ?_⟩
    unfold preF
    ring
  let v : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)) →
      Submodule.span ℚ_[p] (G.gens p (r := r) j jp) := fun q => ⟨_, Submodule.subset_span (hmem q)⟩
  have hv : LinearIndependent ℚ_[p] v := LinearIndependent.of_comp (Submodule.subtype _) hli
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe] at hcard
  rw [card_xiMons_eq] at hcard
  unfold dimY
  rw [mul_comm]
  exact hcard

end Gen

end Formalism.MainNotions.G.SymmetricFormBlocks

end
