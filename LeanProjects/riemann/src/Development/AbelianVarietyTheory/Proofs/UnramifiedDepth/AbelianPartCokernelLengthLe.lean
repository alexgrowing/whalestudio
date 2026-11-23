import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.LenEx
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDimStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem place_mul_bar {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE] (w : Place p OE)
    (hinv : ∀ x, sig p OE (sig p OE x) = x) : w.e * w.bar = 0 := by
  have hb : w.bar * w.bar = w.bar := by
    unfold Place.bar
    rw [← map_mul, w.idem]
  rcases w.prim (w.e * w.bar) (by rw [_root_.mul_mul_mul_comm, w.idem, hb])
    (by rw [mul_right_comm, w.idem]) with h | h
  · exact h
  · exfalso
    apply w.split
    have h2 := congrArg (sig p OE) h
    unfold Place.bar at h h2
    rw [map_mul, hinv, mul_comm, h] at h2
    exact h2.symm

theorem abelian_coker_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H hP hPL w t rm hrm
  obtain ⟨-, -, hstar⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hsig : ∀ x, sig p OE x = sigE p OE x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hinv : ∀ x, sig p OE (sig p OE x) = x := fun x => by rw [hsig, hsig, hS.invol]
  have h0 : w.e * w.bar = 0 := place_mul_bar w hinv
  have he := w.idem
  have hbar : sigE p OE w.e = w.bar := (hsig _).symm
  have hbar' : sigE p OE w.bar = w.e := by rw [← hbar, hS.invol]
  have hb : w.bar * w.bar = w.bar := by rw [← hbar, ← map_mul, w.idem]
  let c : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hcc : ∀ τ : OE →+* O, (τ.comp c).comp c = τ := fun τ => by
    ext a
    simp [c]
  let s : Emb (O := O) w.e ≃ Emb (O := O) w.bar :=
    { toFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.bar).1, hbar', this]⟩
      invFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.e).1, hbar, this]⟩
      left_inv := fun τ => Subtype.ext (hcc τ.1)
      right_inv := fun τ => Subtype.ext (hcc τ.1) }
  have hd := GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim p C v O hv OE g H.ρL w.bar hb w.n (t.trans s)
  obtain ⟨cw, hcw⟩ : ∃ x, HasLen v O (htCoker H w.e w.bar) x :=
    lenEx C v O hv g H.Ht (H.ρL w.e) ((H.ρ w.bar).map (algebraMap ℤ_[p] O))
  refine ⟨cw, hcw, ?_⟩
  have hav := lengthDegree_abelianVariety p g C v O _ _ cp hS H 3 ![w.e, w.bar, 1 - w.e - w.bar] (Equiv.swap 0 1)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
        | exact he
        | exact hb
        | linear_combination h0
        | linear_combination -he - h0
        | linear_combination -hb - h0
        | linear_combination he + hb + 2 * h0)
    (by
      intro i
      fin_cases i
      · simpa using hbar
      · simpa using hbar'
      · have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        simp only [Fin.reduceFinMk, this, Matrix.cons_val, map_sub, map_one, hbar, hbar']
        ring)
    (by simp [Fin.sum_univ_three, hP]) (by simp [hP])
    (by simp [Fin.sum_univ_three, hPL]) (by simp [hPL])
    0 (by decide) _ hd cw hcw
  refine le_trans ?_ hav
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · refine div_le_div_of_nonneg_right ?_ (by linarith)
    have := Finset.sum_le_card_nsmul Finset.univ _ rm (fun j _ => hrm _ ((t.trans s) j).2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this

end GlobalTheory.ChF
