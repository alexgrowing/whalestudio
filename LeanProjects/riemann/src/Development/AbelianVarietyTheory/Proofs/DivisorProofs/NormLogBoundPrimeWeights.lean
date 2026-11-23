import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorsEffectiveFiniteDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorIntegralSubschemeDimensionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.VertBound

theorem abs_num_le : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ num : Form (Cl V.p) D, IsArForm D num → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∀ N : Fin D → HermLB V.p, (∀ j, ∀ l ∈ S, NefOver (N j) l) → |num (Fin.cons (cl M) fun j => cl (N j))| ≤ (∑ l ∈ S, a l * Real.log l) * num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) := by
  intro hP F _ _ Y V D hD num hn M lg hM S a hS hb N hN
  have hX : IsArithVar V.p D := hD ▸ V.ar
  haveI : IsLocallyNoetherian V.X := hX.isLocallyNoetherian
  haveI : IsNoetherian V.X := hX.isNoetherian
  obtain ⟨r, hr, h1, hmult⟩ := GlobalTheory.T.local_height_bounded_by_prime_weights F Y V M lg hM S a hS hb
  have hU := fun l (hl : l.Prime) => GlobalTheory.T.prime_divisors_effective_finite_disjoint _ V.X V.p D hX l hl
  have key : ∀ (l : ℕ) (z : V.X), ∃ c : ℝ, (0 < Scheme.ord ((l : V.X.functionField)) z → l.Prime →
      ∃ (_ : Fact l.Prime) (Z : Scheme.{0}) (i : Z ⟶ V.X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
        (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧
          c = interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i)) ∧ (l ∈ S → 0 ≤ c) := by
    intro l z
    by_cases h : 0 < Scheme.ord ((l : V.X.functionField)) z ∧ l.Prime
    · haveI : Fact l.Prime := ⟨h.2⟩
      obtain ⟨Z, i, hi, hZ, hA, e1, e2⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ V.X V.p D hX l z h.1
      refine ⟨_, fun _ _ => ⟨⟨h.2⟩, Z, i, hi, hZ, hA, e1, e2, rfl⟩, fun hl => ?_⟩
      exact_mod_cast GlobalTheory.T.nef_intersection_number_nonneg_subscheme hP _ V.X V.p D hX l Z i e2 N (fun j => hN j l hl)
    · exact ⟨0, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h, fun _ => le_rfl⟩
  choose dl hdl hdl0 using key
  have key2 : ∀ z, ∃ l : ℕ, (M.div hr).mult z ≠ 0 → l ∈ S ∧ 0 < Scheme.ord ((l : V.X.functionField)) z := by
    intro z
    by_cases hz : (M.div hr).mult z = 0
    · exact ⟨0, fun h => absurd hz h⟩
    · have : ∃ l ∈ S, 0 < Scheme.ord ((l : V.X.functionField)) z := by
        by_contra hcon
        push_neg at hcon
        have hs : ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ) = 0 :=
          Finset.sum_eq_zero fun l hl => by
            have := le_antisymm (hcon l hl) ((hU l (hS l hl).1).1 z)
            simp [this]
        have := hmult z
        rw [hs] at this
        exact hz (by exact_mod_cast abs_nonpos_iff.1 this)
      obtain ⟨l, hl, h⟩ := this
      exact ⟨l, fun _ => ⟨hl, h⟩⟩
  choose ℓ hℓ using key2
  have hB := GlobalTheory.T.height_of_rational_section_via_divisor hP _ V.X V.p D hX num hn M r hr h1 N ℓ (fun z => dl (ℓ z) z) fun z hz => by
    obtain ⟨hl, h⟩ := hℓ z hz
    exact hdl (ℓ z) z h (hS _ hl).1
  have hD' : ∀ l ∈ S, ∑ᶠ z, (Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z =
      num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) := fun l hl => by
    haveI : Fact l.Prime := ⟨(hS l hl).1⟩
    refine GlobalTheory.T.prime_divisor_integral_subscheme_dimension hP _ V.X V.p D hX num hn N l (dl l) fun z hz => ?_
    obtain ⟨_, Z, i, hi, hZ, hA, e1, e2, e3⟩ :=
      hdl l z (lt_of_le_of_ne ((hU l (hS l hl).1).1 z) (Ne.symm hz)) (hS l hl).1
    exact ⟨Z, i, hi, hZ, hA, e1, e2, e3⟩
  have hfin : (Function.support (M.div hr).mult).Finite := (M.div hr).finite_support_mult
  let T : Finset V.X := hfin.toFinset ∪ S.biUnion fun l => if h : l.Prime then (hU l h).2.1.toFinset else ∅
  have hsub1 : Function.support (fun z => ((M.div hr).mult z : ℝ) * dl (ℓ z) z * Real.log (ℓ z)) ⊆ T := by
    intro z hz
    refine Finset.mem_union_left _ (hfin.mem_toFinset.2 fun h0 => hz ?_)
    simp [h0]
  have hsub2 : ∀ l ∈ S, Function.support (fun z => (Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z) ⊆ T := by
    intro l hl z hz
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, hl, ?_⟩)
    rw [dif_pos (hS l hl).1]
    refine (hU l (hS l hl).1).2.1.mem_toFinset.2 fun h0 => hz ?_
    simp [h0]
  have hnn : ∀ z, ∀ l ∈ S, 0 ≤ a l * Real.log l * ((Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z) :=
    fun z l hl => mul_nonneg (mul_nonneg (hS l hl).2 (Real.log_natCast_nonneg l))
      (mul_nonneg (by exact_mod_cast (hU l (hS l hl).1).1 z) (hdl0 l z hl))
  have hterm : ∀ z ∈ T, |((M.div hr).mult z : ℝ) * dl (ℓ z) z * Real.log (ℓ z)| ≤
      ∑ l ∈ S, a l * Real.log l * ((Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z) := by
    intro z _
    by_cases hz : (M.div hr).mult z = 0
    · rw [hz, Int.cast_zero, zero_mul, zero_mul, abs_zero]
      exact Finset.sum_nonneg fun l hl => hnn z l hl
    obtain ⟨hl0, hpos⟩ := hℓ z hz
    have hsum : ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ) =
        a (ℓ z) * (Scheme.ord (((ℓ z : ℕ) : V.X.functionField)) z : ℝ) :=
      Finset.sum_eq_single_of_mem _ hl0 fun l hl hne => by
        rcases (hU (ℓ z) (hS _ hl0).1).2.2 l (hS l hl).1 (Ne.symm hne) z with h | h
        · exact absurd h hpos.ne'
        · simp [h]
    have hd0 := hdl0 (ℓ z) z hl0
    have hlog := Real.log_natCast_nonneg (ℓ z)
    calc |((M.div hr).mult z : ℝ) * dl (ℓ z) z * Real.log (ℓ z)|
        = |((M.div hr).mult z : ℝ)| * (dl (ℓ z) z * Real.log (ℓ z)) := by
          rw [mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg hd0 hlog)]
      _ ≤ (a (ℓ z) * (Scheme.ord (((ℓ z : ℕ) : V.X.functionField)) z : ℝ)) * (dl (ℓ z) z * Real.log (ℓ z)) :=
          mul_le_mul_of_nonneg_right (hsum ▸ hmult z) (mul_nonneg hd0 hlog)
      _ = a (ℓ z) * Real.log (ℓ z) * ((Scheme.ord (((ℓ z : ℕ) : V.X.functionField)) z : ℝ) * dl (ℓ z) z) := by ring
      _ ≤ ∑ l ∈ S, a l * Real.log l * ((Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z) :=
          Finset.single_le_sum (f := fun l => a l * Real.log l * ((Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z))
            (fun l hl => hnn z l hl) hl0
  rw [hB, finsum_eq_sum_of_support_subset _ hsub1]
  calc |∑ z ∈ T, ((M.div hr).mult z : ℝ) * dl (ℓ z) z * Real.log (ℓ z)|
      ≤ ∑ z ∈ T, |((M.div hr).mult z : ℝ) * dl (ℓ z) z * Real.log (ℓ z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ T, ∑ l ∈ S, a l * Real.log l * ((Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z) :=
        Finset.sum_le_sum hterm
    _ = ∑ l ∈ S, a l * Real.log l * ∑ z ∈ T, (Scheme.ord ((l : V.X.functionField)) z : ℝ) * dl l z := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ l ∈ S, a l * Real.log l * num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) :=
        Finset.sum_congr rfl fun l hl => by rw [← hD' l hl, finsum_eq_sum_of_support_subset _ (hsub2 l hl)]
    _ = (∑ l ∈ S, a l * Real.log l) * num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) := by
        rw [Finset.sum_mul]

end GlobalTheory.VertBound

end
