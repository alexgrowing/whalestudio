import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteHomogeneousGeneratorsGradedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqSumAevalBoundedIntCoeffAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GoodH

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_H_of_eq (P : Pair p) {a a' b b' : ℤ} {f : X.functionField} (ha : a = a') (hb : b = b')
    (h : f ∈ P.H a b) : f ∈ P.H a' b' := by
  subst ha hb; exact h

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [Pair.nu]; positivity

theorem mono_mem {D : ℕ} (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (a b : ℤ) (g : X.functionField) (hg : g ∈ P.H a b) (α : Fin (D + 1) → ℕ) (S : Finset (Fin (D + 1))) :
    (∏ l ∈ S, x l ^ α l) * g ∈ P.H ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b ∧
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b σ y ((∏ l ∈ S, x l ^ α l) * g) =
        (∏ l ∈ S, P.nu e 0 σ y (x l) ^ α l) * P.nu a b σ y g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, Nat.cast_zero, mul_zero, zero_add]
    exact ⟨hg, fun _ _ => trivial⟩
  | @insert j S hj ih =>
    obtain ⟨hp1, hp2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (e : ℤ) 0 (x j) (hx j) (α j)
    obtain ⟨hm1, hm2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ hp1 ih.1
    have ea : ((α j : ℕ) : ℤ) * (e : ℤ) + ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) =
        (e : ℤ) * ((∑ l ∈ insert j S, α l : ℕ) : ℤ) + a := by
      rw [Finset.sum_insert hj]; push_cast; ring
    have eb : ((α j : ℕ) : ℤ) * 0 + b = b := by ring
    rw [ea, eb] at hm1 hm2
    have ep : (∏ l ∈ insert j S, x l ^ α l) * g = x j ^ α j * ((∏ l ∈ S, x l ^ α l) * g) := by
      rw [Finset.prod_insert hj, mul_assoc]
    rw [ep]
    refine ⟨hm1, fun σ y => ?_⟩
    rw [hm2, hp2, ih.2, Finset.prod_insert hj, mul_assoc]

end GlobalTheory.HSAmp.GoodH

namespace GlobalTheory.HSAmp.GoodH

theorem goodFam_H : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → GoodFam P D (gdeg P.L D / D.factorial) fun m => P.H m 1 := by
  intro hAr k _ X _ p D hX P hL
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hL
  have he : 0 < e := hx.pos

  have hup : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, (P.H ((e * q + s : ℕ) : ℤ) 1).FG ∧
      Module.finrank ℤ (P.H ((e * q + s : ℕ) : ℤ) 1) ≤
        Module.finrank (ratF x) X.functionField * (q + c + D).choose D := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    refine ⟨c, fun q => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    exact ⟨(h q).1, (h q).2.1⟩

  have hlow : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, Module.finrank (ratF x) X.functionField * (q + D).choose D ≤
      Module.finrank ℤ (P.H ((e * (q + c) + s : ℕ) : ℤ) 1) := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    obtain ⟨c', hc'⟩ := hup s
    refine ⟨c, fun q => ?_⟩
    obtain ⟨v, hv, hli⟩ := (h q).1
    have e1 : ((e * (q + c) + s : ℕ) : ℤ) = (e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ) := by push_cast; ring
    have hfg := (hc' (q + c)).1
    rw [e1] at hfg ⊢
    haveI : Module.Finite ℤ (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1) :=
      Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
    let w : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) →
        P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1 := fun i => ⟨v i, hv i⟩
    have hw : LinearIndependent ℤ w :=
      LinearIndependent.of_comp (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1).subtype.toIntLinearMap hli
    simpa using hw.fintype_card_le_finrank
  have hrank := GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e (Module.finrank (ratF x) X.functionField)
    (fun m => Module.finrank ℤ (P.H (m : ℤ) 1)) he (fun s _ => by
      obtain ⟨c, hc⟩ := hlow s
      obtain ⟨c', hc'⟩ := hup s
      exact ⟨c, c', fun q => ⟨hc q, (hc' q).2⟩⟩)
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hAr k X p D hX P hL e x hx
  have hg : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) = gdeg P.L D / D.factorial := by
    have : (e : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast he.ne')
    rw [hdeg]
    exact mul_div_mul_left _ _ this

  have hkey : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ e * q + s →
      P.H ((e * q + s : ℕ) : ℤ) 1 ≤
        AddSubgroup.closure (ballIn P (P.H ((e * q + s : ℕ) : ℤ) 1) ((e * q + s : ℕ) : ℤ) 1 (C ^ (e * q + s))) := by
    intro s
    classical
    obtain ⟨c, w, Cr, -, hrep⟩ := GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample k X p D hX P hL e x hx (s : ℤ) 1
    let Λ : ℕ → AddSubgroup X.functionField := fun q => P.H ((e : ℤ) * (q : ℤ) + (s : ℤ)) 1
    have hmul : ∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1) := by
      intro q l f hf
      have h := (GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hx.mem l) hf).1
      show x l * f ∈ P.H _ 1
      exact mem_H_of_eq P (by push_cast; ring) (by ring) h
    have hrepr : ∀ q, ∀ f ∈ Λ q, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ,
        (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i := by
      intro q f hf
      obtain ⟨T, h1, h2, -⟩ := hrep q f hf
      exact ⟨T, h1, h2⟩
    obtain ⟨G, hG, hcl⟩ := GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup X.functionField D c x _ w Λ hmul hrepr
    have hb : ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, P.nu a b σ y f ≤ C := by
      intro a b f hf
      obtain ⟨C, hC⟩ := ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b).2 f hf).2
      exact ⟨|C|, abs_nonneg _, fun σ y => (hC σ y).trans (le_abs_self _)⟩
    choose Cx hCx0 hCx using fun l => hb _ _ _ (hx.mem l)
    have hbG : ∀ g : ℕ × X.functionField, ∃ C : ℝ, 0 ≤ C ∧
        (g ∈ G → ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ C) := by
      intro g
      by_cases hg : g ∈ G
      · obtain ⟨C, hC0, hC⟩ := hb _ _ _ (hG g hg)
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hg⟩
    choose Cg hCg0 hCg using hbG
    have hC1 : 1 ≤ 1 + ∑ l, Cx l := le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hCx0 l)
    have hC2 : 1 ≤ 1 + ∑ g ∈ G, Cg g := le_add_of_nonneg_right (Finset.sum_nonneg fun g _ => hCg0 g)
    have hxl : ∀ l σ y, P.nu e 0 σ y (x l) ≤ 1 + ∑ l, Cx l := fun l σ y => (hCx l σ y).trans (by
      have := Finset.single_le_sum (fun j _ => hCx0 j) (Finset.mem_univ l); linarith)
    have hgl : ∀ g ∈ G, ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ 1 + ∑ g ∈ G, Cg g :=
      fun g hg σ y => (hCg g hg σ y).trans (by
        have := Finset.single_le_sum (fun j _ => hCg0 j) hg; linarith)
    refine ⟨(1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g), one_le_mul_of_one_le_of_one_le hC1 hC2, fun q hq => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    refine (hcl q).trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨g, hg, α, hα, rfl⟩
    obtain ⟨h1, h2⟩ := mono_mem P e x hx.mem ((e : ℤ) * (g.1 : ℤ) + s) 1 g.2 (hG g hg) α Finset.univ
    have ea : (e : ℤ) * ((∑ l, α l : ℕ) : ℤ) + ((e : ℤ) * (g.1 : ℤ) + s) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by
      rw [← hα]; push_cast; ring
    rw [ea] at h1 h2
    refine ⟨h1, fun σ y => ?_⟩
    rw [h2]
    have hnu0 : ∀ l, 0 ≤ P.nu e 0 σ y (x l) := fun l => nu_nonneg P _ _ σ y _
    have hqe : q ≤ e * q := Nat.le_mul_of_pos_left q he
    have hsum : ∑ l, α l ≤ e * q + s := by omega
    calc (∏ l, P.nu e 0 σ y (x l) ^ α l) * P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2
        ≤ (∏ l, (1 + ∑ l, Cx l) ^ α l) * (1 + ∑ g ∈ G, Cg g) :=
          mul_le_mul (Finset.prod_le_prod (fun l _ => pow_nonneg (hnu0 l) _)
            fun l _ => pow_le_pow_left₀ (hnu0 l) (hxl l σ y) _) (hgl g hg σ y) (nu_nonneg P _ _ σ y _)
            (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)
      _ = (1 + ∑ l, Cx l) ^ (∑ l, α l) * (1 + ∑ g ∈ G, Cg g) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (1 + ∑ l, Cx l) ^ (e * q + s) * (1 + ∑ g ∈ G, Cg g) ^ (e * q + s) :=
          mul_le_mul (pow_le_pow_right₀ hC1 hsum) (le_self_pow₀ hC2 (by omega)) (by linarith)
            (pow_nonneg (by linarith) _)
      _ = ((1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g)) ^ (e * q + s) := (mul_pow _ _ _).symm
  choose Cs hCs1 hCs using hkey
  refine ⟨fun m => le_rfl, fun m => ?_, ⟨∑ s ∈ Finset.range e, Cs s, ?_, fun m hm => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hup (m % e)
    have h := (hc (m / e)).1
    rw [Nat.div_add_mod] at h
    exact h
  · exact (hCs1 0).trans (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 he))
  · have hs := Nat.mod_lt m he
    have h := hCs (m % e) (m / e) (by rw [Nat.div_add_mod]; exact hm)
    rw [Nat.div_add_mod] at h
    have hle : Cs (m % e) ≤ ∑ s ∈ Finset.range e, Cs s :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 hs)
    refine h.trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨hf, hf'⟩
    exact ⟨hf, fun σ y => (hf' σ y).trans (pow_le_pow_left₀ (zero_le_one.trans (hCs1 _)) hle _)⟩
  · rw [← hg]
    exact hrank

end GlobalTheory.HSAmp.GoodH
