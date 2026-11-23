import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameFormOfLeviCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialCombinationChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIndependentDegreePotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOnLineGramStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
  GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ChernWeilLine

theorem hasChernIntegral_ofDivisors (hG : GlobalTheory.Published.GoodChernNumbers) {F : Type} [Field F] (σ : F →+* ℂ) (Y : Var F)
    {ι : Type} [Fintype ι] (Δ : ι → Y.Dv) (H : Mat (fun _ : ι => 1) Y.Fn → CxPts Y.str σ → Mat (fun _ : ι => 1) ℂ)
    (hH : IsMetricOn (ofDivisors Δ) ⊤ H) (t : ι → ℝ) :
    HasChernIntegral (ofDivisors Δ) ⊤ H ((∑ i, C (t i) * X (i, 1)) ^ Y.dim)
      (Y.interPoly Δ ((∑ i, C (t i) * X i) ^ Y.dim)) := by
  have hGd : IsGood (ofDivisors Δ) ⊤ H := fun y hy => absurd mem_ptsIn_top hy
  have h := hG F σ Y Y ι (fun _ => 1) (ofDivisors Δ) (lineFlag (ofDivisors Δ)) (AlgHom.id F Y.Fn) (𝟙 Y.X)
    (fun x => Δ x.1) (refines_lineFlag _) (isGraded_ofDivisors Δ) ⊤ H hH hGd ((∑ i, C (t i) * X (i, 1)) ^ Y.dim)
  have e1 : chernRoots (fun _ : ι => 1) ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) * fibrePoint (fun _ : ι => 1) =
      (∑ i, C (t i) * X (⟨i, 0⟩ : Root fun _ : ι => 1)) ^ Y.dim := by
    simp [chernRoots, fibrePoint, esymm_one]
  have hexp {κ : Type} (f : ι → MvPolynomial κ ℝ) :
      (∑ i, C (t i) * f i) ^ Y.dim = ∑ s : Fin Y.dim → ι, C (∏ k, t (s k)) * ∏ k, f (s k) := by
    rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.prod_mul_distrib, map_prod]
  have e2 : (Y.interPoly fun x : Root (fun _ : ι => 1) => Δ x.1)
      ((∑ i, C (t i) * X (⟨i, 0⟩ : Root fun _ : ι => 1)) ^ Y.dim) = Y.interPoly Δ ((∑ i, C (t i) * X i) ^ Y.dim) := by
    rw [hexp (fun i => X (⟨i, 0⟩ : Root fun _ : ι => 1)), hexp (fun i => (X i : MvPolynomial ι ℝ)), map_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [C_mul', C_mul', map_smul, map_smul, Var.interPoly_prod, Var.interPoly_prod]
    rfl
  rwa [e1, e2] at h

theorem chernTopPart_sub_eq_mInt {F : Type} [Field F] [NumberField F] {Y : Var F} {M : Man Y.dim} (I : ManIs M Y)
    {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) (P : M.Pot)
    (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a))
    (hQ : ∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i))
    (hP : ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w,
      leviAt (M.A a) (P a) j y w = ∑ i, t i * leviAt (M.A a) (Q i) j y w) :
    (chernTopPart (ofDivisors Δ) (lineGram (cxSt F) fun i => m i (I.ε a))
        ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) 1).real (ptsIn Y.str (I.ε a) ⊤) -
      (chernTopPart (ofDivisors Δ) (lineGram (cxSt F) fun i => m i (I.ε a))
        ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (-1)).real (ptsIn Y.str (I.ε a) ⊤) =
      mInt (M.A a) (fun _ => P a) (fun _ => 1) := by
  have hpot : IsPotential (M.A a) (InhabCalc.combPot Q t 0) :=
    InhabCalc.isPotential_combPot _ Q (fun i => (hQ i).2) t 0 fun j => contDiffOn_const
  rw [GlobalTheory.SameForm.mInt_eq (fun _ => GlobalTheory.T.same_form_of_levi_combination (M.A a) (P a) Q t (fun i => (hQ i).2) hP)]
  have hm := GlobalTheory.T.isMetricOn_line_gram I m a Q hQ
  have htop : ptsIn Y.str (I.ε a) ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  rw [htop]
  exact GlobalTheory.T.chart_independent_degree_potential (M.A a) (I.pt a) (I.alg a) (fun _ => InhabCalc.combPot Q t 0) (fun _ => hpot) _
    (fun c c' y hy hy' => GlobalTheory.T.chern_top_chart_independent _ hm t c c' y hy hy' _ ((ofDivisors Δ).nonempty (under y)).choose_spec)
    (fun j c hc z hz => GlobalTheory.T.potential_combination_chart I m t a Q hQ j c hc z hz _ ((ofDivisors Δ).nonempty _).choose_spec)

theorem int_topPow_eq_interPoly : GlobalTheory.Published.GoodChernNumbers → ∀ {F : Type} [Field F] [NumberField F]
    {Y : GlobalTheory.ProjVar.Var F} {e : ℕ} {M : Man e} (I : ManIs M Y), Y.dim = e → ∀ {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, (GlobalTheory.TrueGeo.cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) (P : M.Pot), I.FormOf m t P →
    M.int (fun _ => P) (fun _ _ => 1) = Y.interPoly Δ ((∑ i, MvPolynomial.C (t i) * MvPolynomial.X i) ^ e) := by
  intro hG F _ _ Y e M I hdim ι _ Δ m t P hP
  subst hdim
  have key (a : Fin (M.n + 1)) :
      mInt (M.A a) (fun _ => P a) (fun _ => 1) = Y.interPoly Δ ((∑ i, C (t i) * X i) ^ Y.dim) := by
    obtain ⟨Q, hQ, hPQ⟩ := hP a
    rw [← chernTopPart_sub_eq_mInt I m t P a Q hQ hPQ]
    exact (hasChernIntegral_ofDivisors hG (I.ε a) Y Δ _ (GlobalTheory.T.isMetricOn_line_gram I m a Q hQ) t).2
  simp only [Man.int]
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    M.κ_eq]
  have : (M.n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

end GlobalTheory.ChernWeilLine
