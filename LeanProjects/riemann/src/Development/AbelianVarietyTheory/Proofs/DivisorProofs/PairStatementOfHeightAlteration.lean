import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverWithInducedNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedByBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalNumberSumOverPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleFamilyValuationPlaces

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx

namespace GlobalTheory.PairTerm

open Classical in

theorem vert_read (hC : Hypotheses2) {F : Type} [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) {ι : Type}
    [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ i, (A i).Induced M (L i) m 0) (hΨ : haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) (p : ℕ) [hp : Fact p.Prime]
    (i₀ i₁ : ι) (e : A i₁ = { A i₀ with lg := (A i₁).lg }) (b : ℝ) (hb : 0 ≤ b)
    (hlg : ∀ v e y, |(A i₀).lg v e y - (A i₁).lg v e y| ≤
      (if resP v = p then b else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) (ν : Fin Y.dim → ι) :
    ∃ (V : Cover Y) (L' : ι → HermLB V.p) (r : ((L' i₀).tens (L' i₁).dual).B.ι → V.X.functionFieldˣ)
      (hr : IsRatSec ((L' i₀).tens (L' i₁).dual).B r),
      (∀ i, Norms V (L' i) (fun x => genAt (A i).D x ^ (m : ℕ)) (fun σ y => (m : ℕ) * lnAdl (A i) σ y)
        (fun v e y => (m : ℕ) * (A i).lg v e y)) ∧
      RatNorms V ((L' i₀).tens (L' i₁).dual) r (fun v e y => (m : ℕ) * ((A i₀).lg v e y - (A i₁).lg v e y)) ∧
      (V.deg : ℝ) * Ψ ((X i₀ - X i₁) * ∏ j, X (ν j)) =
        Real.log p * ∑ᶠ z, (haveI := V.ar.isLocallyNoetherian; ((((L' i₀).tens (L' i₁).dual).div hr).mult z : ℝ)) *
          vertNum p V Y.dim (fun j => L' (ν j)) z := by
  obtain ⟨V, L', hL', hΦ⟩ := GlobalTheory.T.exists_cover_with_induced_norms hC.p4 F Y M ι A L m Ψ hI hΨ
  haveI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
  haveI : IsNoetherian V.X := V.ar.isNoetherian
  have hM := norms_div e (hL' i₀) (hL' i₁)
  obtain ⟨r, hr, h1, hmult, hrn⟩ := GlobalTheory.T.height_bounded_by_bad_primes F Y V _ _ hM {p} (fun _ => (m : ℕ) * b) (by simpa using ⟨hp.out, by positivity⟩)
    (fun v ε y => by
      simp only [Finset.mem_singleton]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine (mul_le_mul_of_nonneg_left (hlg v ε y) (Nat.cast_nonneg _)).trans_eq ?_
      split_ifs <;> ring)
  refine ⟨V, L', r, hr, hL', hrn, ?_⟩
  obtain ⟨num, hn, -⟩ := GlobalTheory.T.arith_intersection_form_exists hC.p4 _ _ V.p _ V.ar
  obtain ⟨rt, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hC.p4 _ _ V.p _ V.ar num hn
  set N : Fin Y.dim → HermLB V.p := fun j => L' (ν j) with hNdef
  have hd : ∀ z, (((L' i₀).tens (L' i₁).dual).div hr).mult z ≠ 0 → ∃ (_ : Fact ((fun _ => p) z).Prime) (Z : Scheme.{0})
      (i : Z ⟶ V.X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod ((fun _ => p) z)) Γ(Z, ⊤)),
      i (genericPoint Z) = z ∧ topologicalKrullDim Z = Y.dim ∧
        (fun z => vertNum p V Y.dim N z) z = interNum (ZMod ((fun _ => p) z)) (structureModule Z)
          (fun j => (N j).B.pull i) := by
    intro z hz
    have hpos : 0 < Scheme.ord ((p : V.X.functionField)) z := by
      refine lt_of_le_of_ne ((GlobalTheory.T.prime_divisors_effective_finite_disjoint _ V.X V.p _ V.ar p hp.out).1 z) fun e => hz ?_
      have := hmult z
      rw [Finset.sum_singleton, ← e, Int.cast_zero, mul_zero] at this
      exact_mod_cast abs_nonpos_iff.1 this
    obtain ⟨Z, i, hi, hZ, hA, e₁, e₂⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ V.X V.p _ V.ar p z hpos
    have hne : Nonempty (VertSub p V.X Y.dim z) := ⟨⟨Z, i, hi, hZ, hA, e₁, e₂⟩⟩
    exact ⟨hp, hne.some.Z, hne.some.i, hne.some.imm, hne.some.int, hne.some.alg, hne.some.gen, hne.some.dim,
      by simp only [vertNum, dif_pos hne]⟩
  have key := GlobalTheory.T.height_of_rational_section_via_divisor hC _ V.X V.p _ V.ar num hn _ r hr h1 N (fun _ => p) (fun z => vertNum p V Y.dim N z) hd
  have hfin : (Function.support fun z => ((((L' i₀).tens (L' i₁).dual).div hr).mult z : ℝ) *
      vertNum p V Y.dim N z).Finite :=
    (((L' i₀).tens (L' i₁).dual).div hr).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have hE : (V.deg : ℝ) * Ψ ((X i₀ - X i₁) * ∏ j, X (ν j)) =
      num (Fin.cons (cl ((L' i₀).tens (L' i₁).dual)) fun j => cl (N j)) := by
    change ((V.deg : ℝ) • Ψ) _ = _
    generalize (V.deg : ℝ) • Ψ = Φ at hΦ
    have := hn ι L' Φ hΦ (Fin.cons (Pi.single i₀ 1 - Pi.single i₁ 1) fun j => Pi.single (ν j) 1)
    have e₂ : lin (Pi.single i₀ 1 - Pi.single i₁ 1 : ι → ℝ) = X i₀ - X i₁ := by
      rw [← TrivFlag.lin_single, ← TrivFlag.lin_single]
      simp only [lin, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Fin.prod_univ_succ, Fin.cons_zero, e₂] at this
    simp only [Fin.cons_succ, TrivFlag.lin_single] at this
    rw [this]
    refine map_congr_rad num fun j => Fin.cases ?_ (fun j => ?_) j
    · have h₁ := neg_mem (add_mem (rt (L' i₀) (L' i₁).dual) (rd (L' i₁)))
      convert h₁ using 1
      simp only [Fin.cons_zero, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      abel
    · simp [Pi.single_apply, hNdef]
  rw [hE, key, ← finsum_mul, mul_comm]

end GlobalTheory.PairTerm

namespace GlobalTheory.PairTerm

open Classical in

theorem pairSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.PairTerm.PairSt := by
  intro h2 hH hRA D O hO p _ W hW hWv z Sx R hR l ν
  obtain ⟨x, P, h⟩ := hO
  rw [h.hm_eq]
  let w := wOf (ArIn.ind Sx) p R l ν
  have hw : ∀ (i : Bool ⊕ Fin (dimFl D.what₂.Tau O.N)), ∀ a ∈ (w i).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
    have ha (b : Bool) : {q | Function.update (ArIn.ind Sx) p b q = true}.Finite :=
      (insert p Sx).finite_toSet.subset fun q hq => by
        by_cases e : q = p
        · simp [e]
        · simpa [ArIn.ind, e] using hq
    intro i a hai
    rcases i with b | i
    · obtain ⟨e₁, e₂⟩ := mem_support_lnSym hai
      exact ⟨e₁ ▸ ha _, e₂⟩
    · obtain ⟨e₁, e₂⟩ := mem_support_lnSym hai
      exact ⟨e₁ ▸ ha _, e₂⟩
  choose M L m Ψ hI hΨ hnum using fun c =>
    (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ O.s x O.Φ c R hR).2 (Bool ⊕ Fin (dimFl D.what₂.Tau O.N)) w hw
  have hb : 0 ≤ 1 / ((p : ℝ) - 1) + vDiff D.host.E p := by
    have h₁ : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have h₂ : 0 ≤ vDiff D.host.E p := by unfold vDiff; positivity
    have h₃ : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  choose V L' r hr hN hrn hread using fun c => vert_read h2 (O.Φ.C c).Y (M c)
    (fun i => adlOf (O.Φ.C c) (metsOf x O.Φ c) (w i)) (L c) (m c) (Ψ c) (hI c) (hΨ c) p (.inl false) (.inl true)
    (adlOf_lnSym_eq (O.Φ.C c) (metsOf x O.Φ c) _ _ (some R) l) _ hb
    (fun v ε y => abs_lgOf_lnSym_update_sub_le (O.Φ.C c) (ArIn.ind Sx) p (some R) l v ε y)
    (fun j => .inr (Fin.cast (O.dim_eq c) j))
  have hμ (b : Bool) (c : O.s.Comp) :
      (Multiset.map w (Sum.inl b ::ₘ Multiset.map Sum.inr (Finset.univ : Finset (Fin (dimFl D.what₂.Tau O.N))).val) :
        Multiset ((arIn O.s O.Φ (metsOf x O.Φ)).A c)) =
      (lnSym (Function.update (ArIn.ind Sx) p b) (some R) l ::ₘ
        Multiset.map (fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2) Finset.univ.val :
          Multiset ((arIn O.s O.Φ (metsOf x O.Φ)).A c)) := by
    erw [Multiset.map_cons, Multiset.map_map]
    rfl
  have hcard (b : Bool) (c : O.s.Comp) :
      Multiset.card (Sum.inl b ::ₘ Finset.univ.val.map Sum.inr : Multiset (Bool ⊕ Fin (dimFl D.what₂.Tau O.N))) = (O.Φ.C c).Y.dim + 1 := by
    simp [O.dim_eq c]
  have hprod (b : Bool) :
      ((Sum.inl b ::ₘ Finset.univ.val.map Sum.inr : Multiset (Bool ⊕ Fin (dimFl D.what₂.Tau O.N))).map MvPolynomial.X).prod =
        (X (Sum.inl b) : MvPolynomial (Bool ⊕ Fin (dimFl D.what₂.Tau O.N)) ℝ) * ∏ i : Fin (dimFl D.what₂.Tau O.N), X (Sum.inr i) := by
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_map]
    rfl
  have hc : ∀ c, (arIn O.s O.Φ (metsOf x O.Φ)).num c (lnSym (Function.update (ArIn.ind Sx) p false) (some R) l ::ₘ
        Finset.univ.val.map fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2) -
      (arIn O.s O.Φ (metsOf x O.Φ)).num c (lnSym (Function.update (ArIn.ind Sx) p true) (some R) l ::ₘ
        Finset.univ.val.map fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2) =
      Real.log p * ((∑ᶠ y, (haveI := (V c).ar.isLocallyNoetherian;
          ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).mult y : ℝ)) *
            vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (.inr j)) y) /
        (((V c).deg : ℝ) * ((m c : ℕ) : ℝ) ^ ((dimFl D.what₂.Tau O.N) + 1) * (Module.finrank ℚ D.what₂.LL : ℝ))) := by
    intro c
    rw [← hμ false c, ← hμ true c]
    rw [hnum c _ (hcard false c), hnum c _ (hcard true c), hprod, hprod, ← sub_div, ← map_sub, ← sub_mul]
    have e₁ := hread c
    have hP : ∏ j : Fin (O.Φ.C c).Y.dim, (X (Sum.inr (Fin.cast (O.dim_eq c) j)) : MvPolynomial (Bool ⊕ Fin (dimFl D.what₂.Tau O.N)) ℝ) =
        ∏ i : Fin (dimFl D.what₂.Tau O.N), X (Sum.inr i) := Fin.prod_congr' (fun i => (X (Sum.inr i) : MvPolynomial (Bool ⊕ Fin (dimFl D.what₂.Tau O.N)) ℝ)) (O.dim_eq c)
    have hv : ∀ y, vertNum p (V c) _ (fun j => L' c (Sum.inr (Fin.cast (O.dim_eq c) j))) y =
        vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (Sum.inr j)) y :=
      fun y => vertNum_cast p (V c) (O.dim_eq c) (fun j => L' c (Sum.inr j)) y
    simp only [hP, hv] at e₁
    have hdeg : (0 : ℝ) < (V c).deg := Nat.cast_pos.2 (V c).deg_pos
    have key : Ψ c ((X (Sum.inl false) - X (Sum.inl true)) * ∏ i : Fin (dimFl D.what₂.Tau O.N), X (Sum.inr i)) =
        Real.log p * (∑ᶠ y, (haveI := (V c).ar.isLocallyNoetherian;
          ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).mult y : ℝ)) *
            vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (.inr j)) y) / (V c).deg := by
      rw [eq_div_iff hdeg.ne', mul_comm]
      exact e₁
    rw [key]
    simp only [O.dim_eq c]
    ring
  have hG : ∀ c, (∑ᶠ y, (haveI := (V c).ar.isLocallyNoetherian;
          ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).mult y : ℝ)) *
            vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (.inr j)) y) = (letI := Formalism.L2.Geo.finPl D p;
        ∑ la : Formalism.L2.Geo.PlL D p, ∑ᶠ y, if LiesOverPl (V c) la.1 y then (haveI := (V c).ar.isLocallyNoetherian;
          ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).mult y : ℝ)) *
            vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (.inr j)) y else 0) := by
    intro c
    haveI := (V c).ar.isLocallyNoetherian
    haveI : IsNoetherian (V c).X := (V c).ar.isNoetherian
    exact GlobalTheory.T.vertical_number_sum_over_places D p (O.var c) (V c) (dimFl D.what₂.Tau O.N) _ _ ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).finite_support_mult.subset
      fun y hy h0 => hy (by simp [h0]))
  rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.mul_sum]
  congr 1
  simp only [hG, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun la _ => ?_
  exact GlobalTheory.T.admissible_family_valuation_places h2 hH hRA D O x P h p W hW hWv z Sx R hR l ν V L' m hN r hr hrn la

end GlobalTheory.PairTerm
