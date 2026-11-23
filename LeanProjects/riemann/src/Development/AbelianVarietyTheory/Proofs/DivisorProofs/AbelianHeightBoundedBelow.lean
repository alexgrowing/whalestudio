import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatValEqValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerOfInducedBundleGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroLocusSectionPullbackExtendsStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem htLow (hE : GlobalTheory.Published.ArExists) (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (hI : A.Induced M L q 0) (hA : Y.ample A.D) :
    ∃ C : ℝ, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → -C ≤ A.ht x := by
  have := M.ar.isIntegral
  obtain ⟨m, hm, N, t, ht⟩ := GlobalTheory.T.power_of_induced_bundle_generated F (cxSt F) Y A M L q 0 hI hA
  have hs : ∀ i, ∃ s : (L.pow m).B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    fun i => GlobalTheory.T.nonzero_locus_section_pullback_extends F Y M _ (L.pow m).isLB (t i)
  choose s hs using hs
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => small_of_shift (𝓞 F) M.X M.p Y.dim M.ar L m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hE _ M.X M.p _ M.ar).1 L
  have hk : (0 : ℝ) < ((q : ℕ) : ℝ) * (A.n : ℕ) := mul_pos (Nat.cast_pos.2 q.pos) (Nat.cast_pos.2 A.n.pos)
  refine ⟨(∑ i, |c i|) / (((q : ℕ) : ℝ) * (A.n : ℕ)), fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ x))
  have hN : (0 : ℝ) < Nat.card (M.X.residueField (M.j x) →+* ℂ) :=
    Nat.cast_pos.2 (NefModel.card_pos M hx)
  have hb : IsPtHt L (M.j x) (h (M.j x) / Nat.card (M.X.residueField (M.j x) →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt (𝓞 F) M.X M.p Y.dim M.ar L m (c i) _ (M.j x) (s i) hm (hc i)
    ((hs i x).2 hi) (ClosedAlg.isAlgPt_of_isClosed F Y M x hx) hb
  rw [HtModel.ht_eq F _ Y A M L q hI x _ hx hb]
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  rw [← neg_div]
  exact div_le_div_of_nonneg_right (h2.trans h1) hk.le

theorem main : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ C : ℝ,
    ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → -C ≤ (O.met.ab c).ht b := by
  intro hP _ D O hO c
  obtain ⟨x, P, h⟩ := hO
  obtain ⟨M, L, q, hI, -⟩ := P.ab_model c
  rw [h.ab_eq]
  exact htLow hP.p4.arExists _ _ _ M L q hI (P.ab_ample c)

end GlobalTheory.AmpleHtLow

end
