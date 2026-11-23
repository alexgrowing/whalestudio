import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
import Development.AutomorphicArithmetic.LocalEmbeddings.PairMain
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmpMain
import Development.AutomorphicArithmetic.DivisorFrames.NormsGiveRationalSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

open private place from Development.AutomorphicArithmetic.LocalEmbeddings.PairMain

private theorem vertNum_eq {F : Type} [Field F] [NumberField F] {Y : Var F} (p : ℕ) [Fact p.Prime] (V : Cover Y) (n : ℕ)
    (N : Fin n → HermLB V.p) (z : V.X) : vertNum p V n N z = (VertCmp.pdeg p (fun j => (N j).B) z : ℝ) := by
  rw [vertNum]
  split_ifs with h
  · rw [UpperTheory.pdeg_eq_of_isDeg p V.X n _ (fun j => (N j).isLB) z _
      ⟨h.some.Z, h.some.i, h.some.imm, h.some.int, h.some.alg, h.some.gen, h.some.dim, rfl⟩]
  · rw [VertCmp.pdeg, dif_neg fun ⟨_, Z, i, a₁, a₂, a₃, a₄, a₅, _⟩ => h ⟨⟨Z, i, a₁, a₂, a₃, a₄, a₅⟩⟩, Int.cast_zero]

private theorem one_comp {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (hp : (p : 𝓞 F) ∈ v.asIdeal) {d : ℕ} (hd : Y.dim = d) (A : Bool ⊕ Fin d → Adl C Y)
    (hD : (A (.inl true)).D = (A (.inl false)).D) (V : Cover Y) (L : Bool ⊕ Fin d → HermLB V.p) (m : ℕ) (hm : m ≠ 0)
    (hL : ∀ i, Norms V (L i) (fun y => genAt (A i).D y ^ m) (fun σ y => (m : ℝ) * lnAdl (A i) σ y)
      (fun v e y => (m : ℝ) * (A i).lg v e y))
    (r : ((L (.inl false)).tens (L (.inl true)).dual).B.ι → V.X.functionFieldˣ)
    (hr : IsRatSec ((L (.inl false)).tens (L (.inl true)).dual).B r)
    (hrn : RatNorms V ((L (.inl false)).tens (L (.inl true)).dual) r
      (fun v e y => (m : ℝ) * ((A (.inl false)).lg v e y - (A (.inl true)).lg v e y)))
    (Q : TrueGeo.Model Y) [IsIntegral Q.X] [IsLocallyNoetherian Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X)
    (m' : ℕ) (hm' : m' ≠ 0) (N : Bool ⊕ Fin d → LB Q.X) (hN : ∀ k, (N k).IsLB)
    (t : ∀ k, (N k).ι → Q.X.functionFieldˣ)
    (ht : ∀ v k, VertCmp.GReads Q v (N k) (t k) fun e y => (m' : ℝ) * VertCmp.lam (A k) v e y)
    (M : LB Q.X) (hM : M.IsLB) (s : M.ι → Q.X.functionFieldˣ) (hs : IsRatSec M s)
    (hMs : ∀ v, VertCmp.GReads Q v M s fun e y =>
      (m' : ℝ) * (VertCmp.lam (A (.inl false)) v e y - VertCmp.lam (A (.inl true)) v e y)) :
    (∑ᶠ y, if LiesOverPl V v y then (haveI := V.ar.isLocallyNoetherian;
      ((((L (.inl false)).tens (L (.inl true)).dual).div hr).mult y : ℝ)) *
        vertNum p V d (fun j => L (.inr j)) y else 0) / ((V.deg : ℝ) * (m : ℝ) ^ (d + 1)) =
    (∑ᶠ y : Q.X, if (Q.p y).asIdeal = v.asIdeal then
      (((divOfRatSec hM hs).mult y * VertCmp.pdeg p (fun k => N (.inr k)) y : ℤ) : ℝ) else 0) / (m' : ℝ) ^ (d + 1) := by
  choose u hu using fun k => UpperTheory.norms_give_rational_sections F Y C (A (.inr k)) V (L (.inr k)) m _ (hL (.inr k))
  have key := CovCmp.vsum_cmp V (Cover.ofModel Q hQ) v p hp hd m m' hm hm'
    (fun v e y => VertCmp.lam (A (.inl false)) v e y - VertCmp.lam (A (.inl true)) v e y)
    (fun k => VertCmp.lam (A (.inr k))) (fun k => (L (.inr k)).isLB) u hu
    ((L (.inl false)).tens (L (.inl true)).dual).isLB hr
    (fun v => ⟨hr, ⊤, trivial, fun e y z yt i _ a₁ a₂ a₃ _ => by
      refine (hrn v e y z yt i a₁ a₂ a₃).symm.trans ?_
      simp only [VertCmp.lam, hD]
      ring⟩)
    (N₂ := fun k => N (.inr k)) (fun k => hN (.inr k)) (fun k => t (.inr k))
    (fun k v => CovCmp.cRead_of_gReads Q hQ (ht v (.inr k))) hM hs (fun v => CovCmp.cRead_of_gReads Q hQ (hMs v))
  rw [Cover.deg_ofModel, Nat.cast_one, one_mul] at key
  refine Eq.trans ?_ key
  congr 1
  refine finsum_congr fun y => ?_
  rw [vertNum_eq, Int.cast_mul]
  exact if_congr Iff.rfl rfl rfl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_family_valuation_places : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → ∀ (D : D7) (O : Setup D)
    (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∀ (p : ℕ) [Fact p.Prime]
    (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits),
    (∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1) →
    ∀ (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ), 2 ≤ R →
    ∀ (l : Ln O.S.Dw) (ν : Fin (dimFl D.what₂.Tau O.N) → Bool × Ln O.S.Dw) (V : ∀ c : O.s.Comp, Cover (O.var c))
      (L' : ∀ c, Bool ⊕ Fin (dimFl D.what₂.Tau O.N) → HermLB (V c).p) (m : O.s.Comp → ℕ+),
      (∀ c i, Norms (V c) (L' c i)
        (fun y => genAt (adlOf (O.Φ.C c) (metsOf x O.Φ c) (wOf (ArIn.ind Sx) p R l ν i)).D y ^ (m c : ℕ))
        (fun σ y => (m c : ℕ) * lnAdl (adlOf (O.Φ.C c) (metsOf x O.Φ c) (wOf (ArIn.ind Sx) p R l ν i)) σ y)
        (fun v e y => (m c : ℕ) * (adlOf (O.Φ.C c) (metsOf x O.Φ c) (wOf (ArIn.ind Sx) p R l ν i)).lg v e y)) →
    ∀ (r : ∀ c, ((L' c (.inl false)).tens (L' c (.inl true)).dual).B.ι → (V c).X.functionFieldˣ)
      (hr : ∀ c, IsRatSec ((L' c (.inl false)).tens (L' c (.inl true)).dual).B (r c)),
      (∀ c, RatNorms (V c) ((L' c (.inl false)).tens (L' c (.inl true)).dual) (r c) (fun v e y => (m c : ℕ) *
        ((adlOf (O.Φ.C c) (metsOf x O.Φ c) (wOf (ArIn.ind Sx) p R l ν (.inl false))).lg v e y -
          (adlOf (O.Φ.C c) (metsOf x O.Φ c) (wOf (ArIn.ind Sx) p R l ν (.inl true))).lg v e y))) →
    ∀ la : Formalism.L2.Geo.PlL D p,
      ∑ c, (∑ᶠ y, if LiesOverPl (V c) la.1 y then (haveI := (V c).ar.isLocallyNoetherian;
          ((((L' c (.inl false)).tens (L' c (.inl true)).dual).div (hr c)).mult y : ℝ)) *
            vertNum p (V c) (dimFl D.what₂.Tau O.N) (fun j => L' c (.inr j)) y else 0) /
        (((V c).deg : ℝ) * ((m c : ℕ) : ℝ) ^ (dimFl D.what₂.Tau O.N + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      Formalism.L2.Geo.wtL D p la * ((((ithOf Fact.out (hW la) (z la).Z (dimFl D.what₂.Tau O.N)).capDeg
                (vdiv Fact.out (hW la) _ _ _ (lnId (z la) Fact.out (hW la) l))
                (∏ i, (lnLB (z la) (ν i).1 (ν i).2).c1) : ℚ) : ℝ) / (cov (z la) : ℝ)) := by
  intro h2 hH _ D O x P _ p _ W hW hWv z Sx R hR l ν V L' m hN r hr hrn la
  let w := wOf (ArIn.ind Sx) p R l ν
  have hw : ∀ (i : Bool ⊕ Fin (dimFl D.what₂.Tau O.N)), ∀ a ∈ (w i).support,
      {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
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
  choose M L m' Ψ hI hΨ _ using fun c =>
    (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ O.s x O.Φ c R hR).2
      (Bool ⊕ Fin (dimFl D.what₂.Tau O.N)) w hw
  have hb : 0 ≤ 1 / ((p : ℝ) - 1) + vDiff D.host.E p := by
    have h₁ : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have h₂ : 0 ≤ vDiff D.host.E p := by unfold vDiff; positivity
    have h₃ : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hA := fun c => adlOf_lnSym_eq (O.Φ.C c) (metsOf x O.Φ c) (Function.update (ArIn.ind Sx) p false)
    (Function.update (ArIn.ind Sx) p true) (some R) l
  have hg := fun c => UpperTheory.arithmetic_function_induced_bound h2 D.what₂.LL (O.Φ.C c).Y (M c) _
    (fun i => adlOf (O.Φ.C c) (metsOf x O.Φ c) (w i)) (L c) (m' c) (Ψ c) (hI c) (hΨ c) p (.inl false) (.inl true)
    (hA c) _ hb
    (fun v ε y => abs_lgOf_lnSym_update_sub_le (O.Φ.C c) (ArIn.ind Sx) p (some R) l v ε y) _ (O.dim_eq c)
  choose Q hQ₁ hQ₂ N t M₀ hM₀ s hs hQ hN' hNt hMs _ _ using hg
  have hpl := place (z la) O.Φ O.dim_eq la.1 la.2 (hWv la) (metsOf x O.Φ) (ArIn.ind Sx)
    (some R) l ν Q hQ (fun c => m' c) (fun c => (m' c).ne_zero) M₀ hM₀ s hs (fun c => hMs c la.1)
    (fun c k => N c (.inr k)) (fun c k => hN' c (.inr k)) (fun c k => t c (.inr k)) (fun c k => hNt c la.1 (.inr k))
  have e₂ (a : ℝ) :
      Formalism.L2.Geo.wtL D p la * a = VertCmp.placeDeg p la.1 * a / (Module.finrank ℚ D.what₂.LL : ℝ) := by
    rw [Formalism.L2.Geo.wtL, VertCmp.placeDeg, ← div_div, div_mul_eq_mul_div]
  refine Eq.trans ?_ ((e₂ _).trans (congrArg (· / (Module.finrank ℚ D.what₂.LL : ℝ)) hpl)).symm
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (div_div _ _ _).symm.trans (congrArg (· / (Module.finrank ℚ D.what₂.LL : ℝ)) ?_)
  exact one_comp p la.1 la.2 (O.dim_eq c) (fun i => adlOf (O.Φ.C c) (metsOf x O.Φ c) (w i))
    ((congrArg Adl.D (hA c)).trans rfl) (V c) (L' c) (m c) (m c).ne_zero (hN c) (r c) (hr c) (hrn c) (Q c) (hQ c) (m' c)
    (m' c).ne_zero (N c) (hN' c) (t c) (hNt c) (M₀ c) (hM₀ c) (s c) (hs c) (hMs c)
