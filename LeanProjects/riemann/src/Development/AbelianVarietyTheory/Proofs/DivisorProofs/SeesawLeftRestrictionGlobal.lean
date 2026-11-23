import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TupLe

variable {D : D7}

theorem isConjPl_div {P P' : Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') : Formalism.L2.DIV.IsConjPl P P' :=
  fun a b e => h a b (by rw [e, Formalism.BasicNotions.Examples₂.star_eq_conj])

theorem lev_isConjPl_iff {P P' : Pl D.host.E} : Lev.IsConjPl P P' ↔ P' = Formalism.L2.DIV.conjPl P := by
  refine ⟨fun h => (isConjPl_div (isConjPl_of_lev h)).eq_conjPl, ?_⟩
  rintro rfl
  have h : Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
  rwa [(isConjPl_div (isConjPl_of_lev h)).eq_conjPl] at h

theorem isConjPl_conjPl_divisor (P : Pl D.host.E) : Formalism.BasicNotions.IsConjPl D.host P (Formalism.L2.DIV.conjPl P) :=
  isConjPl_of_lev (lev_isConjPl_iff.2 rfl)

open Classical in

theorem disjoint_conj {X : Finset (Pl D.host.E)} (hX : SplitSet X) : Disjoint X (X.image Formalism.L2.DIV.conjPl) := by
  refine Finset.disjoint_left.2 fun P hP hQ => ?_
  obtain ⟨P₀, h0, rfl⟩ := Finset.mem_image.1 hQ
  have a1 : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P₀)) (Formalism.L2.DIV.conjPl P₀) :=
    GlobalTheory.MovedIdem.isIdemAt_conj (hX.isIdemAt h0) fun x => Iff.rfl
  have a2 := hX.mul_conj hP h0
  rw [idemAt_eq a1, a1.1.1] at a2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Formalism.L2.DIV.conjPl P₀).ne_bot
  refine (a1.2 x hx0).1 hx ?_
  rw [a2, zero_mul, map_zero]
  exact zero_mem _

open Classical in

theorem idem_add_cA {X : Finset (Pl D.host.E)} (hX : SplitSet X) :
    idem X + cA D (idem X) = idem (X ∪ X.image Formalism.L2.DIV.conjPl) := by
  rw [← idem_eq (GlobalTheory.RefDatumLev.isIdemSum_conjPl hX.isIdemSum), idem, idem, idem, Finset.sum_union (disjoint_conj hX)]

open Classical in

theorem idem_add_cA_eq {X Y : Finset (Pl D.host.E)} (hX : SplitSet X) (hY : SplitSet Y)
    (h : ∀ P, P ∈ X ∪ X.image Formalism.L2.DIV.conjPl ↔ P ∈ Y ∪ Y.image Formalism.L2.DIV.conjPl) :
    idem X + cA D (idem X) = idem Y + cA D (idem Y) := by
  rw [idem_add_cA hX, idem_add_cA hY]
  congr 1
  ext P
  exact h P

open Classical in

theorem mem_half_closure {ch : Set (Pl D.host.E)}
    (hch : ∀ P P', Formalism.BasicNotions.IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) {A B : Finset (Pl D.host.E)}
    (hcl : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ∈ A ∨ Formalism.L2.DIV.conjPl P ∈ B)
    (hne : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ≠ P) (P : Pl D.host.E) :
    P ∈ half ch A ∪ half ch B ∪ (half ch A ∪ half ch B).image Formalism.L2.DIV.conjPl ↔ P ∈ A ∨ P ∈ B := by
  have hY : ∀ P, P ∈ half ch A ∪ half ch B → P ∈ A ∨ P ∈ B := fun P h => by
    rcases Finset.mem_union.1 h with h | h
    exacts [Or.inl (mem_half.1 h).1, Or.inr (mem_half.1 h).1]
  have hmY : ∀ P, P ∈ A ∨ P ∈ B → P ∈ ch → P ∈ half ch A ∪ half ch B := fun P hP hc => by
    rcases hP with h | h
    exacts [Finset.mem_union_left _ (mem_half.2 ⟨h, hc⟩), Finset.mem_union_right _ (mem_half.2 ⟨h, hc⟩)]
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact hY P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      exact hcl P' (hY P' hP')
  · intro hP
    by_cases hc : P ∈ ch
    · exact Finset.mem_union_left _ (hmY P hP hc)
    · have hc' : Formalism.L2.DIV.conjPl P ∈ ch := by
        by_contra hc'
        exact hc ((hch P (Formalism.L2.DIV.conjPl P) (isConjPl_conjPl_divisor P) (hne P hP).symm).2 hc')
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨Formalism.L2.DIV.conjPl P, hmY _ (hcl P hP) hc', Formalism.L2.DIV.conjPl_conjPl P⟩)

theorem not_mem_of_coprime {P : Pl D.host.E} {l q : ℕ} (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (hc : Nat.Coprime l q) :
    (l : 𝓞 D.host.E) ∉ P.asIdeal := fun hl => by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have e : (u : 𝓞 D.host.E) * (l : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * (q : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hq)

open Classical in

theorem placesSt : PlacesSt := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm

end GlobalTheory.BigOn.Exp.TupLe
