import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTwConj
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.MassOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.FibStable PositivityTheory.Rg.BcB.G8
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev th2 (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev loc2 (w : Pl E) (x : GL (Fin a) E) (y : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w x, locEl b w y)

def orb2 (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (c : TwCl (thE E a) × TwCl (thE E b)) : ℂ :=
  ∏ᶠ w ∈ S, twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w)

theorem local_pair_mem_maximal_eventually (x : GL (Fin a) E) (y : GL (Fin b) E) : ∀ᶠ w : Pl E in cofinite, loc2 w x y ∈ K2 a b w := by
  filter_upwards [GoodInt.eventually_mem_KGL x, GoodInt.eventually_mem_KGL (x * thE E a x),
    GoodInt.eventually_mem_KGL y, GoodInt.eventually_mem_KGL (y * thE E b y)] with w h1 h2 h3 h4
  refine ⟨?_, ?_⟩
  · show locEl a w x ∈ _
    unfold locEl
    split_ifs
    exacts [h2, h1]
  · show locEl b w y ∈ _
    unfold locEl
    split_ifs
    exacts [h4, h3]

theorem charpoly_conj2 (w : Pl E) (g y : GLw a w × GLw b w) :
    (nrmL a w (g⁻¹ * y * th2 a b w g).1).val.charpoly = (nrmL a w y.1).val.charpoly ∧
      (nrmL b w (g⁻¹ * y * th2 a b w g).2).val.charpoly = (nrmL b w y.2).val.charpoly :=
  ⟨charpoly_twConj a w g.1 y.1, charpoly_twConj b w g.2 y.2⟩

theorem pairSum (hA : AbsSum) (hF : FinCl2) (hI : Invar2) (hN : Unit2) (hC : Count2) (hU : Unr E) (S : Set (Pl E))
    (hS : IsSection S) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ : IsTestP φ) (P₁ P₂ : E[X]) (h₁ : P₁ ∈ Ell E a)
    (h₂ : P₂ ∈ Ell E b) :
    {c | (pol c.1 = P₁ ∧ pol c.2 = P₂) ∧ orb2 S φ c ≠ 0}.Finite ∧
      (∑ᶠ c, if pol c.1 = P₁ ∧ pol c.2 = P₂ then orb2 S φ c else 0) * 2 ^ (nfac P₁ + nfac P₂) =
        2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hφ⟩ := hφ
  obtain ⟨δ₁, hδ₁⟩ := KapMul.exists_norm E h₁
  obtain ⟨δ₂, hδ₂⟩ := KapMul.exists_norm E h₂
  have hinv : ∀ w y, twOrb (th2 a b w) (K2 a b w) (cls (th2 a b w) y).rep (φ w) = twOrb (th2 a b w) (K2 a b w) y (φ w) := by
    intro w y
    obtain ⟨g, hg⟩ := rep_cls (th2 a b w) y
    rw [hg]
    exact hI E hU a b w _ _ (hK₁.1 w) (hK₂.1 w) _ (hφ.1 w) y g
  have hpol : ∀ (w : Pl E) (y : GLw a w × GLw b w), (nrmL a w (cls (th2 a b w) y).rep.1).val.charpoly = (nrmL a w y.1).val.charpoly ∧
      (nrmL b w (cls (th2 a b w) y).rep.2).val.charpoly = (nrmL b w y.2).val.charpoly := by
    intro w y
    obtain ⟨g, hg⟩ := rep_cls (th2 a b w) y
    rw [hg]
    exact charpoly_conj2 w g y
  have hl : ∀ (w : Pl E) (x : GL (Fin a) E) (y : GL (Fin b) E), (x * thE E a x).val.charpoly = P₁ → (y * thE E b y).val.charpoly = P₂ →
      (nrmL a w (loc2 w x y).1).val.charpoly = atPl w P₁ ∧ (nrmL b w (loc2 w x y).2).val.charpoly = atPl w P₂ :=
    fun w x y hx hy => ⟨by rw [← hx]; exact ThBasic.charpoly_nrmL hU a w x, by rw [← hy]; exact ThBasic.charpoly_nrmL hU b w y⟩
  have key := hA (Pl E) (TwCl (thE E a) × TwCl (thE E b)) S (fun w => TwCl (th2 a b w))
    (fun w => {l | (nrmL a w l.rep.1).val.charpoly = atPl w P₁ ∧ (nrmL b w l.rep.2).val.charpoly = atPl w P₂})
    (fun w => cls _ (loc2 w δ₁ δ₂)) (fun w l => twOrb (th2 a b w) (K2 a b w) l.rep (φ w))
    {c | pol c.1 = P₁ ∧ pol c.2 = P₂} (fun c w => cls _ (loc2 w c.1.rep c.2.rep)) (2 ^ (nfac P₁ + nfac P₂))
    (2 ^ ((a + b) * Fintype.card (InfinitePlace E)))
    (fun w => hF E hU a b w _ _ h₁.2.2.1.map h₂.2.2.1.map)
    (fun w => ⟨(hpol w _).1.trans (hl w _ _ hδ₁ hδ₂).1, (hpol w _).2.trans (hl w _ _ hδ₁ hδ₂).2⟩)
    (by
      filter_upwards [hN E hU a b P₁ h₁ P₂ h₂, hφ.2, local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2 h3 l hl'
      rw [h2, (h1 l.rep _ hl'.1 hl'.2 (hl w _ _ hδ₁ hδ₂).1 (hl w _ _ hδ₁ hδ₂).2 h3).1]
      refine if_congr ?_ rfl rfl
      rw [← cls_eq_iff, cls_rep, eq_comm])
    (fun c hc => ⟨fun w => ⟨(hpol w _).1.trans (hl w _ _ hc.1 hc.2).1, (hpol w _).2.trans (hl w _ _ hc.1 hc.2).2⟩, by
      filter_upwards [hN E hU a b P₁ h₁ P₂ h₂, local_pair_mem_maximal_eventually c.1.rep c.2.rep, local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2 h3
      exact ((cls_eq_iff _ _ _).2 ((h1 _ _ (hl w _ _ hc.1 hc.2).1 (hl w _ _ hc.1 hc.2).2 (hl w _ _ hδ₁ hδ₂).1
        (hl w _ _ hδ₁ hδ₂).2 h3).2 h2)).symm⟩)
    (pow_ne_zero _ two_ne_zero)
    (fun y hy hy' => hC E hU a b S hS P₁ h₁ P₂ h₂ y hy (by
      filter_upwards [hy', local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2
      exact ⟨_, h2, h1⟩))
  simp only [hinv, Set.mem_setOf_eq, Nat.cast_pow, Nat.cast_ofNat] at key
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  refine finprod_mem_congr rfl fun w _ => ?_
  unfold stTw2 clSum
  refine finsum_congr fun d => ?_
  simp only [Set.mem_setOf_eq, Pi.one_apply, one_mul]

theorem orbit_pair_nonzero_local (hN : Unit2) (hZ : Supp) (hU : Unr E) (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (hφ : IsTestP φ) (c : TwCl (thE E a) × TwCl (thE E b)) (h₁ : pol c.1 ∈ Ell E a) (h₂ : pol c.2 ∈ Ell E b)
    (h : orb2 S φ c ≠ 0) : ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧
      (nrmL a w y.1).val.charpoly = atPl w (pol c.1) ∧ (nrmL b w y.2).val.charpoly = atPl w (pol c.2) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hφ⟩ := hφ
  intro w hw
  have hl : ∀ w : Pl E, (nrmL a w (loc2 w c.1.rep c.2.rep).1).val.charpoly = atPl w (pol c.1) ∧
      (nrmL b w (loc2 w c.1.rep c.2.rep).2).val.charpoly = atPl w (pol c.2) :=
    fun w => ⟨ThBasic.charpoly_nrmL hU a w _, ThBasic.charpoly_nrmL hU b w _⟩
  have hfin : ∀ᶠ w in cofinite, twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w) = 1 := by
    filter_upwards [hN E hU a b _ h₁ _ h₂, hφ.2, local_pair_mem_maximal_eventually c.1.rep c.2.rep] with w h1 h2 h3
    rw [h2, (h1 _ _ (hl w).1 (hl w).2 (hl w).1 (hl w).2 h3).1, if_pos ⟨1, by rw [map_one, inv_one, one_mul, mul_one]⟩]
  have hne : twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w) ≠ 0 := by
    intro h0
    apply h
    unfold orb2
    have hf : (S ∩ Function.mulSupport fun w => twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w)).Finite :=
      (Filter.eventually_cofinite.1 hfin).subset fun w hw => hw.2
    rw [finprod_mem_eq_prod _ hf]
    exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0
  obtain ⟨g, hg⟩ := hZ _ _ _ _ _ hne
  exact ⟨_, hg, (charpoly_conj2 w g _).1.trans (hl w).1, (charpoly_conj2 w g _).2.trans (hl w).2⟩

theorem twisted_trace_formula_elliptic_expansion (hA : AbsSum) (hF : FinCl2) (hI : Invar2) (hN : Unit2) (hC : Count2) (hZ : Supp) (hP : FinPol2) :
    G8.G3 := by
  intro E _ _ _ hU a b S hS l₁ l₂ φ hφ hreg
  have hsum := pairSum hA hF hI hN hC hU S hS φ hφ
  have hne := orbit_pair_nonzero_local hN hZ hU S φ hφ
  have hQ := (let ⟨_, _, _, _, h⟩ := hφ; hP E hU a b S hS φ (fun w => (h.1 w).1) h.2)
  set Q₀ := {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧
    (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2} with hQ₀
  have hcop : ∀ p ∈ Q₀, IsCoprime p.1 p.2 := by
    rintro p ⟨-, -, hp⟩
    obtain ⟨w, hw, hr⟩ := hreg
    obtain ⟨y, hy, e1, e2⟩ := hp w hw
    have := hr y hy
    rw [e1, e2, ← Polynomial.map_mul, Polynomial.separable_map] at this
    exact this.isCoprime
  set pc : TwCl (thE E a) × TwCl (thE E b) → E[X] × E[X] := fun c => (pol c.1, pol c.2) with hpc
  have hB : {c | (pol c.1 ∈ Ell E a ∧ pol c.2 ∈ Ell E b) ∧ orb2 S φ c ≠ 0}.Finite := by
    refine (hQ.biUnion fun p hp => (hsum p.1 p.2 hp.1 hp.2.1).1).subset ?_
    rintro c ⟨h1, h2⟩
    exact Set.mem_biUnion (x := pc c) ⟨h1.1, h1.2, hne c h1.1 h1.2 h2⟩ ⟨⟨rfl, rfl⟩, h2⟩
  have hmaps : ∀ c ∈ hB.toFinset, pc c ∈ hQ.toFinset := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc ⊢
    exact ⟨hc.1.1, hc.1.2, hne c hc.1.1 hc.1.2 hc.2⟩
  have e1 : geomRat2 S l₁ l₂ φ = ∑ c ∈ hB.toFinset, kap (pol c.1) * kap (pol c.2) * chW l₁ (pol c.1) * chW l₂ (pol c.2) *
      (orb2 S φ c * 2 ^ (nfac (pol c.1) + nfac (pol c.2))) := by
    unfold geomRat2
    rw [finsum_eq_sum_of_support_subset (s := hB.toFinset)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [Set.Finite.mem_toFinset] at hc
      rw [if_pos hc.1, MassP.mass_kap E hU a c.1.rep hc.1.1, MassP.mass_kap E hU b c.2.rep hc.1.2, pow_add]
      unfold orb2 pol
      ring
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      split_ifs at hc with h
      · exact ⟨h, right_ne_zero_of_mul hc⟩
      · exact absurd rfl hc
  have e3 : ∀ p : E[X] × E[X], p.1 ∈ Ell E a → p.2 ∈ Ell E b →
      (∑ᶠ c, if pol c.1 = p.1 ∧ pol c.2 = p.2 then orb2 S φ c else 0) = ∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c := by
    intro p p1 p2
    rw [finsum_eq_sum_of_support_subset (s := hB.toFinset), Finset.sum_filter]
    · exact Finset.sum_congr rfl fun c _ => if_congr (Prod.ext_iff (x := pc c) (y := p)).symm rfl rfl
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      split_ifs at hc with h
      · exact ⟨⟨h.1 ▸ p1, h.2 ▸ p2⟩, hc⟩
      · exact absurd rfl hc
  have e2 : G8.geomSt2 S l₁ l₂ φ = ∑ p ∈ hQ.toFinset, kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 *
      ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w) := by
    unfold G8.geomSt2
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    refine and_congr_left fun h => ⟨fun hp => ?_, fun hp => ⟨hp.1, hp.2.1, hcop p hp⟩⟩
    have h2 := (hsum p.1 p.2 hp.1 hp.2.1).2
    rw [e3 p hp.1 hp.2.1] at h2
    have h3 : ∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h2
      exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (right_ne_zero_of_mul h) h2.symm
    obtain ⟨c, hc, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
    rw [Finset.mem_filter] at hc
    have := hmaps c hc.1
    rwa [hc.2, Set.Finite.mem_toFinset] at this
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Set.Finite.mem_toFinset] at hp
  have h2 := (hsum p.1 p.2 hp.1 hp.2.1).2
  rw [e3 p hp.1 hp.2.1] at h2
  calc _ = kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 *
        ((∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c) * 2 ^ (nfac p.1 + nfac p.2)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [← (Finset.mem_filter.1 hc).2]
    _ = _ := by rw [h2]; ring

end PositivityTheory.Rg.BcB.G3

end
