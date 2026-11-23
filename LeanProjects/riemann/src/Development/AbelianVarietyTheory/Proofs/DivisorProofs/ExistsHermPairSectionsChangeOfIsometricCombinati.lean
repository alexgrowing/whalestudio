import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.ChangePair
open GlobalTheory.VolBr.NuEq
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_chart (M : HermLB p) (x : X) : ∃ c, x ∈ M.B.U c := by
  have h : x ∈ (⨆ c, M.B.U c) := by rw [M.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem loc_eq (P : Pair p) (a b a' b' i j : ℤ) (f : X.functionField) (ρ ρ' : X.functionFieldˣ) (e g) :
    f * (ρ : X.functionField) ^ i * (ρ' : X.functionField) ^ j =
      P.loc (i * a + j * a') (i * b + j * b') f e g *
        (((ρ : X.functionField) / P.loc a b 1 e g) ^ i * ((ρ' : X.functionField) / P.loc a' b' 1 e g) ^ j) := by
  have hs : (P.r e : X.functionField) ≠ 0 := (P.r e).ne_zero
  have ht : (P.r' g : X.functionField) ≠ 0 := (P.r' g).ne_zero
  simp only [Pair.loc, one_mul]
  rw [div_zpow, div_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    zpow_add₀ hs, zpow_add₀ ht, mul_comm a i, mul_comm b i, mul_comm a' j, mul_comm b' j]
  have h1 := zpow_ne_zero (i * a) hs
  have h2 := zpow_ne_zero (i * b) ht
  have h3 := zpow_ne_zero (j * a') hs
  have h4 := zpow_ne_zero (j * b') ht
  field_simp

end GlobalTheory.HSNef.ChangePair

namespace GlobalTheory.HSNef

open GlobalTheory.VolBr.NuEq ChangePair in

theorem change_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  intro k _ X _ p P a b a' b' M N ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  let Q : Pair p := ⟨M, N, ρ, ρ', hρ, hρ'⟩
  have hw : ∀ (i j : ℤ) (x : X) c d e g, x ∈ M.B.U c → x ∈ N.B.U d → x ∈ P.L.B.U e → x ∈ P.A.B.U g →
      UnitAt x (((ρ c : X.functionField) / P.loc a b 1 e g) ^ i *
        ((ρ' d : X.functionField) / P.loc a' b' 1 e g) ^ j) :=
    fun i j x c d e g hc hd he hg =>
      (NuEq.unitAt_zpow (hu x c e g hc he hg) i).mul (NuEq.unitAt_zpow (hu' x d e g hd he hg) j)
  have hH : ∀ i j : ℤ, Q.H i j = P.H (i * a + j * a') (i * b + j * b') := by
    intro i j
    ext f
    constructor
    · intro hf x e g he hg
      obtain ⟨c, hc⟩ := exists_chart M x
      obtain ⟨d, hd⟩ := exists_chart N x
      have hW := hw i j x c d e g hc hd he hg
      have h := hf x c d hc hd
      change RegAt x (f * _ ^ i * _ ^ j) at h
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g] at h
      have h' := h.mul hW.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hW.ne_zero, mul_one] at h'
    · intro hf x c d hc hd
      obtain ⟨e, he⟩ := exists_chart P.L x
      obtain ⟨g, hg⟩ := exists_chart P.A x
      change RegAt x (f * _ ^ i * _ ^ j)
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g]
      exact (hf x e g he hg).mul (hw i j x c d e g hc hd he hg).regAt
  have hnu : ∀ (i j : ℤ) (f : X.functionField), f ∈ P.H (i * a + j * a') (i * b + j * b') →
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), Q.nu i j σ y f = P.nu (i * a + j * a') (i * b + j * b') σ y f := by
    intro i j f hf σ y
    have hc := mem_pick (M.φ σ).isLB y
    have hd := mem_pick (N.φ σ).isLB y
    have he := mem_pick (P.L.φ σ).isLB y
    have hg := mem_pick (P.A.φ σ).isLB y
    set c := pick (M.φ σ).isLB y
    set d := pick (N.φ σ).isLB y
    set e := pick (P.L.φ σ).isLB y
    set g := pick (P.A.φ σ).isLB y
    have hfQ : f ∈ Q.H i j := (hH i j).symm ▸ hf
    rw [nu_eq k X p Q i j f hfQ σ y c d hc hd, nu_eq k X p P _ _ f hf σ y e g he hg]
    have hU := hu _ c e g (mem_ptsIn.1 hc) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hU' := hu' _ d e g (mem_ptsIn.1 hd) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hreg : RegAt (under y) (P.loc (i * a + j * a') (i * b + j * b') f e g) :=
      hf _ e g (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have eU : ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 e g) y‖ =
        Real.exp ((M.φ σ).φ c y / 2 - (a * (P.L.φ σ).φ e y + b * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU))]
      congr 1
      linarith [hn σ y c e g hc he hg]
    have eU' : ‖ratVal ((ρ' d : X.functionField) / P.loc a' b' 1 e g) y‖ =
        Real.exp ((N.φ σ).φ d y / 2 - (a' * (P.L.φ σ).φ e y + b' * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU'))]
      congr 1
      linarith [hn' σ y d e g hd he hg]
    change ‖ratVal (f * _ ^ i * _ ^ j) y‖ * _ = _
    rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g,
      ratVal_mul hreg ((NuEq.unitAt_zpow hU i).mul (NuEq.unitAt_zpow hU' j)).regAt,
      ratVal_mul (NuEq.unitAt_zpow hU i).regAt (NuEq.unitAt_zpow hU' j).regAt,
      ratVal_zpow' hU, ratVal_zpow' hU', norm_mul, norm_mul, norm_zpow, norm_zpow, eU, eU',
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨Q, rfl, rfl, fun i j R => ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hR⟩
    have hf' : f ∈ P.H (i * a + j * a') (i * b + j * b') := hH i j ▸ hf
    exact ⟨hf', fun σ y => hnu i j f hf' σ y ▸ hR σ y⟩
  · rintro ⟨hf, hR⟩
    exact ⟨(hH i j).symm ▸ hf, fun σ y => (hnu i j f hf σ y).symm ▸ hR σ y⟩

end GlobalTheory.HSNef
