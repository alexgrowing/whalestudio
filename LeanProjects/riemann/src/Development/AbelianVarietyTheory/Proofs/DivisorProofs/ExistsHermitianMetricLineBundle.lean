import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.CechPic
open Filter Topology

namespace GlobalTheory.MetricExists

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem exists_of_isGenerated {B : LB X} (h : IsGenerated B) : ∃ L : HermLB p, L.B = B := by
  have hB := h.isLB
  obtain ⟨n, s, hs⟩ := h
  exact ⟨.fs p hB s hs (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩, rfl⟩

theorem exists_of_tens {B : LB X} (hB : B.IsLB) (M N : HermLB p) (h : N.B = tens B M.B) :
    ∃ L : HermLB p, L.B = B := by
  obtain ⟨_, hN, χ, hc, hj⟩ := N
  obtain rfl : _ = tens B M.B := h
  have e (σ : k →+* ℂ) (a : B.ι) (b : M.B.ι) (y : CxPts p σ) (ha : y ∈ ptsIn p σ (B.U a))
      (hb : y ∈ ptsIn p σ (M.B.U b)) :
      (Weight.cancel hB (χ σ) (M.φ σ)).φ a y = (χ σ).φ (a, b) y + -(M.φ σ).φ b y :=
    (Weight.ofPairs_φ ha hb).trans (sub_eq_add_neg _ _)
  refine ⟨⟨B, hB, fun σ => Weight.cancel hB (χ σ) (M.φ σ), fun σ a y ha => ?_,
    fun σ σ' a y y' hy ha => ?_⟩, rfl⟩
  · have hb := mem_pick M.isLB y
    have hab : y ∈ ptsIn p σ (B.U a ⊓ M.B.U (pick M.isLB y)) := mem_ptsIn_inf.2 ⟨ha, hb⟩
    refine ((hc σ (a, _) y hab).add (M.cInf σ _ y hb).neg).congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hab] with z hz
    exact e σ a _ z (mem_ptsIn_inf.1 hz).1 (mem_ptsIn_inf.1 hz).2
  · have hb := mem_pick M.isLB y
    have hab : y ∈ ptsIn p σ (B.U a ⊓ M.B.U (pick M.isLB y)) := mem_ptsIn_inf.2 ⟨ha, hb⟩
    rw [e σ a _ y ha hb, e σ' a _ y' ((mem_ptsIn_iff_of_conj hy).2 ha) ((mem_ptsIn_iff_of_conj hy).2 hb)]
    exact congrArg₂ (· + -·) (hj σ σ' (a, _) y y' hy hab) (M.conj σ σ' _ y y' hy hb)

theorem exists_of_isProjOver (hp : IsProjOver p) {B : LB X} (hB : B.IsLB) : ∃ L : HermLB p, L.B = B := by
  obtain ⟨N, j, hj, hjp⟩ := hp
  have := isProper_str k N
  have : IsProper p := hjp ▸ inferInstance
  let A : HermLB p := (ProjSpace.hermitianTwistingSheaf k N).pull j hjp
  have hA : IsAmpleLB A.B := (isAmple_projective_O_one k N).pull_of_isAffineHom j
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isGenerated p hA (isLB_dual hB)).exists
  have hP := isLB_lbPow A.isLB t
  have hT := isLB_tens hB hP
  have hG : IsGenerated (tens B (lbPow A.B t)) := by
    refine ht.of_lbIso hT ((cls_eq_iff hT ht.isLB).1 ?_)
    rw [cls_div hP (isLB_dual hB), cls_dual hB, cls_tens hB hP, sub_neg_eq_add, add_comm]
  obtain ⟨L, hL⟩ := exists_of_isGenerated (p := p) hG
  exact exists_of_tens hB (A.pow t) L hL

theorem exists_hermLB : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ B : LB X, B.IsLB → ∃ L : HermLB p, L.B = B :=
  fun _ _ _ _ _ h _ hB => exists_of_isProjOver h.isProjOver hB

end GlobalTheory.MetricExists
