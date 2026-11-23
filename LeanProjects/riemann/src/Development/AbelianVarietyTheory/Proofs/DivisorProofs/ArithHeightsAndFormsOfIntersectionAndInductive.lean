import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.Published

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem ArFormExists.exists_isArithHeight (H : ArFormExists) (hX : IsArithVar p D) (L : HermLB p) :
    ∃ h, L.IsArithHeight h := by
  obtain ⟨Φ, hΦ⟩ := H k X p D hX Unit fun _ => L
  obtain ⟨h, hh, -⟩ := hΦ.1 (Pi.single () 1)
  exact ⟨h, (isometric_comb_single (fun _ : Unit => L) ()).isArithHeight hX hh⟩

theorem ArMix.fnB_of_height (H : ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) D Φ) (n : ι → ℤ) {h : X → ℝ}
    (hh : (comb L n).IsArithHeight h) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  have := hX.isLocallyNoetherian
  have hr : IsRatSec (ArInt.fnB u hu hc).B fun _ => 1 := fun a b h =>
    (map_one _).symm.trans (mul_one _).symm
  have he (z : X) : ((ArInt.fnB u hu hc).div hr).IsEqn z 1 :=
    (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : ((ArInt.fnB u hu hc).div hr).mult z = 0 := (he z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ ((ArInt.fnB u hu hc).div hr) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => (he _).mem_supp_iff.1 hy (unitAt_one _)
  have h₃ (σ) : logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ => 1) = fun y => -(1 / 2) * u σ y := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    change 0 - u σ y / 2 = _
    ring
  rw [(H k X p D hX ι _ L Φ hΦ n h hh _ hr).2, HermLB.archInt, chInt]
  simp only [h₁, h₂, h₃, Weight.chernInt_const_mul, Int.cast_zero, zero_mul, finsum_zero, ← mul_finsum]
  ring

theorem arExists_of_form_of_mix : ArFormExists → ArMix → ArExists := by
  intro HF HM k _ X _ p D hX
  refine ⟨HF.exists_isArithHeight hX, fun ι _ L => ⟨HF k X p D hX ι L, ?_⟩⟩
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := HF k X p D hX _ fun o : Option ι => o.elim (ArInt.fnB (fun _ _ => 2) hu hc) L
  refine ⟨Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (R := ℝ) (some : ι → Option ι)).toLinearMap,
    fun n => ?_, fun P d hd hP => ?_⟩
  · obtain ⟨h, hh⟩ := HF.exists_isArithHeight hX (comb L n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, LinearMap.mulLeft_apply,
      HM.fnB_of_height hX hΦ n hh, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    exact hΦ.2 _ (1 + d) (by omega) ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)

end GlobalTheory.Published
