import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoefB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

open GlobalTheory.CompanionTheory.SiegelND (pairH)
open GlobalTheory.CompanionTheory.ThetaCoefND (gramOf continuous_pairH pairH_ne_zero setIntegral_pairH)
open GlobalTheory.CompanionTheory.HermPoisson (ofHermE)

variable {D : D7}

theorem thS_eq (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {W : HSp D} {n : ℕ} {m : Measure (GA D W)}
    {𝓕 : Set (GA D W)} {Ψ : Mx D W.rank n → ℂ} (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) (x : hermA D n) :
    thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) =
      ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1 := by
  obtain ⟨-, hψn, -, -⟩ := hψ
  have hnorm : ∀ y : Sp W n, ‖pairH ψ (ofHermE (gramOf W y.1)).1 x‖ = 1 := fun y => hψn _
  have key : ∀ (h : GA D W) (y : Sp W n),
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * Ψ (mm (mt W h⁻¹) (rat y.1)) =
        pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) := by
    intro h y
    rw [ip_inv]
    exact congrArg (· * Ψ (mm (mt W h⁻¹) (rat y.1))) (pch_rat ψ x (gramOf W y.1))
  calc thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X)
      = ∫ h in 𝓕, ∑' y : Sp W n, pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) *
          Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := rfl
    _ = ∫ h in 𝓕, ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := by
        congr 1
        funext h
        congr 1
        funext y
        exact key h y
    _ = _ := exch hvol hΨ hC (fun y : Sp W n => pairH ψ (ofHermE (gramOf W y.1)).1 x) hnorm

theorem _root_.PositivityTheory.Rg.Rsw.L.thCoef : LatBound → ThCoef := by
  classical
  intro hLB D n W ψ hψ θ hθ m 𝓕 hm h𝓕 lam 𝓖 hl Ψ hΨ
  obtain ⟨C, hC⟩ := hLB D θ hθ W n Ψ hΨ
  have hvol : m 𝓕 < ⊤ := GlobalTheory.Cmp.RallisRange.vol_lt_top W hm h𝓕
  have hΨc : Continuous Ψ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Ψ hΨ).1
  have hth := fun x => thS_eq ψ hψ hvol hΨc hC x
  have hsum := summable_co hvol hΨc hC
  have hpn : ∀ (S x : hermA D n), ‖pairH ψ S x‖ = 1 := fun S x => hψ.2.1 _
  refine ⟨hvol.ne, ?_, fun β => ?_⟩
  · refine (continuous_tsum (f := fun (y : Sp W n) (x : hermA D n) => pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1)
      (fun y => (continuous_pairH hψ _).mul continuous_const) hsum
      (fun y x => by rw [norm_mul, hpn, one_mul])).congr fun x => (hth x).symm
  obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have hcoef : ∫ x in 𝓖, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) ∂lam =
      ∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0 := by
    have e1 : ∀ x : hermA D n, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) =
        ∑' y : Sp W n, co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x * (pairH ψ (ofHermE β).1 x)⁻¹) :=
      fun x => by
        rw [hth x, pch_rat ψ x β, conj_eq_inv (hpn _ _), ← tsum_mul_right]
        exact tsum_congr fun y => by ring
    rw [integral_congr_ae (ae_of_all _ e1), integral_tsum]
    · refine tsum_congr fun y => ?_
      rw [integral_const_mul]
      split_ifs with h
      · rw [h]
        have e3 : ∀ x, pairH ψ (ofHermE β).1 x * (pairH ψ (ofHermE β).1 x)⁻¹ = 1 := fun x =>
          mul_inv_cancel₀ (pairH_ne_zero hψ _ _)
        simp only [e3, integral_const, measureReal_def, Measure.restrict_apply_univ, hl.2.2]
        simp
      · rw [setIntegral_pairH hψ hl h, mul_zero]
    · intro y
      exact (continuous_const.mul ((continuous_pairH hψ _).mul
        ((continuous_pairH hψ _).inv₀ (pairH_ne_zero hψ _)))).aestronglyMeasurable
    · have e2 : ∀ y : Sp W n, ∫⁻ x in 𝓖, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
          (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ ∂lam = ‖co W m 𝓕 Ψ y.1‖ₑ := fun y => by
        have e4 : ∀ x, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
            (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ = ‖co W m 𝓕 Ψ y.1‖ₑ := fun x => by
          have h5 : ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
              (pairH ψ (ofHermE β).1 x)⁻¹)‖ = ‖co W m 𝓕 Ψ y.1‖ := by
            rw [norm_mul, norm_mul, norm_inv, hpn, hpn]
            simp
          exact (ofReal_norm _).symm.trans ((congrArg ENNReal.ofReal h5).trans (ofReal_norm _))
        simp only [e4, setLIntegral_const, hl.2.2, mul_one]
      simp only [e2]
      exact tsum_co_ne_top hvol hΨc hC
  refine ⟨fun hno => ?_, fun x₀ hr hg => ?_⟩
  · rw [hcoef]
    exact (tsum_congr fun y => if_neg fun h => hno ⟨y.1, y.2, congrArg Subtype.val h⟩).trans tsum_zero
  rw [hcoef]
  obtain ⟨-, -, -, hB, hTG, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : MeasurableConstSMul (GQ W) (GA D W) := ⟨fun γ => measurable_const_mul (γ : GA D W)⟩
  have : SMulInvariantMeasure (GQ W) (GA D W) m := ⟨fun γ s _ => measure_preimage_mul m (γ : GA D W) s⟩
  obtain ⟨e, he⟩ := orbit_equiv W x₀ hr
  let T := {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀}
  let s : Set (Sp W n) := {y | gramOf W y.1 = β}
  let q : s ≃ T :=
    { toFun := fun y => ⟨y.1.1, y.1.2, (congrArg Subtype.val y.2 : gramQ W y.1.1 = β.1).trans hg.symm⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, Subtype.ext (t.2.2.trans hg)⟩
      left_inv := fun y => rfl
      right_inv := fun t => rfl }
  have hpt : ∀ (γ : GQ W) (h : GA D W), Ψ (mm (mt W h⁻¹) (rat (e γ).1)) = Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) :=
    fun γ h => by
      rw [he]
      show Ψ (mm (mt W h⁻¹) (mm (mt W γ) (rat x₀))) = Ψ (mm (mt W (((γ : GA D W))⁻¹ * h)⁻¹) (rat x₀))
      rw [mul_inv_rev, inv_inv, mt_mul]
      exact congrArg Ψ (Matrix.mul_assoc _ _ _).symm
  have hint : Integrable (fun h : GA D W => Ψ (mm (mt W h⁻¹) (rat x₀))) m := by
    refine ⟨(cont_term hΨc x₀).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, h𝓕.lintegral_eq_tsum']
    let g : T → ℝ≥0∞ := fun t => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat t.1))‖ₑ ∂m
    have hinj : Function.Injective fun t : T => (⟨t.1, t.2.1⟩ : Sp W n) := fun t t' h =>
      Subtype.ext (by simpa using congrArg Subtype.val h)
    calc ∑' γ : GQ W, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀))‖ₑ ∂m = ∑' γ, g (e γ) :=
          tsum_congr fun γ => by simp only [g, hpt]
      _ = ∑' t, g t := e.tsum_eq g
      _ ≤ ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun y : Sp W n => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m)
      _ < ⊤ := lint_fin hvol hΨc hC
  calc (∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0)
      = ∑' y : Sp W n, s.indicator (fun y => co W m 𝓕 Ψ y.1) y := tsum_congr fun y => by
        simp only [Set.indicator_apply, s, Set.mem_ofPred_eq]
    _ = ∑' y : s, co W m 𝓕 Ψ y.1.1 := (tsum_subtype s _).symm
    _ = ∑' t : T, co W m 𝓕 Ψ t.1 := q.tsum_eq (fun t => co W m 𝓕 Ψ t.1)
    _ = ∑' γ : GQ W, co W m 𝓕 Ψ (e γ).1 := (e.tsum_eq (fun t => co W m 𝓕 Ψ t.1)).symm
    _ = ∑' γ : GQ W, ∫ h in 𝓕, Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) ∂m :=
        tsum_congr fun γ => integral_congr_ae (ae_of_all _ fun h => hpt γ h)
    _ = orb W m Ψ x₀ := (h𝓕.integral_eq_tsum' _ hint).symm

end PositivityTheory.Rg.Rsw.L.LThCoef

end
