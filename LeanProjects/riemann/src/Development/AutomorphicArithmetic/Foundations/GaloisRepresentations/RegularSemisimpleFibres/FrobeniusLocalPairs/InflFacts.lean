import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {k : Type} [Field k] [ValuativeRel k] {F₀ : Type} [Field F₀] {n : ℕ}

private theorem incl_inj :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := fun a b h =>
  Units.ext <| Matrix.ext fun i j => Subtype.ext
    (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h)

private theorem infl_incl (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y' : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' =
      GeneralLinearGroup.map (algebraMap 𝒪[k] k) y := ⟨y, rfl⟩
  unfold infl
  rw [dif_pos h, incl_inj h.choose_spec]

private theorem infl_not_mem (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {x : GL (Fin n) k}
    (hx : x ∉ KO k n) : infl rd fb x = 0 :=
  dif_neg hx

private theorem principal_congruence_le_maximal_compact (rd : 𝒪[k] →+* F₀) : K1 rd n ≤ KO k n := by
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

private theorem infl_left (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (c * x) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, one_mul]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)) h)

private theorem infl_right (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (x * c) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, mul_one]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem h ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)))

private theorem rd_eq_zero (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (x : 𝒪[k])
    (hx : valuation k (x : k) < 1) : rd x = 0 := by
  by_contra h0
  obtain ⟨y, hy⟩ := hrd (rd x)⁻¹
  have hxy : rd (1 - x * y) = 0 := by
    rw [map_sub, map_mul, hy, mul_inv_cancel₀ h0, map_one, sub_self]
  have hyle : valuation k (y : k) ≤ 1 := y.2
  have hlt : valuation k ((x * y : 𝒪[k]) : k) < 1 := by
    rw [Subring.coe_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hx hyle
  have hval : valuation k ((1 - x * y : 𝒪[k]) : k) = 1 := by
    have : ((1 - x * y : 𝒪[k]) : k) = 1 - ((x * y : 𝒪[k]) : k) := by push_cast; ring
    rw [this, Valuation.map_one_sub_of_lt _ hlt]
  set u : 𝒪[k] := 1 - x * y with hu
  have hu0 : (u : k) ≠ 0 := fun h => by rw [h, map_zero] at hval; exact zero_ne_one hval
  have hinv : valuation k (u : k)⁻¹ ≤ 1 := by rw [map_inv₀, hval, inv_one]
  have hone : u * ⟨(u : k)⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hu0)
  have := congrArg rd hone
  rw [map_mul, hxy, zero_mul, map_one] at this
  exact zero_ne_one this

end Alg

theorem inflFacts :
    UpperTheory.Gal.InertialTypesAlt.L.InflFacts := by
  intro k _ _ _ _ F₀ _ _ rd hrd n
  have hKO : KO k n = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl
  have hU : KO k n = PositivityTheory.Rg.Tf.Loc.unitGL k := rfl
  have hopenKO : IsOpen (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isOpen_integralGL k n
  have hcompKO : IsCompact (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n
  obtain ⟨r, hr0, hr1⟩ : ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 := by
    obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ, zero_lt_iff.2 h0, h⟩
    · exact ⟨γ⁻¹, inv_pos.2 (zero_lt_iff.2 h0), inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨B, hB, hBo, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r hr0 hr1
  have hent : ∀ g ∈ B, ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have hb : valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : g ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    rw [← sub_add_cancel ((g : Matrix (Fin n) (Fin n) k) i j) ((1 : Matrix (Fin n) (Fin n) k) i j)]
    exact Valuation.map_add_le _ (hb.trans hr1.le) h1
  have hBK : B ≤ K1 rd n := by
    intro g hg
    have hgO : g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n :=
      (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k n).2 ⟨hent g hg, hent _ (B.inv_mem hg)⟩
    obtain ⟨y, rfl⟩ : g ∈ KO k n := hgO
    refine ⟨y, ?_, rfl⟩
    change GeneralLinearGroup.map rd y = 1
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hb : valuation k (((GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j -
        (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : GeneralLinearGroup.map (algebraMap 𝒪[k] k) y ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h0 := rd_eq_zero rd hrd ((y : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) (by
      refine lt_of_le_of_lt (le_of_eq ?_) (hb.trans_lt hr1)
      congr 1
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> rfl)
    rw [map_sub, sub_eq_zero] at h0
    simp only [GeneralLinearGroup.map_apply, Units.val_one]
    rw [h0]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hopen : IsOpen (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isOpen_mono hBK hBo
  have hclosed : IsClosed (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopen
  have hcomp : IsCompact (K1 rd n : Set (GL (Fin n) k)) :=
    hcompKO.of_isClosed_subset hclosed (principal_congruence_le_maximal_compact rd)
  have hclosedKO : IsClosed (KO k n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopenKO
  have hsupp : ∀ fb : GL (Fin n) F₀ → ℂ, HasCompactSupport (infl rd fb) := fun fb =>
    HasCompactSupport.intro' hcompKO hclosedKO fun x hx => infl_not_mem rd fb hx
  refine ⟨hU, hopen, hcomp, principal_congruence_le_maximal_compact rd, fun fb y => infl_incl rd fb y, fun fb => ⟨⟨hsupp fb, fun c hc x => ⟨infl_left rd fb hc x, infl_right rd fb hc x⟩⟩, ⟨?_, hsupp fb⟩, ?_⟩⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun z => x⁻¹ * z) ⁻¹' (K1 rd n : Set (GL (Fin n) k)), hopen.preimage (continuous_const.mul continuous_id), by simp [(K1 rd n).one_mem], fun z hz => ?_⟩
    have := infl_right rd fb hz x
    simpa using this
  · intro x hx
    by_contra h
    exact hx (infl_not_mem rd fb h)

end UpperTheory.Gal.InertialTypesAlt.L
