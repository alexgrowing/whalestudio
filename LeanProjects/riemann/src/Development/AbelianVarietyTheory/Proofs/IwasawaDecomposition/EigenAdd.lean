import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLogTheta

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem eigen_add (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c d : G → R) (t : R) (ht : t ≠ 0)
    (hθt : θ t = 0) (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * (y + d g * t ^ (n + 1))) →
      ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w + d g * t := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow, map_add, map_mul, map_pow, hθt,
        zero_pow (Nat.succ_ne_zero _), mul_zero, add_zero]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_form (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.BdR l) (d : GQ l → Per.BdRp l)
    (hb : ∀ g : GQ l, Per.σD g b = b + algebraMap (Per.BdRp l) (Per.BdR l) (d g * C.j C.t)) :
    ∃ (a : ℚ_[l]) (v : Per.BdRp l), b = algebraMap (Per.BdRp l) (Per.BdR l)
      (C.o (algebraMap ℚ_[l] (Om l) a) + C.j C.t * v) := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C (botExt l)
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l (botExt l)
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  let c : GQ l → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : GQ l, Per.σDp g t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, InvDR.j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hθt : Per.θD l t = 0 := (hker t).2 ht1
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : GQ l, Per.σC g x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g _ => by simpa only [hθc] using h g
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : GQ l, Per.σDp g y = c g ^ n * (y + d g * t ^ (n + 1)) := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g]
    simp only [map_mul, map_pow, map_add]
    rw [← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_add (Per.θD l) (fun g : GQ l => Per.σDp g) (fun g => Per.σC g) c d t ht0
    hθt hker' hc (fun g y => hθ g y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g _ => by
    rw [← hθ, hw' g, map_add, map_mul, hθt, mul_zero, add_zero]
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hk
  obtain ⟨v, hv⟩ := hker' (w - C.o (algebraMap ℚ_[l] (Om l) a))
    (by rw [map_sub, C.o_sec.th, hkθ, sub_self])
  refine ⟨a, v, ?_⟩
  rw [← hv, add_sub_cancel]
  have : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (b : P.R.B) (c : GQ l → ℚ_[l]), (∀ g : GQ l, P.actQ g b - b = c g • P.tB) →
    ∃ a : ℚ_[l], P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) ∈ (P.PD (botExt l)).Fil 0 := by
  intro l _ P AI T b c hb
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have hι : ∀ g : GQ l, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun g => by
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at this
    exact this.symm
  have ht : T.eD (P.ιB P.tB) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) := by
    rw [hC.ι, hC.t, Core.tB, C.ι_j]
  have hq : ∀ a : ℚ_[l], T.eD (P.ιB (algebraMap ℚ_[l] P.R.B a)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (algebraMap ℚ_[l] (Om l) a)) := fun a => by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hC.o]
    rfl
  obtain ⟨a, v, h⟩ := core_form l C (T.eD (P.ιB b)) (fun g => C.o (algebraMap ℚ_[l] (Om l) (c g))) fun g => by
    rw [← T.actD, hι, map_mul, ← hq, ← ht, ← map_mul, ← map_mul, ← map_add, ← map_add, ← Algebra.smul_def,
      ← hb, add_sub_cancel]
  refine ⟨a, ?_⟩
  have h1 : T.eD (P.ιB (tInv P)) * algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) = 1 := by
    rw [← ht, ← map_mul, ← map_mul, tInv_mul, map_one, map_one]
  have h2 : T.eD (P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P)) =
      algebraMap (Per.BdRp l) (Per.BdR l) v := by
    rw [map_mul, map_mul, map_sub, map_sub, hq, h, map_add, map_mul]
    linear_combination algebraMap (Per.BdRp l) (Per.BdR l) v * h1
  rw [T.fil, h2]
  have h3 : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
    have := (T.fil (botExt l) 0 1).1 (P.PD (botExt l)).one_mem
    rwa [map_one] at this
  have h4 := (Per.FilD l 0).smul_mem v h3
  rwa [Algebra.smul_def, mul_one] at h4

end GlobalTheory.Pst.NoLogTheta
