import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistSeriesConj

set_option maxHeartbeats 4000000 in

theorem conj_series_twisted : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κw v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → PhaseTie T R κw v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → FixDat B τ → ∀ (ω ω' : PairRep (Vc D i) (Wc D i)) (ψ ψ' : Twist D Circle) (t t' : T0), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' → ψ.Good → ψ'.Good → B.admitted ψ.Q → IsTupOf R B ψ t → IsTupOf R B ψ' t' → ConjChar τ ψ ψ' → ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κw i) τ ζ (ph i • series B.F ω (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) (ph i • series B.F ω' (B.vecFlat ψ') h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κw v₀ O ph hnV hC hT0 hFW hio hQG i hOP hPT c hc u hu B hB hBo τ hτ hfix ω ω' ψ ψ' t t'
    hω hω' hψ hψ' hQ ht ht' hcc
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κw v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κw v₀ hC hTie hio O i hOP)).1
  obtain ⟨ζ0, hζ0, hgb⟩ := GlobalTheory.T.conjugate_thetaSeries_flatDatum_rootOfUnity hCI D G Pl0 T0 A T R F κw v₀ O ph hnV hC hT0 ⟨fw⟩ hio hQG i hOP hPT c hc u hu τ hτ
  have hQ' : B.admitted ψ'.Q := by rw [hcc.1]; exact hQ
  obtain ⟨f, hf⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t).1
  obtain ⟨f', hf'⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t').1
  obtain ⟨s, hs⟩ := hgb t t' (conjTup_of R ht ht' hcc hfix) f f' hf hf'
  set ζ := ζ0 * ((R.xi t' s : Circle) : ℂ) with hζd
  have hζ : ζ ≠ 0 := by
    obtain ⟨n, hn, hpow⟩ := hζ0
    refine mul_ne_zero (fun h0 => ?_) (Circle.coe_ne_zero _)
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  have hL := hC.lev
  obtain ⟨n, hn, hod⟩ := hL.xi_fin t'
  have hxn : (R.xi t' s : Circle) ^ n = 1 := GlobalTheory.OneCover.xi_pow_eq_one D (R.xi t') _ (hL.xi t') n hod s
  have hxc : ((R.xi t' s : Circle) : ℂ) ^ n = 1 := by
    have := congrArg (fun z : Circle => (z : ℂ)) hxn
    simpa using this
  have hroot : IsRoot1 ζ := by
    obtain ⟨m, hm, hpow⟩ := hζ0
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [hζd, mul_pow, pow_mul, hpow, one_pow, one_mul, pow_mul', hxc, one_pow]
  obtain ⟨hfin, ⟨k, hk⟩, hsum⟩ := GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A _ R F hC i B hB hBo
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  obtain ⟨hk0, -⟩ := hsum k fun p => (hk p).1
  choose g0 hg0 using hk0
  have hlift : ∀ p, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm (g0 p))) (k p) := fun p => by
    exact (congrArg (fun z => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) z (k p))
      (R.eG.apply_symm_apply (g0 p))).mpr (hg0 p)
  have hrt : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∀ p, ConjFun (O i) (κw i) τ ζ
      (fun g => ph i * ser R i t f u h (c x) (g * k p)) (fun g => ph i * ser R i t' f' u h (c x') (g * k p)) :=
    fun h hh x x' hx p => GlobalTheory.ConjGen.conjFun_mul_right (O i) (κw i) hτ hE (hlift p) hζ (hs h hh x x' hx)
  have hcp : ∀ p, τ ((((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) = (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) := fun p => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix.2.1 p]
  have hx₀ : ConjVec i τ (0 : VsV D i ℂ) 0 := by
    unfold ConjVec
    simp
  have hCF0 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hs 1 (one_mem _) 0 0 hx₀)
  refine ⟨ζ, hroot, fun h hh x x' hx => ?_⟩
  have e1 : (ph i • series B.F ω (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) =
      fun g => ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * (ph i * ser R i t f u h (c x) (g * k p)) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ConjGen.series_weil hB hQ hω (hBo.isWeil hC.thP.ωP ht),
      GlobalTheory.ConjGen.series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : (ph i • series B.F ω' (B.vecFlat ψ') h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) =
      fun g => ∑ p, τ (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * (ph i * ser R i t' f' u h (c x') (g * k p)) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ConjGen.series_weil hB hQ' hω' (hBo.isWeil hC.thP.ωP ht'),
      GlobalTheory.ConjGen.series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcp]
    ring
  rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
  exact GlobalTheory.ConjGen.cf_sum hζ hCF0 _ _ _ fun p => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hrt h hh x x' hx p)

end GlobalTheory.TwistSeriesConj
