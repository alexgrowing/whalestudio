import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.OpsRows

variable {D : D7}

def rt (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun F h => F (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem sum_rt (V : HSp D) (B : Finset (GA D V)) : ∑ γ ∈ B, rt V γ = heckeLin V B := by
  ext F h
  simp [heckeLin, rt, LinearMap.sum_apply, Finset.sum_apply]

theorem opOf_rt (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : opOf (rt V) P c = hk V P c := by
  unfold opOf hk
  exact Finsupp.sum_congr fun d _ => by rw [sum_rt]

theorem hk_single (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : hk V P (Finsupp.single d 1) = heckeLin V (rep V P d) := by
  unfold hk
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem sphOp_rep {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold rep
  rw [dif_pos h]
  exact h.choose_spec

theorem rep_of_not {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : rep V P d = ∅ := by
  unfold rep
  rw [dif_neg h]

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse]

theorem eq_conj {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') : P' = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
  refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
  obtain ⟨c', h1, h2⟩ := h c hc
  have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
  show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
  rwa [this]

theorem rep_supp {V : HSp D} {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) (d : List ℤ) :
    ∀ γ ∈ rep V P d, SuppF V f γ := by
  by_cases hd : IsLab V P d
  · obtain ⟨e', f', -, -, -, h', -, -, -, -, -, -, -, hs, -⟩ := sphOp_rep hd
    obtain ⟨-, rfl⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f h).2.2.2.1 e' f' h'
    exact hs
  · simp [rep_of_not hd]

theorem hk_comm (V : HSp D) (P P' : Pl D.host.E) (d d' : List ℤ) (u : GA D V → ℂ) (hu : ∀ k ∈ hyp V P, rt V k u = u) :
    hk V P (Finsupp.single d 1) (hk V P' (Finsupp.single d' 1) u) =
      hk V P' (Finsupp.single d' 1) (hk V P (Finsupp.single d 1) u) := by
  have key := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨e, f, h⟩ := key.2.1 P
  obtain ⟨e', f', h'⟩ := key.2.1 P'
  have h1 := key.2.2.1 P e f h
  rcases h1.2.2.2.2 P' e' f' h' with h0 | ⟨-, rfl | hc⟩
  · rw [hk_single, hk_single]
    funext g
    simp only [heckeLin_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
    rw [mul_assoc, mul_assoc, ((key.1 f h1.1 h1.2.1).2.2 f' a b h0 (rep_supp h d a ha) (rep_supp h' d' b hb)).eq]
  · simp only [← opOf_rt]
    exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V _ _ _ _ (rt V) u hu
  · obtain rfl := eq_conj hc
    simp only [← opOf_rt]
    rw [(GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 _ _ (rt V) u hu,
      (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 _ _ (rt V) _ ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.1 _ _ (rt V) u hu)]
    exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V _ _ _ _ (rt V) u hu

variable {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S}

theorem mult_lev {J : Set (GA D V)} {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro v k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, mul_add]
  | smul a x _ hx => simp [hx, mul_left_comm]

theorem postOn_hk (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = c.sum fun d z => z • postOn M (hk V P (Finsupp.single d 1)) U := by
  ext1 v
  simp only [postOn_apply, hk_single, Finsupp.sum, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  simp only [hk, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

theorem exists_lift {X : Type} [AddCommGroup X] [Module ℂ X] (H : HMod X) (hi : Function.Injective H.e) (L : X →ₗ[ℂ] X)
    (hL : ∀ x, L (H.e x) ∈ LinearMap.range H.e) : ∃ h : Module.End ℂ H.H, ∀ x, H.e (h x) = L (H.e x) := by
  refine ⟨(LinearEquiv.ofInjective H.e hi).symm.toLinearMap ∘ₗ (L ∘ₗ H.e).codRestrict _ hL, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective H.e hi).apply_symm_apply ((L ∘ₗ H.e).codRestrict _ hL x))
  exact this

theorem exists_ops (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕) (H : HMod (MMap M)) (W : Submodule ℂ (MMap M)) (hH : H.Is W (ipM M μ 𝓕))
    (hW : W ≤ Mult θ M (J : Set (GA D V)) χ) (ok : Pl D.host.E → Prop)
    (hfull : ∀ P d B, Hecke₂ V (J : Set (GA D V)) χ SF P d B ↔ ok P ∧ SphOp V P d B)
    (hhyp : ∀ P, ok P → ∀ k ∈ hyp V P, k ∈ J ∧ χ k = 1)
    (hkeep : ∀ P, ok P → ∀ c, ∀ U ∈ W, postOn M (hk V P c) U ∈ W) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H.H,
      (∀ P, ok P → ∀ c x, H.e (h P c x) = postOn M (hk V P c) (H.e x)) ∧ NormalFam ok h ∧
      (⨆ a, (partFull θ M (J : Set (GA D V)) χ SF a).comap H.e) = ⊤ ∧
      (∀ a P, ok P → ∀ cc, ∀ x ∈ (partFull θ M (J : Set (GA D V)) χ SF a).comap H.e, h P cc x = evC V P (a P) cc • x) ∧
      ∀ (a : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, ok P → IsLab V P d → h P (Finsupp.single d 1) x = a P d • x) →
        x ∈ (partFull θ M (J : Set (GA D V)) χ SF a).comap H.e := by
  obtain ⟨hi, hr, hip⟩ := hH
  have hmW : ∀ x, H.e x ∈ W := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hex : ∀ P c, ∃ h : Module.End ℂ H.H, ok P → ∀ x, H.e (h x) = postOn M (hk V P c) (H.e x) := by
    intro P c
    by_cases hP : ok P
    · obtain ⟨h, hh⟩ := exists_lift H hi (postOn M (hk V P c)) fun x => hr ▸ hkeep P hP c _ (hmW x)
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose h hh using hex
  have hfix : ∀ P, ok P → ∀ x v, ∀ k ∈ hyp V P, rt V k (H.e x v) = H.e x v := by
    intro P hP x v k hk
    funext g
    have := mult_lev (hW (hmW x)) v k (hhyp P hP k hk).1 g
    rwa [(hhyp P hP k hk).2, one_mul] at this
  have hlin : ∀ P, ok P → ∀ c, h P c = c.sum fun d z => z • h P (Finsupp.single d 1) := by
    intro P hP c
    ext x
    apply hi
    rw [hh P c hP, postOn_hk]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hh P _ hP]
  have hzero : ∀ P, ok P → ∀ d, ¬ IsLab V P d → h P (Finsupp.single d 1) = 0 := by
    intro P hP d hd
    ext x
    apply hi
    rw [hh P _ hP, hk_single, rep_of_not hd, LinearMap.zero_apply, map_zero]
    ext v g
    simp [postOn_apply, heckeLin_apply]
  have hcomm1 : ∀ P P', ok P → ok P' → ∀ d d', Commute (h P (Finsupp.single d 1)) (h P' (Finsupp.single d' 1)) := by
    intro P P' hP hP' d d'
    ext x
    apply hi
    simp only [Module.End.mul_apply, hh P _ hP, hh P' _ hP']
    ext1 v
    exact hk_comm V P P' d d' _ (hfix P hP x v)
  have hadj1 : ∀ P, ok P → ∀ d, LinearMap.adjoint (h P (Finsupp.single d 1)) = h P (Finsupp.single (dualLab d) 1) := by
    intro P hP d
    have hdd := ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d).1
    by_cases hd : IsLab V P d
    · symm
      rw [LinearMap.eq_adjoint_iff]
      intro x y
      have e1 : ∀ d z, H.e (h P (Finsupp.single d 1) z) = heckeOn M (rep V P d) (H.e z) := fun d z => by
        rw [hh P _ hP, hk_single]; rfl
      rw [hip, hip, e1, e1]
      refine GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel D V S θ M J χ SF μ 𝓕 hθ hμ h𝓕 hS P (dualLab d) _ _ ((hfull _ _ _).2 ⟨hP, sphOp_rep (hdd.1 hd)⟩)
        ((hfull _ _ _).2 ⟨hP, ?_⟩) _ (hW (hmW x)) _ (hW (hmW y)) (e1 _ x ▸ hW (hmW _)) (e1 _ y ▸ hW (hmW _))
      rw [dualLab_dualLab]
      exact sphOp_rep hd
    · rw [hzero P hP d hd, hzero P hP _ (fun h' => hd (hdd.2 h')), map_zero]
  have hin : ∀ (a : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, ok P → IsLab V P d → h P (Finsupp.single d 1) x = a P d • x) →
      x ∈ (partFull θ M (J : Set (GA D V)) χ SF a).comap H.e := by
    intro a x hx
    rw [Submodule.mem_comap, mem_partFull]
    refine ⟨hW (hmW x), fun P d B hB v => ?_⟩
    obtain ⟨hP, hB⟩ := (hfull _ _ _).1 hB
    have e1 := ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 d B hB).2 _ (rt V) _ (hfix P hP x v)
    rw [← LinearMap.sum_apply, sum_rt, opOf_rt] at e1
    have e2 := hh P (Finsupp.single d 1) hP x
    rw [hx P d hP ⟨B, hB⟩, map_smul] at e2
    rw [e1]
    exact (congrArg (fun U : MMap M => U v) e2).symm
  refine ⟨h, fun P hP c => hh P c hP, ⟨fun P P' hP hP' c c' => ?_, fun P hP c => ?_⟩, ?_, fun a P hP cc x hx => ?_, hin⟩
  · rw [hlin P hP c, hlin P' hP' c']
    exact Commute.sum_left _ _ _ fun d _ => Commute.sum_right _ _ _ fun d' _ =>
      ((hcomm1 P P' hP hP' d d').smul_left _).smul_right _
  · rw [hlin P hP c, hlin P hP (dualC _), dualC, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul]),
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [LinearEquiv.map_smulₛₗ, hadj1 P hP]
    rfl
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition
      (fun i : {P // ok P} × List ℤ => h i.1.1 (Finsupp.single i.2 1)) (fun i j => hcomm1 _ _ i.1.2 j.1.2 _ _)
      (fun i => ⟨(i.1, dualLab i.2), (hadj1 _ i.1.2 _).symm⟩)
    rw [eq_top_iff, ← h2]
    refine iSup_le fun x y hy => ?_
    classical
    refine Submodule.mem_iSup_of_mem (fun P d => if hP : ok P then x (⟨P, hP⟩, d) else 0) (hin _ y fun P d hP _ => ?_)
    rw [h1, Submodule.mem_iInf] at hy
    rw [dif_pos hP]
    exact Module.End.mem_eigenspace_iff.1 (hy (⟨P, hP⟩, d))
  · rw [Submodule.mem_comap, mem_partFull] at hx
    rw [hlin P hP cc, evC, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : IsLab V P d
    · rw [if_pos hd, LinearMap.smul_apply, mul_smul]
      congr 1
      apply hi
      rw [hh P _ hP, hk_single, map_smul]
      ext1 v
      exact hx.2 P d _ ((hfull _ _ _).2 ⟨hP, sphOp_rep hd⟩) v
    · rw [if_neg hd, hzero P hP d hd]
      simp

theorem exists_opsE : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∃ h, IsOpsE R h ∧ NormalFam (Good R A.μ0) h ∧ (⨆ c, EEc R SF c) = ⊤ ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ EEc R SF c, h P cc x = evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, Good R A.μ0 P → IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ EEc R SF c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF
  obtain ⟨hQ, hg, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have lev := fun P (hP : Good R A.μ0 P) => GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hP).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := exists_ops (θ := R.θ) (M := R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF R.ν0 R.fd0 hC.models.inf hC.models.ν0.1.1 hC.models.ν0.2 hS.2.1 R.HE _ hC.models.HE
    (goodPart_le _ _ _ _ _) (Good R A.μ0)
    (fun P d B => ⟨fun hB => by
        have hP : Good R A.μ0 P := by
          obtain ⟨_, _, _, _, hO, -⟩ := hB
          exact (hoff SF hSF P).1 hO
        exact ⟨hP, (((lev P hP).2.1 SF d B).1 hB).2⟩,
      fun hB => ((lev P hB.1).2.1 SF d B).2 ⟨(hoff SF hSF P).2 hB.1, hB.2⟩⟩)
    (fun P hP => (lev P hP).1)
    (fun P hP c U hU => by
      obtain ⟨hU1, hU2⟩ := (mem_goodPart _ _ _ _ _ _).1 hU
      refine (mem_goodPart _ _ _ _ _ _).2 ⟨(lev P hP).2.2.2.2 _ _ _ c hC.models.inf U hU1, fun v => ?_⟩
      have hfix : ∀ k ∈ hyp (Yc D 0) P, ∀ g, U v (g * k) = U v g := fun k hk g => by
        rw [mult_lev hU1 v k ((lev P hP).1 k hk).1 g, ((lev P hP).1 k hk).2, one_mul]
      rw [postOn_apply]
      conv_rhs => rw [← hU2 v]
      simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      exact (lev P hP).2.2.2.1 c _ _ hfix)
  refine ⟨h, h1, h2, ?_, fun c => h4 _, fun c => h5 _⟩
  rw [eq_top_iff, ← h3]
  refine iSup_le fun a => le_iSup_of_le (fun P d => a P (dualLab d)) (le_of_eq ?_)
  simp only [EEc, partDual, dualLab_dualLab]
  rfl

end GlobalTheory.Hk3.OpsRows

end
