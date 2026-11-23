import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphOpsModel

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sphOp_rep {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  rw [dif_pos h]
  exact h.choose_spec

theorem heckeOn_rep_of_not (M : DSModel V S) {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) (U : MMap M) :
    heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
  ext v g
  unfold GlobalTheory.Hk3.rep
  rw [dif_neg h, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
  rfl

theorem postOn_single (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  rw [GlobalTheory.LevOp.postOn_hk, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
    one_smul]

section Model

variable {M : DSModel V S} {HM : HMod (MMap M)} {P : Pl D.host.E} {h : (List ℤ →₀ ℂ) → Module.End ℂ HM.H}

theorem op_eq_sum (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    (c : List ℤ →₀ ℂ) : h c = c.sum fun d z => z • h (Finsupp.single d 1) := by
  refine LinearMap.ext fun x => inj ?_
  rw [hh, GlobalTheory.LevOp.postOn_hk, Finsupp.sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, map_smul, hh, postOn_single]

theorem op_single_of_not (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {d : List ℤ} (hd : ¬ IsLab V P d) : h (Finsupp.single d 1) = 0 := by
  refine LinearMap.ext fun x => inj ?_
  rw [hh, postOn_single, heckeOn_rep_of_not M hd, LinearMap.zero_apply, map_zero]

theorem op_eigen (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {a : List ℤ → ℂ} {x : HM.H} (hx : ∀ d, IsLab V P d → h (Finsupp.single d 1) x = a d • x) (c : List ℤ →₀ ℂ) :
    h c x = evC V P a c • x := by
  rw [op_eq_sum inj hh, evC, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply]
  split_ifs with hd
  · rw [hx d hd, mul_smul]
  · rw [op_single_of_not inj hh hd, LinearMap.zero_apply, smul_zero, zero_smul]

end Model

theorem exists_ops (θ : InfFam D) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (a : ℂ) (ok : Pl D.host.E → Prop)
    (hM : HM.Is (Mult θ M (J : Set (GA D V)) χ) fun T T' => a * ipM M μ 𝓕 T T') (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕)
    (hfull : ∀ P, ok P → ∀ d B, Hecke₂ V (J : Set (GA D V)) χ ∅ P d B ↔ SphOp V P d B)
    (hkeep : ∀ P, ok P → ∀ c, ∀ U ∈ Mult θ M (J : Set (GA D V)) χ, postOn M (hk V P c) U ∈ Mult θ M (J : Set (GA D V)) χ) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ HM.H,
      (∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x)) ∧ NormalFam ok h := by
  obtain ⟨inj, hr, hip⟩ := hM
  have hmem : ∀ x, HM.e x ∈ Mult θ M (J : Set (GA D V)) χ := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hex : ∀ P c, ∃ h : Module.End ℂ HM.H, ok P → ∀ x, HM.e (h x) = postOn M (hk V P c) (HM.e x) := fun P c => by
    by_cases hP : ok P
    · obtain ⟨h, hh⟩ := exists_lift HM.e inj (postOn M (hk V P c)) fun x => hr ▸ hkeep P hP c _ (hmem x)
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose h hh using hex
  have hh' : ∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x) := fun P hP c => hh P c hP
  have hdual : ∀ P, ok P → ∀ d, IsLab V P d → IsLab V P (dualLab d) := fun P hP d ⟨B, hB⟩ => by
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (GlobalTheory.HeckeAdjoint.realUnif D P) ((hfull P hP d B).2 hB)
    exact ⟨B', (hfull P hP _ B').1 hB'⟩
  refine ⟨h, hh', fun P P' hP hP' c c' => ?_, fun P hP c => ?_⟩
  · rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P' hP') c']
    refine Commute.sum_left _ _ _ fun d _ => Commute.sum_right _ _ _ fun d' _ => ?_
    refine Commute.smul_left (Commute.smul_right ?_ _) _
    by_cases hd : IsLab V P d
    · by_cases hd' : IsLab V P' d'
      · refine LinearMap.ext fun x => inj ?_
        rw [Module.End.mul_apply, Module.End.mul_apply, hh' P hP, hh' P' hP', hh' P' hP', hh' P hP]
        simp only [postOn_single]
        exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (GlobalTheory.HeckeAdjoint.realUnif D P)
          ((hfull P hP d _).2 (sphOp_rep hd)) ((hfull P' hP' d' _).2 (sphOp_rep hd'))
          (((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v)
      · rw [op_single_of_not inj (hh' P' hP') hd']
        exact Commute.zero_right _
    · rw [op_single_of_not inj (hh' P hP) hd]
      exact Commute.zero_left _
  · have key : ∀ d, LinearMap.adjoint (h P (Finsupp.single d 1)) = h P (Finsupp.single (dualLab d) 1) := fun d => by
      by_cases hd : IsLab V P d
      · symm
        rw [LinearMap.eq_adjoint_iff]
        intro x y
        rw [hip, hip, hh' P hP, hh' P hP, postOn_single, postOn_single]
        refine congrArg (a * ·) (GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel D V S θ M J χ ∅ μ 𝓕 hθ hμ h𝓕 hS P (dualLab d) _ _
          ((hfull P hP _ _).2 (sphOp_rep (hdual P hP d hd))) ?_ _ (hmem x) _ (hmem y) ?_ ?_)
        · rw [dualLab_dualLab]
          exact (hfull P hP _ _).2 (sphOp_rep hd)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem x)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem y)
      · have hd' : ¬ IsLab V P (dualLab d) := fun h' => hd (dualLab_dualLab d ▸ hdual P hP _ h')
        rw [op_single_of_not inj (hh' P hP) hd, op_single_of_not inj (hh' P hP) hd', map_zero]
    rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P hP) (dualC _), dualC,
      Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • h P (Finsupp.single d 1)) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_mapRange_index (h := fun d (z : ℂ) => z • h P (Finsupp.single (dualLab d) 1)) (fun _ => zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [LinearEquiv.map_smulₛₗ, key]
    rfl

theorem parts_of_projector {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ok : Pl D.host.E → Prop) (lab : Pl D.host.E → List ℤ → Prop) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hN : NormalFam ok h) (p : Module.End ℂ H) (hp : p * p = p) (he : ∀ P, ok P → ∀ cc, Commute (h P cc) p)
    (W : (Pl D.host.E → List ℤ → ℂ) → Submodule ℂ H)
    (hW : ∀ c x, x ∈ W c ↔ p x = x ∧ ∀ P d, ok P → lab P d → h P (Finsupp.single d 1) x = c P d • x) :
    (⨆ c, W c) = LinearMap.range p ∧
      ∀ c (g : Module.End ℂ H), Commute p g → (∀ P, ok P → ∀ cc, Commute (h P cc) g) → (W c).map g ≤ W c := by
  refine ⟨le_antisymm (iSup_le fun c x hx => ⟨x, ((hW c x).1 hx).1⟩) ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition
      (fun j : {j : Pl D.host.E × List ℤ // ok j.1} => h j.1.1 (Finsupp.single j.1.2 1))
      (fun j k => hN.1 _ _ j.2 k.2 _ _) (fun j => ⟨⟨(j.1.1, dualLab j.1.2), j.2⟩, by
        rw [hN.2 _ j.2, dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single, star_one]⟩)
    rw [LinearMap.range_eq_map, ← h2, Submodule.map_iSup]
    refine iSup_le fun y => ?_
    classical
    refine le_iSup_of_le (fun P d => if hP : ok P then y ⟨(P, d), hP⟩ else 0) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [h1, SetLike.mem_coe, Submodule.mem_iInf] at hx
    refine (hW _ _).2 ⟨LinearMap.congr_fun hp x, fun P d hP _ => ?_⟩
    have h3 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d), hP⟩)
    have h4 : h P (Finsupp.single d 1) (p x) = p (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (he P hP _).eq x
    rw [dif_pos hP, h4, ← map_smul]
    exact congrArg _ h3
  · rintro c g hg hg' _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := (hW c x).1 hx
    refine (hW _ _).2 ⟨?_, fun P d hP hd => ?_⟩
    · have h4 : p (g x) = g (p x) := LinearMap.congr_fun hg.eq x
      rw [h4, h1]
    · have h4 : h P (Finsupp.single d 1) (g x) = g (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (hg' P hP _).eq x
      rw [h4, h2 P d hP hd, map_smul]

theorem sphericalOperators_forms_on_rank_space_normal_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i, ∃ h, IsOpsW R i h ∧ NormalFam (Good R A.μ0) h ∧ (∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g)) ∧ (⨆ c, Wcc R SF i c) = LinearMap.range (eH R i) ∧ (∀ c g, (Wcc R SF i c).map (R.gW i (sg0 D A) g) ≤ Wcc R SF i c) ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ Wcc R SF i c, h P cc x = evC (Wc D i) P (c P) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, eH R i x = x → (∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x) → x ∈ Wcc R SF i c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have hM := hC.models.HW i (sg0 D A)
  have inj : Function.Injective (R.HW i (sg0 D A)).e := hM.1
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hM.2.1 ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  obtain ⟨e1, e2, e3, -⟩ := GlobalTheory.T.goodProjector_unitaryFormsModel_laws R F hC hX i
  obtain ⟨h, hh, hN⟩ := exists_ops R.θ (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv))
    (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i) (R.HW i (sg0 D A)) _ (Good R A.μ0) hM hC.models.inf
    (hC.models.νW i).1.1 (hC.models.νW i).2 (hS.2.2 i)
    (fun P hP d B => ((hlev P hP).2.1 ∅ d B).trans (and_iff_right GlobalTheory.LevOp.offS_empty))
    (fun P hP c => (hlev P hP).2.2.2.2 _ R.θ _ c hC.models.inf)
  have hg : ∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g) := fun P hP cc g => by
    refine LinearMap.ext fun x => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hh P hP, hC.models.gW, hC.models.gW, hh P hP]
    refine MultilinearMap.ext fun v => ((hlev P hP).2.2.2.1 cc (R.eG g) _ fun k hk y => ?_).symm
    rw [hlv x v k ((hlev P hP).1 k hk).1, ((hlev P hP).1 k hk).2, one_mul]
  have he : ∀ P, Good R A.μ0 P → ∀ cc, Commute (h P cc) (eH R i) := fun P hP cc =>
    Commute.sum_right _ _ _ fun g _ => (hg P hP cc g).smul_right _
  have hW : ∀ (c : Pl D.host.E → List ℤ → ℂ) x, x ∈ Wcc R SF i c ↔ eH R i x = x ∧
      ∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x := fun c x => by
    unfold Wcc
    rw [Submodule.mem_comap, Submodule.mem_inf, e3, mem_partFull]
    refine and_congr_right fun _ => ⟨fun hx P d hP hd => inj ?_, fun hx => ⟨hmem x, fun P d B hB v => ?_⟩⟩
    · rw [hh P hP, postOn_single, map_smul]
      exact MultilinearMap.ext fun v => hx.2 P d _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) v
    · have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      have hd : IsLab (Wc D i) P d := ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
      have h1 := congrArg (R.HW i (sg0 D A)).e (hx P d hP hd)
      rw [hh P hP, postOn_single, map_smul] at h1
      rw [GlobalTheory.SphericalOps.labelUnique (J := levG _ (R.βW i) (R.datWp i R.triv)) (GlobalTheory.HeckeAdjoint.realUnif D) P d B _ hB
        (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) _ (hlv x v)]
      exact congrArg (fun U => U v) h1
  obtain ⟨h1, h2⟩ := parts_of_projector (Good R A.μ0) (IsLab (Wc D i)) h hN (eH R i) e1 he (Wcc R SF i) hW
  refine ⟨h, hh, hN, hg, h1, fun c g => h2 c _ (e2 g) fun P hP cc => hg P hP cc g, ?_, fun c x h1 h2 => (hW c x).2 ⟨h1, h2⟩⟩
  intro c P hP cc x hx
  exact op_eigen inj (hh P hP) (fun d hd => ((hW c x).1 hx).2 P d hP hd) cc

end GlobalTheory.SphOpsModel

end
