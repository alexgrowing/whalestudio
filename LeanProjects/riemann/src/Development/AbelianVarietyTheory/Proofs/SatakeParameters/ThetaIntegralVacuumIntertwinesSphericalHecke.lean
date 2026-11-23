import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIntHecke

theorem integral_move {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (K : Set H) (x : H)
    (A A' : Finset H) (Kn F : H → ℂ) (hA : ∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂)
    (hA' : ∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) (hcard : A'.card = A.card)
    (hFl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hFr : ∀ k ∈ K, ∀ h, F (h * k) = F h)
    (hKl : ∀ γ ∈ Γ, ∀ h, Kn (γ * h) = Kn h) (hKr : ∀ k ∈ K, ∀ h, Kn (h * k) = Kn h)
    (hx : IntegrableOn (fun h => Kn h * F (h * x)) 𝓕 μ) :
    IntegrableOn (fun h => Kn h * ∑ a ∈ A, F (h * a)) 𝓕 μ ∧
      IntegrableOn (fun h => (∑ a ∈ A', Kn (h * a)) * F h) 𝓕 μ ∧
      ∫ h in 𝓕, Kn h * ∑ a ∈ A, F (h * a) ∂μ = ∫ h in 𝓕, (∑ a ∈ A', Kn (h * a)) * F h ∂μ := by
  have hu : ∀ γ ∈ Γ, ∀ h, (fun h => Kn h * F (h * x)) (γ * h) = (fun h => Kn h * F (h * x)) h := by
    intro γ hγ h
    simp only [hKl γ hγ, mul_assoc, hFl γ hγ]
  have h1e : ∀ a ∈ A, ∃ y, (fun h => Kn h * F (h * a)) = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, funext fun h => ?_⟩
    simp only
    rw [hKr k₁ hk₁, ← mul_assoc, hFr k₂ hk₂, ← mul_assoc]
  have h2e : ∀ a ∈ A', ∃ y, (fun h => Kn (h * a) * F h)
      = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, funext fun h => ?_⟩
    have : h * (k₁ * x⁻¹) * x = h * k₁ := by group
    simp only [this]
    rw [hFr k₁ hk₁, ← mul_assoc, hKr k₂ hk₂]
  have key : ∀ u : H → ℂ, (∃ y, u = fun h => (fun h => Kn h * F (h * x)) (h * y)) →
      IntegrableOn u 𝓕 μ ∧ ∫ h in 𝓕, u h ∂μ = ∫ h in 𝓕, Kn h * F (h * x) ∂μ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨integrableOn_fundamentalDomain_mul_right h𝓕 y _ hu hx,
      setIntegral_fundamentalDomain_mul_right h𝓕 y _ hu⟩
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine ⟨integrable_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integrable_finsetSum _ fun a ha => (key _ (h2e a ha)).1, ?_⟩
  rw [integral_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integral_finsetSum _ fun a ha => (key _ (h2e a ha)).1,
    Finset.sum_congr rfl fun a ha => (key _ (h1e a ha)).2,
    Finset.sum_congr rfl fun a ha => (key _ (h2e a ha)).2, Finset.sum_const, Finset.sum_const, hcard]

variable {D : D7}

theorem exists_dual (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) (h : SphOp V P d R) :
    ∃ α ∈ GfC V, ∃ R', SphOp V P (dualLab d) R' ∧ R'.card = R.card ∧
      (∀ γ ∈ R, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      ∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨e, f, ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := h
  obtain ⟨he, v, hf⟩ := HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := HeckeDual.exists_skew D
  have := HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h3, h2⟩
      obtain ⟨k, rfl⟩ := (HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := HeckeDual.exists_rep_inv
    (HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  have hh : ∀ (β γ : GA D V), (∃ k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k},
      γ = k₁ * β * k₂) → ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * β * k₂ := by
    rintro β γ ⟨k₁, g₁, k₂, g₂, rfl⟩
    exact ⟨k₁, ⟨g₁.1, e, f, hef, g₁.2⟩, k₂, ⟨g₂.1, e, f, hef, g₂.2⟩, rfl⟩
  refine ⟨_, GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v a), R',
    ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1,
    fun γ hγ => (HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => hh _ _ (hrep.1 γ hγ).2, fun γ hγ => hh _ _ (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul _ _), one_smul]

theorem opOf_dualC {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (c : List ℤ →₀ ℂ) :
    opOf π P (dualC c) = ∑ d ∈ c.support, c d • ∑ γ ∈ Hk3.rep V P (dualLab d), π γ := by
  unfold opOf dualC
  rw [Finsupp.sum_mapDomain_index (by exact fun _ => zero_smul _ _) (by exact fun _ _ _ => add_smul _ _ _)]
  rfl

theorem exists_dual_rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) :
    ∃ α ∈ GfC V, ∃ R' : Finset (GA D V), R'.card = (Hk3.rep V P d).card ∧
      (∀ γ ∈ Hk3.rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      (∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M),
        (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R', π γ u = ∑ γ ∈ Hk3.rep V P (dualLab d), π γ u := by
  by_cases h : IsLab V P d
  · have hs : SphOp V P d (Hk3.rep V P d) := by
      unfold Hk3.rep
      rw [dif_pos h]
      exact h.choose_spec
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual V P d _ hs
    refine ⟨α, hα, R', h2, h3, h4, fun M _ _ π u hu => ?_⟩
    rw [((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 _ _ h1).2 M π u hu, opOf_single, LinearMap.sum_apply]
  · have h0 : Hk3.rep V P d = ∅ := dif_neg h
    have h1 : Hk3.rep V P (dualLab d) = ∅ := dif_neg fun h' => h (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d).1.2 h')
    exact ⟨1, one_mem _, ∅, by rw [h0], by simp [h0], by simp, fun M _ _ π u _ => by rw [h1]⟩

theorem hk_apply (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (g : GA D V) :
    hk V P c F g = ∑ d ∈ c.support, c d * ∑ γ ∈ Hk3.rep V P d, F (g * γ) := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem liftInt_hk : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (GA D T)) (𝓕 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓕 ν → VacFix ψ om P → ∀ cS cT, Match ψ om P cS (dualC cT) → ∀ f, IsVacAt ψ S T P f → ∀ Φ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ hyp T P, ∀ h, Φ (h * k) = Φ h) → (∀ g, ∀ y ∈ GfC T, IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO om) f (hk T P cT Φ) = hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f Φ) := by
  intro D ψ S T χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cT hM f hf Φ hΦl hΦr hint
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have : ν.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D T ν hν
  obtain ⟨hl, hr⟩ := GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hW f hf.1
  have hfT : ∀ k ∈ hyp T P, om (1, k) f = f := fun k hk => by
    obtain ⟨e, f', hef⟩ : ∃ e f', IsPrimeIdem P e f' := hk.2.imp fun _ h => h.imp fun _ h => h.1
    refine hfix f hf 1 ⟨⟨one_mem _, fun y => ?_, by simp⟩, e, f', hef, fun i j => ?_⟩ k hk
    · have : finMat D.sp.cm.sig S.gram (1 : GA D S) = 1 := by
        unfold finMat
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this, Matrix.one_mulVec]
    · have : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this, sub_self, Matrix.zero_apply, mul_zero]
  have hth : ∀ g h a b, thetaKO om (g * a) (h * b) f = om (g, h) (om (a, b) f) 0 := fun g h a b => by
    unfold thetaKO
    rw [show ((g * a, h * b) : GA D S × GA D T) = (g, h) * (a, b) from rfl, map_mul, Module.End.mul_apply]
  funext g
  have step : ∀ d, IntegrableOn (fun h => thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) 𝓕 ν ∧
      IntegrableOn (fun h => (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) 𝓕 ν ∧
      ∫ h in 𝓕, thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a) ∂ν =
        ∫ h in 𝓕, (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h ∂ν := fun d => by
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual_rep T P d
    have h5 := h4 _ (om.comp (MonoidHom.inr _ _)) f hfT
    have h6 : ∀ h, ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f = ∑ a ∈ R', thetaKO om g (h * a) f := fun h => by
      have h7 := congrArg (fun u => om (g, h) u 0) h5
      simp only [map_sum, Finset.sum_apply] at h7
      have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
      simp only [h8]
      exact h7.symm
    simp only [h6]
    exact integral_move h𝓕 (hyp T P) α _ R' (fun h => thetaKO om g h f) Φ h2 h3 h1 hΦl hΦr
      (fun γ hγ h => by simpa only [one_mul] using hl 1 (one_mem _) γ hγ g h)
      (fun k hk h => by simpa only [one_mul, mul_one] using hr 1 k 1 (by rw [hfT k hk, one_smul]) g h)
      (hint g α hα)
  have hker : ∀ h, ∑ d ∈ cT.support, cT d * ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f =
      ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f := fun h => by
    have h7 := congrArg (fun u => om (g, h) u 0) (hM f hf)
    rw [opOf_dualC] at h7
    simp only [opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h7
    have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
    have h9 : ∀ a, thetaKO om (g * a) h f = om (g, h) (om (a, 1) f) 0 := fun a => by rw [← hth, mul_one]
    simp only [h8, h9]
    exact h7.symm
  have hi1 : ∀ g, IntegrableOn (fun h => thetaKO om g h f * Φ h) 𝓕 ν := fun g => by
    simpa only [mul_one] using hint g 1 (one_mem _)
  rw [hk_apply]
  unfold Lift.liftInt
  calc ∫ h in 𝓕, thetaKO om g h f * hk T P cT Φ h ∂ν
      = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * (thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) ∂ν := by
        congr 1
        funext h
        rw [hk_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => mul_left_comm _ _ _
    _ = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * ((∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) ∂ν := by
        rw [integral_finsetSum _ fun d _ => (step d).1.const_mul _,
          integral_finsetSum _ fun d _ => (step d).2.1.const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_const_mul, (step d).2.2]
    _ = ∫ h in 𝓕, ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f * Φ h ∂ν := by
        congr 1
        funext h
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [hker]
    _ = _ := by
        rw [integral_finsetSum _ fun d _ => (integrable_finsetSum _ fun a _ => hi1 (g * a)).const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun a _ => hi1 (g * a)]

end GlobalTheory.ThetaIntHecke
