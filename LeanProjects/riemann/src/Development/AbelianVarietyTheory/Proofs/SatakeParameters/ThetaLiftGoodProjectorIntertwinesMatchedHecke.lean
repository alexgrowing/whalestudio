import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftHecke

theorem integral_comb {G H X M ι κ : Type} [Group G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (K : Set H)
    [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (om : H × G →* Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ)
    (L : X →ₗ[ℂ] M) (F : H → X) (s : Finset ι) (c : ι → ℂ) (A A' : ι → Finset H) (s' : Finset κ) (c' : κ → ℂ)
    (B : κ → Finset G)
    (hl : ∀ w, ∀ γ ∈ Γ, ∀ h g, ℓ (om (γ * h, g) (L w)) = ℓ (om (h, g) (L w)))
    (hfix : ∀ w, ∀ k ∈ K, om (k, 1) (L w) = L w)
    (hFl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hFr : ∀ k ∈ K, ∀ h, F (h * k) = F h)
    (hint : ∀ g y, IntegrableOn (fun h => ℓ (om (h, g) (L (F (h * y))))) 𝓕 μ)
    (hd : ∀ d, ∃ α, ∃ R' : Finset H, R'.card = (A d).card ∧ (∀ a ∈ A d, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * α * k₂) ∧
      (∀ a ∈ R', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * α⁻¹ * k₂) ∧
      ∀ w, ∑ a ∈ R', om (a, 1) (L w) = ∑ a ∈ A' d, om (a, 1) (L w))
    (hM : ∀ w, ∑ d ∈ s, c d • ∑ a ∈ A' d, om (a, 1) (L w) = ∑ d ∈ s', c' d • ∑ b ∈ B d, om (1, b) (L w)) (g : G) :
    ∫ h in 𝓕, ℓ (om (h, g) (L (∑ d ∈ s, c d • ∑ a ∈ A d, F (h * a)))) ∂μ =
      ∑ d ∈ s', c' d * ∑ b ∈ B d, ∫ h in 𝓕, ℓ (om (h, g * b) (L (F h))) ∂μ := by
  have hmul : ∀ h a g b m, om (h * a, g * b) m = om (h, g) (om (a, b) m) := fun h a g b m => by
    rw [show ((h * a, g * b) : H × G) = (h, g) * (a, b) from rfl, map_mul, Module.End.mul_apply]
  have hm1 : ∀ h a m, om (h, g) (om (a, 1) m) = om (h * a, g) m := fun h a m => by rw [← hmul, mul_one]
  have hm2 : ∀ h b m, om (h, g) (om (1, b) m) = om (h, g * b) m := fun h a m => by rw [← hmul, mul_one]
  have hu : ∀ x, ∀ γ ∈ Γ, ∀ h, (fun h => ℓ (om (h, g) (L (F (h * x))))) (γ * h) =
      (fun h => ℓ (om (h, g) (L (F (h * x))))) h := fun x γ hγ h => by
    simp only [hl _ γ hγ, mul_assoc, hFl γ hγ]
  have key : ∀ x (u : H → ℂ), (∃ y, u = fun h => (fun h => ℓ (om (h, g) (L (F (h * x))))) (h * y)) →
      IntegrableOn u 𝓕 μ ∧ ∫ h in 𝓕, u h ∂μ = ∫ h in 𝓕, ℓ (om (h, g) (L (F (h * x)))) ∂μ := by
    rintro x _ ⟨y, rfl⟩
    exact ⟨integrableOn_fundamentalDomain_mul_right h𝓕 y _ (hu x) (hint g x),
      setIntegral_fundamentalDomain_mul_right h𝓕 y _ (hu x)⟩
  have step : ∀ d, IntegrableOn (fun h => ℓ (om (h, g) (∑ a ∈ A' d, om (a, 1) (L (F h))))) 𝓕 μ ∧
      ∑ a ∈ A d, ∫ h in 𝓕, ℓ (om (h, g) (L (F (h * a)))) ∂μ =
        ∫ h in 𝓕, ℓ (om (h, g) (∑ a ∈ A' d, om (a, 1) (L (F h)))) ∂μ := fun d => by
    obtain ⟨α, R', h1, h2, h3, h4⟩ := hd d
    have e1 : ∀ a ∈ A d, ∫ h in 𝓕, ℓ (om (h, g) (L (F (h * a)))) ∂μ =
        ∫ h in 𝓕, ℓ (om (h, g) (L (F (h * α)))) ∂μ := fun a ha => by
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h2 a ha
      refine (key α _ ⟨k₁, funext fun h => ?_⟩).2
      simp only
      rw [← hm1 h k₁, hfix _ k₁ hk₁, ← mul_assoc, hFr k₂ hk₂, ← mul_assoc]
    have e2 : ∀ a ∈ R', ∃ y, (fun h => ℓ (om (h * a, g) (L (F h)))) =
        fun h => (fun h => ℓ (om (h, g) (L (F (h * α))))) (h * y) := fun a ha => by
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h3 a ha
      refine ⟨k₁ * α⁻¹, funext fun h => ?_⟩
      have : h * (k₁ * α⁻¹) * α = h * k₁ := by group
      simp only [this]
      rw [hFr k₁ hk₁, ← mul_assoc, ← hm1 _ k₂, hfix _ k₂ hk₂]
    simp only [← h4, map_sum, hm1]
    refine ⟨integrable_finsetSum _ fun a ha => (key α _ (e2 a ha)).1, ?_⟩
    rw [integral_finsetSum _ fun a ha => (key α _ (e2 a ha)).1, Finset.sum_congr rfl e1,
      Finset.sum_congr rfl fun a ha => (key α _ (e2 a ha)).2, Finset.sum_const, Finset.sum_const, h1]
  have hi1 : ∀ g, IntegrableOn (fun h => ℓ (om (h, g) (L (F h)))) 𝓕 μ := fun g => by
    simpa only [mul_one] using hint g 1
  calc _ = ∫ h in 𝓕, ∑ d ∈ s, c d * ∑ a ∈ A d, ℓ (om (h, g) (L (F (h * a)))) ∂μ := by
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∫ h in 𝓕, ∑ d ∈ s, c d * ℓ (om (h, g) (∑ a ∈ A' d, om (a, 1) (L (F h)))) ∂μ := by
        rw [integral_finsetSum _ fun d _ => (integrable_finsetSum _ fun a _ => hint g a).const_mul _,
          integral_finsetSum _ fun d _ => (step d).1.const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun a _ => hint g a, (step d).2]
    _ = ∫ h in 𝓕, ∑ d ∈ s', c' d * ∑ b ∈ B d, ℓ (om (h, g * b) (L (F h))) ∂μ := by
        congr 1
        funext h
        have := congrArg (fun m => ℓ (om (h, g) m)) (hM (F h))
        simp only [map_sum (om (h, g)), map_sum ℓ, map_smul, smul_eq_mul, hm2] at this ⊢
        exact this
    _ = _ := by
        rw [integral_finsetSum _ fun d _ => (integrable_finsetSum _ fun a _ => hi1 (g * a)).const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun a _ => hi1 (g * a)]

variable {D : D7}

theorem one_mem_hyp (S : HSp D) (P : Pl D.host.E) : (1 : GA D S) ∈ hyp S P := by
  obtain ⟨e, f', hef⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.1 P
  refine ⟨⟨one_mem _, fun y => ?_, by simp⟩, e, f', hef, fun i j => ?_⟩
  · have : finMat D.sp.cm.sig S.gram (1 : GA D S) = 1 := by
      unfold finMat
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.one_mulVec]
  · have : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, sub_self, Matrix.zero_apply, mul_zero]

theorem theta_comb {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hpos : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) (hfix : VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : Match ψ om P (dualC cS) cT) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ w, IsVacAt ψ S T P (L w)) (F : GA D S → X) (hc : Continuous F)
    (hFl : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) (hFr : ∀ k ∈ hyp S P, ∀ h, F (h * k) = F h) (g : GA D T) :
    ∫ h in 𝓕, thetaKO om h g (L (∑ d ∈ cS.support, cS d • ∑ a ∈ Hk3.rep S P d, F (h * a))) ∂ν =
      hk T P cT (fun g => ∫ h in 𝓕, thetaKO om h g (L (F h)) ∂ν) g := by
  have : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
  have : ν.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D S ν hν
  have hfS : ∀ w, ∀ k ∈ hyp S P, om (k, 1) (L w) = L w := fun w k hk => hfix _ (hL w) k hk 1 (one_mem_hyp T P)
  rw [ThetaIntHecke.hk_apply]
  refine integral_comb h𝓕 (hyp S P) om (LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0) L F cS.support cS
    (Hk3.rep S P) (fun d => Hk3.rep S P (dualLab d)) cT.support cT (Hk3.rep T P) (fun w γ hγ h g => ?_) hfS hFl hFr
    (fun g y => ?_) (fun d => ?_) (fun w => ?_) g
  · have := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hW _ (hL w).1).1 γ hγ 1 (one_mem _) h g
    rwa [one_mul] at this
  · exact GlobalTheory.WeilParts.integrableOn_theta_definite D ψ hW.std S T χS χT om hW hpos X L (fun w => (hL w).1)
      (fun h => F (h * y)) (hc.comp (continuous_mul_right y)) (fun γ hγ h => by rw [mul_assoc, hFl γ hγ]) ν 𝓕 hν h𝓕 g
  · obtain ⟨α, -, R', h1, h2, h3, h4⟩ := ThetaIntHecke.exists_dual_rep S P d
    exact ⟨α, R', h1, h2, h3, fun w => h4 _ (om.comp (MonoidHom.inl _ _)) (L w) (hfS w)⟩
  · have h7 := hM _ (hL w)
    rw [ThetaIntHecke.opOf_dualC] at h7
    simp only [opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply] at h7
    exact h7

theorem rep_mem_GfC (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : ∀ a ∈ Hk3.rep V P d, a ∈ GfC V := by
  rcases GlobalTheory.LevOp.rep_cases (V := V) (P := P) d with h | ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩
  · simp [h]
  · exact fun a ha => (hc.1 a ha).1

theorem shift_abs {H Gf W : Type} [Group H] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (κ : H) (hκ : ρ κ⁻¹ = 1) (f : Gf → W) (h : H) :
    ρ (h * κ)⁻¹ (f (p (h * κ))) = ρ h⁻¹ (f (p h * p κ)) := by
  rw [map_mul p, _root_.mul_inv_rev, map_mul ρ, hκ, one_mul]

theorem ext_mul {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Bridge.Gf V → c.W) {a : GA D V} (ha : a ∈ GfC V) (h : GA D V) :
    c.ext f (h * a) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict a)) :=
  shift_abs (finHom V).rangeRestrict c.ρ a (hc.1 _ ((GfC V).inv_mem ha)) f h

theorem ext_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W)
    (h : GA D V) :
    c.ext (hkF V P z f) h = ∑ d ∈ z.support, z d • ∑ a ∈ Hk3.rep V P d, c.ext f (h * a) := by
  have e : c.ext (hkF V P z f) h = c.ρ h⁻¹ (∑ d ∈ z.support, z d • ∑ a ∈ Hk3.rep V P d,
    f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict a)) := rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_sum, Finset.sum_congr rfl fun a ha => ext_mul c hc f (rep_mem_GfC V P d a ha) h]

theorem one_pow_notMem (P : Pl D.host.E) (n : ℕ) : ((1 ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  rw [one_pow, Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top

theorem level_abs {Γ Gf W : Type} [Group Γ] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gf}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gf} {χ : J →* ℂˣ} {f : Gf → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    {k : Gf} (hk : k ∈ J) (h1 : ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) = 1) (h : Gf) : f (h * k) = f h := by
  have h3 := hf 1 h ⟨k, hk⟩
  rw [h1, map_one, map_one, one_mul, one_smul] at h3
  exact h3

theorem ext_level {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ)
    {k : GA D V} (hk : k ∈ levG V β (flag1L L)) (h1 : levChi V β (flag1L L) k = 1) (h : GA D V) :
    c.ext f (h * k) = c.ext f h := by
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := hk.2
  have h2 : (((levEnv V β L).χ ⟨_, hJ⟩ : ℂˣ) : ℂ) = 1 := h1
  exact (ext_mul c hc f hk.1 h).trans (congrArg (c.ρ h⁻¹) (level_abs hf hJ h2 _))

theorem mult_eq_of_unit {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hS : SchurMult θ M J χ μ 𝓕) {U U' : MMap M} (hU : U ∈ Mult θ M J χ)
    (hU' : U' ∈ Mult θ M J χ) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (h : U v = U' v) : U = U' := by
  have h0 := GlobalTheory.multT_eq_zero_of_apply_eq_zero θ M J χ μ 𝓕 hθ hμ h𝓕 hS (PiTensorProduct.lift (U - U'))
    ⟨U - U', sub_mem hU hU', rfl⟩ (PiTensorProduct.tprod ℂ v) (fun e => ?_) (by
      rw [PiTensorProduct.lift.tprod, MultilinearMap.sub_apply, h, sub_self])
  · exact sub_eq_zero.1 (PiTensorProduct.lift.injective (h0.trans (map_zero _).symm))
  · have h1 := GlobalTheory.tprodInnerFun_tprod v v
    rw [e, map_zero, Finset.prod_eq_one fun τ _ => ?_] at h1
    · exact zero_ne_one h1
    · rw [Submodule.coe_inner, inner_self_eq_norm_sq_to_K, hv τ]
      simp

theorem gaL_hk {G : Type} [Group G] [Fintype G] {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : LevDat D.host.E ℂ V.rank} (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ) {P : Pl D.host.E} {c : List ℤ →₀ ℂ}
    {Φ : GA D V → ℂ} (h : ∀ g0, actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) :
    gaL V β L eG z (hk V P c Φ) = hk V P c (gaL V β L eG z Φ) := by
  unfold gaL
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg (z g • ·) (h _)

theorem theta_form {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hs : S.SigOK) (hp : S.IsPosDef) {Kf : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {ν : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hν : IsMeasDef S Kf ν 𝓕) (hfix : VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : Match ψ om P (dualC cS) cT) (c : CoefA S) (hc : c.Is) {β : GL (Fin S.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hβ : IsSDFrame S β Λ 1) {L : LevDat D.host.E ℂ S.rank}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) {f f' : Bridge.Gf S → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ) (hf' : f' = hkF S P cS f)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ φ, IsVacAt ψ S T P (pt φ))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {u u' : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f h))) ∂ν)
    (hu' : ∀ g, u' g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f' h))) ∂ν) : u' = hk T P cT u := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators S β Λ _ (flag1L L) hB P (one_pow_notMem P n) hP).1
  funext g
  have key := theta_comb hW hpos hν.1.1 hν.2 hfix hM (pt ∘ₗ io) (fun w => hpt _) (c.ext f)
    (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf) (GlobalTheory.ThetaIntegrand.ext_invariant c hf)
    (fun k hk h => ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h) g
  rw [hu', funext hu, hf']
  simp only [ext_hkF c hc]
  exact key

theorem mult_laws {G : Type} [Group G] [Fintype G] {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ)
    (M : DSModel V S) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ)
    (c : List ℤ →₀ ℂ) {U : MMap M} (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) :
    postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) ∧
      postOn M (gaL V β L eG z) (postOn M (hk V P c) U) = postOn M (hk V P c) (postOn M (gaL V β L eG z) U) := by
  obtain ⟨n, hB⟩ := hβ
  obtain ⟨h1, -, -, h4, h5⟩ := GlobalTheory.LevOp.level_operators V β Λ _ L hB P (one_pow_notMem P n) hP
  refine ⟨h5 S θ M c hθ U hU, MultilinearMap.ext fun u => ?_⟩
  simp only [postOn_apply]
  refine gaL_hk eG z fun g0 => h4 c g0 _ fun k hk h => ?_
  have := (GlobalTheory.mult_value_left_cont_level θ M _ _ U hU u).2.2 k (h1 k hk).1 h
  rwa [(h1 k hk).2, one_mul] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem thF_eq_integral (hP : R.IsThP) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    R.thF i t x (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e x) h))) ∂(R.νV i t) :=
  (hP.thF i t).elim fun _ h => (congrFun (h.2 x v) g).trans
    (h.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v) g)

theorem thF_low (hC : Core R F) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωP i t) P) {cV cW : List ℤ →₀ ℂ} (hM : Match R.ψ (R.ωP i t) P (dualC cV) cW)
    {y y' : (R.HV i t).H} (hy : (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    R.thF i t y' (fun ρ => v ρ) = hk (Wc D i) P cW (R.thF i t y fun ρ => v ρ) :=
  theta_form (hC.thP.ωP i t) (D.sp.V_sig _) (hC.models.vpos i) (hC.models.νV i t) hfix hM (R.cV i) (hC.models.cV i)
    (hC.lev.βV i) (L := R.datVt i t) hP ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)) hy
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) ((GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hP).2.2 i) (R.ioP i (PiTensorProduct.tprod ℂ v))
    (thF_eq_integral hC.thP i t y v) (thF_eq_integral hC.thP i t y' v)

theorem wall_laws (hC : Core R F) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P) (c : List ℤ →₀ ℂ)
    {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wall i (sg0 D A)) :
    postOn _ (hk (Wc D i) P c) U ∈ R.Wall i (sg0 D A) ∧
      postOn _ (R.eWf i (sg0 D A)) (postOn _ (hk (Wc D i) P c) U) =
        postOn _ (hk (Wc D i) P c) (postOn _ (R.eWf i (sg0 D A)) U) :=
  mult_laws hC.models.inf (R.MW i (sg0 D A)) (hC.lev.βW i) (L := R.datWp i R.triv)
    (fun PP h => hP PP (h.imp_right fun h => absurd h (Finset.notMem_empty _))) R.eG _ c hU

theorem thF_match (hC : Core R F) (hS : SchurAll R) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωP i t) P) {cV cW : List ℤ →₀ ℂ} (hM : Match R.ψ (R.ωP i t) P (dualC cV) cW)
    {y y' : (R.HV i t).H} (hy : (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y)) :
    R.thF i t y' = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) (R.thF i t y) :=
  (hC.thP.ioP i t).2.2.elim fun v hv => hv.elim fun _ hw =>
    mult_eq_of_unit hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 (hS.2.2 i) (hC.thP.thF_mem i t y')
      (wall_laws hC i t hP cW (hC.thP.thF_mem i t y)).1 (fun ρ => v ρ) hw.1 (thF_low hC i t hP hfix hM hy v)

theorem matchW_of_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t P, Good R t P → VacFix R.ψ (R.ωP i t) P → ∀ cV cW, Match R.ψ (R.ωP i t) P (dualC cV) cW → MatchW R i t P cV cW := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS i t P hP hfix cV cW hM y y' hy
  exact (hC.thP.thG i t y').trans ((congrArg (postOn _ (R.eWf i (sg0 D A))) (thF_match hC hS i t hP hfix hM hy)).trans
    ((wall_laws hC i t hP cW (hC.thP.thF_mem i t y)).2.trans
      (congrArg (postOn _ (hk (Wc D i) P cW)) (hC.thP.thG i t y).symm)))

end GlobalTheory.DefLiftHecke
