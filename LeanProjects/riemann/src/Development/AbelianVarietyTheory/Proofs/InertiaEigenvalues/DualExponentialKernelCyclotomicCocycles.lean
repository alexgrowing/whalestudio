import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialExistsUniqueCyclotomicLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesCharRepModPowLeOfDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DependentOfCardLe

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.ExpKernel

variable {l : ℕ} [Fact l.Prime]

theorem cocycles_dependent (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK)
    (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s) (e : ℕ)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = Module.finrank ℚ_[l] (Ks K s) + 1 + 1)
    (z : ι → GQ l → ℚ_[l])
    (hz : ∀ i, CocOn (Gj K s) (fun σ y => ((χ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ (z i)) :
    ∃ c : ι → ℚ_[l], c ≠ 0 ∧ ∀ σ ∈ Gj K s, ∑ i, c i * z i σ = 0 := by
  classical
  set L := Ks K s with hL
  set N := s + padicValNat l (e + 1) with hN
  obtain ⟨hΦ1, -⟩ := continuous_fixingSubgroupEquiv L
  set Φ := L.fixingSubgroupEquiv with hΦ
  let χZ : Formalism.GaloisCohomology.GK l L →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l L) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (χ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hχ (isCyc_cycChar l)]; rfl
  let ψ : Formalism.GaloisCohomology.GK l L →* ℤ_[l]ˣ := χZ ^ (-(e : ℤ))
  have hψ : ∀ g, ((ψ g : ℤ_[l]) : ℚ_[l]) =
      ((χ (Φ.symm g : GQ l) ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    rw [Units.val_zpow_eq_zpow_val, ← hχZ]
    have h1 : ψ g = χZ g ^ (-(e : ℤ)) := rfl
    have h2 := map_zpow (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom) (χZ g) (-(e : ℤ))
    have h3 := congrArg Units.val h2
    rw [Units.val_zpow_eq_zpow_val] at h3
    rw [h1]
    exact h3
  have hψc : Continuous fun g => (ψ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hψ, Units.val_zpow_eq_zpow_val]
    exact (hχ.continuous.comp (continuous_subtype_val.comp hΦ1)).zpow₀ _
      fun g => Or.inl (Units.ne_zero _)
  obtain ⟨g₀, hg₀, hg₁⟩ := (gen_dense l _ χ (GlobalTheory.InertiaEigenvalues.isActC_galActC l) hχ K s hs).1
  have hg : ‖(χZ (Φ ⟨g₀, hg₀⟩) : ℤ_[l]) * (ψ (Φ ⟨g₀, hg₀⟩)⁻¹ : ℤ_[l]) - 1‖ =
      (l : ℝ) ^ (-(N : ℤ)) := by
    have h1 := LiftExp.norm_zpow_sub_one l s hs _ hg₁ ((e + 1 : ℕ) : ℤ) (by omega)
    rw [padicValInt.of_nat] at h1
    rw [PadicInt.norm_def]
    push_cast
    rw [hχZ, hψ, hN]
    push_cast at h1 ⊢
    rw [← h1]
    congr 2
    simp only [map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_inv, Units.val_inv_eq_inv_val,
      inv_zpow', neg_neg]
    rw [zpow_add_one₀ (Units.ne_zero _), mul_comm]
  let ε := Fintype.equivFinOfCardEq hι
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.Cyc.CocycleCount.dependent_of_card_le l (Formalism.GaloisCohomology.GK l L) ψ (l ^ N) (Module.finrank ℚ_[l] L + 1)
    (fun r hr => by
      have hcont : ReciprocityTheory.Gal.ContAction (ReciprocityTheory.Gal.charRep (redChar ψ r)) :=
        contAction_charRep _ ((continuous_toZModPow _).comp hψc)
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have hdual := hT l L (finite_Ks K s) r (ZMod (l ^ r))
        (ReciprocityTheory.Gal.charRep (redChar ψ r)) hr hcont
      exact GlobalTheory.Cyc.CocycleCount.card_cocycles_charRep_modPow_le_of_duality l _ χZ ψ hψc N r _ _ hg hdual.1 hdual.2.2.2.2.1
        (hE l L (finite_Ks K s) r (ZMod (l ^ r)) (ReciprocityTheory.Gal.charRep (redChar ψ r)) hr hcont))
    (fun i g => z (ε.symm i) (Φ.symm g : GQ l))
    (fun i => (hz _).1.comp_continuous (continuous_subtype_val.comp hΦ1) fun g => (Φ.symm g).2)
    (fun i g h => by
      rw [hψ, map_mul]
      exact (hz _).2.2 _ (Φ.symm g).2 _ (Φ.symm h).2)
  refine ⟨fun i => c (ε i), fun h => hc0 (funext fun i => ?_), fun σ hσ => ?_⟩
  · simpa using congrFun h (ε.symm i)
  · have h1 := hc (Φ ⟨σ, hσ⟩)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [← h1, ← ε.sum_comp]
    simp

variable {LT : LocTheory} {G : Subgroup (GQ l)} {e : ℕ}

theorem expStar_zero : ExpStar LT G e (fun _ => 0) 0 :=
  ⟨⟨continuousOn_const, fun _ _ => trivial, fun _ _ _ _ => by simp⟩, 0, zero_mem _,
    fun _ _ => by simp⟩

theorem expStar_add {z z' : GQ l → ℚ_[l]} {α α' : Om l} (h : ExpStar LT G e z α)
    (h' : ExpStar LT G e z' α') : ExpStar LT G e (fun σ => z σ + z' σ) (α + α') := by
  obtain ⟨h1, b, hb, h2⟩ := h
  obtain ⟨h1', b', hb', h2'⟩ := h'
  refine ⟨⟨h1.1.add h1'.1, fun _ _ => trivial, fun σ hσ τ hτ => ?_⟩, b + b', add_mem hb hb',
    fun σ hσ => ?_⟩
  · simp only [h1.2.2 σ hσ τ hτ, h1'.2.2 σ hσ τ hτ]
    ring
  · convert add_mem (h2 σ hσ) (h2' σ hσ) using 1
    simp only [map_add]
    ring

theorem expStar_smul {z : GQ l → ℚ_[l]} {α : Om l} (c : ℚ_[l]) (h : ExpStar LT G e z α) :
    ExpStar LT G e (fun σ => c * z σ) (c • α) := by
  obtain ⟨h1, b, hb, h2⟩ := h
  refine ⟨⟨continuousOn_const.mul h1.1, fun _ _ => trivial, fun σ hσ τ hτ => ?_⟩,
    qB (LT l) c * b, qB_mul_mem c hb, fun σ hσ => ?_⟩
  · simp only [h1.2.2 σ hσ τ hτ]
    ring
  · convert qB_mul_mem c (h2 σ hσ) using 1
    simp only [map_mul, Algebra.smul_def, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (LT l).R.BdR]
    ring

theorem expStar_congr {z z' : GQ l → ℚ_[l]} {α : Om l} (h : ExpStar LT G e z α)
    (hz : ∀ σ ∈ G, z' σ = z σ) : ExpStar LT G e z' α := by
  obtain ⟨h1, b, hb, h2⟩ := h
  refine ⟨⟨h1.1.congr hz, fun _ _ => trivial, fun σ hσ τ hτ => ?_⟩, b, hb, fun σ hσ => ?_⟩
  · rw [hz _ (mul_mem hσ hτ), hz _ hσ, hz _ hτ]
    exact h1.2.2 σ hσ τ hτ
  · rw [hz _ hσ]
    exact h2 σ hσ

theorem expStar_sum {ι : Type} (S : Finset ι) (z : ι → GQ l → ℚ_[l]) (α : ι → Om l)
    (c : ι → ℚ_[l]) (h : ∀ i, ExpStar LT G e (z i) (α i)) :
    ExpStar LT G e (fun σ => ∑ i ∈ S, c i * z i σ) (∑ i ∈ S, c i • α i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using expStar_zero
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact expStar_add (expStar_smul _ (h a)) ih

theorem kernel_line (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K : FinExt l) (s : ℕ)
    (hs : Lev l s) (e : ℕ) (z z₀ : GQ l → ℚ_[l]) (hz : ExpStar D.loc (Gj K s) e z 0)
    (hz₀ : ExpStar D.loc (Gj K s) e z₀ 0) (hne : ∃ σ ∈ Gj K s, z₀ σ ≠ 0) :
    ∃ a : ℚ_[l], ∀ σ ∈ Gj K s, z σ = a * z₀ σ := by
  classical
  haveI := finite_Ks K s
  let v := Module.finBasis ℚ_[l] (Ks K s)
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hex : ∀ i, ∃ (a : ℚ_[l]) (w : GQ l → ℚ_[l]), a ≠ 0 ∧
      ExpStar D.loc (Gj K s) e w ((l : Om l) ^ betaE l s e * (a • (v i : Om l))) := by
    intro i
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max ‖(v i : Om l)‖ 1)⁻¹)
      (by positivity)
    obtain ⟨w, -, hw⟩ := GlobalTheory.ExpImage.expStar_image D l K s hs e (a • (v i : Om l))
      ((Ks K s).smul_mem (v i).2) (by
        rw [norm_smul]
        calc ‖a‖ * ‖(v i : Om l)‖ ≤ (max ‖(v i : Om l)‖ 1)⁻¹ * max ‖(v i : Om l)‖ 1 := by
              gcongr; exact le_max_left _ _
          _ = 1 := inv_mul_cancel₀ (by positivity))
    exact ⟨a, w, norm_pos_iff.1 ha0, hw⟩
  choose a w ha hw using hex
  let Z : Option (Option (Fin (Module.finrank ℚ_[l] (Ks K s)))) → GQ l → ℚ_[l] :=
    fun o => o.elim z fun o' => o'.elim z₀ w
  let A : Option (Option (Fin (Module.finrank ℚ_[l] (Ks K s)))) → Om l :=
    fun o => o.elim 0 fun o' => o'.elim 0 fun i => (l : Om l) ^ betaE l s e * (a i • (v i : Om l))
  have hZA : ∀ o, ExpStar D.loc (Gj K s) e (Z o) (A o) := by
    rintro (_ | _ | i)
    exacts [hz, hz₀, hw i]
  obtain ⟨c, hc0, hc⟩ := cocycles_dependent h2 h4 (D.loc l).χQ (D.loc l).χQ_cyc K s hs e
    (by simp) Z (fun o => (hZA o).1)
  have h1 := expStar_congr (expStar_sum Finset.univ Z A c hZA) (z' := fun _ => 0)
    (fun σ hσ => (hc σ hσ).symm)
  have hA : ∑ o, c o • A o = (l : Om l) ^ betaE l s e *
      ((∑ i, (c (some (some i)) * a i) • v i : Ks K s) : Om l) := by
    simp only [Fintype.sum_option, A, Option.elim, smul_zero, zero_add]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, mul_smul_comm (c _)]
  have h3 := (GlobalTheory.ExpDef.expStar_existsUnique D l K s hs e).2 _ _ 0
    (by rw [hA]; exact mul_mem (zpow_mem (natCast_mem _ _) _) (Subtype.prop _)) (zero_mem _)
    h1 expStar_zero
  rw [hA, mul_eq_zero, or_iff_right (zpow_ne_zero _ hl0), ZeroMemClass.coe_eq_zero] at h3
  have h5 : ∀ i, c (some (some i)) = 0 := fun i =>
    (mul_eq_zero.1 (Fintype.linearIndependent_iff.1 v.linearIndependent _ h3 i)).resolve_right (ha i)
  have h6 : ∀ σ ∈ Gj K s, c none * z σ + c (some none) * z₀ σ = 0 := fun σ hσ => by
    simpa [Fintype.sum_option, Z, h5] using hc σ hσ
  have h7 : c none ≠ 0 := by
    intro h
    obtain ⟨σ, hσ, hσ0⟩ := hne
    have h8 := h6 σ hσ
    rw [h, zero_mul, zero_add] at h8
    apply hc0
    funext o
    rcases o with _ | _ | i
    exacts [h, (mul_eq_zero.1 h8).resolve_right hσ0, h5 i]
  refine ⟨-(c (some none) / c none), fun σ hσ => ?_⟩
  field_simp
  linear_combination h6 σ hσ

theorem exists_unramified_hom (F : FinExt l) : ∃ z : GQ l → ℤ_[l], Continuous z ∧
    (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
    (∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0) ∧ ∃ σ ∈ GK F, z σ ≠ 0 := by
  obtain ⟨⟨φ, hφ⟩, hord⟩ := GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l
  obtain ⟨z, h1, h2, h3⟩ := GlobalTheory.UnramifiedDegree.exists_degree l (GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l) hord
  refine ⟨z, h1, h2, fun σ hσ => ?_, ?_⟩
  · simpa using h3 σ 0 fun n hn x hx => by simpa using GlobalTheory.InertFix.inertia_fix l n hn σ hσ x hx
  · haveI := F.2
    haveI : Finite (GQ l ⧸ GK F) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen F.1)
    haveI : (GK F).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := GK F)) φ
    refine ⟨φ ^ n, hmem, ?_⟩
    rw [h3 (φ ^ n) n fun m hm x hx => ?_]
    · exact_mod_cast hn.ne'
    · clear hn hmem
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hφ m hm x hx, map_pow, ih, ← pow_mul, pow_succ]

theorem expStar_unramified (D : Formalism.BasicNotions.D7) (F : FinExt l) (z : GQ l → ℤ_[l]) (h1 : Continuous z)
    (h2 : ∀ σ τ, z (σ * τ) = z σ + z τ)
    (h3 : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0) :
    ExpStar D.loc (GK F) 0 (fun σ => (z σ : ℚ_[l])) 0 := by
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK F
  set AI := D.locA l
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedCrys.exists_witt_coboundary (p := l)
    (AI.actT.comp (GK F).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK F))).eventually
      (GlobalTheory.UnramifiedCrys.eventually_actT_eq AI y m hm hy)) (fun g => z g)
    (h1.comp continuous_subtype_val) (fun g h => h2 g h)
    (fun g hg => h3 g fun x hx =>
      GlobalTheory.UnramifiedCrys.norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
  refine ⟨⟨((continuous_iff_coe _).1 h1).continuousOn, fun _ _ => trivial,
    fun σ _ τ _ => by simp [h2]⟩, io AI b, io_mem AI b, fun σ hσ => ?_⟩
  have h4 : io AI (AI.actW σ b - b) = qB (D.loc l) (z σ : ℚ_[l]) := by
    rw [← io_zl AI (D.locT l)]
    exact congrArg (io AI) (hb ⟨σ, hσ⟩)
  rw [map_sub, io_act] at h4
  convert Submodule.zero_mem _ using 1
  simp only [map_zero, zero_mul, mul_zero, sub_zero, Nat.cast_zero, neg_zero, zpow_zero,
    Units.val_one, map_one, one_mul]
  rw [h4, sub_self]

theorem ker_expStar : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → (0 < e → CobOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z) ∧ (e = 0 → ∀ σ ∈ Gj K s, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0) := by
  intro D h2 h4 l _ K s hs e z hz
  have hχ : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨g₀, hg₀, hg₁⟩ := (gen_dense l _ _ (GlobalTheory.InertiaEigenvalues.isActC_galActC l) hχ K s hs).1
    have h0 : ExpStar D.loc (Gj K s) e
        (fun σ => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) - 1) 0 := by
      refine ⟨⟨?_, fun _ _ => trivial, fun σ _ τ _ => ?_⟩, 1, one_mem_FilB, fun σ _ => ?_⟩
      · simp only [Units.val_zpow_eq_zpow_val]
        exact ((hχ.continuous.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).sub
          continuous_const).continuousOn
      · simp only [map_mul, mul_zpow, Units.val_mul]
        ring
      · simp
    obtain ⟨a, ha⟩ := kernel_line D h2 h4 K s hs e z _ hz h0 ⟨g₀, hg₀, by
      have h1 := LiftExp.norm_zpow_sub_one l s hs _ hg₁ (-(e : ℤ)) (by omega)
      rw [← norm_pos_iff, Units.val_zpow_eq_zpow_val, h1]
      exact zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _⟩
    exact ⟨a, trivial, fun σ hσ => by rw [ha σ hσ]; ring⟩
  · rintro rfl σ hσ hI
    obtain ⟨u, hu1, hu2, hu3, τ, hτ, hu4⟩ := exists_unramified_hom (l := l) ⟨Ks K s, finite_Ks K s⟩
    obtain ⟨a, ha⟩ := kernel_line D h2 h4 K s hs 0 z (fun σ => (u σ : ℚ_[l])) hz
      (expStar_unramified D ⟨Ks K s, finite_Ks K s⟩ u hu1 hu2 hu3)
      ⟨τ, hτ, fun h => hu4 (PadicInt.coe_eq_zero.1 h)⟩
    rw [ha σ hσ, hu3 σ hI]
    simp

end GlobalTheory.Cyc.ExpKernel
