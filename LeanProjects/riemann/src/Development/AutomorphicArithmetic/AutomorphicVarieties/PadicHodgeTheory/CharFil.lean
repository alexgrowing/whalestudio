import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.CharFil

section Generic

open GlobalTheory.SplitJump

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)

private theorem split_fil (a : ℤ) (W W' : Matrix (Fin n) (Fin n) BdR) (hWW : W * W' = 1)
    (hW : ∀ i j, W i j ∈ PD.Fil a) (hW' : ∀ i j, W' i j ∈ PD.Fil (-a))
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W)
    (y : V ⊗[Qp] BdR) (hy : y ∈ DdR PD ρ) (b : ℤ) :
    (b ≤ a → y ∈ FilV PD (LL := LL) (V := V) b) ∧ (a < b → y ∈ FilV PD (LL := LL) (V := V) b → y = 0) := by
  obtain ⟨k, hk⟩ := exists_coord PD ρ e W W' hWW hg y hy
  have hc : coord e BdR y = W.mulVec fun i => algebraMap K BdR (k i) := by
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  refine ⟨fun hb => ?_, fun hb hF => ?_⟩
  · rw [mem_filV PD e]
    intro i
    rw [hc]
    refine fil_mono PD hb ?_
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    exact (PD.Fil a).smul_mem _ (hW i j)
  · rw [mem_filV PD e] at hF
    have hk0 : ∀ i, k i = 0 := fun i => by
      refine eq_zero_of_mem_fil_one PD _ ?_
      rw [congrFun hk i]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact fil_mono PD (by omega) (PD.Fil_mul _ _ _ _ (hW' i j) (hF j))
    apply (coord e BdR).injective
    rw [hc, map_zero]
    funext i
    simp [hk0, Matrix.mulVec, dotProduct]

end Generic

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]

private theorem val_integral {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] (μ : G →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (g : G) : IsIntegral ℤ_[l] (μ g : E) := by
  let j : E →ₐ[ℚ_[l]] Om l := IsAlgClosed.lift
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap j.toLinearMap
  let d : G →* Om l := (j : E →* Om l).comp ((Units.coeHom E).comp μ)
  have hd : ‖d g‖ = 1 := GlobalTheory.UnramifiedChar.norm_eq_one_of_compact d (hj.comp hμ) g
  let LL : FinExt l := ⟨j.fieldRange, Module.Finite.of_surjective j.rangeRestrict.toLinearMap j.rangeRestrict_surjective⟩
  have h1 : (⟨j (μ g), ⟨_, rfl⟩⟩ : ↥LL.1) ∈ OL LL := (GlobalTheory.Per.Val.mem_OL_iff LL _).2 hd.le
  have h2 : IsIntegral ℤ_[l] (j (μ g)) := IsIntegral.map (LL.1.val.restrictScalars ℤ_[l]) h1
  exact (isIntegral_algHom_iff (j.restrictScalars ℤ_[l]) j.injective).1 h2

omit [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in

private theorem exists_int_basis : ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E),
    ∀ x : E, IsIntegral ℤ_[l] x ↔ ∀ i, ‖e.repr x i‖ ≤ 1 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have : IsTorsionFree ℤ_[l] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E _
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E _
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  refine GlobalTheory.Cyc.LatBasis.exists_basis_of_submodule (integralClosure ℤ_[l] E).toSubmodule fun x => ?_
  have hx : IsAlgebraic ℤ_[l] x := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  exact hx.exists_integral_multiple

open GlobalTheory.UnramifiedCrys GlobalTheory.UnramifiedRep in

private theorem exists_split [IsTopologicalRing E] (K : FinExt l) (μ : ↥(GK K) →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (hI : ∀ g ∈ IK K, μ g = 1) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E) (W W' : Matrix (Fin n) (Fin n) (Bdr l)), W * W' = 1 ∧
      (∀ i j, W i j ∈ ((PP l).PD K).Fil 0) ∧ (∀ i j, W' i j ∈ ((PP l).PD K).Fil 0) ∧
      ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] (Bdr l) (e.repr (chRep μ g (e j)) i)) *
        W.map (((PP l).PD K).actdR g) = W := by
  have := compactSpace_GK K
  obtain ⟨Ti⟩ := tiedP l
  set P := PP l
  set AI := AIP l
  obtain ⟨n, e, he⟩ := exists_int_basis (l := l) (E := E)
  have hρ : ∀ g x, chRep μ g x = (μ g : E) * x := fun _ _ => rfl
  have hint : ∀ g i j, ‖e.repr (chRep μ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 ((val_integral μ hμ g).mul ((he (e j)).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := exists_matrixHom (chRep μ) e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hμ.mul (continuous_const (y := e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, hρ, hρ, h, map_one])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (chRep μ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
  have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
    change (P.PD K).ι (AI.ιA a) ∈ _
    rw [P.PD_ι]
    exact AI.ainf_image_mem_filtration_zero K a
  refine ⟨n, e, f.mapMatrix W, f.mapMatrix W⁻¹, ?_, fun i j => hf _, fun i j => hf _, fun g => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
        algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
    exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
      ((P.PD K).ι_comm g)

omit [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
private theorem cycA_val (g : GQ l) : cycA l l E g = Units.map (algebraMap ℚ_[l] E : ℚ_[l] →* E) ((PP l).χQ g) := by
  ext
  change algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E _
  rw [(cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
  rfl

omit [FiniteDimensional ℚ_[l] E] in
private theorem cont_cycA [IsTopologicalRing E] (w : ℤ) : Continuous fun g : GQ l => ((cycA l l E g ^ w : Eˣ) : E) := by
  have h1 : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val
  have h2 : Continuous fun g : GQ l => cyc l l g ^ w := (cycFacts l l).1.zpow w
  refine (h1.comp (Units.continuous_val.comp h2)).congr fun g => ?_
  exact congrArg Units.val (map_zpow (Units.map (algebraMap ℤ_[l] E : ℤ_[l] →* E)) (cyc l l g) w)

private theorem gk_case [IsTopologicalRing E] (K : FinExt l) (κ : ↥(GK K) →* Eˣ)
    (hκ : Continuous fun g => (κ g : E)) (w : ℤ) (hI : ∀ g ∈ IK K, κ g = cycA l l E g ^ w)
    (y : E ⊗[ℚ_[l]] Bdr l) (hy : y ∈ DdR ((PP l).PD K) (chRep κ)) (b : ℤ) :
    (b ≤ -w → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b) ∧
      (-w < b → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b → y = 0) := by
  obtain ⟨T⟩ := tiedP l
  let μ : ↥(GK K) →* Eˣ := κ * ((cycA l l E).comp (GK K).subtype) ^ (-w)
  have hμ : ∀ g, μ g = κ g * cycA l l E g ^ (-w) := fun _ => rfl
  obtain ⟨n, e, W, W', hWW, hW, hW', hg⟩ := exists_split K μ
    (hκ.mul ((cont_cycA (-w)).comp continuous_subtype_val))
    (fun g hg => by rw [hμ, hI g hg, zpow_neg, mul_inv_cancel])
  set t := GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) K
  have ht : (t : Bdr l) = ((PP l).PD K).ι ((PP l).PD K).t := rfl
  refine split_fil ((PP l).PD K) (chRep κ) e (-w) (((t ^ (-w) : (Bdr l)ˣ) : Bdr l) • W)
    (((t ^ w : (Bdr l)ˣ) : Bdr l) • W') ?_ (fun i j => ?_) (fun i j => ?_) (fun g => ?_) y hy b
  · rw [Matrix.smul_mul, Matrix.mul_smul, hWW, smul_smul, zpow_neg, Units.inv_mul, one_smul]
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K (-w)) (hW i j)
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K w) (hW' i j)
  · conv_rhs => rw [← hg g]
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, map_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hχ : ((PP l).PD K).χ g = (PP l).χQ g := Units.ext ((PP l).PD_χ K g)
    have h1 : chRep μ g (e k) = (((PP l).χQ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • chRep κ g (e k) := by
      change (μ g : E) * e k = _ • ((κ g : E) * e k)
      rw [hμ, cycA_val, ← map_zpow, Algebra.smul_def, Units.val_mul, Units.coe_map]
      simp only [MonoidHom.coe_coe]
      ring
    rw [GlobalTheory.DRDual.act_zpow _ t ht, hχ, h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    ring

end UpperTheory.V.Loc.CharFil

open UpperTheory.V.Loc.CharFil in
theorem UpperTheory.V.Loc.charFil :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → IsDr φ (chRep κ) ∧ ∀ i : ℤ, (i ≤ -w → FilD φ (chRep κ) i = Ddr φ (chRep κ)) ∧ (-w < i → FilD φ (chRep κ) i = ⊥) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w ⟨U, hU, hw⟩
  have hφU : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  have hc : ContAction (chRep κ) := (hκ.comp continuous_fst).mul continuous_snd
  have hcU : ContAction ((chRep κ).comp U.subtype : Representation E U E) :=
    (hκ.comp (continuous_subtype_val.comp continuous_fst)).mul continuous_snd
  refine ⟨((isCrys_isDR_restrict_openSubgroup φ hφ _ hc).2 U hU).2.2 ((isCrys_isDR_restrict_openSubgroup _ hφU _ hcU).1 (crUnr _ hφU _ hcU w fun g hg x => ?_)),
    fun i => ?_⟩
  · change (κ g : E) • x = _
    rw [hw g g.2 hg]
    rfl
  obtain ⟨K, e, -, he, hf, -, -, -⟩ := openField _ hφU
  have hf' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    have := DFunLike.congr_fun hf (e.symm g)
    simpa using this.symm
  let κ' : ↥(GK K) →* Eˣ := (κ.comp U.subtype).comp e.symm.toMonoidHom
  have hF : FilT E E i = FilV ((PP l).PD K) (LL := E) (V := E) i := by
    have : (((PP l).PD (botExt l)).Fil i).restrictScalars ℚ_[l] = (((PP l).PD K).Fil i).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ i)
    unfold FilT FilV
    rw [this]
  have key : ∀ y ∈ Ddr φ (chRep κ), (i ≤ -w → y ∈ FilT E E i) ∧ (-w < i → y ∈ FilT E E i → y = 0) := by
    intro y hy
    rw [hF]
    refine gk_case K κ' (hκ.comp (continuous_subtype_val.comp he)) w (fun g hg => ?_) y ?_ i
    · have := hw (e.symm g) (e.symm g).2 (by rw [hf']; exact (memIK K g).1 hg)
      rw [hf'] at this
      exact this
    · refine (Submodule.mem_iInf _).2 fun g => ?_
      have h1 := (Submodule.mem_iInf _).1 hy (e.symm g)
      have h2 : actVdR ((PP l).PD K) (chRep κ') g = actD φ (chRep κ) (e.symm g) := by
        unfold actVdR actD
        rw [hf']
        congr 1
        exact LinearMap.ext fun z => (PP l).PD_actdR K g z
      rw [h2]
      exact h1
  exact ⟨fun h => inf_eq_left.2 fun y hy => (key y hy).1 h,
    fun h => (Submodule.eq_bot_iff _).2 fun y hy => (key y hy.1).2 h hy.2⟩
