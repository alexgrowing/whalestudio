import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComponentEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulLeFinrankDdROfSpans
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinBasisSubsetOfIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanDOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFilteredStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData

noncomputable section

namespace GlobalTheory.DRFil

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open scoped Formalism.Per

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    [FiniteDimensional Qp K] [CharZero Qp] [FiniteDimensional Qp LL]

theorem exists_adapted_of_surjective (hF : IsField F) [FiniteDimensional LL V'] (ρ : Representation LL G V)
    (ρ' : Representation LL G V') [FiniteDimensional LL ↥(DdR PD ρ')] (g : V →ₗ[LL] V')
    (hg : ∀ σ v, g (ρ σ v) = ρ' σ (g v)) (hs : Function.Surjective g) (h : FilSpans PD ρ) (τ : K →ₐ[Qp] LL) :
    (∃ (m : ℕ) (d : Fin m → V' ⊗[Qp] F) (k : Fin m → ℤ), Adapted PD ρ' τ d k) ∧
      ∀ a, (FildR PD ρ τ a).map (ext Qp F g) = FildR PD ρ' τ a := by
  classical
  have hle : ∀ a, (FildR PD ρ τ a).map (ext Qp F g) ≤ FildR PD ρ' τ a := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ext_mem_FildR PD ρ ρ' g hg τ hx
  obtain ⟨m, d, k, hli, hA⟩ := GlobalTheory.filtration_adapted_basis (fun a => (FildR PD ρ τ a).map (ext Qp F g))
    (fun a b hab => Submodule.map_mono (FildR_antitone PD ρ τ hab))
    (Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ') (iSup_le fun a y hy => (hle a hy).1.1))
    (fun x hx => eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hle a (hx a)).2)
  have hmem : ∀ i, d i ∈ FildR PD ρ' τ (k i) := fun i =>
    hle _ ((hA (k i)).ge (Submodule.subset_span ⟨i, le_refl (k i), rfl⟩))
  have had : Adapted PD ρ' τ d k := by
    refine ⟨hmem, GlobalTheory.DRFil.indep_of_linearIndependent_DdRE PD ρ' τ d hF (fun i => (hmem i).1) hli, fun n y hy => ?_⟩
    let q : V' ⊗[Qp] F → Prop := fun y => ∃ r : Fin m → LL ⊗[Qp] F,
      (∀ i, r i ∈ FilV PD (LL := LL) (V := LL) (n - k i)) ∧ y = ∑ i, sm Qp F LL V' (r i) (d i)
    have q0 : q 0 := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    have qa : ∀ x y, q x → q y → q (x + y) := by
      rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
      exact ⟨r + s, fun p => Submodule.add_mem _ (hr p) (hs p), by
        simp only [map_add, hx, hy, Pi.add_apply, LinearMap.add_apply, Finset.sum_add_distrib]⟩
    have qs : ∀ (c : LL) x, q x → q (c • x) := by
      rintro c x ⟨r, hr, hx⟩
      exact ⟨c • r, fun p => Submodule.smul_mem _ _ (hr p), by
        simp only [map_smul, hx, Pi.smul_apply, LinearMap.smul_apply, Finset.smul_sum]⟩
    have qm : ∀ (a : ℤ) (b : F), b ∈ PD.Fil (n - a) → ∀ x ∈ Submodule.span LL (d '' {i | a ≤ k i}),
        q (mulR Qp F LL V' b x) := by
      intro a b hb x hx
      induction hx using Submodule.span_induction with
      | zero => simpa using q0
      | add x y _ _ hx hy => rw [map_add]; exact qa _ _ hx hy
      | smul c x _ hx => rw [map_smul]; exact qs _ _ hx
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        refine ⟨Pi.single i ((1 : LL) ⊗ₜ[Qp] b), fun j => ?_, ?_⟩
        · by_cases hj : j = i
          · subst hj
            rw [Pi.single_eq_same]
            exact tmul_mem_FilV PD _ (fil_antitone PD (sub_le_sub_left hi n) hb)
          · rw [Pi.single_eq_of_ne hj]
            exact Submodule.zero_mem _
        · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
            Pi.single_eq_same, sm_one_tmul]
    obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD g hs hy
    obtain ⟨m', k', b, e, he, rfl⟩ := h n x hx
    change q _
    rw [map_sum, map_sum]
    refine Finset.sum_induction _ q qa q0 fun i _ => ?_
    rw [ext_mulR, ← sm_one_tmul, sm_comm, sm_one_tmul, ← ext_sm]
    refine qm (k' i) (b i) (he i).2.2 _ ((hA (k' i)).le ⟨_, ⟨?_, ?_⟩, rfl⟩)
    · exact sm_idem_mem_DdRE PD ρ τ (he i).1
    · exact sm_idem_mem_FilV PD τ (he i).2.1
  exact ⟨⟨m, d, k, had⟩, fun a => (hA a).trans (had.fil_eq a).symm⟩

theorem exists_adapted (hF : IsField F) [FiniteDimensional LL V] (ρ : Representation LL G V)
    [FiniteDimensional LL ↥(DdR PD ρ)] (h : FilSpans PD ρ) (τ : K →ₐ[Qp] LL) :
    ∃ (m : ℕ) (d : Fin m → V ⊗[Qp] F) (k : Fin m → ℤ), Adapted PD ρ τ d k :=
  (exists_adapted_of_surjective PD hF ρ ρ LinearMap.id (fun _ _ => rfl) Function.surjective_id h τ).1

omit [FiniteDimensional Qp K] [CharZero Qp] [FiniteDimensional Qp LL] in
theorem twist_jumps (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (htw : IsTwistRep (cycLL PD LL) ρ ρ') (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1))
    (h : IsDR PD ρ) : IsDR PD ρ' ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD ρ' τ (a - 1) ↔ IsJumpV PD ρ τ a) ∧ multV PD ρ' τ (a - 1) = multV PD ρ τ a := by
  obtain ⟨Φ, hD, hF⟩ := exists_twist_equiv PD ρ ρ' htw u hu hu'
  refine ⟨?_, fun τ a => ?_⟩
  · obtain ⟨e, -⟩ := htw
    rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h, e.finrank_eq]
  · have e1 : a - 1 + 1 = a + 1 - 1 := by ring
    unfold IsJumpV multV
    rw [e1, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact ⟨(Submodule.map_injective_of_injective Φ.injective).ne_iff, rfl⟩

omit [FiniteDimensional Qp LL] in
theorem component_iso (h : TensInj PD) (ρ : Representation LL G V)
    (hs : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)))
    (τ : K →ₐ[Qp] LL) :
    ∃ e : ↥(DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) ≃ₗ[LL] ↥(DdRE PD ρ τ),
      ∀ x : ↥(DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))),
        ιV PD (LL := LL) (V := V) (x : V ⊗[Qp] B) - (e x : V ⊗[Qp] F) ∈ Submodule.span LL
          {z | ∃ (c : K), ∃ y ∈ DdR PD ρ,
            z = mulVdR (Qp := Qp) (K := K) (BdR := F) (LL := LL) (V := V) c y - τ c • y} := by
  obtain ⟨e, he⟩ := exists_component_equiv PD h ρ hs τ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K)) fun _ => rfl
  refine ⟨e, fun x => ?_⟩
  rw [he]
  exact sub_sm_idem_mem PD ρ τ (ιV_mem_DdR PD ρ x.2.1)

end Generic

theorem zpow_neg_mul_cancel {R : Type} [CommRing R] (u : Rˣ) (k : ℤ) (b : R) :
    ((u ^ (-k) : Rˣ) : R) * (((u ^ k : Rˣ) : R) * b) = b := by
  rw [zpow_neg, Units.inv_mul_cancel_left]

theorem sum_conv {ι ι' : Type} [Fintype ι] [Fintype ι'] (k : ι → ℤ) (k' : ι' → ℤ) (S : Finset ℤ)
    (hS : ∀ i, k i ∈ S) (c : ℤ) : (∑ p : ι × ι', if k p.1 + k' p.2 = c then (1 : ℤ) else 0) =
      ∑ a ∈ S, (∑ i, if k i = a then (1 : ℤ) else 0) * ∑ j, if k' j = c - a then (1 : ℤ) else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hS i)]
  exact Finset.sum_congr rfl fun j _ => if_congr (by omega) rfl rfl

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
include T

theorem isField_dR : IsField P.R.BdR := by
  obtain ⟨C, -⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨_, _, -, -, -, -, _⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  exact T.eD.toMulEquiv.isField (IsFractionRing.toField (K := Per.BdR l) (Per.BdRp l)).toIsField

theorem inv_t_mem (K : FinExt l) (u : P.R.BdR) (hu : (P.PD K).ι (P.PD K).t * u = 1) :
    u ∈ (P.PD K).Fil (-1) := by
  obtain ⟨s, hs, h⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  rw [P.PD_ι, P.period_datum_t_eq] at hu
  have e : u = s := by
    rw [← one_mul u, ← h, mul_right_comm, hu, one_mul]
  rw [e]
  exact (T.fil K _ _).2 ((T.fil _ _ _).1 hs)

theorem tensInj (K : FinExt l) : TensInj (P.PD K) := fun m c hc b hb =>
  GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m c hc b (by simpa only [P.PD_ι] using hb)

section Rep

variable (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem isDR_of_spans (h : Spans (P.PD K) ρ) : IsDR (P.PD K) ρ := by
  have := K.2
  have := LL.2
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans (P.PD K) ρ h1 h)

theorem filSpans (h : IsDR (P.PD K) ρ) : FilSpans (P.PD K) ρ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL V ρ h

theorem crys (h : IsCrys (P.PD K) ρ) : IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ,
    ∃ (m : ℕ) (c : Fin m → ↥K.1) (x : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, x i ∈ Dcris (P.PD K) ρ) ∧
      y = ∑ i, mulR ℚ_[l] P.R.BdR ↥LL.1 V (algebraMap ↥K.1 P.R.BdR (c i))
        (ιV (P.PD K) (LL := ↥LL.1) (V := V) (x i)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  exact isDR_of_isCrys (P.PD K) (tensInj T K) ρ h2 h

end Rep

open GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

variable (K LL : FinExt l)

theorem crysDeRhamAt : CrysDeRhamAt P K LL := fun L h => (crys T K LL L.ρ h).1

theorem ddRSpanAt : DdRSpanAt P K LL := by
  intro L h
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, c, x, hx, rfl⟩ := (crys T K LL L.ρ h).2 y hy
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨c i, x i, hx i, rfl⟩
  · rintro _ ⟨c, x, hx, rfl⟩
    exact mulR_mem_DdR (P.PD K) L.ρ c (ιV_mem_DdR (P.PD K) L.ρ hx)

theorem ddRInjAt : DdRInjAt P K LL := fun _ _ m c x hc _ h =>
  (tensInj T K).tensor (LL := ↥LL.1) m c hc x h

theorem componentIsoAt : ComponentIsoAt P K LL := by
  intro L h τ
  have := K.2
  exact component_iso (P.PD K) (tensInj T K) L.ρ (crys T K LL L.ρ h).2 τ

theorem unramOntoAt : UnramOntoAt P K LL := by
  intro hK L h
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ιV_mem_DdR (P.PD K) L.ρ hx
  · obtain ⟨m, c, x, hx, rfl⟩ := (crys T K LL L.ρ h).2 y hy
    refine Submodule.sum_mem _ fun i _ => ⟨_, mulR_mem_Dcris (P.PD K) L.ρ ⟨(c i).1, (c i).2, hK (c i).2⟩ (hx i), ?_⟩
    rw [ιV_mulR, AlgHom.commutes]
    rfl

theorem tdR_zpow_mem (a : ℤ) : ((tdR P K ^ a : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD K).Fil a := by
  have h1 : (tdR P K : P.R.BdR) ∈ (P.PD K).Fil 1 := (P.PD K).mem_filtration_one
  have h2 : ((tdR P K)⁻¹ : P.R.BdRˣ).1 ∈ (P.PD K).Fil (-1) := inv_t_mem T K _ (tdR P K).mul_inv
  induction a using Int.induction_on with
  | zero => simpa using (P.PD K).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD K).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul]
    exact (P.PD K).Fil_mul _ _ _ _ ih h2

theorem filZeroAt : FilZeroAt P K LL := by
  intro L h
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, k, b, d, hd, rfl⟩ := filSpans T K LL L.ρ h 0 y hy
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨k i, ((tdR P K ^ k i : P.R.BdRˣ) : P.R.BdR) * b i, ?_, d i, ⟨(hd i).1, (hd i).2.1⟩, ?_⟩
    · simpa using (P.PD K).Fil_mul _ _ _ _ (tdR_zpow_mem T K (k i)) (hd i).2.2
    · exact congrArg (fun c => mulVR L c (d i)) (zpow_neg_mul_cancel (tdR P K) (k i) (b i)).symm
  · rintro _ ⟨a, b, hb, d, hd, rfl⟩
    have := mulR_mem_FilV (P.PD K) (LL := ↥LL.1)
      ((P.PD K).Fil_mul _ _ _ _ (tdR_zpow_mem T K (-a)) hb) hd.2
    rwa [add_zero, neg_add_cancel] at this

theorem strictAt : StrictAt P K LL := by
  rintro L₀ L₁ L₂ f g ⟨hf, hg, hi, hex, hs⟩ - h₁ - τ a
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₂.V L₂.ρ).1
  refine ⟨fun x _ hx => ext_injective f hi (hx.trans (map_zero _).symm), fun y => ⟨?_, ?_⟩, fun z => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ext_mem_FildR _ _ _ f hf τ hx, (ext_exact f g hex hs _).2 ⟨x, rfl⟩⟩
  · rintro ⟨hy, h0⟩
    obtain ⟨x, rfl⟩ := (ext_exact f g hex hs y).1 h0
    exact ⟨x, mem_FildR_of_ext _ _ _ f hf hi τ hy, rfl⟩
  · rw [← (exists_adapted_of_surjective (P.PD K) (isField_dR T) L₁.ρ L₂.ρ g hg hs
      (filSpans T K LL L₁.ρ h₁) τ).2 a]
    rfl

theorem dualJumpsAt : DualJumpsAt P K LL := by
  rintro L L' β ⟨hβ, hβ'⟩ h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L.V L.ρ).1
  have hs := filSpans T K LL L.ρ h
  refine ⟨isDR_of_spans T K LL L'.ρ
    (GlobalTheory.DRFil.spans_dual_of_spans (P.PD K) L.ρ L'.ρ β (isField_dR T) hβ hβ' (hs.spans _)), fun τ a => ?_⟩
  obtain ⟨m, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) L.ρ hs τ
  obtain ⟨d', had'⟩ := had.dual L'.ρ β hβ hβ'
  rw [had.isJumpV_iff, had'.isJumpV_iff, had.multV_eq, had'.multV_eq]
  simp only [neg_eq_iff_eq_neg, and_self]

theorem tensorJumpsAt : TensorJumpsAt P K LL := by
  intro L₁ L₂ L₃ e he h₁ h₂
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₁.V L₁.ρ).1
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₂.V L₂.ρ).1
  have hs₁ := filSpans T K LL L₁.ρ h₁
  have hs₂ := filSpans T K LL L₂.ρ h₂
  refine ⟨isDR_of_spans T K LL L₃.ρ (Spans.tensor _ e he (hs₁.spans _) (hs₂.spans _)), fun τ c => ?_⟩
  obtain ⟨m, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) L₁.ρ hs₁ τ
  obtain ⟨m', d', k', had'⟩ := exists_adapted (P.PD K) (isField_dR T) L₂.ρ hs₂ τ
  have had₃ := had.tensor had' L₃.ρ e he
  refine ⟨?_, fun S hS => ?_⟩
  · simp only [had.isJumpV_iff, had'.isJumpV_iff, had₃.isJumpV_iff]
    exact ⟨fun ⟨p, hp⟩ => ⟨_, _, ⟨p.1, rfl⟩, ⟨p.2, rfl⟩, hp⟩,
      fun ⟨_, _, ⟨i, hi⟩, ⟨j, hj⟩, h⟩ => ⟨(i, j), by rw [hi, hj, h]⟩⟩
  · simp only [had.multV_eq, had'.multV_eq, had₃.multV_eq]
    exact sum_conv k k' S (fun i => hS _ ((had.isJumpV_iff _).2 ⟨i, rfl⟩)) c

theorem twistJumpsAt : TwistJumpsAt P K LL := fun L L' htw h =>
  twist_jumps (P.PD K) L.ρ L'.ρ htw _ (tdR P K).mul_inv (inv_t_mem T K _ (tdR P K).mul_inv) h

theorem potCrysDeRhamAt : PotCrysDeRhamAt P K LL := fun L K' hK h =>
  isDR_of_spans T K LL L.ρ (GlobalTheory.DRFil.spans_descent l P K K' LL hK L.V L.ρ
    ((filSpans T K' LL _ (crys T K' LL _ h).1).spans _))

omit T in

theorem deRhamComparison (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (h : GlobalTheory.Per.IsStd P AI) : DeRhamComparison l P := by
  obtain ⟨T⟩ := h
  exact ⟨fun K _ LL _ => crysDeRhamAt T K LL, fun K _ LL _ => ddRSpanAt T K LL,
    fun K _ LL _ => componentIsoAt T K LL, fun K _ LL _ => unramOntoAt T K LL,
    fun K _ LL _ => filZeroAt T K LL, fun K _ LL _ => strictAt T K LL, fun K _ LL _ => dualJumpsAt T K LL,
    fun K _ LL _ => tensorJumpsAt T K LL, fun K _ LL _ => twistJumpsAt T K LL,
    fun K _ LL _ => potCrysDeRhamAt T K LL⟩

end GlobalTheory.DRFil
