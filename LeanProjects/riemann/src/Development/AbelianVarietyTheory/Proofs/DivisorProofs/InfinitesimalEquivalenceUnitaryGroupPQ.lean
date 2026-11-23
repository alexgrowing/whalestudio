import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff

section

open Matrix Topology Filter

namespace GlobalTheory.GKPort

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.D.gk.HC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_smD {v : H} (hv : v ∈ smD ε σ) :
    Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v := by
  rw [mem_smD_iff] at hv
  intro m Xs hX
  have hc := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_contDiff m Xs
  have hmem : ∀ t : Fin m → ℝ, Formalism.QuantumDeterminants.inUH (Formalism.REAL.Jm ε)
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) :=
    fun t => Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem _ m Xs (fun i => hX i) t
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hv _ (hmem t0)
  have hev : (fun t : Fin m → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) v)
      =ᶠ[𝓝 t0] fun t => F ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

end GlobalTheory.GKPort

end

section

open Matrix

noncomputable section

namespace GlobalTheory.GKPort.KFinLink

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.GKPort.KFinLink

end

end

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.GKPort.Closure

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem dsigC_mem_sub (hV : IsGKSub ε ρ V) (Y : Matrix (Fin n) (Fin n) ℂ) {v : H} (hv : v ∈ V) :
    PI.DSInfCharCap.dsigC ε ρ Y v ∈ V := by
  rw [dsigC_eq]
  exact add_mem (hV.lieStable _ (cre_mem Y) v hv) (Submodule.smul_mem _ _ (hV.lieStable _ (cim_mem Y) v hv))

def vAct (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V where
  toFun Y :=
    { toFun := fun v => ⟨PI.DSInfCharCap.dsigC ε ρ Y v, dsigC_mem_sub hV Y v.2⟩
      map_add' := fun v w => Subtype.ext (dsigC_add_vec (hV.smooth v v.2) (hV.smooth w w.2) Y)
      map_smul' := fun c v => Subtype.ext (dsigC_smul_vec (hV.smooth v v.2) Y c) }
  map_add' Y Z := LinearMap.ext fun v => Subtype.ext (dsigC_add hρ (hV.smooth v v.2) Y Z)
  map_smul' c Y := LinearMap.ext fun v => Subtype.ext (dsigC_smul hρ (hV.smooth v v.2) c Y)

theorem vAct_coe (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    ((vAct hρ hV Y v : V) : H) = PI.DSInfCharCap.dsigC ε ρ Y v := rfl

theorem vAct_of_mem (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (v : V) :
    ((vAct hρ hV X v : V) : H) = dRep ρ X v := by
  rw [vAct_coe, dsigC_eq, cre_of_mem hX, cim_of_mem hX, dRep_zero, smul_zero, add_zero]

theorem vAct_decomp (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    vAct hρ hV X = vAct hρ hV (cre ε X) + Complex.I • vAct hρ hV (cim ε X) := by
  conv_lhs => rw [← cre_add_cim (ε := ε) X]
  rw [map_add, map_smul]

theorem vAct_bracket_of_mem (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hY : Y ∈ lieSet ε) :
    vAct hρ hV (X * Y - Y * X) = vAct hρ hV X * vAct hρ hV Y - vAct hρ hV Y * vAct hρ hV X := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [vAct_of_mem hρ hV (bracket_mem hX hY), LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Submodule.coe_sub]
  simp only [vAct_of_mem hρ hV hX, vAct_of_mem hρ hV hY]
  exact (dRep_add_bracket hρ (hV.smooth v v.2) hX hY).2

theorem vAct_bracket (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    vAct hρ hV (X * Y - Y * X) = vAct hρ hV X * vAct hρ hV Y - vAct hρ hV Y * vAct hρ hV X := by
  have hm : ∀ X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ,
      (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
        (X1 * Y1 - Y1 * X1) + Complex.I • (X1 * Y2 - Y2 * X1) + Complex.I • (X2 * Y1 - Y1 * X2) -
          (X2 * Y2 - Y2 * X2) := by
    intro X1 X2 Y1 Y2
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul,
      smul_sub, smul_add, smul_neg, neg_smul, Complex.I_mul_I]
    module
  have h := hm (cre ε X) (cim ε X) (cre ε Y) (cim ε Y)
  rw [cre_add_cim, cre_add_cim] at h
  rw [h, map_sub, map_add, map_add, map_smul, map_smul, vAct_bracket_of_mem hρ hV (cre_mem X) (cre_mem Y),
    vAct_bracket_of_mem hρ hV (cre_mem X) (cim_mem Y), vAct_bracket_of_mem hρ hV (cim_mem X) (cre_mem Y),
    vAct_bracket_of_mem hρ hV (cim_mem X) (cim_mem Y), vAct_decomp hρ hV X, vAct_decomp hρ hV Y]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul,
    smul_sub, smul_add, smul_neg, neg_smul, Complex.I_mul_I]
  module

def vE (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) (a b : Fin n) : Module.End ℂ V :=
  vAct hρ hV (single a b 1)

theorem actM_vE (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) (X : Matrix (Fin n) (Fin n) ℂ) :
    ReciprocityTheory.ChartRestriction.DS.actM (vE hρ hV) X = vAct hρ hV X := by
  have hX : X = ∑ a, ∑ b, X a b • single a b (1 : ℂ) := by
    ext i j
    simp [Matrix.sum_apply, single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, ReciprocityTheory.ChartRestriction.DS.actM, vE]

theorem isGlRep_vE (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) :
    ReciprocityTheory.ChartRestriction.DS.IsGlRep (vE hρ hV) := by
  intro a b c d
  simp only [vE]
  rw [← vAct_bracket, single_mul_single', single_mul_single', map_sub]
  split_ifs <;> simp

theorem isDerivedOn_vE (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) :
    ReciprocityTheory.ChartRestriction.DS.IsDerivedOn ε ρ V (vE hρ hV) := by
  refine ⟨isGlRep_vE hρ hV, fun k hk v hv => hV.kStable k hk v hv, fun X hX v => ?_⟩
  rw [actM_vE, vAct_of_mem hρ hV hX]
  have h : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (v : H)) (dRep ρ X v) 0 :=
    (differentiableAt_orbit (hV.smooth v v.2) hX).hasDerivAt
  simpa only [Complex.coe_smul] using h

def vIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (Λ : Fin n → ℝ) :
    Submodule ℂ H :=
  sSup {S | S ≤ V ∧ IsKTypeOf ε ρ Λ S}

theorem vIso_le (Λ : Fin n → ℝ) : vIso ε ρ V Λ ≤ V := sSup_le fun _ hS => hS.1

theorem vIso_le_kIso (Λ : Fin n → ℝ) : vIso ε ρ V Λ ≤ GlobalTheory.KFinDual.kIso ε ρ Λ :=
  sSup_le_sSup fun _ hS => hS.2

theorem isURepOn_Kset (hU : IsURepOn (UJset ε) ρ) : IsURepOn (Kset ε) ρ :=
  ⟨⟨hU.1.1, fun a ha b hb => hU.1.2 a (mem_UJset_of_mem_Kset ha) b (mem_UJset_of_mem_Kset hb)⟩,
    fun g hg => hU.2.1 g (mem_UJset_of_mem_Kset hg),
    fun v => (hU.2.2 v).mono fun _ hk => mem_UJset_of_mem_Kset hk⟩

theorem le_iSup_vIso (hU : IsURepOn (Kset ε) ρ)
    (hirr : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S →
      (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S)
    (hV : IsGKSub ε ρ V) : V ≤ ⨆ Λ : Fin n → ℝ, vIso ε ρ V Λ := by
  classical
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ V → F ≤ ⨆ Λ : Fin n → ℝ, vIso ε ρ V Λ := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _ _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK hFV
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, vIso ε ρ V Λ :=
        (le_sSup (s := {S : Submodule ℂ H | S ≤ V ∧ IsKTypeOf ε ρ Λ S}) ⟨hSF.trans hFV, hΛ⟩).trans
          (le_iSup (fun Λ => vIso ε ρ V Λ) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K (inf_le_right.trans hFV))
      exact hle
  intro v hv
  obtain ⟨S, hS, hvS, hSK⟩ := hV.kFin v hv
  haveI : FiniteDimensional ℂ (S ⊓ V : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
  exact key _ (S ⊓ V) inferInstance le_rfl (fun k hk u hu => ⟨hSK k hk u hu.1, hV.kStable k hk u hu.2⟩)
    inf_le_right ⟨hvS, hv⟩

theorem kType_exists [CompleteSpace H] (hU : IsURepOn (UJset ε) ρ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S →
      (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S :=
  (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hU.1 hU.2.2 fun k hk => hU.2.1 k (mem_UJset_of_mem_Kset hk)).1

theorem mem_of_mem_closure [CompleteSpace H] (hU : IsURepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (hA : IsAdmissibleSub ε ρ V) {w : H} (hw : w ∈ V.topologicalClosure) (hk : IsKFin ε ρ w) : w ∈ V := by
  classical
  have hUK := isURepOn_Kset hU
  have hty := kType_exists hU
  obtain ⟨s, hs⟩ := GlobalTheory.KFinDual.exists_finset (GlobalTheory.KFinDual.decomp n ε H ρ hUK hty) w hk
  set A : Submodule ℂ H := s.sup (vIso ε ρ V) with hAdef
  haveI : ∀ Λ, FiniteDimensional ℂ (vIso ε ρ V Λ) := fun Λ => hA Λ
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_finset_sup _ _
  have hAV : A ≤ V := Finset.sup_le fun Λ _ => vIso_le Λ
  have hAK : A ≤ s.sup (GlobalTheory.KFinDual.kIso ε ρ) :=
    Finset.sup_le fun Λ hΛ => (vIso_le_kIso Λ).trans (Finset.le_sup hΛ)
  have ha : A.starProjection w ∈ A := A.starProjection_apply_mem w
  set w' : H := w - A.starProjection w with hw'
  have hw'C : w' ∈ V.topologicalClosure := sub_mem hw (Submodule.le_topologicalClosure _ (hAV ha))
  have hw'K : w' ∈ s.sup (GlobalTheory.KFinDual.kIso ε ρ) := sub_mem hs (hAK ha)
  have hperpA : w' ∈ Aᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hperpV : ∀ y ∈ V, ⟪w', y⟫_ℂ = 0 := by
    intro y hy
    refine Submodule.iSup_induction (vIso ε ρ V) (motive := fun y => ⟪w', y⟫_ℂ = 0)
      (le_iSup_vIso hUK hty hV hy) (fun Λ y hyΛ => ?_) (by simp)
      (fun y₁ y₂ h₁ h₂ => by simp [inner_add_right, h₁, h₂])
    by_cases hΛ : Λ ∈ s
    · exact Submodule.inner_left_of_mem_orthogonal
        ((Finset.le_sup (f := vIso ε ρ V) hΛ) hyΛ) hperpA
    · exact GlobalTheory.KFinDual.finset_orth hUK s hΛ w' hw'K y (vIso_le_kIso Λ hyΛ)
  have hmem : w' ∈ Vᗮ := (Submodule.mem_orthogonal' _ _).2 fun y hy => hperpV y hy
  have hcl : V.topologicalClosure ≤ Vᗮᗮ :=
    V.topologicalClosure_minimal (Submodule.le_orthogonal_orthogonal V) (Submodule.isClosed_orthogonal _)
  have h0 : w' = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal hmem (hcl hw'C)
    exact inner_self_eq_zero.1 this
  have : w = A.starProjection w := sub_eq_zero.1 h0
  rw [this]
  exact hAV ha

theorem casimir_eq_etr {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    ReciprocityTheory.ChartRestriction.DS.casimir E = etr E 2 := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimir, etr, Formalism.REAL.epow, Finset.sum_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def vK (hV : IsGKSub ε ρ V) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) : Module.End ℂ V :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

theorem vK_coe (hV : IsGKSub ε ρ V) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) (v : V) :
    ((vK hV κ hκ v : V) : H) = ρ κ v := rfl

theorem vAct_kconj (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    vK hV κ hκ * vAct hρ hV Y = vAct hρ hV (κ * Y * κ⁻¹) * vK hV κ hκ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, vK_coe, vAct_coe, vAct_coe, vK_coe, dsigC_eq, dsigC_eq,
    cre_kconj hκ, cim_kconj hκ,
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cre_mem Y) v (hV.smooth v v.2),
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cim_mem Y) v (hV.smooth v v.2), map_add, map_smul]

theorem vAct_conj_etr (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    etr (fun a b => vAct hρ hV (P * single a b 1 * P⁻¹)) k = etr (fun a b => vAct hρ hV (single a b 1)) k := by
  have : (fun a b => vAct hρ hV (P * single a b 1 * P⁻¹)) =
      fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • vAct hρ hV (single c d 1) := by
    funext a b
    rw [conj_single]
    simp only [map_sum, map_smul]
  rw [this]
  exact GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix (fun a b => vAct hρ hV (single a b 1)) P hP k

theorem casimir_kequiv (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (v w : V) (hw : (w : H) = ρ κ v) :
    ((ReciprocityTheory.ChartRestriction.DS.casimir (vE hρ hV) w : V) : H) = ρ κ ((ReciprocityTheory.ChartRestriction.DS.casimir (vE hρ hV) v : V) : H) := by
  have hw' : w = vK hV κ hκ v := Subtype.ext (by rw [hw, vK_coe])
  have hU : IsUnit κ := (isUnit_iff_isUnit_det κ).2 (isUnit_det_of_left_inverse (kset_facts hκ).1)
  have hint := etr_intertwine (fun a b => vAct hρ hV (single a b 1))
    (fun a b => vAct hρ hV (κ * single a b 1 * κ⁻¹)) (vK hV κ hκ) (fun a b => vAct_kconj hρ hV hκ _) 2
  rw [vAct_conj_etr hρ hV κ hU 2] at hint
  have hE : vE hρ hV = fun a b => vAct hρ hV (single a b 1) := rfl
  rw [casimir_eq_etr, hE]
  rw [hw', ← vK_coe hV κ hκ, ← Module.End.mul_apply, ← Module.End.mul_apply, hint]

theorem casimir_symm (hU : IsURepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) (x y : V) :
    ⟪ReciprocityTheory.ChartRestriction.DS.casimir (vE hU.1 hV) x, y⟫_ℂ = ⟪x, ReciprocityTheory.ChartRestriction.DS.casimir (vE hU.1 hV) y⟫_ℂ := by
  have hI := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hU (isDerivedOn_vE hU.1 hV)
  simp only [ReciprocityTheory.ChartRestriction.DS.casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hI, hI, ← mul_assoc]
  have : ReciprocityTheory.ChartRestriction.DS.adjSign ε a b * ReciprocityTheory.ChartRestriction.DS.adjSign ε b a = 1 := by
    unfold ReciprocityTheory.ChartRestriction.DS.adjSign
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, one_mul]

theorem vIso_kStable (Λ : Fin n → ℝ) : IsKStableOn ε ρ (vIso ε ρ V Λ) := by
  intro k hk v hv
  unfold vIso at hv
  rw [sSup_eq_iSup'] at hv
  refine Submodule.iSup_induction _ (motive := fun v => ρ k v ∈ vIso ε ρ V Λ) hv ?_ ?_ ?_
  · intro S x hx
    exact le_sSup (s := {S : Submodule ℂ H | S ≤ V ∧ IsKTypeOf ε ρ Λ S}) S.2 (S.2.2.2.1 k hk x hx)
  · simp
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

theorem casimir_mem_vIso (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) (Λ : Fin n → ℝ)
    (x : V) (hx : (x : H) ∈ vIso ε ρ V Λ) :
    ((ReciprocityTheory.ChartRestriction.DS.casimir (vE hρ hV) x : V) : H) ∈ vIso ε ρ V Λ := by
  set C : Module.End ℂ V := ReciprocityTheory.ChartRestriction.DS.casimir (vE hρ hV) with hC
  let P : Submodule ℂ V := (vIso ε ρ V Λ).comap (V.subtype ∘ₗ C)
  have hle : vIso ε ρ V Λ ≤ P.map V.subtype := by
    refine sSup_le ?_
    rintro S ⟨hSV, hS⟩ y hy
    refine ⟨⟨y, hSV hy⟩, ?_, rfl⟩
    haveI := hS.1
    let ι : S →ₗ[ℂ] V := Submodule.inclusion hSV
    let T : S →L[ℂ] H := LinearMap.toContinuousLinearMap (V.subtype ∘ₗ C ∘ₗ ι)
    have hT : ∀ s : S, T s = ((C (ι s) : V) : H) := fun _ => rfl
    show ((C ⟨y, hSV hy⟩ : V) : H) ∈ vIso ε ρ V Λ
    have hy' : ((C ⟨y, hSV hy⟩ : V) : H) = T ⟨y, hy⟩ := rfl
    rw [hy']
    by_cases h0 : T = 0
    · rw [h0]; simp
    · have hty := GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S H ρ T hS (fun k hk a b hab => by
        rw [hT, hT]
        exact casimir_kequiv hρ hV hk (ι a) (ι b) hab) h0
      have hle : LinearMap.range (T : S →ₗ[ℂ] H) ≤ V := by
        rintro _ ⟨s, rfl⟩
        exact (C (ι s)).2
      exact le_sSup (s := {S : Submodule ℂ H | S ≤ V ∧ IsKTypeOf ε ρ Λ S}) ⟨hle, hty⟩ ⟨_, rfl⟩
  obtain ⟨x', hx', he⟩ := hle hx
  have : x' = x := Subtype.ext he
  subst this
  exact hx'

theorem rep_mem_closure_of_vIso [CompleteSpace H] (hU : IsURepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V)
    (hA : IsAdmissibleSub ε ρ V) (Λ : Fin n → ℝ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) {x : H}
    (hx : x ∈ vIso ε ρ V Λ) : ρ g x ∈ V.topologicalClosure := by
  classical
  have hD := isDerivedOn_vE hU.1 hV
  set C : Module.End ℂ V := ReciprocityTheory.ChartRestriction.DS.casimir (vE hU.1 hV) with hC
  let A' : Submodule ℂ V := (vIso ε ρ V Λ).comap V.subtype
  haveI hfin : FiniteDimensional ℂ (vIso ε ρ V Λ) := hA Λ
  haveI : FiniteDimensional ℂ A' := by
    have e := Submodule.equivMapOfInjective V.subtype Subtype.val_injective A'
    have : FiniteDimensional ℂ (A'.map V.subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional e.symm
  have hCA : ∀ y ∈ A', C y ∈ A' := fun y hy => casimir_mem_vIso hU.1 hV Λ y hy
  let T : Module.End ℂ A' := C.restrict hCA
  have hT : T.IsSymmetric := fun a b => casimir_symm hU hV a.1 b.1
  have htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤ := by
    have := hT.orthogonalComplement_iSup_eigenspaces_eq_bot
    exact Submodule.orthogonal_eq_bot_iff.1 this
  have main : ∀ y : A', ρ g ((y : V) : H) ∈ V.topologicalClosure := by
    intro y
    have hy : y ∈ ⨆ μ, Module.End.eigenspace T μ := by rw [htop]; trivial
    refine Submodule.iSup_induction _ (motive := fun y : A' => ρ g ((y : V) : H) ∈ V.topologicalClosure) hy
      (fun μ z hz => ?_) (by simp) (fun a b ha hb => by
        simpa only [Submodule.coe_add, map_add] using add_mem ha hb)
    by_cases hz0 : z = 0
    · simp [hz0]
    have hreal : (starRingEnd ℂ) μ = μ :=
      hT.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨hz, hz0⟩)
    obtain ⟨c, rfl⟩ : ∃ c : ℝ, (c : ℂ) = μ := ⟨μ.re, (Complex.conj_eq_iff_real.1 hreal).choose_spec ▸ by simp⟩
    let W : Submodule ℂ V := (Module.End.eigenspace T (c : ℂ)).map A'.subtype
    have hWf : FiniteDimensional ℂ W := inferInstance
    have hWc : ∀ v ∈ W, ReciprocityTheory.ChartRestriction.DS.casimir (vE hU.1 hV) v = (c : ℂ) • v := by
      rintro _ ⟨u, hu, rfl⟩
      have := Module.End.mem_eigenspace_iff.1 hu
      exact congrArg Subtype.val this
    have hWK : ∀ k ∈ ReciprocityTheory.ChartRestriction.DS.Kset ε, ∀ v ∈ W, ∃ w ∈ W, (w : H) = ρ k v := by
      rintro k hk _ ⟨u, hu, rfl⟩
      have hkV : ρ k ((u : V) : H) ∈ V := hV.kStable k hk _ (u : V).2
      have hkA : (⟨_, hkV⟩ : V) ∈ A' := vIso_kStable Λ k hk _ u.2
      refine ⟨⟨_, hkV⟩, ⟨⟨_, hkA⟩, ?_, rfl⟩, rfl⟩
      refine Module.End.mem_eigenspace_iff.2 (Subtype.ext (Subtype.ext ?_))
      have h1 := casimir_kequiv hU.1 hV hk (u : V) ⟨_, hkV⟩ rfl
      have h2 := Module.End.mem_eigenspace_iff.1 hu
      have h3 : ReciprocityTheory.ChartRestriction.DS.casimir (vE hU.1 hV) (u : V) = (c : ℂ) • (u : V) := congrArg Subtype.val h2
      rw [h3] at h1
      show ((C ⟨_, hkV⟩ : V) : H) = (c : ℂ) • ρ k ((u : V) : H)
      rw [hC, h1]
      exact (ρ k).map_smul _ _
    have hWst := ReciprocityTheory.ChartRestriction.DS.isKStableSub_of_kStable hU hD W hWf hWK
    have hz' := ReciprocityTheory.ChartRestriction.DS.closure_genSub_stable hU hD hWf hWst hWc g hg ((z : V) : H)
      (Submodule.le_topologicalClosure _ ⟨(z : V), (le_sInf fun _ hT' => hT'.1 :
        W ≤ ReciprocityTheory.ChartRestriction.DS.genSub (vE hU.1 hV) W) ⟨z, hz, rfl⟩, rfl⟩)
    exact Submodule.topologicalClosure_mono (Submodule.map_subtype_le _ _) hz'
  exact main ⟨⟨x, vIso_le Λ hx⟩, hx⟩

theorem admissibleClosure_gKSubmodule : GlobalTheory.Published.AdmissibleClosure := by
  intro n ε H _ _ _ σ hU V hV hA
  refine ⟨fun g hg w hw => ?_, fun w hw hk => mem_of_mem_closure hU hV hA hw hk⟩
  have hgen : ∀ v ∈ V, σ g v ∈ V.topologicalClosure := by
    intro v hv
    refine Submodule.iSup_induction (vIso ε σ V) (motive := fun v => σ g v ∈ V.topologicalClosure)
      (le_iSup_vIso (isURepOn_Kset hU) (kType_exists hU) hV hv)
      (fun Λ y hy => rep_mem_closure_of_vIso hU hV hA Λ hg hy) (by simp)
      (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
  have hw' : w ∈ closure (V : Set H) := by rwa [← Submodule.topologicalClosure_coe]
  have := map_mem_closure (σ g).continuous hw' (t := (V.topologicalClosure : Set H)) hgen
  rwa [(Submodule.isClosed_topologicalClosure V).closure_eq] at this

section Equiv

variable [CompleteSpace H]

theorem isGKSub_kFinVec (hU : IsURepOn (UJset ε) ρ) (hI : IsIrredOn (UJset ε) ρ) :
    IsGKSub ε ρ (kFinVec ε ρ) := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H ρ hU hI
  exact ⟨fun v hv => GlobalTheory.GKPort.smoothVec_of_smD (h1 v hv), fun v hv => hv, isKStableOn_kFinVec ε ρ,
    fun X hX v hv => GlobalTheory.GKPort.KFinLink.isLieStable_of hU hI X hX v hv⟩

theorem finiteDimensional_kIso' (hU : IsURepOn (UJset ε) ρ) (hI : IsIrredOn (UJset ε) ρ) (Λ : Fin n → ℝ) :
    FiniteDimensional ℂ (GlobalTheory.KFinDual.kIso ε ρ Λ) := by
  by_cases hex : ∃ S₀ : Submodule ℂ H, IsKTypeOf ε ρ Λ S₀
  · obtain ⟨S₀, hS₀⟩ := hex
    have hfd := GlobalTheory.GKPort.KFinLink.isAdmissible_of hU hI S₀ (GlobalTheory.KFinVec.isIrrKSub_of_isKTypeOf hS₀)
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_ : _ ≤ GlobalTheory.KFinVec.kIsotypic ε ρ S₀)
    obtain ⟨B, hB, hBS⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hU.1 hU.2.2 fun k hk =>
      hU.2.1 k (mem_UJset_of_mem_Kset hk)).2 Λ S₀ S hS₀ hS
    have hT : GlobalTheory.KFinVec.IsKMapFrom ε ρ S₀ ((B : H →ₗ[ℂ] H) ∘ₗ S₀.subtype) := fun k hk s s' hs => by
      show B s' = ρ k (B s)
      rw [hs, hB k hk]
    refine le_trans ?_ (GlobalTheory.KFinVec.range_le_kIsotypic hT)
    rw [LinearMap.range_comp, Submodule.range_subtype, hBS]
  · have : {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} = ∅ := Set.eq_empty_of_forall_notMem fun S hS => hex ⟨S, hS⟩
    unfold GlobalTheory.KFinDual.kIso
    rw [this, sSup_empty]
    infer_instance

theorem dRep_skew (hU : IsURepOn (UJset ε) ρ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {v w : H}
    (hv : SmoothVec (lieSet ε) ρ v) (hw : SmoothVec (lieSet ε) ρ w) :
    ⟪dRep ρ X v, w⟫_ℂ = -⟪v, dRep ρ X w⟫_ℂ :=
  (((GlobalTheory.SmVecCalc.smooth_calculus n H (Jm ε) ρ (GlobalTheory.GKLie.Jm_conjTranspose ε) (GlobalTheory.GKLie.isUnit_Jm_det ε) hU v hv).2.2 X hX).2.2.2.2 w
    hw).1

end Equiv

section Two

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem exists_kIso_ne_bot [Nontrivial H₁] (hU : IsURepOn (UJset ε) σ₁) :
    ∃ Λ, GlobalTheory.KFinDual.kIso ε σ₁ Λ ≠ ⊥ := by
  by_contra hc
  push_neg at hc
  have hall : ∀ v : H₁, IsKFin ε σ₁ v → v = 0 := fun v hv => by
    have h := GlobalTheory.KFinDual.decomp n ε H₁ σ₁ (isURepOn_Kset hU) (kType_exists hU) v hv
    have h0 : (⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H₁ | IsKTypeOf ε σ₁ Λ S}) = ⊥ := iSup_eq_bot.2 hc
    rw [h0] at h
    exact (Submodule.mem_bot ℂ).1 h
  obtain ⟨x, hx⟩ := exists_ne (0 : H₁)
  have hd := GlobalTheory.HcPort.kfinDense_UJC hU
  obtain ⟨a, ha, hK⟩ := Metric.dense_iff.1 hd x (‖x‖) (norm_pos_iff.2 hx)
  rw [hall a hK] at ha
  simp at ha

theorem form_prop [Nontrivial H₁] (hU₁ : IsURepOn (UJset ε) σ₁) (hI₁ : IsIrredOn (UJset ε) σ₁)
    (hU₂ : IsURepOn (UJset ε) σ₂) (hI₂ : IsIrredOn (UJset ε) σ₂) (T : H₁ →ₗ[ℂ] H₂)
    (hTf : ∀ v, IsKFin ε σ₁ v → IsKFin ε σ₂ (T v))
    (hinj : ∀ v, IsKFin ε σ₁ v → T v = 0 → v = 0)
    (hK : ∀ k ∈ Kset ε, ∀ v, IsKFin ε σ₁ v → T (σ₁ k v) = σ₂ k (T v))
    (hL : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ₁ v → T (dRep σ₁ X v) = dRep σ₂ X (T v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v w, IsKFin ε σ₁ v → IsKFin ε σ₁ w → ⟪T v, T w⟫_ℂ = (c : ℂ) * ⟪v, w⟫_ℂ := by
  classical
  have hUK₁ := isURepOn_Kset hU₁
  have hUK₂ := isURepOn_Kset hU₂
  have hG₁ := isGKSub_kFinVec hU₁ hI₁
  have hG₂ := isGKSub_kFinVec hU₂ hI₂
  obtain ⟨Λ₀, hΛ₀⟩ := exists_kIso_ne_bot hU₁
  set A : Submodule ℂ H₁ := GlobalTheory.KFinDual.kIso ε σ₁ Λ₀ with hAdef
  haveI : FiniteDimensional ℂ A := finiteDimensional_kIso' hU₁ hI₁ Λ₀
  have hAK : ∀ x ∈ A, IsKFin ε σ₁ x := fun x hx => GlobalTheory.KFinDual.kIso_le Λ₀ hx
  haveI : Nontrivial A := Submodule.nontrivial_iff_ne_bot.2 hΛ₀
  let L : A →L[ℂ] H₂ := LinearMap.toContinuousLinearMap (T ∘ₗ A.subtype)
  have hL' : ∀ x : A, L x = T x := fun _ => rfl
  let P : A →L[ℂ] A := (ContinuousLinearMap.adjoint L) ∘L L
  have hP : ∀ x y : A, ⟪P x, y⟫_ℂ = ⟪L x, L y⟫_ℂ := fun x y =>
    ContinuousLinearMap.adjoint_inner_left L y (L x)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (P : Module.End ℂ A)
  obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
  have hPy : P y = μ • y := Module.End.mem_eigenspace_iff.1 hy.1
  have hy0 : (y : H₁) ≠ 0 := fun h => hy.2 (Subtype.ext h)
  have hTy0 : T y ≠ 0 := fun h => hy0 (hinj _ (hAK _ y.2) h)
  have hnum : (starRingEnd ℂ) μ * ((‖(y : H₁)‖ : ℂ) ^ 2) = ((‖T y‖ : ℂ) ^ 2) := by
    have h1 := hP y y
    rw [hPy, inner_smul_left, hL', Submodule.coe_inner, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  set c : ℝ := ‖T y‖ ^ 2 / ‖(y : H₁)‖ ^ 2 with hc
  have hny : 0 < ‖(y : H₁)‖ := norm_pos_iff.2 hy0
  have hnT : 0 < ‖T y‖ := norm_pos_iff.2 hTy0
  have hcpos : 0 < c := by positivity
  have hμc : (starRingEnd ℂ) μ = (c : ℂ) := by
    have hne : ((‖(y : H₁)‖ : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hny.ne')
    rw [hc]
    push_cast
    rw [eq_div_iff hne]
    exact hnum
  have hkey : ∀ w, IsKFin ε σ₁ w → ⟪T y, T w⟫_ℂ = (c : ℂ) * ⟪(y : H₁), w⟫_ℂ := by
    intro w hw
    have hd := GlobalTheory.KFinDual.decomp n ε H₁ σ₁ hUK₁ (kType_exists hU₁) w hw
    refine Submodule.iSup_induction _ (motive := fun w => ⟪T y, T w⟫_ℂ = (c : ℂ) * ⟪(y : H₁), w⟫_ℂ) hd
      (fun Λ z hz => ?_) (by simp) (fun a b ha hb => by simp only [map_add, inner_add_right, ha, hb]; ring)
    by_cases hΛ : Λ = Λ₀
    · subst hΛ
      have h1 := hP y ⟨z, hz⟩
      rw [hPy, inner_smul_left, hμc, hL', hL', Submodule.coe_inner] at h1
      exact h1.symm
    · have hne : Λ₀ ≠ Λ := fun h => hΛ h.symm
      have h1 := GlobalTheory.KFinDual.kIso_orth hUK₁ hΛ (y : H₁) y.2 z hz
      have h2 := GlobalTheory.KFinDual.kIso_orth hUK₂ hΛ (T y)
        (GlobalTheory.KFinDual.map_kIso_le (ρ := σ₁) (π := σ₂) (T := T) hK Λ₀ (Submodule.mem_map_of_mem y.2)) (T z)
        (GlobalTheory.KFinDual.map_kIso_le (ρ := σ₁) (π := σ₂) (T := T) hK Λ (Submodule.mem_map_of_mem hz))
      rw [h1, h2, mul_zero]
  let R : Submodule ℂ H₁ :=
    { carrier := {x | IsKFin ε σ₁ x ∧ ∀ w, IsKFin ε σ₁ w → ⟪T x, T w⟫_ℂ = (c : ℂ) * ⟪x, w⟫_ℂ}
      add_mem' := fun {a b} ha hb => ⟨(kFinVec ε σ₁).add_mem ha.1 hb.1, fun w hw => by
        simp only [map_add, inner_add_left, ha.2 w hw, hb.2 w hw]; ring⟩
      zero_mem' := ⟨(kFinVec ε σ₁).zero_mem, fun w _ => by simp⟩
      smul_mem' := fun r a ha => ⟨(kFinVec ε σ₁).smul_mem r ha.1, fun w hw => by
        simp only [map_smul, inner_smul_left, ha.2 w hw]; ring⟩ }
  have hRle : R ≤ GlobalTheory.KFinVec.kFinSub ε σ₁ := fun x hx => hx.1
  have hRst : GlobalTheory.KFinVec.IsLieStable ε σ₁ R := by
    intro X hX x hx
    have hdx : IsKFin ε σ₁ (dRep σ₁ X x) := hG₁.lieStable X hX x hx.1
    refine ⟨hdx, fun w hw => ?_⟩
    have hdw : IsKFin ε σ₁ (dRep σ₁ X w) := hG₁.lieStable X hX w hw
    rw [hL X hX x hx.1, dRep_skew hU₂ hX (hG₂.smooth _ (hTf x hx.1)) (hG₂.smooth _ (hTf w hw)), ← hL X hX w hw,
      hx.2 _ hdw, dRep_skew hU₁ hX (hG₁.smooth _ hx.1) (hG₁.smooth _ hw)]
    ring
  have hyR : (y : H₁) ∈ R := ⟨hAK _ y.2, hkey⟩
  rcases GlobalTheory.GKPort.KFinLink.lieIrr_of hU₁ hI₁ R hRle hRst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hyR)) hy0
  · exact ⟨c, hcpos, fun v w hv _ => by
      have hvR : v ∈ R := h ▸ (hv : v ∈ GlobalTheory.KFinVec.kFinSub ε σ₁)
      exact hvR.2 w ‹_›⟩

end Two

theorem infinitesimalEquivalence_unitaryGroupPQ : GlobalTheory.Published.InfinitesimalEquivalence := by
  intro n ε H₁ _ _ _ _ H₂ _ _ _ _ σ₁ σ₂ hU₁ hI₁ hU₂ hI₂ e he
  classical
  have hG₁ := isGKSub_kFinVec hU₁ hI₁
  have hG₂ := isGKSub_kFinVec hU₂ hI₂
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((kFinVec ε σ₂).subtype ∘ₗ e.toLinearMap)
  have hTe : ∀ v : kFinVec ε σ₁, T v = (e v : H₂) := fun v => LinearMap.congr_fun hT v
  have hTf : ∀ v, IsKFin ε σ₁ v → IsKFin ε σ₂ (T v) := fun v hv => by
    rw [hTe ⟨v, hv⟩]; exact (e ⟨v, hv⟩).2
  obtain ⟨c, hc, hB⟩ := form_prop hU₁ hI₁ hU₂ hI₂ T hTf
    (fun v hv h => by
      have h1 : e ⟨v, hv⟩ = 0 := Subtype.ext (by rw [← hTe ⟨v, hv⟩]; exact h)
      exact congrArg Subtype.val (e.map_eq_zero_iff.1 h1))
    (fun k hk v hv => by
      have hkv := isKStableOn_kFinVec ε σ₁ k hk v hv
      rw [hTe ⟨_, hkv⟩, hTe ⟨v, hv⟩]
      exact he.1 k hk ⟨v, hv⟩ ⟨_, hkv⟩ rfl)
    (fun X hX v hv => by
      have hxv := hG₁.lieStable X hX v hv
      rw [hTe ⟨_, hxv⟩, hTe ⟨v, hv⟩]
      exact he.2 X hX ⟨v, hv⟩ ⟨_, hxv⟩ rfl)
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  set r : ℝ := (√c)⁻¹ with hr
  have hrpos : 0 < r := inv_pos.2 hs
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrpos.ne'
  have hD : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}, IsURepOn (UJset ε) σ →
      DenseRange (kFinVec ε σ).subtype := fun hU => by
    have := GlobalTheory.HcPort.kfinDense_UJC hU
    refine this.mono ?_
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have d₁ := hD hU₁
  have d₂ : DenseRange ((r : ℂ) • (kFinVec ε σ₂).subtype) := (hD hU₂).mono (by
    rintro _ ⟨v, rfl⟩
    exact ⟨(r : ℂ)⁻¹ • v, by
      rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hr0, one_smul]⟩)
  have hn : ∀ v, ‖((r : ℂ) • (kFinVec ε σ₂).subtype) (e v)‖ = ‖(kFinVec ε σ₁).subtype v‖ := fun v => by
    have h2 : ‖(e v : H₂)‖ ^ 2 = c * ‖(v : H₁)‖ ^ 2 := by
      have h := congrArg Complex.re (hB v v v.2 v.2)
      rw [Complex.re_ofReal_mul, hTe v] at h
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact h
    have h3 : ‖(e v : H₂)‖ = √c * ‖(v : H₁)‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (e v : H₂)), h2, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
    show ‖(r : ℂ) • (e v : H₂)‖ = ‖(v : H₁)‖
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hrpos.le, h3, hr, inv_mul_cancel_left₀ hs.ne']
  let U := e.extendOfIsometry (kFinVec ε σ₁).subtype ((r : ℂ) • (kFinVec ε σ₂).subtype) d₁ d₂ hn
  have hUe : ∀ v : kFinVec ε σ₁, U v = (r : ℂ) • (e v : H₂) := fun v =>
    LinearEquiv.extendOfIsometry_eq e _ _ d₁ d₂ hn v
  have hρ₁ := hU₁.1
  have hρ₂ := hU₂.1
  have hD₁ := isDerivedOn_vE hρ₁ hG₁
  have hD₂ := isDerivedOn_vE hρ₂ hG₂

  have hcomm : ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (v : kFinVec ε σ₁),
      e (vAct hρ₁ hG₁ Y v) = vAct hρ₂ hG₂ Y (e v) := by
    have hX : ∀ X ∈ lieSet ε, ∀ v : kFinVec ε σ₁, e (vAct hρ₁ hG₁ X v) = vAct hρ₂ hG₂ X (e v) := fun X hX v =>
      Subtype.ext (by
        rw [vAct_of_mem hρ₂ hG₂ hX]
        exact he.2 X hX v _ (vAct_of_mem hρ₁ hG₁ hX v))
    intro Y v
    rw [vAct_decomp hρ₁ hG₁ Y, vAct_decomp hρ₂ hG₂ Y]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hX _ (cre_mem Y), hX _ (cim_mem Y)]

  obtain ⟨cs, hcs⟩ := GlobalTheory.HcPort.casimirActsByScalar_indefUnitary n ε H₁ σ₁ hU₁ hI₁
  have hsm := (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H₁ σ₁ hU₁ hI₁).1
  have hcas : ∀ v, ReciprocityTheory.ChartRestriction.DS.casimir (vE hρ₁ hG₁) v = (cs : ℂ) • v := fun v => Subtype.ext (by
    have h1 := ReciprocityTheory.ChartRestriction.DS.casU_eq_casimir hD₁ v
    have h2 := ReciprocityTheory.ChartRestriction.DS.casU_eq_casimir (ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hU₁) ⟨(v : H₁), hsm _ v.2⟩
    rw [hcs] at h2
    rw [← h1]
    exact h2)
  have main : ∀ g ∈ UJset ε, ∀ w : kFinVec ε σ₁, U (σ₁ g w) = σ₂ g (U w) := by
    intro g hg w
    obtain ⟨S, hSf, hwS, hSK⟩ := w.2
    let W : Submodule ℂ (kFinVec ε σ₁) := S.comap (kFinVec ε σ₁).subtype
    have hWf : FiniteDimensional ℂ W := by
      have e' := Submodule.equivMapOfInjective (kFinVec ε σ₁).subtype Subtype.val_injective W
      have : FiniteDimensional ℂ (W.map (kFinVec ε σ₁).subtype) :=
        Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
      exact LinearEquiv.finiteDimensional e'.symm
    have hWK : ReciprocityTheory.ChartRestriction.DS.IsKStableSub ε (vE hρ₁ hG₁) W :=
      ReciprocityTheory.ChartRestriction.DS.isKStableSub_of_kStable hU₁ hD₁ W hWf fun k hk v hv =>
        ⟨⟨_, isKStableOn_kFinVec ε σ₁ k hk v v.2⟩, hSK k hk v hv, rfl⟩
    have := GlobalTheory.HcPort.graphD hU₁ hU₂ hD₁ hD₂ (vE hρ₁ hG₁) LinearMap.id ((r : ℂ) • e.toLinearMap)
      (fun _ _ h => h) (fun _ _ _ => rfl)
      (fun a b v => by
        simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, vE, hcomm])
      hcas U.toContinuousLinearEquiv.toContinuousLinearMap (fun v => hUe v) hWf hWK
      (show w ∈ W from hwS) hg
    simpa [hUe w] using this
  refine ⟨U, r, hrpos, fun g hg x => ?_, hUe⟩
  exact d₁.induction_on (p := fun x => U (σ₁ g x) = σ₂ g (U x)) x
    (isClosed_eq (U.continuous.comp (σ₁ g).continuous) ((σ₂ g).continuous.comp U.continuous))
    fun w => main g hg w

end GlobalTheory.GKPort.Closure

namespace GlobalTheory

theorem gkGlobalisation_holds : GlobalTheory.Published.GKGlobalisation :=
  ⟨GlobalTheory.GKPort.Closure.admissibleClosure_gKSubmodule, GlobalTheory.GKPort.Closure.infinitesimalEquivalence_unitaryGroupPQ⟩

end GlobalTheory

end
