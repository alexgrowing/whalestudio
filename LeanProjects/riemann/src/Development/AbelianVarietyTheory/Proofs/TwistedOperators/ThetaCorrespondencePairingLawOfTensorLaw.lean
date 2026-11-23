import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitarySpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairOfTens

open GlobalTheory.InvPairingTensor (exists_real_parts)
open GlobalTheory.ArchRec.PairTensor

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] (g : U →ₗ[ℂ] U')
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul, map_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ)
    (v : V) : v ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem ctr_ne_zero {U : Type} [AddCommGroup U] [Module ℂ U] (Λ : Ix p q → ℚ)
    (h1 : Module.finrank ℂ ↥(hwSub R.HK.act Λ) = 1) (z : R.HK.V ⊗[ℂ] U) (hz : z ≠ 0)
    (hw : ∀ a, TensorProduct.map (R.HK.act (Eab a a)) LinearMap.id z = ((Λ a : ℚ) : ℂ) • z)
    (hn : ∀ a b, posC a b → TensorProduct.map (R.HK.act (Eab a b)) LinearMap.id z = 0)
    (v : R.HK.V) (hv : IsHW R.HK.act Λ v) : ctr R U v z ≠ 0 := by
  intro h0
  apply hz
  refine eq_zero_of_ctr R U z fun w => ?_
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  let d : R.HK.V ⊗[ℂ] U →ₗ[ℂ] R.HK.V :=
    (TensorProduct.rid ℂ R.HK.V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l
  have hd : ∀ a b, d (a ⊗ₜ b) = l b • a := fun a b => by simp [d]
  have hdA : ∀ (A : Module.End ℂ R.HK.V) y, d (TensorProduct.map A LinearMap.id y) = A (d y) := by
    intro A y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.map_tmul, hd, hd, map_smul, LinearMap.id_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hdc : ∀ u y, l (ctr R U u y) = ⟪R.ι u, R.ι (d y)⟫_ℂ := by
    intro u y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [ctr_tmul, hd, map_smul, map_smul, inner_smul_right, smul_eq_mul, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, inner_add_right]
  have hmem : d z ∈ hwSub R.HK.act Λ := by
    rw [mem_hwSub]
    exact ⟨fun a => by rw [← hdA, hw, map_smul], fun a b hab => by rw [← hdA, hn a b hab, map_zero]⟩
  have hv0 : (⟨v, hv.2⟩ : hwSub R.HK.act Λ) ≠ 0 := fun h => hv.1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0).1 h1 ⟨d z, hmem⟩
  have hc' : c • v = d z := congrArg Subtype.val hc
  have h2 := hdc v z
  rw [h0, map_zero, ← hc', map_smul, inner_smul_right] at h2
  have hvv : ⟪R.ι v, R.ι v⟫_ℂ ≠ 0 := fun h =>
    hv.1 (R.ι_inj (by rw [map_zero]; exact inner_self_eq_zero.1 h))
  have hc0 : c = 0 := (mul_eq_zero.1 h2.symm).resolve_right hvv
  rw [hdc, ← hc', hc0, zero_smul, map_zero, inner_zero_right]

variable {σ : Type} {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
  {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}

theorem exists_tintw (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s)
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V) (hB : PLift a₁ a₂ R (fun Z => M.act Z) B) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = ctr R M.V v (f P) := by
  obtain ⟨f, hf, hBf⟩ := exists_map R a₁ h₁ hA B hB.1
  refine ⟨f, ⟨hf, fun Z => ?_⟩, hBf⟩
  have hreal : ∀ X ∈ upq r s, ∀ P, f (a₂ X P) = TensorProduct.map LinearMap.id (M.act X) (f P) := by
    intro X hX P
    refine ext_ctr R _ _ _ fun y => ?_
    rw [ctr_map, ← hBf, ← hBf]
    exact hB.2 X hX P y
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_right, TensorProduct.map_smul_right, hreal X hX, hreal Y hY]

theorem exists_tintw_inc (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s) {U : Type} [AddCommGroup U] [Module ℂ U]
    (b : Mat r s → Module.End ℂ U) (inc : M.V →ₗ[ℂ] U) (hi : Function.Injective inc)
    (he : ∀ Z ∈ upq r s, ∀ y, inc (M.act Z y) = b Z (inc y))
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B)
    (hr : ∀ P v, B P v ∈ LinearMap.range inc) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = inc (ctr R M.V v (f P)) := by
  obtain ⟨g, hg⟩ := inc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  let B₀ : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V :=
    { toFun := fun P =>
        { toFun := fun v => g (B P v)
          map_add' := fun v w => by rw [map_add, map_add]
          map_smul' := fun c v => by rw [LinearMap.map_smulₛₗ, map_smul] }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have h0 : ∀ P v, inc (B₀ P v) = B P v := by
    intro P v
    obtain ⟨y, hy⟩ := hr P v
    change inc (g (B P v)) = _
    rw [← hy]
    exact congrArg inc (LinearMap.congr_fun hg y)
  obtain ⟨f, hf, hBf⟩ := exists_tintw (a₂ := a₂) R h₁ hA M B₀
    ⟨fun Z hZ P v => hi (by rw [map_add, h0, h0, map_zero]; exact hB.1 Z hZ P v),
     fun Z hZ P v => hi (by rw [h0, he Z hZ, h0]; exact hB.2 Z hZ P v)⟩
  exact ⟨f, hf, fun P v => by rw [← hBf, h0]⟩

theorem exists_both (h₁ : IsGK a₁) (h₂ : IsGK a₂) (hA : AdmGK R.HK) {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (b : Mat r s → Module.End ℂ U) (hb : IsUAct b)
    (B B' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B) (hB' : PLift a₁ a₂ R b B') :
    ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U) (f f' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V ⊗[ℂ] MM.M.V),
      Function.Injective inc ∧ (∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y)) ∧
      TIntw a₁ a₂ R.HK MM.M f ∧ TIntw a₁ a₂ R.HK MM.M f' ∧
      (∀ P v, B P v = inc (ctr R _ v (f P))) ∧ ∀ P v, B' P v = inc (ctr R _ v (f' P)) := by
  obtain ⟨MM, inc, hi, hr, he⟩ := GlobalTheory.T.exists_unitary_module_onto_span_of_intertwining r s (MvPolynomial σ ℂ) U (R.HK.V ⊕ R.HK.V) a₂ b
    (Sum.elim (fun v => B.flip v) (fun v => B'.flip v)) h₂ hb (by
      rintro (v | v) Z hZ P
      · exact hB.2 Z hZ P v
      · exact hB'.2 Z hZ P v)
  obtain ⟨f, hf, hBf⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B hB fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inl v, P, rfl⟩
  obtain ⟨f', hf', hBf'⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B' hB' fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inr v, P, rfl⟩
  exact ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩

theorem pairLaw_of_tensLaw : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁) (T₂ : GrpData r s) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ), IsGK a₁ → IsGK a₂ → AdmGK R₁.HK → Module.finrank ℂ ↥(hwSub R₁.HK.act Λ₁) = 1 → TensLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ → PairLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ := by
  intro p q r s T₁ σ a₁ a₂ R₁ T₂ R₂ Λ₁ Λ₂ h₁ h₂ hA h1 hT
  refine ⟨hT.ex, hT.uniq, fun U _ _ b hb B hB hB0 => ?_, ?_⟩
  · have hne : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (inc : M →ₗ[ℂ] U)
        (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] M), (∀ P v, B P v = inc (ctr R₁ _ v (f P))) → f ≠ 0 := by
      intro M _ _ inc f hf h0
      apply hB0
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hf, h0]
      simp
    refine ⟨?_, fun Φ hΦ => ⟨fun v hv => ?_, fun B' hB' hΦ' => ?_⟩⟩
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨⟨N, e, hee, hrf⟩, -⟩ := hT.unit MM f hf (hne inc f hBf)
      refine ⟨inc ∘ₗ N.subtype ∘ₗ e.toLinearMap, hi.comp (Subtype.val_injective.comp e.injective),
        fun Z hZ x => ?_, le_antisymm ?_ ?_⟩
      · change inc (e (R₂.HK.act Z x) : N) = b Z (inc (e x : N))
        rw [hee, he Z hZ]
      · rintro _ ⟨x, rfl⟩
        haveI : Nontrivial (hwSub R₁.HK.act Λ₁) := Module.nontrivial_of_finrank_eq_succ h1
        obtain ⟨⟨v, hvm⟩, hv⟩ := exists_ne (0 : hwSub R₁.HK.act Λ₁)
        have hvv : ⟪R₁.ι v, R₁.ι v⟫_ℂ ≠ 0 := fun h =>
          hv (Subtype.ext (R₁.ι_inj (by rw [ZeroMemClass.coe_zero, map_zero]; exact inner_self_eq_zero.1 h)))
        have hm : TensorProduct.map LinearMap.id N.subtype (v ⊗ₜ[ℂ] e x) ∈ LinearMap.range f := by
          rw [hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨P, hP⟩ := hm
        have h3 : B P v = ⟪R₁.ι v, R₁.ι v⟫_ℂ • inc (e x : N) := by
          rw [hBf, hP, ctr_map, ctr_tmul, map_smul, map_smul]; rfl
        have h4 : (inc ∘ₗ N.subtype ∘ₗ e.toLinearMap) x = (⟪R₁.ι v, R₁.ι v⟫_ℂ)⁻¹ • B P v := by
          rw [h3, inv_smul_smul₀ hvv]; rfl
        rw [h4]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨P, v, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨P, v, rfl⟩
        have hm : f P ∈ LinearMap.range (TensorProduct.map LinearMap.id N.subtype) := by
          rw [← hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨z, hz⟩ := hm
        refine ⟨e.symm (ctr R₁ N v z), ?_⟩
        rw [hBf, ← hz, ctr_map]
        simp
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hΦw := (mem_hwSub _ _ _).1 hΦ.2.1.2
      have hcomm : ∀ X, TensorProduct.map (R₁.HK.act X) LinearMap.id (f Φ) = f (a₁ X Φ) :=
        fun X => (LinearMap.congr_fun (hf.1 X) Φ).symm
      rw [hBf, ← map_zero inc]
      exact hi.ne (ctr_ne_zero R₁ Λ₁ h1 (f Φ) (hj Φ hΦ).1 (fun a => by rw [hcomm, hΦw.1, map_smul])
        (fun a c hac => by rw [hcomm, hΦw.2 a c hac, map_zero]) v hv.1)
    · obtain ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩ := exists_both R₁ h₁ h₂ hA b hb B B' hB hB'
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hff : f' = f := (hj Φ hΦ).2 f' hf' (ext_ctr R₁ _ _ _ fun v => hi (by rw [← hBf, ← hBf', hΦ']))
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hBf, hBf', hff]
  · obtain ⟨f₀, hf₀, hf0, hall⟩ := hT.line
    obtain ⟨B₀, hB₀, hBf⟩ := exists_pairing R₁ a₁ f₀ hf₀.1
    refine ⟨B₀, fun h0 => hf0 ?_, ⟨hB₀, fun Z hZ P v => ?_⟩, fun B hB => ?_⟩
    · refine LinearMap.ext fun P => eq_zero_of_ctr R₁ _ _ fun v => ?_
      rw [← hBf, h0]; rfl
    · have := LinearMap.congr_fun (hf₀.2 Z) P
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
      rw [hBf, hBf, this, ctr_map]
    · obtain ⟨f, hf, hBf'⟩ := exists_tintw R₁ h₁ hA R₂.HK B hB
      obtain ⟨c, rfl⟩ := hall f hf
      refine ⟨c, LinearMap.ext fun P => LinearMap.ext fun v => ?_⟩
      rw [hBf', LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hBf, map_smul]

end GlobalTheory.ArchRec.PairOfTens
