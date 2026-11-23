import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnit
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKB

noncomputable section

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, finEmb_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_mem (σ : E →ₐ[F] E) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : sigR (Fv F v) σ y ∈ intLoc F E v := sigR_mem_intLoc σ hy

def sR (σ : E →ₐ[F] E) : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict (intLoc F E v) fun y => sigR_mem v σ y.2

@[simp] theorem coe_sR (σ : E →ₐ[F] E) (y : intLoc F E v) : (sR v σ y : Fv F v ⊗[F] E) = sigR (Fv F v) σ y := rfl

theorem absBar_le_one (τ : E →ₐ[F] FvBar F v) (y : intLoc F E v) : absBar F v (finEmb F v τ y) ≤ 1 := (le_absFin F v τ y).trans (absFin_le_one_of_mem_intLoc y.2)

def p0 (τ : E →ₐ[F] FvBar F v) : Ideal (intLoc F E v) where
  carrier := {y | absBar F v (finEmb F v τ y) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add, map_add] at *
    exact (absBar_add_le F v _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
    rw [(absBar_eq_zero F v).2 rfl]; exact zero_lt_one
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul, absBar_mul] at *
    calc absBar F v (finEmb F v τ c) * absBar F v (finEmb F v τ y) ≤ 1 * absBar F v (finEmb F v τ y) :=
          mul_le_mul_of_nonneg_right (absBar_le_one v τ c) zero_le
      _ < 1 := by rw [one_mul]; exact hy

theorem absBar_finEmb_one (τ : E →ₐ[F] FvBar F v) : absBar F v (finEmb F v τ 1) = 1 := by
  rw [map_one]; simpa using absBar_algebraMap F v 1

theorem prime_valuation_ne_top (τ : E →ₐ[F] FvBar F v) : p0 v τ ≠ ⊤ := by
  intro h
  have : (1 : intLoc F E v) ∈ p0 v τ := h ▸ Submodule.mem_top
  change absBar F v (finEmb F v τ ((1 : intLoc F E v) : Fv F v ⊗[F] E)) < 1 at this
  rw [OneMemClass.coe_one, absBar_finEmb_one] at this
  exact lt_irrefl _ this

theorem isUnit_of_absBar (y : intLoc F E v) (h : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ y) = 1) :
    IsUnit y := by
  have hne : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ (y : Fv F v ⊗[F] E) ≠ 0 := by
    intro τ h0
    have h1 := h τ
    rw [h0, (absBar_eq_zero F v).2 rfl] at h1
    exact zero_ne_one h1
  have hinj : Function.Injective (LinearMap.mulLeft (Fv F v) (y : Fv F v ⊗[F] E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [LinearMap.mulLeft_apply] at hz
    apply absFin_eq_zero_iff.1
    refine le_antisymm (Finset.sup_le fun τ _ => ?_) bot_le
    have h1 := congrArg (finEmb F v τ) hz
    rw [map_mul, map_zero] at h1
    rw [le_zero_iff, absBar_eq_zero]
    exact (mul_eq_zero.1 h1).resolve_left (hne τ)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  rw [LinearMap.mulLeft_apply] at hz
  have hzmem : z ∈ intLoc F E v := by
    rw [mem_intLoc_iff_absFin_le_one]
    refine Finset.sup_le fun τ _ => ?_
    have e1 := absBar_finEmb_one v τ
    have h1 := congrArg (fun w => absBar F v (finEmb F v τ w)) hz
    simp only [map_mul, absBar_mul, h τ, one_mul] at h1
    rw [h1, e1]
  exact isUnit_iff_exists_inv.2 ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

theorem emb_cases (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) (τ0 τ : E →ₐ[F] FvBar F v) :
    τ = τ0 ∨ τ = τ0.comp σ := by
  classical
  by_contra hne
  push_neg at hne
  have hd : τ0 ≠ τ0.comp σ := by
    intro h
    apply hσ1
    ext x
    have hx : τ0 x = τ0 (σ x) := congrArg (fun g => g x) h
    exact (τ0.injective hx).symm
  have hc := card_algHom_le_finrank F E (FvBar F v)
  rw [h2, ← Fintype.card_eq_nat_card] at hc
  have h3 : ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hd]
    simp [hne.1, hne.2]
  have h4 := Finset.card_le_univ ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v))
  omega

theorem exists_max (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) :
    ∃ 𝔭 : Ideal (intLoc F E v), 𝔭.IsMaximal ∧ ∀ x, x ∉ 𝔭 → sR v σ x ∉ 𝔭 → IsUnit x := by
  have τ0 : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal _ (prime_valuation_ne_top v τ0)
  refine ⟨𝔭, hmax, fun x hx hsx => isUnit_of_absBar v x fun τ => ?_⟩
  have hone : ∀ w : intLoc F E v, w ∉ 𝔭 → absBar F v (finEmb F v τ0 w) = 1 := by
    intro w hw
    exact le_antisymm (absBar_le_one v τ0 w) (not_lt.1 fun hlt => hw (hle (show w ∈ p0 v τ0 from hlt)))
  rcases emb_cases v σ hσ1 h2 τ0 τ with rfl | rfl
  · exact hone x hx
  · have h5 := hone _ hsx
    rwa [coe_sR, finEmb_sigR] at h5

theorem isUnit_two (h : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : intLoc F E v) := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = ((2 : F) : Fv F v) := by
      rw [show (2 : F) = 1 + 1 by norm_num, HeightOneSpectrum.adicCompletion.coe_add,
        HeightOneSpectrum.adicCompletion.coe_one]
      norm_num
    have e2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat (algebraMap (𝓞 F) F) 2).symm
    rw [e, HeightOneSpectrum.adicCompletion.valued_coe, e2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact h
  have hmem : (2 : Fv F v)⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have h0 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have h2 : (2 : Fv F v ⊗[F] E) = (2 : Fv F v) ⊗ₜ[F] (1 : E) := by
    rw [show (2 : Fv F v) = 1 + 1 by norm_num, TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    norm_num
  have hc : ((2 : intLoc F E v) : Fv F v ⊗[F] E) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  refine isUnit_iff_exists_inv.2 ⟨⟨_, tmul_mem_intLoc hmem (1 : 𝓞 E)⟩, Subtype.ext ?_⟩
  push_cast
  rw [hc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ h0, one_mul,
    ← Algebra.TensorProduct.one_def]

end PositivityTheory.Rg.Rsw.L.LGenK
