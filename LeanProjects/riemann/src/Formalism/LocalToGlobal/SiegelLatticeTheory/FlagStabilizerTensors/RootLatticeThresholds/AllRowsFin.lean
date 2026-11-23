import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsConv

noncomputable section

open MeasureTheory NumberField

namespace Formalism.L2.SG.Pf.AllRowsFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsConv

variable {D : D7} (X : HidaSetting D)

def V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal

theorem g_pos : 1 ≤ X.B.g := Nat.one_le_iff_ne_zero.2 (Formalism.L2.SG.Pf.RowDictPf.level_ne_zero X)

theorem Kg_fin : X.B.μf (X.B.I.Kg X.B.g) < ⊤ := by
  have hK : IsCompact X.B.I.Kset := Formalism.L2.SG.Closed.AutKCompact_holds X.B.I
  exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) hK.measure_lt_top

theorem V_pos : 0 < V X := by
  have hpos : 0 < X.B.μf (X.B.I.Kg X.B.g) :=
    (X.B.I.topf_open X.B.g (g_pos X)).measure_pos X.B.μf ⟨1, Formalism.L2.SG.AllRowsOf.one_mem_Kg X⟩
  exact ENNReal.toReal_pos hpos.ne' (Kg_fin X).ne

theorem V_ne : (V X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (V_pos X).ne'

def BiInv (f : X.B.I.Gf → ℂ) : Prop :=
  (∀ x, f x ≠ 0 → x ∈ X.B.I.Kset) ∧ (∀ x, ∀ n ∈ X.B.I.Kg X.B.g, f (x * n) = f x) ∧
    (∀ x, ∀ n ∈ X.B.I.Kg X.B.g, f (n * x) = f x)

theorem biInv_e : BiInv X X.B.e := by
  refine ⟨X.B.e_adm.2.2.2.2.1, fun x n hn => ?_, fun x n hn => ?_⟩
  · have := X.B.e_adm.2.2.2.2.2.1 x 1 (Formalism.L2.SG.AllRowsOf.one_mem_Kg X) n hn
    rwa [one_mul] at this
  · have := X.B.e_adm.2.2.2.2.2.1 x n hn 1 (Formalism.L2.SG.AllRowsOf.one_mem_Kg X)
    rwa [mul_one] at this

theorem biInv_egA (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ) :
    BiInv X (egA X a) := by
  refine ⟨fun x hx => by_contra fun h => hx (egA_of_not_mem X a h), fun x n hn => egA_mul X a x hn, fun x n hn => ?_⟩
  by_cases hx : x ∈ X.B.I.Kset
  · have hnx : n * x ∈ X.B.I.Kset := K_mul X.B.I hn.1 hx
    have hn1 : rhoX X ⟨n, hn.1⟩ = 1 := (rhoX_eq_one_iff X _).2 hn
    have e : rhoX X ⟨n * x, hnx⟩ = rhoX X ⟨x, hx⟩ := by
      rw [show (⟨n * x, hnx⟩ : KSub X.B.I) = ⟨n, hn.1⟩ * ⟨x, hx⟩ from rfl, map_mul, hn1, one_mul]
    calc egA X a (n * x) = a.coeff (rhoX X ⟨n * x, hnx⟩) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) :=
          egA_rhoX X a ha ⟨n * x, hnx⟩
      _ = a.coeff (rhoX X ⟨x, hx⟩) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by rw [e]
      _ = egA X a x := (egA_rhoX X a ha ⟨x, hx⟩).symm
  · have hnx : n * x ∉ X.B.I.Kset := fun h => hx (by
      have := K_mul X.B.I (K_inv X.B.I hn.1) h
      rwa [inv_mul_cancel_left] at this)
    rw [egA_of_not_mem X a hnx, egA_of_not_mem X a hx]

theorem biInv_eT (S : Set (Tup2 D)) : BiInv X (eT X S) :=
  ⟨fun x hx => by_contra fun h => hx (eT_of_not_mem X S h), fun x n hn => eT_mul X S x hn,
    fun x n hn => eT_mul_left X S x hn⟩

theorem conv_sum [Fintype (KSub X.B.I ⧸ KgN X.B.I X.B.g)] {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) (x : X.B.I.Gf) :
    X.B.I.convF X.B.μf f₁ f₂ x = (V X : ℂ) * ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g,
      f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) * f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * x) := by
  rw [convF_fin X.B.I X.B.μf (g_pos X) (Kg_fin X) hf₁.1 hf₁.2.1 hf₂.2.2 x]
  rfl

instance instNeZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finiteReductionGroup (D : D7) : Fintype (G0g D.nd) := by classical infer_instance

variable {X} (hS : Function.Surjective (rhoX X))
include hS

def sec (γ : G0g D.nd) : KSub X.B.I := Classical.choose (hS γ)

theorem rho_sec (γ : G0g D.nd) : rhoX X (sec hS γ) = γ := Classical.choose_spec (hS γ)

def hat (f : X.B.I.Gf → ℂ) (γ : G0g D.nd) : ℂ := (V X : ℂ) * f (sec hS γ)

theorem val_hat {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (x : KSub X.B.I) :
    f x = hat hS f (rhoX X x) / (V X : ℂ) := by
  unfold hat
  have hk' : (((sec hS (rhoX X x))⁻¹ * x : KSub X.B.I) : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
    (rhoX_eq_one_iff X _).1 (by rw [map_mul, map_inv, rho_sec, inv_mul_cancel])
  have e : (x : X.B.I.Gf) =
      (sec hS (rhoX X x) : X.B.I.Gf) * (((sec hS (rhoX X x))⁻¹ * x : KSub X.B.I) : X.B.I.Gf) := by
    push_cast
    group
  rw [e, hf.2.1 _ _ hk', mul_div_cancel_left₀ _ (V_ne X)]

theorem ker_eq : (rhoX X).ker = KgN X.B.I X.B.g := by
  ext x
  rw [MonoidHom.mem_ker, rhoX_eq_one_iff]
  rfl

def qEquiv : (KSub X.B.I ⧸ KgN X.B.I X.B.g) ≃* G0g D.nd :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq hS).symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ hS)

theorem qEquiv_mk (k : KSub X.B.I) : qEquiv hS (QuotientGroup.mk k) = rhoX X k := rfl

theorem qEquiv_out (q : KSub X.B.I ⧸ KgN X.B.I X.B.g) : qEquiv hS q = rhoX X q.out := by
  have h := qEquiv_mk hS q.out
  rwa [QuotientGroup.out_eq'] at h

def instFintypeQ : Fintype (KSub X.B.I ⧸ KgN X.B.I X.B.g) := Fintype.ofEquiv _ (qEquiv hS).symm.toEquiv

theorem biInv_conv {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) :
    BiInv X (X.B.I.convF X.B.μf f₁ f₂) := by
  haveI := instFintypeQ hS
  refine ⟨fun x hx => ?_, fun x n hn => ?_, fun x n hn => ?_⟩
  · by_contra hxK
    apply hx
    rw [conv_sum X hf₁ hf₂]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q _ => ?_)
    have : f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * x) = 0 := by
      by_contra h
      apply hxK
      have := K_mul X.B.I (q.out : KSub X.B.I).2 (hf₂.1 _ h)
      rwa [mul_inv_cancel_left] at this
    rw [this, mul_zero]
  · rw [conv_sum X hf₁ hf₂, conv_sum X hf₁ hf₂]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_assoc, hf₂.2.1 _ n hn]
  · rw [conv_sum X hf₁ hf₂, conv_sum X hf₁ hf₂]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    set c : X.B.I.Gf := ((q.out : KSub X.B.I) : X.B.I.Gf)
    have hc : c⁻¹ ∈ X.B.I.Kset := K_inv X.B.I (q.out : KSub X.B.I).2
    have hn' : c⁻¹ * n * c⁻¹⁻¹ ∈ X.B.I.Kg X.B.g := Kg_conj' X.B.I X.B.g hc hn
    have e : c⁻¹ * (n * x) = (c⁻¹ * n * c⁻¹⁻¹) * (c⁻¹ * x) := by group
    rw [e, hf₂.2.2 _ _ hn']

theorem conv_hat {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) (γ : G0g D.nd) :
    hat hS (X.B.I.convF X.B.μf f₁ f₂) γ = ∑ δ : G0g D.nd, hat hS f₁ δ * hat hS f₂ (δ⁻¹ * γ) := by
  haveI := instFintypeQ hS
  have key : ∀ q : KSub X.B.I ⧸ KgN X.B.I X.B.g,
      hat hS f₁ (qEquiv hS q) * hat hS f₂ ((qEquiv hS q)⁻¹ * γ) =
        (V X : ℂ) * ((V X : ℂ) * (f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) *
          f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf)))) := by
    intro q
    have hm : ((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf) ∈ X.B.I.Kset :=
      K_mul X.B.I (K_inv X.B.I (q.out : KSub X.B.I).2) (sec hS γ).2
    have e2 : rhoX X ⟨_, hm⟩ = (qEquiv hS q)⁻¹ * γ := by
      have : (⟨_, hm⟩ : KSub X.B.I) = (q.out)⁻¹ * sec hS γ := rfl
      rw [this, map_mul, map_inv, rho_sec, qEquiv_out]
    have h1 : hat hS f₁ (rhoX X q.out) = (V X : ℂ) * f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) := by
      rw [val_hat hS hf₁ q.out]; field_simp [V_ne X]
    have h2 : hat hS f₂ (rhoX X ⟨_, hm⟩) = (V X : ℂ) * f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf)) := by
      rw [val_hat hS hf₂ ⟨_, hm⟩]; field_simp [V_ne X]
    rw [qEquiv_out, ← qEquiv_out hS q, ← e2, qEquiv_out, h1, h2]
    ring
  calc hat hS (X.B.I.convF X.B.μf f₁ f₂) γ = (V X : ℂ) * X.B.I.convF X.B.μf f₁ f₂ (sec hS γ) := rfl
    _ = (V X : ℂ) * ((V X : ℂ) * ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g, f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) *
          f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf))) := by rw [conv_sum X hf₁ hf₂]
    _ = ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g, hat hS f₁ (qEquiv hS q) * hat hS f₂ ((qEquiv hS q)⁻¹ * γ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => (key q).symm
    _ = ∑ δ : G0g D.nd, hat hS f₁ δ * hat hS f₂ (δ⁻¹ * γ) :=
      Fintype.sum_equiv (qEquiv hS).toEquiv _ _ (fun _ => rfl)

theorem hat_inj {f f' : X.B.I.Gf → ℂ} (hf : BiInv X f) (hf' : BiInv X f') (h : ∀ γ, hat hS f γ = hat hS f' γ) :
    f = f' := by
  funext x
  by_cases hx : x ∈ X.B.I.Kset
  · have e1 := val_hat hS hf ⟨x, hx⟩
    have e2 := val_hat hS hf' ⟨x, hx⟩
    simp only at e1 e2
    rw [e1, e2, h]
  · have h1 : f x = 0 := by
      by_contra h0
      exact hx (hf.1 x h0)
    have h2 : f' x = 0 := by
      by_contra h0
      exact hx (hf'.1 x h0)
    rw [h1, h2]

theorem hat_egA (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (γ : G0g D.nd) : hat hS (egA X a) γ = a.coeff γ := by
  unfold hat
  rw [egA_rhoX (X := X) a ha, rho_sec]
  show (V X : ℂ) * (a.coeff γ / (V X : ℂ)) = a.coeff γ
  field_simp [V_ne X]

theorem hat_eT (S : Set (Tup2 D)) (γ : G0g D.nd) :
    hat hS (eT X S) γ = ∑ δ : G0g D.nd, hat hS X.B.e δ * (ES S).coeff (δ⁻¹ * γ) := by
  unfold eT
  rw [conv_hat hS (biInv_e X) (biInv_egA X _ (ES_conj S))]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [hat_egA hS _ (ES_conj S)]

theorem hat_e_idem (γ : G0g D.nd) : ∑ δ : G0g D.nd, hat hS X.B.e δ * hat hS X.B.e (δ⁻¹ * γ) = hat hS X.B.e γ := by
  rw [← conv_hat hS (biInv_e X) (biInv_e X), X.B.e_adm.2.1]

end Formalism.L2.SG.Pf.AllRowsFin
