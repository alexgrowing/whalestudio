import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndicatorIdentity

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelCommTw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]

def IsTwEquiv (l' l : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) *
      Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)

variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}

theorem unram_val {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (u z : kˣ) (hz : valuation k ((z * u : kˣ) : k) = 1) :
    (χ z : ℂ) = (χ u : ℂ)⁻¹ := by
  have := congrArg (fun w : ℂˣ => (w : ℂ)) (hχ _ hz)
  simp only [map_mul, Units.val_mul, Units.val_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem theta_mem (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := fun h hh => by
  have hv := valuation_det_of_fix Q₀.lat (h := h) (by rw [← Pair.smul_lat, hh])
  have := hθ 1 h v (phiOneSB P₀ Q₀) (phiOneSB P₀ Q₀) fun x => by
    have e := phiOne_smul (x := x) (P := P₀) (Q := Q₀) 1 h
    rw [one_smul, hh] at e
    simp only [phiOneSB, map_one, hl _ hv, Units.val_one, one_mul]
    simpa using e
  simpa using this.symm

variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hl hθ P₀ Q₀ (φ P₀)

theorem KK_mem (φ : Form k n' V') : KK hl hθ P₀ Q₀ φ ∈ EqForm π := formOf_mem _ _ _

theorem KK_smul (φ : Form k n' V') (h : GL n k) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = π h (θ (φ P₀) (phiOneSB P₀ Q₀)) := formOf_smul π Q₀ _ h

theorem KK_move (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = ((l' u : ℂ) * (l u : ℂ))⁻¹ • θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ fun x => ?_).symm
  simp only [phiOneSB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, phiOne_smul, unram_val hl' u _ hg,
    unram_val hl u _ hh]
  rw [mul_inv]

theorem KK_same (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n}
    (hP : P.lat = P₀.lat) (hQ : Q.lat = Q₀.lat) : KK hl hθ P₀ Q₀ φ Q = θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [KK_move hl hθ P₀ Q₀ hl' hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP)
    (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]
  simp

theorem KK_up (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'}
    {Q : Pair k n} (hP : P.ker = P₀.lat) (hQ : Q.ker = Q₀.lat) :
    KK hl hθ P₀ Q₀ φ Q = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [Pair.smul_ker] at hP hQ
  exact KK_move hl hθ P₀ Q₀ hl' hφ q.unit g h (GlobalTheory.KernelComm.valuation_det q _ hP)
    (GlobalTheory.KernelComm.valuation_det q _ hQ)

theorem U_KK (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    U q (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (U q φ) := by
  classical
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (U_mem_EqForm q (KK_mem hl hθ P₀ Q₀ φ))
    (Submodule.smul_mem _ _ (KK_mem hl hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hl hθ P₀ Q₀ φ) Q₀ =
      ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ •
        ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hl hθ P₀ Q₀ hl' q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    exact (GlobalTheory.KernelComm.sum_target q P₁.hasVal_vec Q₀ x).trans (GlobalTheory.KernelComm.sum_source q P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hl hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    rw [KK_same hl hθ P₀ Q₀ hl' (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    GlobalTheory.KernelComm.card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'

theorem KK_dia (hl' : IsUnram l') (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hl hθ P₀ Q₀ (dia s φ) = dia s (KK hl hθ P₀ Q₀ φ) := by
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (KK_mem hl hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hl hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hl hθ P₀ Q₀ hl' hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hl hθ P₀ Q₀ hl' (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm

theorem KK_ram (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ φ ∈ Mram k n V := by
  have : Nm (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (Nm φ) := by
    simp only [Nm, LinearMap.sum_apply, map_sum, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  rw [show Nm φ = 0 from h, map_zero] at this
  exact this

theorem FFStar_KK (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (GsStar χ φ) := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hl hθ P₀ Q₀ hl' hφ h), h1,
    U_KK hl hθ P₀ Q₀ hl' q h2]

theorem KK_FFStar (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ (FFStar q χ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q χ (KK hl hθ P₀ Q₀ φ) := by
  rw [FFStar_KK hl hθ P₀ Q₀ hl' q χ hφ h, smul_smul, mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _)
    (Units.ne_zero _)), one_smul]

end GlobalTheory.KernelCommTw

namespace GlobalTheory.KernelCommTw

theorem kernelsCommuteTwisted : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = c • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀
  refine ⟨(l' q.unit : ℂ) * (l q.unit : ℂ), mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), ?_⟩
  intro V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommTw
