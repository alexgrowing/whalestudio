import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairContragredientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexiveStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitFlip Matrix
open scoped TensorProduct

namespace GlobalTheory.HoweFlipPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def trH (m n : ℕ) : Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin n) (Fin m) k where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

def trSB (m n : ℕ) : SB (Matrix (Fin m) (Fin n) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin m) k) where
  toFun Φ := ⟨fun Y => (Φ : Matrix (Fin m) (Fin n) k → ℂ) Yᵀ,
    Φ.2.1.comp_continuous continuous_id.matrix_transpose, Φ.2.2.comp_homeomorph (trH n m)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem trSB_apply (m n : ℕ) (Φ : SB (Matrix (Fin m) (Fin n) k)) (Y : Matrix (Fin n) (Fin m) k) :
    (trSB m n Φ : Matrix (Fin n) (Fin m) k → ℂ) Y = (Φ : Matrix (Fin m) (Fin n) k → ℂ) Yᵀ := rfl

theorem trSB_trSB (m n : ℕ) (Φ : SB (Matrix (Fin m) (Fin n) k)) : trSB n m (trSB m n Φ) = Φ := by
  ext Y; simp

theorem nabs_rpow_cast (x : kˣ) (r : ℝ) : ((nabs k x ^ r : ℝ) : ℂ) = apow x (r : ℂ) := by
  rw [apow, Complex.ofReal_cpow (show (0 : ℝ) ≤ nabs k x from NNReal.coe_nonneg _)]

def chi (d : ℕ) (ν α : kˣ →* ℂˣ) : GL (Fin d) k →* ℂˣ :=
  (α / ν).comp (Matrix.GeneralLinearGroup.det.comp (SplitFlip.invT (k := k) (D := Fin d)))

theorem om_tr (n d : ℕ) (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (h' : GL (Fin d) k)
    (Φ : Matrix (Fin d) (Fin n) k → ℂ) :
    ((chi d ν α h' : ℂˣ) : ℂ) • (fun Y : Matrix (Fin n) (Fin d) k => om ν g h' Φ Yᵀ) =
      omB ν α g (SplitFlip.invT h') (fun Y => Φ Yᵀ) := by
  funext Y
  have hx : Matrix.GeneralLinearGroup.det (SplitFlip.invT h') = (Matrix.GeneralLinearGroup.det h')⁻¹ := gdet_invT h'
  have harg : (g.valᵀ * Y * (SplitFlip.invT h').val)ᵀ = (h'⁻¹ : GL (Fin d) k).val * Yᵀ * g.val := by
    rw [invT_val, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, Matrix.mul_assoc]
  simp only [chi, om, omB, Pi.smul_apply, smul_eq_mul, MonoidHom.comp_apply, gdet, hx, harg, nabs_rpow_cast,
    Fintype.card_fin, MonoidHom.div_apply, apow_inv, map_inv, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  push_cast
  rw [neg_div]
  field_simp

theorem continuous_invT' (d : ℕ) : Continuous (SplitFlip.invT (k := k) (D := Fin d)) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem isSmoothChar_chi (d : ℕ) {ν α : kˣ →* ℂˣ} (hν : IsSmoothChar ν) (hα : IsSmoothChar α) :
    IsSmoothChar (chi d ν α) := by
  have h : IsSmoothChar (α / ν) := by rw [div_eq_mul_inv]; exact hα.mul hν.inv
  exact h.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp (continuous_invT' d))

theorem isAdmissible_twist' {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {χ : G →* ℂˣ} (hπ : IsAdmissible π)
    (hχ : IsSmoothChar χ) : IsAdmissible (twist π χ) := by
  refine ⟨isSmooth_twist hπ.1 hχ, fun K ho hc => ?_⟩
  have h1 : IsOpen ((K ⊓ χ.ker : Subgroup G) : Set G) := ho.inter hχ
  have h2 : IsCompact ((K ⊓ χ.ker : Subgroup G) : Set G) :=
    hc.inter_right (Subgroup.isClosed_of_isOpen _ hχ)
  have := hπ.2 _ h1 h2
  refine Submodule.finiteDimensional_of_le (S₂ := fixed π (K ⊓ χ.ker)) fun v hv => ?_
  intro h
  have h3 := hv ⟨h.1, h.2.1⟩
  have h4 : χ h.1 = 1 := h.2.2
  simp only [fixed, eig, MonoidHom.one_apply, Units.val_one, one_smul] at h3 ⊢
  simpa [twist_apply, h4] using h3

theorem isAdmissible_comp_invT {d : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin d) k) V} (hπ : IsAdmissible π) :
    IsAdmissible (π.comp (SplitFlip.invT (k := k) (D := Fin d)) : Representation ℂ (GL (Fin d) k) V) := by
  have hc := continuous_invT' (k := k) d
  have hinv : ∀ g : GL (Fin d) k, SplitFlip.invT (SplitFlip.invT g) = g := invT_invT
  have ho : IsOpenMap (SplitFlip.invT (k := k) (D := Fin d)) := fun U hU => by
    have : (SplitFlip.invT (k := k) (D := Fin d)) '' U = SplitFlip.invT ⁻¹' U := by
      ext g; exact ⟨by rintro ⟨x, hx, rfl⟩; simpa [hinv] using hx, fun hg => ⟨_, hg, hinv g⟩⟩
    rw [this]; exact hU.preimage hc
  refine ⟨fun v => (hπ.1 v).preimage hc, fun K hKo hKc => ?_⟩
  have e : fixed (π.comp (SplitFlip.invT (k := k) (D := Fin d)) : Representation ℂ (GL (Fin d) k) V) K =
      fixed π (K.map SplitFlip.invT) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact hπ.2 _ (ho _ hKo) (hKc.image hc)

variable {n d : ℕ} {ν α : kˣ →* ℂˣ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def flipRep (ν α : kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin d) k) U) : Representation ℂ (GL (Fin d) k) U :=
  twist (π.comp (SplitFlip.invT (k := k) (D := Fin d))) (chi d ν α)

theorem thetaPair_flip (π : Representation ℂ (GL (Fin d) k) U) (σ : Representation ℂ (GL (Fin n) k) W)
    (Q : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] W) (hQ0 : Q ≠ 0)
    (hQ : ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : SB (Matrix (Fin n) (Fin d) k)),
      (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = omB ν α g h Ψ → ∀ u, Q Ψ' (π h u) = σ g (Q Ψ u)) :
    ThetaPair ν σ (flipRep ν α π) := by
  refine ⟨Q ∘ₗ trSB d n, fun h0 => hQ0 (LinearMap.ext fun Ψ => ?_), fun g h' Φ Φ' hΦ F => ?_⟩
  · have := LinearMap.congr_fun h0 (trSB n d Ψ)
    simpa [trSB_trSB] using this
  · let Ψ'' : SB (Matrix (Fin n) (Fin d) k) := ((chi d ν α h' : ℂˣ) : ℂ) • trSB d n Φ'
    have hΨ : (Ψ'' : Matrix (Fin n) (Fin d) k → ℂ) = omB ν α g (SplitFlip.invT h') (trSB d n Φ) := by
      have e := om_tr n d ν α g h' Φ
      rw [← hΦ] at e
      exact e
    have key := hQ g (SplitFlip.invT h') (trSB d n Φ) Ψ'' hΨ F
    simp only [Ψ'', map_smul, LinearMap.smul_apply] at key
    simp only [LinearMap.comp_apply, flipRep, twist_apply, MonoidHom.coe_comp, Function.comp_apply, map_smul]
    exact key

theorem isSmooth_of_pair (hν : IsSmoothChar ν) (π : Representation ℂ (GL (Fin d) k) U)
    (σ : Representation ℂ (GL (Fin n) k) W) (hσ : σ.IsIrreducible)
    (Q : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] W) (hQ0 : Q ≠ 0)
    (hQ : ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : SB (Matrix (Fin n) (Fin d) k)),
      (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = omB ν α g h Ψ → ∀ u, Q Ψ' (π h u) = σ g (Q Ψ u)) :
    IsSmooth σ := by
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  let S : Subrepresentation σ := ⟨smoothPart σ, fun g v hv => smoothPart_stable σ g v hv⟩
  obtain ⟨Ψ, u, hne⟩ : ∃ Ψ u, Q Ψ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ0 (LinearMap.ext fun Ψ => LinearMap.ext fun u => h Ψ u)
  have hmem : Q Ψ u ∈ smoothPart σ := by
    have hop := (om_isSmoothRepresentation k (Fin n) (Fin d) ν hν).2.2.2.2 (trSB n d Ψ).1 (trSB n d Ψ).2
    have hO : IsOpen {g : GL (Fin n) k | om ν g 1 (trSB n d Ψ).1 = (trSB n d Ψ).1} :=
      hop.preimage (Continuous.prodMk continuous_id continuous_const)
    have h1 : (1 : GL (Fin n) k) ∈ {g : GL (Fin n) k | om ν g 1 (trSB n d Ψ).1 = (trSB n d Ψ).1} :=
      (om_isSmoothRepresentation k (Fin n) (Fin d) ν hν).1 _
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hO.mem_nhds h1) fun g hg => ?_)
    have hB : (Ψ : Matrix (Fin n) (Fin d) k → ℂ) = omB ν α g 1 Ψ := by
      have := om_tr n d ν α g 1 (trSB n d Ψ).1
      simp only [map_one, Units.val_one, one_smul] at this
      have e2 : (fun Y => (trSB n d Ψ : Matrix (Fin d) (Fin n) k → ℂ) Yᵀ) = (Ψ : Matrix (Fin n) (Fin d) k → ℂ) := by
        funext Y; simp
      rw [e2] at this
      rw [← this]
      funext Y
      have hg' : om ν g 1 (trSB n d Ψ).1 = (trSB n d Ψ).1 := hg
      rw [hg']
      simp
    have := hQ g 1 Ψ Ψ hB u
    simpa using this.symm
  rcases eq_bot_or_eq_top S with h | h
  · exact absurd (show Q Ψ u = 0 from (Submodule.mem_bot ℂ).1 (show Q Ψ u ∈ (⊥ : Subrepresentation σ).toSubmodule from h ▸ hmem)) hne
  · intro v
    have : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact this

end GlobalTheory.HoweFlipPair

open GlobalTheory.HoweFlipPair in

theorem GlobalTheory.HoweFlipPair.uniq : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν α : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU ν → GlobalTheory.KSplit.IsSmU α →
    ∀ (U V V' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (GL (Fin d) k) U) (ρ : Representation ℂ (GL (Fin n) k) V) (ρ' : Representation ℂ (GL (Fin n) k) V'),
      π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π → ρ.IsIrreducible → ρ'.IsIrreducible →
      ∀ (P : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] V) (P' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] V'),
        P ≠ 0 → P' ≠ 0 →
        (∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)),
          (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omB ν α g h Ψ → ∀ u, P Ψ' (π h u) = ρ g (P Ψ u)) →
        (∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)),
          (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omB ν α g h Ψ → ∀ u, P' Ψ' (π h u) = ρ' g (P' Ψ u)) →
        Nonempty (ρ.Equiv ρ') := by
  intro hK k _ _ _ _ n d ν α hν hα U V V' _ _ _ _ _ _ π ρ ρ' hπi hπa hρi hρ'i P P' hP0 hP'0 hP hP'
  have HD := GlobalTheory.T.howe_duality_of_minguez hK.minguezThetaGL
  have hνs : IsSmoothChar ν := hν.1
  have hαs : IsSmoothChar α := hα.1
  have hχ := isSmoothChar_chi (k := k) d hνs hαs
  have hsurj : Function.Surjective (SplitFlip.invT (k := k) (D := Fin d)) := fun g => ⟨SplitFlip.invT g, invT_invT g⟩
  have hπ'a : IsAdmissible (flipRep ν α π) := isAdmissible_twist' (isAdmissible_comp_invT hπa) hχ
  have hπ'i : (flipRep ν α π).IsIrreducible :=
    GlobalTheory.HoweBridge.irr_twist (GlobalTheory.HoweBridge.irr_comp _ hsurj hπi) _
  have hρs := isSmooth_of_pair hνs π ρ hρi P hP0 hP
  have hρ's := isSmooth_of_pair hνs π ρ' hρ'i P' hP'0 hP'
  have hq := GlobalTheory.T.theta_pair_contragredient_quotient k n d ν V U ρ (flipRep ν α π) hνs hπ'a (thetaPair_flip π ρ P hP0 hP)
  have hq' := GlobalTheory.T.theta_pair_contragredient_quotient k n d ν V' U ρ' (flipRep ν α π) hνs hπ'a (thetaPair_flip π ρ' P' hP'0 hP')
  have hc := GlobalTheory.T.smoothContragredient_irreducible_and_reflexive (GL (Fin d) k) (GlobalTheory.ThetaLiftGL.compactOpen_basis k d) U U _ _ hπ'a hπ'a
  exact (HD k n d ν hνs).2 V V' _ ρ ρ' (contra (flipRep ν α π)) hρs hρi hρ's hρ'i
    (isSmooth_contra _) (hc.1 hπ'i) hq hq'
