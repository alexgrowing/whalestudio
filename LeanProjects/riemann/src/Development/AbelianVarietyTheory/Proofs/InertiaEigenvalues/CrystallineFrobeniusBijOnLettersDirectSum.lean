import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.PhiD

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_letter (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ (∀ g, actVB PD ρ g x = x) ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp [DcrisL, Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem phi_injective : Function.Injective (φVB PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj

theorem iota_injective : Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem phi_mem (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B),
      φVB PD (LL := LL) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro x hx
  rw [mem_letter] at hx ⊢
  refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  rw [← h2, hx.2, map_smul, h]

theorem iSupIndep_letter : iSupIndep fun τ : K₀ →ₐ[Qp] LL => DcrisL PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K₀) (a : LL) => Module.End.eigenspace
      (mulVB (Qp := Qp) (K₀ := K₀) (B := B) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K₀ →ₐ[Qp] LL => (τ : K₀ → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ((mem_letter PD ρ τ x).1 hx).2

variable [FiniteDimensional LL V] [IsDomain B]

theorem phi_bijOn (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ)
    (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    Set.BijOn (φVB PD (LL := LL) (V := V)) (DcrisL PD ρ τ') (DcrisL PD ρ τ) := by
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine ⟨phi_mem PD ρ τ τ' h, (phi_injective PD).injOn, fun y hy => ?_⟩
  have hi : Function.Injective ((φVB PD (LL := LL) (V := V)).restrict (phi_mem PD ρ τ τ' h)) :=
    fun x y hxy => Subtype.ext (phi_injective PD (congrArg Subtype.val hxy))
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV])).1 hi
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem iSup_letter (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ) :
    (⨆ τ : K₀ →ₐ[Qp] LL, DcrisL PD ρ τ) = Dcris PD ρ := by
  classical
  haveI := PD.finK₀
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine Submodule.eq_of_le_of_finrank_eq (iSup_le fun τ => inf_le_left) ?_
  have hinj := (iSupIndep_letter PD ρ).dfinsupp_lsum_injective
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hinj]
  change finrank LL (DirectSum _ fun τ => ↥(DcrisL PD ρ τ)) = _
  rw [Module.finrank_directSum]
  simp only [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hc]
  exact hV.symm

end General

theorem phi_letters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW l _ K s LL h W T hV
  haveI := GlobalTheory.RegularRing.isDomain_of_tied (D.locT l) K
  have hc : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K) := by
    rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  refine ⟨fun i => phi_bijOn _ T.ρ hc hV _ _ fun c => ?_, ?_,
    (iSupIndep_letter ((D.loc l).PD K) T.ρ).comp W.emb_bij.1, iota_injective _⟩
  · have := AlgHom.congr_fun (W.emb_σ (i - 1)) c
    rw [sub_add_cancel] at this
    exact this.symm
  · rw [← iSup_letter _ T.ρ hc hV]
    exact W.emb_bij.2.iSup_comp (fun τ => DcrisL ((D.loc l).PD K) T.ρ τ)

end GlobalTheory.NL.PhiD
