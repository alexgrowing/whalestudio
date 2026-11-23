import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemImgLatIff
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {ι : Type} [Fintype ι] {V V₁ : Type}

section Idx

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.idx (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (h : relIdx (latA Λ δ Ae) Λ ≠ 0) :
    relIdx (latA Λ₁ δ₁ Ae₁) Λ₁ ≠ 0 := by
  obtain ⟨S, hS⟩ := (repsExist V _ _ h).1
  let f : S → Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁ := fun x =>
    QuotientAddGroup.mk ⟨e x.1 i₀, (c.lat x.1).1 (hS.1 x.1 x.2) i₀⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      have hY : e.symm (Pi.single i₀ (y : V₁)) ∈ Λ := by
        refine (c.lat _).2 fun i => ?_
        rw [LinearEquiv.apply_symm_apply]
        by_cases hi : i = i₀
        · subst hi; rw [Pi.single_eq_same]; exact y.2
        · rw [Pi.single_eq_of_ne hi]; exact Λ₁.zero_mem
      obtain ⟨x, hx, hxy⟩ := hS.2.2 _ hY
      refine ⟨⟨x, hx⟩, ?_⟩
      have h2 := (c.mem_latA _).1 hxy i₀
      rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.single_eq_same] at h2
      show (QuotientAddGroup.mk _ : Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) = QuotientAddGroup.mk y
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -(e x i₀) + (y : V₁) ∈ _
      rwa [neg_add_eq_sub]
  haveI : Finite (Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) := Finite.of_surjective f hf
  exact AddSubgroup.index_ne_zero_of_finite

end Idx

theorem unit_sq (a : ℂ) (ha : a ≠ 0) : ((‖a‖ : ℂ) / a) ^ 2 = conj a / a := by
  have h : ((‖a‖ : ℂ)) ^ 2 = a * conj a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [div_pow, h]
  field_simp

variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  [FiniteDimensional ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem const_copies (hLat : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ)
    (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁)
    (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (hn : Even (Fintype.card ι)) (hr : Even (Module.finrank ℂ V₁))
    (hG : ∀ S₁ : Finset V₁, IsReps (latA Λ₁ δ₁ Ae₁) Λ₁ S₁ → gaussC H₁ α₁ Ae₁ S₁ ^ 2 = 1)
    (θ : V → ℂ) (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ = LinearMap.det (δ₁ : V₁ →ₗ[ℂ] V₁) ^ (Fintype.card ι / 2) •
      inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · haveI : Subsingleton V := e.injective.subsingleton
    have h1 : imgLat (δ : V →ₗ[ℂ] V) Λ = Λ := by
      ext x
      rw [Subsingleton.elim x 0]
      exact ⟨fun _ => Λ.zero_mem, fun _ => AddSubgroup.zero_mem _⟩
    rw [h1, Formalism.L2.Ker.inter_self H hU.herm Λ α hU.semi hθ.2, Fintype.card_eq_zero, Nat.zero_div, pow_zero, one_smul]
    funext z
    show θ (δ.symm z) = θ z
    rw [Subsingleton.elim (δ.symm z) z]
  · obtain ⟨S₁, hS₁⟩ := (repsExist V₁ _ _ (c.idx i₀ (UC.latA_idx_ne hLat hU))).1
    have hc := unitaryConstant V H Λ α δ Ae hLat hU hLine (prodReps e S₁) (c.reps hS₁) θ hθ
    rw [hc]
    congr 1
    obtain ⟨k, hk⟩ := hn
    have hk2 : Fintype.card ι / 2 = k := by omega
    have hk' : Fintype.card ι = 2 * k := by omega
    have ha : LinearMap.det (Ae₁ : V₁ →ₗ[ℂ] V₁) ≠ 0 := (LinearEquiv.isUnit_det' Ae₁).ne_zero
    have hd := detCayley V₁ H₁ hH₁ hP₁ δ₁ Ae₁ hI₁ hA₁
    rw [hr.neg_one_pow, one_mul] at hd
    rw [c.gauss hS₁.1, det_copies e (Ae : V →ₗ[ℂ] V) (Ae₁ : V₁ →ₗ[ℂ] V₁) c.cay, hk2, hk', pow_mul (gaussC _ _ _ _),
      hG S₁ hS₁, one_pow, mul_one, norm_pow, Complex.ofReal_pow, ← div_pow, pow_mul, unit_sq _ ha, hd,
      mul_div_assoc, div_self ha, mul_one]

end Formalism.L2.PairingIndexBounds.Eq.J
