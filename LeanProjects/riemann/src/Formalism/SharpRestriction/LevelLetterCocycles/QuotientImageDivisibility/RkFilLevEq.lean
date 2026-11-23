import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct Formalism.BasicNotions

section Even

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable [NeZero n] (W : LocWach PD LL O v n)

theorem rk_filLev_eq (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i) (a : ℤ) :
    Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a = FildR PD T.ρ τ a := by
  rw [((hQ hK T.V T.ρ hT).2 τ).2.2 a, hτ]
  unfold Formalism.MainNotions.WachCoordinates.FilLev
  simp only [Nat.cast_zero, sub_zero, pow_zero]
  congr 1
  exact Submodule.map_id _

theorem rk_ιDi_eq (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i = DdRE PD T.ρ τ := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
  rw [← hτ]
  exact rk_DcrisL_map W hK hQ T hT τ

variable {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}

private theorem exists_embedding_extending_emb (hK : Function.Bijective (algebraMap K₀ K)) (i : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i := by
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  refine ⟨(W.emb i).comp (e.symm : K →ₐ[Qp] K₀), ?_⟩
  ext x
  show W.emb i (e.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb i x
  rw [show IsScalarTower.toAlgHom Qp K₀ K x = e x from rfl, e.symm_apply_apply]

private theorem eta_le_b_add_of_SetCS (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n) : η ≤ b i + S := by
  obtain ⟨-, hp11, -, -, -, -, -, -, hbig, -⟩ := hS
  have hp : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hlam : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.lam
    rcases Nat.eq_zero_or_pos (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) with h0 | h0
    · rw [h0]; simp
    · have : (1 : ℝ) ≤ 2 * ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      have := Real.logb_nonneg (by linarith : (1 : ℝ) < PD.p) this
      linarith
  have hA : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.aR
    have h1 : 0 ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (sq_nonneg _)
    linarith
  have h := hbig i
  have : (η : ℝ) ≤ (b i : ℝ) := by linarith
  have : η ≤ b i := by exact_mod_cast this
  omega

theorem rk_evenQ₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 0) :
    finrank LL ↥((Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (-(η : ℤ))).map
      (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 0).mkQ) ≤ m := by
  have hK : Function.Bijective (algebraMap K₀ K) := hS.1.1
  have hT2 : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hsum := hS.2.2.2.2.2.2.2.1
  obtain ⟨τ, hτ⟩ := exists_embedding_extending_emb W hK i
  rw [rk_filLev_eq W hK hQ T₂ hT2 i τ hτ, rk_filLev_eq W hK hQ T₂ hT2 i τ hτ]
  haveI hfd : FiniteDimensional LL ↥(DdRE PD T₂.ρ τ) := ((hQ hK T₂.V T₂.ρ hT2).2 τ).1
  have hfdF : ∀ a : ℤ, FiniteDimensional LL ↥(FildR PD T₂.ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (show FildR PD T₂.ρ τ a ≤ DdRE PD T₂.ρ τ from inf_le_left)
  haveI := hfdF (-(η : ℤ))
  haveI := hfdF 0
  have hNA : FildR PD T₂.ρ τ 0 ≤ FildR PD T₂.ρ τ (-(η : ℤ)) :=
    rk_fildR_anti (PD := PD) (ρ := T₂.ρ) (τ := τ) (by omega)
  have hrk := LinearMap.finrank_range_add_finrank_ker
    ((FildR PD T₂.ρ τ 0).mkQ.domRestrict (FildR PD T₂.ρ τ (-(η : ℤ))))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hNA).finrank_eq] at hrk

  have htel : ∀ k : ℕ, (finrank LL ↥(FildR PD T₂.ρ τ (-(k : ℤ))) : ℤ) - finrank LL ↥(FildR PD T₂.ρ τ 0) =
      ∑ j ∈ Finset.range k, multV PD T₂.ρ τ (-((j : ℤ) + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold Formalism.WeaklyAdmissibleFiltrations.multV
      have e1 : (-((k : ℤ) + 1) + 1) = -(k : ℤ) := by ring
      have e2 : (-(((k + 1 : ℕ)) : ℤ)) = -((k : ℤ) + 1) := by push_cast; ring
      rw [e1, e2]
      ring
  let emb : ℕ ↪ ℤ := ⟨fun j : ℕ => -((j : ℤ) + 1), fun x y h => by have h' : -((x : ℤ) + 1) = -((y : ℤ) + 1) := h; omega⟩
  have hsub : (Finset.range η).map emb ⊆
      Finset.Icc (-(η : ℤ)) (η : ℤ) := by
    intro a ha
    rw [Finset.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    show -(η : ℤ) ≤ -((j : ℤ) + 1) ∧ -((j : ℤ) + 1) ≤ (η : ℤ)
    omega
  have h2 : ∑ j ∈ Finset.range η, multV PD T₂.ρ τ (-((j : ℤ) + 1)) ≤
      ∑ a ∈ Finset.Icc (-(η : ℤ)) (η : ℤ), multV PD T₂.ρ τ a := by
    calc ∑ j ∈ Finset.range η, multV PD T₂.ρ τ (-((j : ℤ) + 1))
        = ∑ a ∈ (Finset.range η).map emb, multV PD T₂.ρ τ a := (Finset.sum_map (Finset.range η) emb (multV PD T₂.ρ τ)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => rk_multV_nonneg (PD := PD) (T := T₂) (τ := τ) (a := a))
  have h3 := hsum i τ hτ
  have h1 := htel η
  have hz : ((finrank LL ↥((FildR PD T₂.ρ τ (-(η : ℤ))).map (FildR PD T₂.ρ τ 0).mkQ) : ℕ) : ℤ) +
      finrank LL ↥(FildR PD T₂.ρ τ 0) = finrank LL ↥(FildR PD T₂.ρ τ (-(η : ℤ))) := by
    exact_mod_cast hrk
  have : ((finrank LL ↥((FildR PD T₂.ρ τ (-(η : ℤ))).map (FildR PD T₂.ρ τ 0).mkQ) : ℕ) : ℤ) ≤ m := by
    linarith
  exact_mod_cast this

theorem rk_low₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 0) (a : ℤ) (ha : a ≤ -((b i + S : ℕ) : ℤ)) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a := by
  have hK : Function.Bijective (algebraMap K₀ K) := hS.1.1
  have hT2 : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hηb := eta_le_b_add_of_SetCS W hS i
  obtain ⟨τ, hτ⟩ := exists_embedding_extending_emb W hK i
  rw [rk_ιDi_eq W hK hQ T₂ hT2 i τ hτ, rk_filLev_eq W hK hQ T₂ hT2 i τ hτ a]
  haveI : FiniteDimensional LL ↥(DdRE PD T₂.ρ τ) := ((hQ hK T₂.V T₂.ρ hT2).2 τ).1
  have hJ := rk_jumps₂ W hE hC hQ hS i τ hτ
  obtain ⟨lo, hlo⟩ := rk_fildR_lo (PD := PD) (ρ := T₂.ρ) (τ := τ)

  have key : ∀ k : ℕ, lo + k ≤ a → FildR PD T₂.ρ τ (lo + k) = DdRE PD T₂.ρ τ := by
    intro k
    induction k with
    | zero => intro _; simpa using hlo lo le_rfl
    | succ k ih =>
      intro hk
      push_cast at hk
      have h1 : lo + (k : ℤ) ≤ a := by linarith
      have hnj : ¬ Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD T₂.ρ τ (lo + k) := by
        intro hj
        have hw := hJ _ hj
        unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at hw
        rw [if_pos hi] at hw
        rcases hw with hw | hw
        · have := hw.1
          push_cast at this ha
          omega
        · have := hw.1
          push_cast at ha
          omega
      unfold Formalism.WeaklyAdmissibleFiltrations.IsJumpV at hnj
      push_neg at hnj
      push_cast
      rw [← add_assoc, hnj, ih h1]
  rcases le_or_gt a lo with h | h
  · rw [hlo a h]
  · have hk : lo + (((a - lo).toNat : ℕ) : ℤ) = a := by omega
    rw [← hk, key _ (le_of_eq hk)]

end Even

end Formalism.MainNotions.N.Pv.LocalLengthBound
