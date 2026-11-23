import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTCoeffFormulaCommDistinctPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRangeMulEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Comm

open CongruenceSubgroup

theorem cj_sub {Γ : Type} (u v : Γ → ℂ[X]) : cj (u - v) = cj u - cj v := by
  funext γ
  simp [cj, Polynomial.map_sub]

theorem intCast_of_dvd {m n : ℕ} (h : m ∣ n) {x a : ℤ} (hx : ((x : ℤ) : ZMod n) = a) :
    ((x : ℤ) : ZMod m) = a := by
  have := congrArg (ZMod.castHom h (ZMod m)) hx
  simpa using this

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : GlobalTheory.Hk.IsDia N l d σ)
    (hτ : GlobalTheory.Hk.IsDia N l e τ) : GlobalTheory.Hk.IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h1)
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]
    ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]
    ring

theorem gamma_le_lev (N l : ℕ) : Gamma (N * l) ≤ Lev N l := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  refine ⟨?_, ?_⟩
  · change γ ∈ Gamma1 N
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h00)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h11)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h10)
  · change γ ∈ Gamma0 l
    rw [Gamma0_mem]
    simpa using intCast_of_dvd (dvd_mul_left l N) (a := 0) (by simpa using h10)

theorem comm_of_decomp {Γ : Subgroup SL(2, ℤ)} {w : ℕ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (hAc : ∀ z, cj (A z) = A (cj z)) (hBc : ∀ z, cj (B z) = B (cj z))
    (x y b : Γ → ℂ[X]) (hx : A (B x) - B (A x) ∈ B1 Γ w) (hy : A (B y) - B (A y) ∈ B1 Γ w)
    (hb : b ∈ B1 Γ w) :
    A (B (x + cj y + b)) - B (A (x + cj y + b)) ∈ B1 Γ w := by
  have hcj : ∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w := (cj_mem_Z1_cj_mem_B1_per_smul Γ w).2.1
  have e : A (B (x + cj y + b)) - B (A (x + cj y + b)) =
      (A (B x) - B (A x)) + cj (A (B y) - B (A y)) + (A (B b) - B (A b)) := by
    simp only [cj_sub, hAc, hBc, map_add]
    abel
  rw [e]
  exact add_mem (add_mem hx (hcj _ hy)) (sub_mem (hA _ (hB _ hb)) (hB _ (hA _ hb)))

theorem per_comm {Γ : Subgroup SL(2, ℤ)} {w : ℕ} {k : ℤ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (FA FB : (ℍ → ℂ) → ℍ → ℂ)
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (mA : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FA ⇑f)
    (mB : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FB ⇑f)
    (eA : ∀ f : ModularForm Γ k, per Γ w (FA ⇑f) - A (per Γ w ⇑f) ∈ B1 Γ w)
    (eB : ∀ f : ModularForm Γ k, per Γ w (FB ⇑f) - B (per Γ w ⇑f) ∈ B1 Γ w)
    (hc : ∀ f : ModularForm Γ k, FA (FB ⇑f) = FB (FA ⇑f)) (f : ModularForm Γ k) :
    A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) ∈ B1 Γ w := by
  obtain ⟨g, hg⟩ := mB f
  obtain ⟨g', hg'⟩ := mA f
  have h1 := eB f
  have h2 := eA g
  have h3 := eA f
  have h4 := eB g'
  rw [hg] at h2
  rw [hg'] at h4
  have e : A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) =
      -A (per Γ w (FB ⇑f) - B (per Γ w ⇑f)) - (per Γ w (FA (FB ⇑f)) - A (per Γ w (FB ⇑f))) +
        (per Γ w (FB (FA ⇑f)) - B (per Γ w (FA ⇑f))) + B (per Γ w (FA ⇑f) - A (per Γ w ⇑f)) := by
    rw [hc f]
    simp only [map_sub]
    abel
  rw [e]
  exact add_mem (add_mem (sub_mem (neg_mem (hA _ h1)) h2) h4) (hB _ h3)

theorem heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  intro N l k hN hl hlN hk hodd q q' σ σ' τ τ' d d' hq hqNl hq' hq'Nl hσ hσ' hτ hτ' z hz
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨bUl, bDd, bTq, bDia, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN hl hlN
  have eqv := fun f => GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant N l k hN hl hlN hk f

  have opT : ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
      GlobalTheory.Hk.IsDia N l q σ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), TqZ (Lev N l) (k - 2) q σ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (TqZ (Lev N l) (k - 2) q σ z) = TqZ (Lev N l) (k - 2) q σ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = TqF (k : ℤ) q σ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro q σ hq hqn hs
    have dq : GlobalTheory.Hk.IsDia N l q σ := (bDia N l q σ).1 (by rwa [Int.cast_natCast])
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin (q + 1)) (dg 1 q) (tqFam q σ)
      (by simp [dg, Matrix.det_fin_two, hq.pos]) (rT q σ hq hqn hs)
    refine ⟨dq, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).1 q σ hq hqn hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.heckeT_modularForm N l q k σ hN0 hq hqn dq f
    exact ⟨g, hg.trans (bTq _ _ _ _ hq.pos).symm⟩

  have opU :
      (∀ z ∈ B1 (Lev N l) (k - 2), UlZ (Lev N l) (k - 2) l z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (UlZ (Lev N l) (k - 2) l z) = UlZ (Lev N l) (k - 2) l (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = UlF (k : ℤ) l ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin l) (dg 1 l) (ulFam l)
      (by simp [dg, Matrix.det_fin_two, hl.pos]) rU
    refine ⟨H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.1⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.uOp_modularForm N l l k hN0 hl0 hl (dvd_mul_left l N) f
    exact ⟨g, hg.trans (bUl _ _ _ hl0).symm⟩

  have opD : ∀ (d : ZMod N) (τ : SL(2, ℤ)), IsDiam N l d τ →
      GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), DdZ (Lev N l) (k - 2) τ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (DdZ (Lev N l) (k - 2) τ z) = DdZ (Lev N l) (k - 2) τ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = DdF (k : ℤ) τ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (DdF (k : ℤ) τ ⇑f) - DdZ (Lev N l) (k - 2) τ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro d τ hs
    have dτ : GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ := (bDia N l (mat τ 1 1) τ).1 ⟨hs.1, rfl⟩
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) Unit (mat τ) (fun _ => mat τ)
      (by simp [mat]) (rD d τ hs)
    refine ⟨dτ, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.2 d τ hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.dia_modularForm N l k (mat τ 1 1) τ hN0 dτ f
    exact ⟨g, hg.trans (bDd _ _ _).symm⟩

  obtain ⟨f, h, hES⟩ := GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle N (N * l) (Lev N l) k hN (Nat.mul_pos hN0 hl0)
    (gamma_le_lev N l) inf_le_left hodd hk z hz
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B1 (Lev N l) (k - 2),
      z = per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b :=
    ⟨_, hES, by abel⟩
  have hh : ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = ⇑h := ⟨ModularFormClass.modularForm h, rfl⟩
  obtain ⟨hm, hhm⟩ := hh
  have pair : ∀ (A B : Module.End ℂ (Lev N l → ℂ[X])) (FA FB : (ℍ → ℂ) → ℍ → ℂ),
      (∀ z ∈ B1 (Lev N l) (k - 2), A z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (A z) = A (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FA ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FA ⇑f) - A (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ z ∈ B1 (Lev N l) (k - 2), B z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (B z) = B (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FB ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FB ⇑f) - B (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ f : ModularForm (Lev N l) (k : ℤ), FA (FB ⇑f) = FB (FA ⇑f)) →
      A (B (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) -
        B (A (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) ∈ B1 (Lev N l) (k - 2) := by
    rintro A B FA FB ⟨hA, hAc, mA, eA⟩ ⟨hB, hBc, mB, eB⟩ hc
    have hy := per_comm A B FA FB hA hB mA mB eA eB hc hm
    rw [hhm] at hy
    exact comm_of_decomp A B hA hB hAc hBc _ _ b (per_comm A B FA FB hA hB mA mB eA eB hc f) hy hb

  have eT : ∀ (q : ℕ) (σ : SL(2, ℤ)), 0 < q → ∀ g, TqF (k : ℤ) q σ g = GlobalTheory.Hk.heckeT k q σ g :=
    fun q σ hq g => bTq _ q σ g hq
  have eU : ∀ g, UlF (k : ℤ) l g = GlobalTheory.Hk.uOp l g := fun g => bUl _ l g hl0
  have eD : ∀ (τ : SL(2, ℤ)) g, DdF (k : ℤ) τ g = GlobalTheory.Hk.dia k τ g := fun τ g => bDd _ τ g
  obtain ⟨dq, oTq⟩ := opT q σ hq hqNl hσ
  obtain ⟨dq', oTq'⟩ := opT q' σ' hq' hq'Nl hσ'
  obtain ⟨dτ, oDτ⟩ := opD d τ hτ
  obtain ⟨dτ', oDτ'⟩ := opD d' τ' hτ'
  refine ⟨pair _ _ _ _ oTq oTq' ?_, pair _ _ _ _ oTq opU ?_, pair _ _ _ _ oTq oDτ ?_,
    pair _ _ _ _ opU oDτ ?_, pair _ _ _ _ oDτ oDτ' ?_⟩
  · intro f
    simp only [eT q σ hq.pos, eT q' σ' hq'.pos]
    exact GlobalTheory.Hk.heckeT_comm N l q q' k σ σ' hN0 hq hq' hqNl hq'Nl dq dq' f
  · intro f
    simp only [eT q σ hq.pos, eU]
    exact (GlobalTheory.Hk.uOp_heckeT_comm N l l q k σ hN0 hl0 hl (dvd_mul_left l N) hq hqNl dq f).symm
  · intro f
    simp only [eT q σ hq.pos, eD]
    exact GlobalTheory.Hk.heckeT_dia_comm N l q k (mat τ 1 1) σ τ hN0 hq hqNl dq dτ f
  · intro f
    simp only [eU, eD]
    exact GlobalTheory.Hk.uOp_dia_comm N l l k (mat τ 1 1) τ hN0 hl0 hl (dvd_mul_left l N) dτ f
  · intro f
    simp only [eD]
    exact (GlobalTheory.Hk.dia_mul N l k _ _ τ' τ (τ' * τ) hN0 dτ' dτ (isDia_mul dτ' dτ) f).trans
      (GlobalTheory.Hk.dia_mul N l k _ _ τ τ' (τ' * τ) hN0 dτ dτ'
        (by rw [mul_comm (mat τ 1 1)]; exact isDia_mul dτ' dτ) f).symm

end GlobalTheory.HeckeFamilyMatrices.Comm
