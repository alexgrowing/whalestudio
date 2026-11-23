import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPolyStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDimStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChosenDiamondMatrixLetterOperatorsCosetSumsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1GammStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.SSPotBr

def opZ (N l w : ℕ) : Letter → Module.End ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ)
  | Letter.T q => GlobalTheory.HeckeFamilyMatrices.TqZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w q (sgD N l q)
  | Letter.U => GlobalTheory.HeckeFamilyMatrices.UlZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w l
  | Letter.D d => GlobalTheory.HeckeFamilyMatrices.DdZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w (sgD N l d)

section
open GlobalTheory.HeckeFamilyMatrices Polynomial

theorem eichlerShimuraCoboundaries_le_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  rintro z ⟨⟨p, hp⟩, rfl⟩
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change GlobalTheory.HeckeFamilyMatrices.slP w (mat (γ * δ : Γ)) p - p = GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) (GlobalTheory.HeckeFamilyMatrices.slP w (mat γ) p - p) + (GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) p - p)
    have e : mat (γ * δ : Γ) = mat γ * mat δ := by
      simp only [mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [e, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

end

theorem letter_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) :
    ∀ F ∈ Pot ℂ w (Gam N l), opL ℂ N l T F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (opL ℂ N l T F) = opZ N l w T (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro F hF
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨hsg, hTq, hU, hD⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN hl hlN
  cases T with
  | T q =>
    obtain ⟨hq, hqN⟩ := hT
    have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)
    rw [hTq q, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 q) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q hcop)) F hF
  | U =>
    rw [hU, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 l) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU F hF
  | D d =>
    rw [hD d, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) _ _ hN0 hl0 (by simp) (rD _ _ (hsg d hT)) F hF

theorem lift_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) {P : FreeAlgebra ℂ Letter}
    (hP : P ∈ admissibleLettersSubalgebra ℂ N l) :
    ∀ F ∈ Pot ℂ w (Gam N l), FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (FreeAlgebra.lift ℂ (opL ℂ N l) P F) =
        FreeAlgebra.lift ℂ (opZ N l w) P (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  have hN0 : 0 < N := by omega
  obtain ⟨-, hadd, hsmul⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws w N l hN0 hl.pos
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro F hF
    simp only [FreeAlgebra.lift_ι_apply]
    exact letter_pot N l w hN hl hlN T hT F hF
  | algebraMap r =>
    intro F hF
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).smul_mem r hF, hsmul r F⟩
  | add x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hx F hF
    obtain ⟨h3, h4⟩ := hy F hF
    simp only [map_add, LinearMap.add_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).add_mem h1 h3, by rw [hadd, h2, h4]⟩
  | mul x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hy F hF
    obtain ⟨h3, h4⟩ := hx _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h3, by rw [h4, h2]⟩

end GlobalTheory.KZ.SSPotBr

namespace GlobalTheory.KZ.SSPotBr

theorem ssPotB_at_newform : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N →
    Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
    α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
    ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α →
    (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  intro k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 lam hlT hlU hlD
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hsg, -, -, -⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN5 hl hlN
  have hcopq : ∀ q, q.Prime → ¬ q ∣ N * l → Nat.Coprime q N := fun q hq hqN =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)

  obtain ⟨q0, hq0le, hq0⟩ := Nat.exists_infinite_primes (N * l + 1)
  have hq0N : ¬ q0 ∣ N * l := fun h => by
    have := Nat.le_of_dvd (Nat.mul_pos hN0 hl0) h; omega

  have hpres : ∀ t, admitted N l t →
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) := by
    intro t ht
    cases t with
    | T q =>
      obtain ⟨hq, hqN⟩ := ht
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q (hcopq q hq hqN)))
      exact ⟨a, b⟩
    | U =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU
      exact ⟨a, b⟩
    | D d =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _ (by simp) (rD _ _ (hsg d ht))
      exact ⟨a, b⟩

  have comm := fun (q q' d d' : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N * l)
      (hd : Nat.Coprime d N) (hd' : Nat.Coprime d' N) =>
    GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 N l k hN5 hl hlN hk3 hk q q' (sgD N l q) (sgD N l q') (sgD N l d) (sgD N l d') (d : ZMod N)
      (d' : ZMod N) hq hqN hq' hq'N (hsg q (hcopq q hq hqN)) (hsg q' (hcopq q' hq' hq'N)) (hsg d hd) (hsg d' hd')
  have h1N : Nat.Coprime 1 N := Nat.coprime_one_left N
  have hcomm : ∀ t t', admitted N l t → admitted N l t' → ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2),
      opZ N l (k - 2) t (opZ N l (k - 2) t' z) - opZ N l (k - 2) t' (opZ N l (k - 2) t z) ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro t t' ht ht' z hz
    cases t with
    | T q =>
      cases t' with
      | T q' => exact (comm q q' 1 1 ht.1 ht.2 ht'.1 ht'.2 h1N h1N z hz).1
      | U => exact (comm q q 1 1 ht.1 ht.2 ht.1 ht.2 h1N h1N z hz).2.1
      | D d => exact (comm q q d 1 ht.1 ht.2 ht.1 ht.2 ht' h1N z hz).2.2.1
    | U =>
      cases t' with
      | T q' =>
        have := (comm q' q' 1 1 ht'.1 ht'.2 ht'.1 ht'.2 h1N h1N z hz).2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U => rw [sub_self]; exact Submodule.zero_mem _
      | D d => exact (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht' h1N z hz).2.2.2.1
    | D d =>
      cases t' with
      | T q' =>
        have := (comm q' q' d 1 ht'.1 ht'.2 ht'.1 ht'.2 ht h1N z hz).2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U =>
        have := (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht h1N z hz).2.2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | D d' => exact (comm q0 q0 d d' hq0 hq0N hq0 hq0N ht ht' z hz).2.2.2.2

  have key : ∀ e : (ZMod N)ˣ → ℕ, (∀ u, Nat.Coprime (e u) N) → (∀ u, ((e u : ℕ) : ZMod N) = u) →
      ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      (∀ q, q.Prime → ¬ q ∣ N * l → (opZ N l (k - 2) (Letter.T q) - lam (Letter.T q) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (opZ N l (k - 2) Letter.U - lam Letter.U • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) ∧
      ∀ u d, e u = d → (opZ N l (k - 2) (Letter.D d) - lam (Letter.D d) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro e he1 he2 z hz n hgen
    have hσD : ∀ u : (ZMod N)ˣ, GlobalTheory.HeckeFamilyMatrices.IsDiam N l (u : ZMod N) (sgD N l (e u)) := fun u => by
      have := hsg (e u) (he1 u); rwa [he2 u] at this
    have hchi : ∀ u : (ZMod N)ˣ, lam (Letter.D (e u)) = g.χ (ZMod.castHom hN (ZMod g.M) (u : ZMod N)) := fun u => by
      rw [hlD _ (he1 u), ← he2 u, map_natCast (ZMod.castHom hN (ZMod g.M))]
    obtain ⟨cT, cU, cD⟩ := GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 (fun q => sgD N l q)
      (fun u => sgD N l (e u)) (fun q hq hqN => hsg q (hcopq q hq hqN)) hσD z hz n
      (fun q hq hqN => by have h := hgen (Letter.T q) ⟨hq, hqN⟩; rw [hlT q hq hqN] at h; exact h)
      (by have h := hgen Letter.U trivial; rw [hlU] at h; exact h)
      (fun u => by have h := hgen (Letter.D (e u)) (he1 u); rw [hchi u] at h; exact h)
    refine ⟨fun q hq hqN => ?_, ?_, ?_⟩
    · rw [hlT q hq hqN]; exact cT q hq hqN
    · rw [hlU]; exact cU
    · rintro u d rfl
      rw [hchi u]; exact cD u
  have hval1 : ∀ u : (ZMod N)ˣ, Nat.Coprime (u : ZMod N).val N := fun u => ZMod.val_coe_unit_coprime u
  have hval2 : ∀ u : (ZMod N)ˣ, (((u : ZMod N).val : ℕ) : ZMod N) = u := fun u => ZMod.natCast_zmod_val _
  have heig : ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      ∀ t, admitted N l t → (opZ N l (k - 2) t - lam t • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro z hz n hgen t ht
    cases t with
    | T q => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).1 q ht.1 ht.2
    | U => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).2.1
    | D d =>
      have hd : Nat.Coprime d N := ht
      refine (key (fun u => if (u : ZMod N) = (d : ZMod N) then d else (u : ZMod N).val) ?_ ?_ z hz n hgen).2.2
        (ZMod.unitOfCoprime d hd) d (if_pos (ZMod.coe_unitOfCoprime d hd))
      · intro u; split_ifs
        · exact hd
        · exact hval1 u
      · intro u; split_ifs with h
        · exact h.symm
        · exact hval2 u
  obtain ⟨P, hP, hP1, hPz⟩ := GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ) (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2))
    (GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) Letter (admitted N l) (opZ N l (k - 2)) lam (eichlerShimuraCoboundaries_le_eichlerShimuraCocycles _ _)
    (GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional N l (k - 2) hN0 hl0) (fun t ht => (hpres t ht).1) (fun t ht => (hpres t ht).2) hcomm heig
  refine ⟨P, hP, hP1, fun F hF T hT => ?_⟩
  obtain ⟨hD1, hD2, hD3⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws (k - 2) N l hN0 hl0
  obtain ⟨hPF, hcPF⟩ := lift_pot N l (k - 2) hN5 hl hlN hP F hF
  obtain ⟨hTF, hcTF⟩ := letter_pot N l (k - 2) hN5 hl hlN T hT _ hPF
  have hG : (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) = opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) +
        (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F := by
    simp [sub_eq_add_neg, neg_smul]
  have hGpot : opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) + (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈
      Pot ℂ (k - 2) (Gam N l) :=
    (Betti.potSub ℂ (k - 2) (Gam N l)).add_mem hTF ((Betti.potSub ℂ (k - 2) (Gam N l)).smul_mem _ hPF)
  rw [hG]
  refine (hD1 _ hGpot).2.2 ?_
  rw [hD2, hD3, hcTF, hcPF]
  have := hPz (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) (hD1 F hF).1 T hT
  simpa [sub_eq_add_neg, neg_smul] using this

end GlobalTheory.KZ.SSPotBr
