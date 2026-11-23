import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nsmul_half (p : SplitPt D k) {S T : HSp D} {LS MS : Lat S} {LT MT : Lat T} (hLS : IsSelfDualC S LS)
    (hLT : IsSelfDualC T LT) (hMS : IsSelfDualC S MS) (hMT : IsSelfDualC T MT) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v),
      IsHalf p.e u → N • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  obtain ⟨M, hM, hMm⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := S) (T := T) hMS.1.fg hMT.1.fg hLS.1 hLT.1
  refine ⟨M, hM, fun u hu hh => ?_⟩
  have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he heε (hMm u (GlobalTheory.PlaceModel.latO_le_top _ hu))).1
  have h2 : p.e • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
  rwa [smul_comm, h2] at h1

theorem isHalf_nsmul {S T : HSp D} {e : AE D} {u : WO S T} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem sbHalf_mono : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ Φ : WO S T → ℂ, IsSBHalf p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ := by
  intro D k _ _ _ _ p S T LS MS LT MT hLS hLT hMS hMT Φ hΦ
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_half p hMS hMT hLS hLT
  obtain ⟨M, hM, hMm⟩ := exists_nsmul_half p hLS hLT hMS hMT
  obtain ⟨h1, k', hk', h2, h3⟩ := hΦ
  refine ⟨h1, k' * N * M, Nat.mul_pos (Nat.mul_pos hk' hN) hM, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hu' : M • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
      nsmul_mem hu M
    have e : (k' * N * M) • u = k' • (N • (M • u)) := by rw [smul_smul, smul_smul, mul_assoc]
    rw [e]
    exact h2 _ (hNm _ hu' (isHalf_nsmul hh M)) (isHalf_nsmul (isHalf_nsmul hh M) N) t
  · have ht' := h1 t ht
    have e : (k' * N * M) • t = M • (N • (k' • t)) := by
      rw [smul_smul, smul_smul, mul_comm M N, mul_comm (N * M) k', mul_assoc]
    rw [e]
    exact hMm _ (nsmul_mem (h3 t ht) N) (isHalf_nsmul (isHalf_nsmul ht' k') N)

theorem placeIdem_mul {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    algebraMap (AF D.host.F) (AE D) ε * a = a := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  obtain ⟨hi, hw⟩ := GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 ha
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun w => ?_
  · rw [map_mul, GlobalTheory.FinPl.LatMem.compInf_eq_zero hi, mul_zero]
  · rw [map_mul]
    have he : GlobalTheory.AdelicU.compFin D.host.F D.host.E w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) =
        evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    by_cases hv : w = v
    · subst hv
      rw [he, h1]
      exact one_mul _
    · rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt a w, hw w hv, mul_zero]

theorem eq_add_halves (p : SplitPt D k) {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT (· = p.v)) : p.e • u + cA D p.e • u = u := by
  obtain ⟨ε, hε, heq⟩ := p.above
  rw [← add_smul, heq]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact placeIdem_mul hε (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)

theorem smul_conj_zero (e e' : AE D) (h : e' * cA D e' = 0) {S T : HSp D} (u : WO S T) (hu : e' • u = u) :
    cA D e' • (e • u) = 0 := by
  rw [← hu, smul_smul, smul_smul]
  rw [mul_comm (cA D e') e]
  rw [mul_assoc]
  rw [mul_comm (cA D e') e']
  rw [h, mul_zero, zero_smul]

theorem isHalf_add {S T : HSp D} {e : AE D} {a b : WO S T} (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e (a + b) :=
  fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]

theorem latVac_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) (Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)))) := by
  intro D k _ _ _ _ p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have hce : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination hce + hec
  set Λ' := latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ'
  have hΦ₀ : IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
      (halfInd p.e Λ') :=
    sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT _ (GlobalTheory.isSBHalf_halfInd p.e Λ')
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T MS MT hψ hMS hMT).1
  have hLL' : ∀ x ∈ Λ', IsHalf p.e x → ∀ y ∈ Λ', ψ (symplO S T x y) = 1 := fun x hx hh y hy =>
    (hdual x (GlobalTheory.PlaceModel.infPart_half hε heε ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh))).1
      (GlobalTheory.PlaceModel.latO_le_top _ hx) y (GlobalTheory.PlaceModel.latO_le_top _ hy)
  have hX : ∀ x ∈ Λ', IsHalf p.e x → heisO ψ S T x (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x hx hh
    rw [← hTm.trans _ hΦ₀ x hh]
    congr 1
    funext t
    have hc : (t + x ∈ Λ' ∧ IsHalf p.e (t + x)) ↔ (t ∈ Λ' ∧ IsHalf p.e t) := by
      rw [Λ'.add_mem_cancel_right hx]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    show halfInd p.e Λ' (t + x) = halfInd p.e Λ' t
    unfold halfInd
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  have hY : ∀ y ∈ Λ', IsHalf (cA D p.e) y → heisO ψ S T y (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro y hy hh
    rw [← hTm.modul _ hΦ₀ y hh]
    congr 1
    funext t
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [hLL' t h.1 h.2 y hy, one_mul]
    · simp [halfInd, h]
  have key : ∀ x y : WO S T, x ∈ Λ' → IsHalf p.e x → y ∈ Λ' → IsHalf (cA D p.e) y →
      ψ (symplOH S T y x) = 1 → heisO ψ S T (x + y) (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x y hx hxh hy hyh h1
    have h := GlobalTheory.PlaceModel.heisL_heisL S T ψ y x (Tm (halfInd p.e Λ'))
    change heisO ψ S T y (heisO ψ S T x (Tm (halfInd p.e Λ'))) =
      ψ (symplOH S T y x) • heisO ψ S T (y + x) (Tm (halfInd p.e Λ')) at h
    rw [hX x hx hxh, hY y hy hyh, h1, one_smul, add_comm] at h
    exact h.symm
  have hpart : ∀ u ∈ Λ', (p.e • u ∈ Λ' ∧ IsHalf p.e (p.e • u)) ∧
      (cA D p.e • u ∈ Λ' ∧ IsHalf (cA D p.e) (cA D p.e • u)) := by
    intro u hu
    have a1 := GlobalTheory.PlaceModel.idem_smul_mem hε he heε (GlobalTheory.PlaceModel.latO_le_top _ hu)
    have a2 := GlobalTheory.PlaceModel.idem_smul_mem hε hce heε' (GlobalTheory.PlaceModel.latO_le_top _ hu)
    exact ⟨⟨a1.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a1.2⟩, ⟨a2.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a2.2⟩⟩
  refine ⟨fun w hw => ?_, fun e' hse' u hu hh => ?_⟩
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart w hw
    have e2 : 2 • w = (p.e • w + p.e • w) + (cA D p.e • w + cA D p.e • w) := by
      conv_lhs => rw [← eq_add_halves p hw]
      abel
    rw [e2]
    refine key _ _ (add_mem hx hx) (isHalf_add hxh hxh) (add_mem hy hy) (isHalf_add hyh hyh) ?_
    have hb : ψ (symplO S T (cA D p.e • w) (p.e • w)) = 1 := by
      rw [GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hLL' _ hx hxh _ hy, inv_one]
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    have h3 : symplOH S T (cA D p.e • w + cA D p.e • w) (p.e • w + p.e • w) =
        symplO S T (cA D p.e • w) (p.e • w) + symplO S T (cA D p.e • w) (p.e • w) := by
      unfold symplOH
      simp only [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right]
      linear_combination (2 * symplO S T (cA D p.e • w) (p.e • w)) * h2
    rw [h3, AddChar.map_add_eq_mul, hb, one_mul]
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart u hu
    rw [← eq_add_halves p hu]
    refine key _ _ hx hxh hy hyh ?_
    obtain ⟨-, hse2, -⟩ := hse'
    have hu' : e' • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
    have h0 : symplO S T (cA D p.e • u) (p.e • u) = 0 := by
      have e1 : cA D p.e • u = e' • (cA D p.e • u) := by rw [smul_comm, hu']
      have e2 : cA D e' • (p.e • u) = 0 := smul_conj_zero p.e e' hse2 u hu'
      rw [e1, GlobalTheory.PlaceModel.symplO_smul, e2, GlobalTheory.PlaceModel.symplO_zero_right]
    unfold symplOH
    rw [h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FinPl.Rebase

end
