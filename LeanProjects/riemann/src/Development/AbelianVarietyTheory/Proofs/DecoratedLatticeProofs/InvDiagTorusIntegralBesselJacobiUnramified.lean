import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLineStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvStep

variable {D : D7}

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := by
  have h1 : t.1 = diagonal (fun k => t.1 k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [diagonal_apply_ne _ h, ht a b h]
  have hm : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have h3 : ∀ a b, t.1 a a * (t⁻¹).1 a b = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    rw [h1, diagonal_mul] at this
    exact this
  have h4 : ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := fun k => by
    have := h3 k k; rwa [one_apply_eq] at this
  refine ⟨h1, ?_, h4⟩
  ext a b
  by_cases h : a = b
  · subst h; simp
  · rw [diagonal_apply_ne _ h]
    have e := h3 a b
    rw [one_apply_ne h] at e
    calc (t⁻¹).1 a b = (t⁻¹).1 a a * (t.1 a a * (t⁻¹).1 a b) := by
          rw [← mul_assoc, mul_comm ((t⁻¹).1 a a), h4, one_mul]
      _ = 0 := by rw [e, mul_zero]

theorem mat_mem_idAt {P : Pl D → Prop} {m n k l : ℕ} (A : Mx D m n) (M : Mx D n k) (B : Mx D k l)
    (hM : ∀ a b, M a b ∈ idAt D P) (i : Fin m) (j : Fin l) : (A ⬝ M ⬝ B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hM a b)

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P := by
  have hm : ∀ a b, (mt S (d.levi t) - 1) a b ∈ idAt D P := by
    intro a b
    have h := (MonoidHom.mem_ker).1 ht
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idAt D P) => u.1 a b) h
    simp only [Units.val_one] at h2
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have e1 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S) (d.levi t)).1 =
      (mt S (d.levi t)).map (Ideal.Quotient.mk (idAt D P)) := rfl
    rw [e1, Matrix.map_apply] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e : t.1 - 1 = d.pX ⬝ (mt S (d.levi t) - 1) ⬝ d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d.pX_jX, Matrix.mul_assoc, ← blockX, blockX_levi]
  rw [← Matrix.sub_apply, e]
  exact mat_mem_idAt _ _ _ hm i j

theorem symplO_extX_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem trace_single_mul {ρ : ℕ} (i : Fin ρ) (β : AE D) (M : Mx D ρ ρ) :
    (Matrix.single i i β ⬝ M).trace = β * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem adj_single {ρ : ℕ} (i : Fin ρ) (β : AE D) : adj (Matrix.single i i β) = Matrix.single i i (cA D β) := by
  ext a b
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨h1.2, h1.1⟩ h2 | exact absurd ⟨h2.2, h2.1⟩ h1 | exact map_zero _

set_option maxHeartbeats 1000000 in

theorem vac_fix_Y : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (LS : Lat S) (LT : Lat T) (v : Pl D), Tame D v → ∀ f, Vac ψ S T LS LT (· = v) f → ∀ y : Mx D T.rank ρ, d.extY T y ∈ latO S T (LS : Set _) (LT : Set _) (· = v) → heisO ψ S T (d.extY T y) f = f := by
  intro D ψ S S₀ T ρ d LS LT v hT f hf y hy
  have hsm : ∀ (c : AE D) (z : Mx D T.rank ρ), c • d.extY T z = d.extY T (c • z) := by
    intro c z
    rw [HypDec.extY_apply, HypDec.extY_apply, Matrix.smul_mul]
  have hadd : ∀ y₁ y₂ : Mx D T.rank ρ, heisO ψ S T (d.extY T (y₁ + y₂)) f =
      heisO ψ S T (d.extY T y₁) (heisO ψ S T (d.extY T y₂) f) := by
    intro y₁ y₂
    funext w
    simp only [heisO, map_add]
    rw [GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.symplOH_extY_extY, add_zero, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul, add_assoc]
    ring
  rcases hT.2 with h2 | ⟨e, ε, he, hε, hb⟩
  · have hε : IsPlaceIdem D v (GlobalTheory.SplitIdem.placeHom D.host.F v 1) :=
      ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
        fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
    obtain ⟨a, ha, ha2⟩ : ∃ a : AE D, finPart D a ∈ intAE D ∧
        2 * a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v 1) := by
      obtain ⟨yv, hyv⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
      rw [map_ofNat] at hyv
      have hy' : (2 : Fv D.host.F v) * yv = 1 := congrArg Subtype.val hyv
      refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v yv), ?_, ?_⟩
      · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v yv, 1, rfl⟩
      · rw [two_mul, ← map_add, ← map_add, ← two_mul, hy']
    have h1 : 2 • (a • d.extY T y) = d.extY T y := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have h3 := hf.2.1 (a • d.extY T y) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hy)
    rwa [h1] at h3
  · have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have hint : ∀ c : AE D, c * c = c → finPart D c ∈ intAE D := fun c hc =>
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc])
    have hu : d.extY T y = d.extY T (e • y) + d.extY T (cA D e • y) := by
      rw [← hsm, ← hsm, ← add_smul, hb, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have f1 : heisO ψ S T (d.extY T (e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e (hint e he.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
    have f2 : heisO ψ S T (d.extY T (cA D e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 _ he' _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (hint _ he'.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he'.1])
    rw [hu, ← map_add, hadd, f2, f1]

end GlobalTheory.FinPl.InvStep

namespace GlobalTheory.FinPl.InvStep

set_option maxHeartbeats 1000000 in

theorem inv_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i
  obtain ⟨-, h2, -⟩ := diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV
    hG.monoW hG.cols i _ hc1 ?_
  intro b hb hY
  have hfix := vac_fix_Y D ψ B.V B.V₀ J.W ρ B.d LV LW v hG.tame f hf _ hY
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have hg : heisO ψ B.V J.W (actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)))
      (s.om (1, J.d.levi t) f) = s.om (1, J.d.levi t) f := by
    rw [← s.weil.om_heis 1 (J.d.levi t) _ f hf.1, hfix]
  have hact : actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)) =
      B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extY_apply, HypDec.extY_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, HypDec.levi_jY, Matrix.mul_assoc J.d.jY]
  have hS : ∀ a c, Matrix.single i i b a c ∈ idAt D (· = v) := by
    intro a c
    rw [Matrix.single_apply]
    split_ifs
    · exact hb
    · exact zero_mem _
  have hMx : MxAt (· = v) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro a c
    have := mat_mem_idAt (J.d.jY ⬝ adj (t⁻¹).1) (Matrix.single i i b) 1 hS a c
    rwa [Matrix.mul_one, Matrix.mul_assoc] at this
  have hpair : ∀ U : Mx D ρ ρ, pairS J.W (J.d.jX ⬝ U) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) =
      cA D b * ((t⁻¹).1 i i * U i i) := by
    intro U
    rw [pairS, adj_mul, adj_mul, adj_adj, adj_single, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY), HypDec.gram_YX, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc, trace_single_mul]
    congr 1
    conv_lhs => rw [h2]
    rw [diagonal_mul]
  have hUI : UInv J.W (xZero J.d) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro u
    have h1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
    have e := hpair 1
    rw [Matrix.mul_one] at e
    rw [xZero, hpair, e, h1, one_apply_eq]
  have hd := hF.Heisenberg₂.dual _ hθ _ hMx hUI
  rw [hact] at hg
  rw [hg] at hd
  have hψ : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d))
      (B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)))) = 1 := by
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hd w
    simp only [Pi.smul_apply, smul_eq_mul] at h1 hw
    exact mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← hψ, symplO_extX_extY, symplO_extX_extY]
  congr 3
  have e := hpair 1
  rw [Matrix.mul_one, one_apply_eq, mul_one] at e
  rw [xZero, e, pairS, adj_mul, adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY),
    HypDec.gram_YX, Matrix.one_mul, trace_single_mul, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

end GlobalTheory.FinPl.InvStep
