import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RatioStep

variable {D : D7}

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

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

theorem conj_transv {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (t : GL (Fin ρ) (AE D))
    (ht : ∀ i j, i ≠ j → t.1 i j = 0) {i j : Fin ρ} (hij : i ≠ j) (c : AE D) :
    (d.levi t)⁻¹ * d.levi (GlobalTheory.GLGen.transvGL hij c) * d.levi t =
      d.levi (GlobalTheory.GLGen.transvGL hij ((t⁻¹).1 i i * c * t.1 j j)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  obtain ⟨h1, h2, h3⟩ := diag_inv t ht
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  show (t⁻¹).1 * Matrix.transvection i j c * t.1 = Matrix.transvection i j ((t⁻¹).1 i i * c * t.1 j j)
  conv_lhs => rw [h2, h1]
  exact GlobalTheory.GLGen.diag_transv_diag _ _ (fun k => by rw [mul_comm]; exact h3 k) hij c

theorem transv_mem_UX {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (c : AE D) :
    GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := by
  rw [mem_UX]
  intro a b
  show (b < a → (Matrix.transvection i j c) a b = 0) ∧ (Matrix.transvection i j c) a a = 1
  refine ⟨fun hba => ?_, ?_⟩
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    rw [one_apply_ne (ne_of_gt hba), zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd (hba.trans hlt) (lt_irrefl _)
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_eq]
    rw [if_neg, add_zero]
    rintro ⟨rfl, e⟩
    exact hij e.symm

theorem upSum_transv {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = c := by
  have e : (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = Matrix.transvection i j c := rfl
  rw [e]
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hj]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hij, and_self, if_true, zero_add]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · have hbk : b ≠ k := fun e => by rw [e] at h; omega
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hbk, zero_add]
      rw [if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

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

theorem opA_levi_one (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om (dW.levi u) 1 Ξ = Ξ := by
  unfold opA
  rw [show dW.levi u = dW.levi u * 1 from (mul_one _).symm, jacT_levi_mul ψ dW V₀ _ (yZero_mul V₀ _ hu),
    jacT_one]
  show (om (1, 1)) Ξ = Ξ
  rw [show ((1 : GA D V₀), (1 : GA D W₀)) = 1 from rfl, map_one]
  rfl

theorem psiFlag_transv (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {i j : Fin ρ}
    (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    psiFlag ψ d (d.levi (GlobalTheory.GLGen.transvGL hij c)) = psiE ψ c := by
  rw [psiFlag, blockX_levi, upSum_transv hij hj c]

set_option maxHeartbeats 1000000 in

theorem psi_root {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (hU : UnrAt s v) {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)}
    (hF : IsFlatBF s (· = v) 𝔉) {f : WO B.V J.W → ℂ} (hf : Vac ψ B.V J.W LV LW (· = v) f)
    (t : GL (Fin ρ) (AE D)) (ht : J.d.levi t ∈ grpAt J.W (· = v)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
    {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (hj : j.1 = i.1 + 1) (c : AE D)
    (hK : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t)) :
    psiE ψ c = 1 := by
  have hu : GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := transv_mem_UX hij hlt c
  have hnF : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ flagN J.d := J.d.levi_mem_NFlag hu
  have hnG : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ grpAt J.W (· = v) := by
    have e : J.d.levi (GlobalTheory.GLGen.transvGL hij c) = J.d.levi t *
        ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) * (J.d.levi t)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem ht hK.1) (inv_mem ht)
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have h1K : InK B.V LV (· = v) 1 := ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have hfix : s.om (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) f = f :=
    GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (by rintro w rfl; exact ⟨hG.tame, hU.1, hU.2⟩) f hf 1 _ h1K hK
  have hom : s.om (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.emb0 1) (s.om (1, J.d.levi t) f) =
      s.om (1, J.d.levi t) f := by
    rw [map_one, mul_one]
    have e : (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c)) * ((1 : GA D B.V), J.d.levi t) =
        ((1 : GA D B.V), J.d.levi t) *
          (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) := by
      simp only [Prod.mk_mul_mk, one_mul]
      congr 1
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfix]
  have heq := hF.equiv _ hθ _ hnF hnG 1 (one_mem _)
  have hψ := psiFlag_transv ψ J.d hij hj c
  rw [hom] at heq
  have hA : opA ψ J.d B.o B.ζ s.om₀ (J.d.levi (GlobalTheory.GLGen.transvGL hij c)) 1 (𝔉 (s.om (1, J.d.levi t) f)) =
      𝔉 (s.om (1, J.d.levi t) f) := opA_levi_one ψ J.d B.o B.ζ s.om₀ hu _
  rw [hA, hψ] at heq
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
  have h1 := congrFun heq w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
  have h2 : star (psiE ψ c) = 1 := mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← star_star (psiE ψ c), h2, star_one]

set_option maxHeartbeats 1000000 in

theorem ratio_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i j hj
  have hij : i ≠ j := fun e => by rw [e] at hj; omega
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨-, -, h3⟩ := diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d ht i i
    rwa [one_apply_eq] at this
  have htj : (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) j j
    rwa [one_apply_eq] at this
  have hx1 : t.1 i i * (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have e : t.1 i i * (t⁻¹).1 j j - 1 = (t.1 i i - 1) * (t⁻¹).1 j j + ((t⁻¹).1 j j - 1) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hti) htj
  refine GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon D B.V B.V₀ ρ B.d LV LV₀ v hG.tame hG.sdV hG.monoV i j _ hx1 ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * (t.1 i i * (t⁻¹).1 j j)) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, colMul B.d.jX j a ∈ latV B.V LV (· = v) → colMul B.d.jX i (r * o * a) ∈ latV B.V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hWV := GlobalTheory.T.latticeLineRatio_transport_of_columnsCarryLines D B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV hG.monoW hG.cols
    i j (r * o) hro hRo
  have hK := GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW i j hij (r * o) hro hWV
  have hc : (t⁻¹).1 i i * (r * o * (t.1 i i * (t⁻¹).1 j j)) * t.1 j j = r * o := by
    linear_combination (r * o * (t.1 j j * (t⁻¹).1 j j)) * h3 i + (r * o) * h3 j
  have hK' : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij (r * o * (t.1 i i * (t⁻¹).1 j j))) *
      J.d.levi t) := by
    rw [conj_transv J.d t htd hij, hc]
    exact hK
  have := psi_root s hG hU hF hf t ht hne hij hlt hj _ hK'
  rwa [mul_right_comm r o] at this

end GlobalTheory.FinPl.RatioStep
