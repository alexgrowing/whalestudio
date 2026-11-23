import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LineDual

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩

theorem intAt_add' {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem latV_entry_mem_idAt {S : HSp D} {M : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S M P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem idV_mem_idAt {𝔞 : FI D} {v : Pl D} {t : AE D} (ht : t ∈ idV 𝔞 v) : t ∈ idAt D (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt (fun w hw => hα w hw) _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

def pr (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ l, (∑ m, cA D (w m) * gA S m l) * y l

theorem pr_zero_left (S : HSp D) (y : Fin S.rank → AE D) : pr S 0 y = 0 := by simp [pr]
theorem pr_zero_right (S : HSp D) (w : Fin S.rank → AE D) : pr S w 0 = 0 := by simp [pr]
theorem pr_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : pr S (w + w') y = pr S w y + pr S w' y := by
  simp [pr, add_mul, Finset.sum_add_distrib]
theorem pr_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : pr S w (y + y') = pr S w y + pr S w y' := by
  simp [pr, mul_add, Finset.sum_add_distrib]
theorem pr_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : pr S (-w) y = -pr S w y := by
  simp [pr]
theorem pr_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : pr S w (-y) = -pr S w y := by
  simp [pr]

theorem pr_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    pr S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (∑ m, ∑ l, star (x m) * S.gram m l * x' l) := by
  have hc : ∀ m, cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star (x m) :=
    fun _ => rfl
  have hg : ∀ m l, gA S m l = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram m l := fun _ _ => rfl
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [pr, one_mul]
  simp only [hc, hg, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.tmul_sum]

theorem pr_mem_intAt {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {P : Pl D → Prop} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S M P) (hy : y ∈ latV S M P) : pr S w y ∈ intAt D P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hw
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [pr_gen]
      obtain ⟨b, hb⟩ := (hM.2 x').1 hx' x hx
      refine ⟨LatMem.tmul_mem_idAt (fun v hv => by rw [map_mul, hα v hv, zero_mul]) _, ?_⟩
      rw [← hb]
      exact AddSubgroup.subset_closure ⟨α * β, LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pr_zero_right]; exact intAt_zero' _
    | add z z' _ _ hz hz' => rw [pr_add_right]; exact intAt_add' hz hz'
    | neg z _ hz => rw [pr_neg_right]; exact intAt_neg' hz
  | zero => rw [pr_zero_left]; exact intAt_zero' _
  | add w w' _ _ hw hw' => rw [pr_add_left]; exact intAt_add' hw hw'
  | neg w _ hw => rw [pr_neg_left]; exact intAt_neg' hw

theorem line_pair_mem_idV : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hline h𝔠 y hy
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hX : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
    sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem_idAt hy l)
  have hcX := cA_mem_idAt hX
  have hcint : ∀ s, s ∈ intAt D (· = v) → cA D s ∈ intAt D (· = v) := by
    intro s hs
    have e2 : s ∈ idV (D.host.AA ^ (0 : ℤ)) v := by rw [zpow_zero]; exact (h1 s).2 hs
    have e3 := (h4 0 s).1 e2
    rw [zpow_zero] at e3
    exact (h1 _).1 e3
  have key := (h2 𝔠 1 h𝔠 one_ne_zero _ hcX).1 (fun t ht => ?_)
  · rwa [one_mul] at key
  · have htI : t ∈ idAt D (· = v) := idV_mem_idAt ht
    have htz : t • ratV (vecB o ζ) ∈ latV S M (· = v) := (hline t htI).2 ht
    have hp := pr_mem_intAt hM htz hy
    have he : pr S (t • ratV (vecB o ζ)) y = cA D t * ∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l := by
      simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [he] at hp
    have h5 := hcint _ hp
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm] at h5
    exact (h1 _).2 h5

end GlobalTheory.LineDual

end
