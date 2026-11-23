import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.GLTwo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def FrameOf {n n₁ n₂ r : ℕ} (c : E) (H : Plane E n n₁) (H₁ : Plane E n₁ n₂) (X Y : Matrix (Fin n) (Fin r) E)
    (h1 : 1 < r) : Prop :=
  (∀ k, X k ⟨0, by omega⟩ = H.x k) ∧ (∀ k, X k ⟨1, h1⟩ = (H.ι *ᵥ H₁.x) k) ∧
    (∀ k, Y k ⟨0, by omega⟩ = c⁻¹ * H.y k) ∧ ∀ k, Y k ⟨1, h1⟩ = c⁻¹ * (H.ι *ᵥ H₁.y) k

theorem IsHypPlane.skew (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (i j : Fin n₁) : σ (W₁.J j i) = -W₁.J i j := by
  rw [← h.2.2.2.2.2, GlobalTheory.LeviPlaneSection.gram_apply, GlobalTheory.LeviPlaneSection.gram_apply,
    GlobalTheory.LeviPlaneSection.form_skew hσ hsk (fun r => H.ι r i), neg_neg]

theorem IsHypPlane.decompA (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) (v : Fin n → AE F E) :
    ∃ (α β : AE F E) (z : Fin n₁ → AE F E), v = α • incV F H.x + β • incV F H.y + incM F H.ι *ᵥ z := by
  choose α β z hz using fun j : Fin n => GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hsk hσ h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hd (Pi.single j 1)
  have e : ∀ j : Fin n, (Pi.single j 1 : Fin n → AE F E) = inclR (F := F) (AF F) (α j) • incV F H.x +
      inclR (F := F) (AF F) (β j) • incV F H.y + incM F H.ι *ᵥ incV F (z j) := fun j => by
    rw [← GlobalTheory.UnipCocptForm.incV_mulVec]
    funext i
    have := congrArg (inclR (F := F) (AF F)) (congrFun (hz j) i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Pi.single_apply, apply_ite, map_one,
      map_zero] at this
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, incV] using this
  refine ⟨∑ j, v j * inclR (F := F) (AF F) (α j), ∑ j, v j * inclR (F := F) (AF F) (β j), ∑ j, v j • incV F (z j), ?_⟩
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Fin n → AE F E) from by
    funext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [e, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem IsHypPlane.levi_unique (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) {t : (AE F E)ˣ}
    {h₁ : UA σ W₁.J} {m m' : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t h₁ m) (hm' : IsLevi (W₁ := W₁) H t h₁ m') :
    m = m' := by
  refine Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun j => ?_))
  obtain ⟨α, β, z, e⟩ := h.decompA hσ hsk hd (Pi.single j 1)
  change mat m *ᵥ _ = mat m' *ᵥ _
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, hm'.1, hm'.2.1, hm'.2.2]

theorem IsHypPlane.exists_leviHom (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n}
    {W₁ : Spc F E n₁} (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) :
    ∃ M : UA σ W₁.J →* UA σ W.J, Continuous M ∧ (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) ∧
      ∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J := by
  obtain ⟨M, hc, hM, hr⟩ := GlobalTheory.LeviPlaneSection.leviSection W W₁ H hσ hsk h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2 hd
  refine ⟨MonoidHom.mk' M fun a b => h.levi_unique hσ hsk hd (hM _) ?_, hc, hM, hr⟩
  obtain ⟨ax, ay, aι⟩ := hM a
  obtain ⟨cx, cy, cι⟩ := hM b
  simp only [inv_one, Units.val_one, map_one, one_smul] at ax ay cx cy
  refine ⟨?_, ?_, ?_⟩
  · simp only [Units.val_one, one_smul]
    change (mat (M a) * mat (M b)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cx, ax]
  · simp only [inv_one, Units.val_one, map_one, one_smul]
    change (mat (M a) * mat (M b)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cy, ay]
  · change (mat (M a) * mat (M b)) * _ = _ * (mat a * mat b)
    rw [Matrix.mul_assoc, cι, ← Matrix.mul_assoc, aι, Matrix.mul_assoc]

theorem IsHypPlane.mem_unip_iff (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n}
    {W₁ : Spc F E n₁} (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) {c : E}
    (hc : c ≠ 0) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ (c • W.J.map σ) X Y) (h0 : 0 < r)
    (hX : ∀ k, X k ⟨0, h0⟩ = H.x k) (g : UA σ W.J) :
    g ∈ unip σ W H ↔ toGAd hσ W.J hc g ∈ GlobalTheory.StdPar.unip σ (c • W.J.map σ) X {⟨0, h0⟩} := by
  rw [GlobalTheory.StdPar.unip_singleton hW, GlobalTheory.UnipCocptForm.mem_unip_iff σ hσ W W₁.J H hsk h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2 hd c hc g]
  have e : GlobalTheory.StdPar.initCols X ⟨0, h0⟩ = Matrix.of fun i (_ : Fin 1) => H.x i := by
    ext i j
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    exact hX i
  rw [e]

theorem toGAd_mem_ratPts (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (g : UA σ J) : toGAd hσ J hc g ∈ ratPts σ (c • J.map σ) ↔ g ∈ ratU σ J := by
  constructor
  · intro h
    obtain ⟨v, -, hv2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    exact Subgroup.mem_subgroupOf.2 ⟨v, hv2⟩
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 h
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)
    have h2 := (toGAd hσ J hc g).2
    have e : (toGAd hσ J hc g).1.1 = m.1.map (inclR (F := F) (AF F)) := by
      change g.1.1 = _
      rw [← hm]; rfl
    change Formalism.UG.cT _ (toGAd hσ J hc g).1.1 * Matrix.map _ (inclR (F := F) (AF F)) * (toGAd hσ J hc g).1.1 =
      Matrix.map _ (inclR (F := F) (AF F)) at h2
    rw [e, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul] at h2
    exact Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective h2

theorem continuous_toGAd (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    Continuous (toGAd hσ J hc) ∧ Continuous (toGAd hσ J hc).symm :=
  ⟨continuous_subtype_val.subtype_mk _, continuous_subtype_val.subtype_mk _⟩

end GlobalTheory.ThK.GLTwo

end
