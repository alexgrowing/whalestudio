import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

noncomputable section

namespace GlobalTheory.StdFrame

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OrthFrame (V : HSpace E) : Prop :=
  (∀ a b, V.hT (V.frame a) (V.frame b) = if a = b then 1 else 0) ∧ ∀ a, V.frame a ∈ V.L0

theorem orthFrame_stdSpace (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n p q : ℕ) :
    OrthFrame (Examples₂.stdSpace hstar n (fun _ => false) p q) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar n (fun _ => false) p q a b).trans rfl,
    fun a => (Submodule.subset_span ⟨a, rfl⟩ : Pi.basisFun E (Fin n) a ∈ Examples₂.stdLat n)⟩

theorem OrthFrame.gram_eq {V : HSpace E} (h : OrthFrame V) : V.gram = 1 := by
  ext a b
  rw [Matrix.one_apply]
  exact h.1 a b

theorem OrthFrame.mem_iff {V : HSpace E} (h : OrthFrame V) (x : Fin V.rank → E) :
    ∑ a, x a • V.frame a ∈ V.L0 ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx a
    have hd : ∑ a, x a • V.frame a ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 := by
      rw [V.baseLattice_isUnimodular]; exact hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hd
    have h1 : V.hT (V.frame a) (∑ b, x b • V.frame b) ∈ (1 : Submodule (𝓞 E) E) := hd _ (h.2 a)
    simpa [map_sum, map_smul, h.1] using h1
  · intro hx
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx a)
    rw [← ho, algebraMap_smul]
    exact V.L0.smul_mem o (h.2 a)

def reframe (V : HSpace E) (b : Module.Basis (Fin V.rank) E V.V) : HSpace E := { V with frame := b }

theorem sigOK_reframe (hτ : ∀ (τ : E →+* ℂ) a, τ (star a) = starRingEnd ℂ (τ a)) {V : HSpace E} (hV : V.SigOK)
    (b : Module.Basis (Fin V.rank) E V.V) : (reframe V b).SigOK := by
  intro τ
  obtain ⟨e, P, hP⟩ := hV τ
  have hfam := map_family (reframe V b) τ (hτ τ) V.frame
  set M : Matrix (Fin V.rank) (Fin V.rank) ℂ := (b.toMatrix V.frame).map τ with hM
  set N : Matrix (Fin V.rank) (Fin V.rank) ℂ := (V.frame.toMatrix b).map τ with hN
  have hMN : M * N = 1 := by
    rw [hM, hN, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hNM : N * M = 1 := by
    rw [hM, hN, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let G : Matrix (Fin V.rank) (Fin V.rank) ℂ := (reframe V b).gram.map τ
  have hg : V.gram.map τ = Mᴴ * G * M := hfam
  let Q : GL (Fin (V.sig τ).1 ⊕ Fin (V.sig τ).2) ℂ :=
    ⟨M.submatrix e.symm e.symm, N.submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, hMN, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hNM, Matrix.submatrix_one_equiv]⟩
  show Formalism.UG.HasSignature G (V.sig τ).1 (V.sig τ).2
  refine ⟨e, Q * P, ?_⟩
  refine Eq.trans ?_ hP
  have hQ : Q.val = M.submatrix e.symm e.symm := rfl
  rw [hg, Units.val_mul, hQ]
  simp only [Formalism.UG.P.cT_conj_eq, Matrix.conjTranspose_mul, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [← Matrix.submatrix_mul_equiv _ _ _ e.symm, ← Matrix.submatrix_mul_equiv _ _ _ e.symm]
  simp only [Matrix.mul_assoc]

theorem exists_orthFrame (V : HSpace E) {n : ℕ} (hn : V.rank = n) (h : Formalism.HermitianLatticesTheory.IsOrthoLattice V.hT V.L0 n) :
    ∃ b, OrthFrame (reframe V b) := by
  subst hn
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  refine ⟨Module.Basis.mk h1 h2.ge, fun (a b : Fin V.rank) => ?_, fun (a : Fin V.rank) => ?_⟩
  · show V.hT (Module.Basis.mk h1 h2.ge a) (Module.Basis.mk h1 h2.ge b) = _
    rw [Module.Basis.mk_apply, Module.Basis.mk_apply, h4]
    rfl
  · show Module.Basis.mk h1 h2.ge a ∈ V.L0
    rw [Module.Basis.mk_apply, h3]
    exact Submodule.subset_span ⟨a, rfl⟩

theorem exists_gram_ne_one (V : HSpace E) (hr : 0 < V.rank) : ∃ b, (reframe V b).gram ≠ 1 := by
  by_cases h : V.gram = 1
  · refine ⟨V.frame.unitsSMul fun _ => Units.mk0 (2 : E) two_ne_zero, fun h' => ?_⟩
    have h1 := congrFun (congrFun h ⟨0, hr⟩) ⟨0, hr⟩
    have h2 : V.hT ((V.frame.unitsSMul fun _ => Units.mk0 (2 : E) two_ne_zero) ⟨0, hr⟩)
        ((V.frame.unitsSMul fun _ => Units.mk0 (2 : E) two_ne_zero) ⟨0, hr⟩) = 1 :=
      (congrFun (congrFun h' ⟨0, hr⟩) ⟨0, hr⟩).trans (Matrix.one_apply_eq _)
    rw [Matrix.one_apply_eq, HSpace.gram] at h1
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, map_smul, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, h1, map_ofNat] at h2
    norm_num at h2
  · exact ⟨V.frame, h⟩

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hLat_one {D : D7} (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem vStd_iff_gram_and_lattice (D : D7) (i : Fin D.R.m) :
    VStd D i ↔ (Vc D i).gram = 1 ∧
      L0c D (Vc D i) = ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) : Set (Fin (Vc D i).rank → D.host.E)) := by
  rw [VStd, hLat_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]

def FrameChoice (D : D7) (i : Fin D.R.m) : Prop := OrthFrame (D.sp.V ((i : ℕ) + 1))

theorem vStd_of_frameChoice : ∀ (D : D7) (i : Fin D.R.m), FrameChoice D i → VStd D i := by
  intro D i h
  refine (vStd_iff_gram_and_lattice D i).2 ⟨h.gram_eq, ?_⟩
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact (h.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem vStd_iff_frameChoice (D : D7) (i : Fin D.R.m) : VStd D i ↔ FrameChoice D i := by
  refine ⟨fun h => ?_, vStd_of_frameChoice D i⟩
  obtain ⟨h1, h2⟩ := (vStd_iff_gram_and_lattice D i).1 h
  refine ⟨fun a b => (congrFun (congrFun h1 a) b).trans Matrix.one_apply, fun a => ?_⟩
  have h3 : (Pi.single a 1 : Fin (Vc D i).rank → D.host.E) ∈ L0c D (Vc D i) := by
    rw [h2, SetLike.mem_coe, Submodule.mem_pi]
    intro b _
    by_cases hb : b = a
    · subst hb
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne hb]
      exact zero_mem _
  have h4 : ∑ b, (Pi.single a 1 : Fin (Vc D i).rank → D.host.E) b • (Vc D i).frame b ∈ (Vc D i).L0 := h3
  simpa [Pi.single_apply] using h4

theorem vStd_of_eq_stdSpace (D : D7) (i : Fin D.R.m)
    (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n p q : ℕ)
    (h : D.sp.V ((i : ℕ) + 1) = Examples₂.stdSpace hstar n (fun _ => false) p q) : VStd D i := by
  refine vStd_of_frameChoice D i ?_
  rw [FrameChoice, h]
  exact orthFrame_stdSpace hstar n p q

theorem nV_pos (R : Ranks) : 0 < R.nV := by
  have := R.rank_add_five_le
  unfold Ranks.nV
  omega

theorem neg_eq_false_of_vStd (D : D7) (i : Fin D.R.m) (h : VStd D i) : D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  let τ := D.host.φ₀
  have hs := D.sp.V_sig ((i : ℕ) + 1) τ
  rw [factVSig _ _ D.sp _ (by omega) (by omega) τ, if_pos hneg] at hs
  have h1 : Formalism.UG.HasSignature ((Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)).map τ)
      (Vc D i).rank 0 := by
    have h0 : (Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)) = 1 := h.1
    rw [h0, Matrix.map_one _ (map_zero _) (map_one _)]
    simpa using Formalism.UG.P.stdform_sig_one (n := Fin (Vc D i).rank)
  have h2 := (sig_family (Vc D i) τ (D.sp.cm.cmUnram.2.1 τ) _ h1 hs).1
  have := nV_pos D.R
  simp only at h2
  omega

def reframeV (D : D7) (b : ∀ j, Module.Basis (Fin (D.sp.V j).rank) D.host.E (D.sp.V j).V) : D7 :=
  { D with
    sp := { D.sp with
      V := fun j => reframe (D.sp.V j) (b j)
      V_sig := fun j => sigOK_reframe D.sp.cm.cmUnram.2.1 (D.sp.V_sig j) (b j) } }

theorem exists_reframe_vStd (D : D7) (hpos : ∀ i : Fin D.R.m, D.sp.Vneg ((i : ℕ) + 1) = false) :
    ∃ b, ∀ i : Fin D.R.m, VStd (reframeV D b) i := by
  have key : ∀ j, ∃ b, 1 ≤ j → j ≤ D.R.m → OrthFrame (reframe (D.sp.V j) b) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · have h := D.sp.V_std j hj.1 hj.2
      have hn : D.sp.Vneg j = false := by
        have := hpos ⟨j - 1, by omega⟩
        rwa [show j - 1 + 1 = j by omega] at this
      rw [hn, if_neg Bool.false_ne_true] at h
      obtain ⟨b, hb⟩ := exists_orthFrame _ (D.sp.V_rank j hj.1 hj.2) h
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨(D.sp.V j).frame, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose b hb using key
  exact ⟨b, fun i => vStd_of_frameChoice (reframeV D b) i (hb _ (by omega) i.2)⟩

theorem neg_eq_false_of_posDef (D : D7) (i : Fin D.R.m) (h : (Vc D i).IsPosDef) :
    D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  have h1 := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) D.host.φ₀
  rw [if_pos hneg] at h1
  have h2 := congrArg Prod.snd ((h D.host.φ₀).symm.trans h1)
  exact (nV_pos D.R).ne h2

theorem exists_reframe_vStd_of_posDef (D : D7) (hpos : ∀ i : Fin D.R.m, (Vc D i).IsPosDef) :
    ∃ b, ∀ i : Fin D.R.m, VStd (reframeV D b) i :=
  exists_reframe_vStd D fun i => neg_eq_false_of_posDef D i (hpos i)

theorem exists_reframe_not_vStd (D : D7) : ∃ b, ∀ i : Fin D.R.m, ¬ VStd (reframeV D b) i := by
  have key : ∀ j, ∃ b, 1 ≤ j → j ≤ D.R.m → (reframe (D.sp.V j) b).gram ≠ 1 := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · obtain ⟨b, hb⟩ := exists_gram_ne_one (D.sp.V j) (by rw [D.sp.V_rank j hj.1 hj.2]; exact nV_pos D.R)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨(D.sp.V j).frame, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose b hb using key
  exact ⟨b, fun i h => hb _ (by omega) i.2 h.1⟩

end GlobalTheory.StdFrame
