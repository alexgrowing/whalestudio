import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.GLinkPf

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem inN_of_nlam (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T)) : (frF F hT).InN (n : S.V →ₗ[E] S.V) := by
  obtain ⟨⟨hiso, -⟩, hXa, hperp⟩ := h
  refine ⟨fun x y => hiso y x, n.bijective, fun a => ?_, fun y hy => ?_⟩
  · rw [GlobalTheory.TypeAsm.FibProof.frF_e, fv_cast, GlobalTheory.TypeAsm.FibProof.frF_Xa]
    exact hXa a.val (F.e a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
  · rw [GlobalTheory.TypeAsm.FibProof.frF_X]
    apply hperp
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    change x ∈ F.X at hx
    rw [← GlobalTheory.TypeAsm.FibProof.frF_X F hT] at hx
    have hle : (frF F hT).X ≤ LinearMap.ker (S.hT.flip y) := by
      unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
      rw [Submodule.span_le]
      rintro _ ⟨a, -, rfl⟩
      have := hy a
      rw [GlobalTheory.TypeAsm.FibProof.spH_B] at this
      exact p_symm_zero S this
    exact hle hx

end Gen

variable {D : D7} {X : HidaSetting D}

theorem smul_top (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n • (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
  rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.2 n.surjective

theorem mem_gam_iff (u : D.what₂.Word) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (hF : N.F = F0 X u)
    (hF' : N.F' = F0 X u) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n ∈ N.Gam (VS D).L0 ↔ n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := by
  unfold GlobalTheory.DegCnt.NF.Gam GlobalTheory.DegCnt.NF.R
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hR, hst⟩
    have hT : n ∈ NLam ⊤ (lf D (X.Fu u)) := by
      clear hst
      induction hR using Subgroup.closure_induction with
      | mem s hs =>
        have h1 := hs.1
        rw [hF] at h1
        exact GlobalTheory.TypeAsm.FibProof.nlam_of_inN (lf D (X.Fu u)).fl (tu_ne D u) h1 (smul_top s)
      | one => exact GlobalTheory.LoopC.FrEqv.one_mem_NLam
      | mul x y _ _ hx hy => exact GlobalTheory.LoopC.FrEqv.mul_mem_NLam hy hx
      | inv x _ hx => exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam hx
    exact ⟨⟨hT.1.1, by rw [GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact hst⟩, hT.2.1, hT.2.2⟩
  · intro h
    refine ⟨Subgroup.subset_closure ?_, ?_⟩
    · have h1 : (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) := inN_of_nlam (lf D (X.Fu u)).fl (tu_ne D u) h
      rw [hF, hF']
      exact ⟨h1, h1⟩
    · rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact h.1.2

theorem trI_act (C : Choice X 1) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (τ : D.what₂.Tau) (y : (VS D).V) :
    Matrix.of (trI C x.1 τ) *ᵥ phiV C τ y = phiV C τ (n y) := by
  obtain ⟨_, hQQi, _, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := hx
  have hM1' : uMat (x.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3 y
  have e : Matrix.of (trI C x.1 τ) = Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x.1 (vOf X τ)) := by
    unfold trI; exact Matrix.of.apply_symm_apply _
  rw [e]
  unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG
  rw [hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hQ]

theorem eq_of_act (C : Choice X 1) {m m' : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (h : ∀ τ y, Matrix.of (m τ) *ᵥ phiV C τ y = phiV C τ (n y))
    (h' : ∀ τ y, Matrix.of (m' τ) *ᵥ phiV C τ y = phiV C τ (n y)) : m = m' := by
  funext τ
  have hL : Matrix.mulVecLin (Matrix.of (m τ)) = Matrix.mulVecLin (Matrix.of (m' τ)) :=
    LinearMap.ext_on_range (GlobalTheory.TypeAsm.GramPf.phiV_span C τ) (fun y => by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h τ y, h' τ y])
  apply Matrix.of.injective
  ext i j
  have := congrFun (LinearMap.congr_fun hL (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

end GlobalTheory.TypeAsm.GLinkPf

namespace GlobalTheory.TypeAsm

theorem realPts_Gam_eq_trI_image_NOinf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  intro D _ X _ u C _ N hF hF'
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    have hL := (GLinkPf.mem_gam_iff u N hF hF' n).1 hn
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hL.1.1
    refine ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hL⟩, ?_⟩
    exact GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, n, hx, rfl, hL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    exact ⟨n, (GLinkPf.mem_gam_iff u N hF hF' n).2 hL, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm
