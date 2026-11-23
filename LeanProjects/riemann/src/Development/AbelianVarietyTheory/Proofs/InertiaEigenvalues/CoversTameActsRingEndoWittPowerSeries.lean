import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverRing

variable {l : ℕ} [hl : Fact l.Prime]

theorem smul_eq_zero_ainf {c : ℤ_[l]} (hc : c ≠ 0) {z : Ainf l} (h : c • z = 0) : z = 0 := by
  have h1 := PadicInt.unitCoeff_spec hc
  rw [h1, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc] at h
  have h2 : (l : Ainf l) ^ c.valuation * z = 0 :=
    ((PadicInt.unitCoeff hc).isUnit.map (algebraMap ℤ_[l] (Ainf l))).mul_right_eq_zero.1 h
  have key : ∀ n : ℕ, ∀ z : Ainf l, (l : Ainf l) ^ n * z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih => intro z h; exact ih z (ainf_torsionFree _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact key _ z h2

theorem one_tmul_inj {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Nontrivial O]
    {x y : Ainf l} (h : (1 : O) ⊗ₜ[ℤ_[l]] x = (1 : O) ⊗ₜ[ℤ_[l]] y) : x = y := by
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_zero (b.repr.injective (by ext i; simp [hc i]))
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] (Ainf l) ((b.coord i).rTensor (Ainf l) w)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (smul_eq_zero_ainf hi h1)

variable {a : ℕ} [NeZero a]

theorem exists_root {e : ℕ} [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]
    (γ : TameGal ↥LL.1 l e a) :
    ∃ c : Wq l a, ∀ τ, algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ c) = γ.root τ := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have he : e = l ^ a - 1 := by
    have := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a); omega
  set w : ↥LL.1 := ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) with hwdef
  have hw : (w : Om l) = ω := by
    refine (algebraMap (Om l) ℂ_[l]).injective ?_
    have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
    simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
    exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)
  have hwp : IsPrimitiveRoot w e := by
    rw [he]
    refine IsPrimitiveRoot.of_map_of_injective (f := (LL.1).val) ?_ Subtype.val_injective
    simpa [hw] using hω
  have hpow : (((γ.left : (↥LL.1)ˣ) : ↥LL.1)) ^ e = 1 := (mem_rootsOfUnity' _ _).1 γ.left.2
  obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one hpow
  refine ⟨WittVector.teichmuller l z ^ k, fun τ => ?_⟩
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z ^ k)) : ↥(OL LL)) : ↥LL.1) = _
  rw [map_pow, sigma_pow_teich, map_pow, map_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hwdef,
    TameGal.root, powL_apply]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hk]
  ring

end GlobalTheory.BKGal.CoverRing

open GlobalTheory.BKGal.CoverRing GlobalTheory.BKGal.CoverBridge in

theorem GlobalTheory.BKGal.covers_ringEndo : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a),
    Covers ↥LL.1 (thetaW a LL) ϖ g γ →
      ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  intro l _ a e _ _ ϖ LL _ _ g γ hcov
  obtain ⟨c, hc⟩ := exists_root LL γ
  refine ⟨(rescale c).comp (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
    Wq l a →+* Wq l a)), fun x => ?_⟩
  have h := hcov (toAc (thetaW a LL) ↥LL.1 x)
    (toAc (thetaW a LL) ↥LL.1 (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x))) (fun τ => toAc_rescale (thetaW a LL) γ c hc x τ)
  rw [PiSys.iTot_toAc, PiSys.iTot_toAc, galOA_tmul] at h
  exact (one_tmul_inj h).symm
