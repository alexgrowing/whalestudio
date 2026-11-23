import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobCoord

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem frob_mem_invL_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) : frob K l f ∈ invL l (S O K e) :=
  frob_mem_invL l (fun _ h => frob_mem_S l h) hf

theorem iSl_frob (ϖ : PiSys l e) (f : invL l (S O K e)) :
    ϖ.iSl O K ⟨frob K l f, frob_mem_invL_S f.2⟩ = frobOB l O (ϖ.iSl O K f) := by
  let F : invL l (S O K e) →+* invL l (S O K e) :=
    (frob K l).toRingHom.restrict _ _ fun _ h => frob_mem_invL_S h
  have key : (ϖ.iSl O K).toRingHom.comp F = (frobOB l O).toRingHom.comp (ϖ.iSl O K).toRingHom := by
    have hS : ∀ (x : S O K e) (h : frob K l (x : K⟦X⟧) ∈ invL l (S O K e)) (h' : (x : K⟦X⟧) ∈ invL l (S O K e)),
        ϖ.iSl O K ⟨frob K l x, h⟩ = frobOB l O (ϖ.iSl O K ⟨x, h'⟩) := fun x h h' => by
      rw [ϖ.iSl_of_mem O K (frob_mem_S l x.2) h, ϖ.iSl_of_mem O K x.2 h', ϖ.iS_frob O K x, frobOB_toOB]
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) ?_
    ext x
    exact hS x _ _
  exact RingHom.congr_fun key f

theorem frobOB_idem (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    frobOB l O (idem (constB t) τ) = idem (constB t) (τ + 1) := by
  change frobOB l O (toOB l O (toOCr l O (idem (constA t) τ))) = toOB l O (toOCr l O (idem (constA t) (τ + 1)))
  rw [frobOB_toOB, frobOCr_toOCr, frobOA_idem]

theorem iB_frob (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ZMod a → invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨frob K l (g (τ - 1)), frob_mem_invL_S (g (τ - 1)).2⟩) = frobOB l O (ϖ.iB t K g) :=
  (map_glue (frobOB l O).toRingHom 1 (frobOB_idem t) fun τ => (iSl_frob ϖ (g (τ - 1))).symm).symm

theorem iB_of_A (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (F : ZMod a → A O K)
    (h : ∀ τ, (F τ : K⟦X⟧) ∈ invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨F τ, h τ⟩) = toB l O (ϖ.iTot t K F) :=
  (ϖ.iB_of_mem t K fun τ => ⟨F τ, A_le_S l e (F τ).2⟩).trans (congrArg (toOB l O) (ϖ.iC_of_mem t K F))

theorem toBcris_phi (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ)
    (Y : Matrix ι ι (OA l O)) :
    (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) →
      ∀ m m' : P.MMl, m'.1 = P.phi m.1 →
        toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' =
          (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  intro hY m m' hm
  choose f hf hYf using hY
  set c := coordL P (invL l (S O K e)) m with hc
  set c' := coordL P (invL l (S O K e)) m' with hc'

  have step1 : ∀ i τ, frob K l (E K l e) ^ α * (c' i τ : K⟦X⟧) =
      ∑ j, (frobAc l (f i j) τ : K⟦X⟧) * frob K l (c j (τ - 1) : K⟦X⟧) := by
    intro i τ
    have h1 : (c' i τ : K⟦X⟧) = frob K l (m.1 (τ - 1) i) := by
      change (P.mxInv τ *ᵥ m'.1 τ) i = _
      rw [hm, PhiMod.phi_apply, Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
    have h2 : m.1 (τ - 1) i = ∑ j, P.mx (τ - 1) i j * (c j (τ - 1) : K⟦X⟧) := by
      rw [← mx_mulVec_coordL P _ m (τ - 1)]
      simp only [Matrix.mulVec, dotProduct, hc]
    rw [h1, h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_frobAc, frobTot_apply, hf i j (τ - 1), map_mul, map_mul, map_pow, mul_assoc]

  let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
    fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
  let cF : ι → ZMod a → invL l (S O K e) :=
    fun j τ => ⟨frob K l (c j (τ - 1)), frob_mem_invL_S (c j (τ - 1)).2⟩
  have step2 : ∀ i, liftA (frobAc l fun _ => EIn l e (A O K)) ^ α * c' i =
      ∑ j, liftA (frobAc l (f i j)) * cF j := by
    intro i
    funext τ
    apply Subtype.ext
    simp only [liftA, cF, Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AddSubmonoidClass.coe_finsetSum]
    exact step1 i τ
  ext i
  have h3 := congrArg (ϖ.iB t K) (step2 i)
  rw [map_mul, map_pow, map_sum] at h3
  simp only [Finset.sum_congr rfl fun j _ => map_mul (ϖ.iB t K) (liftA (frobAc l (f i j))) (cF j)] at h3
  simp only [liftA, iB_of_A, cF, iB_frob, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
  rw [Pi.smul_apply, smul_eq_mul, toBcris_apply, ← hc', h3]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hYf, toBcris_apply, ← hc]

end GlobalTheory.BKGal.FrobCoord
