import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexTransferAlongProjection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertLatIndex

open GlobalTheory.InertLoc Formalism.UG

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.map_surjective (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (fun b => ⟨pairA D.host.F 0 b, rfl⟩) Function.surjective_id b
  exact ⟨a, ha⟩

theorem ker_finPart_le {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P}
    {π : AE D →+* LP D P} (hC : Chart e σ π) : RingHom.ker (finPart D) ≤ RingHom.ker π := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (hC.2.2.1 a).2 ?_
  refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := D.host.F) (A := _) (B := _) _ ?_ ?_
  · show infPart D (e * a) = 0
    rw [map_mul, hC.1.2.2, zero_mul]
  · show finPart D (e * a) = 0
    rw [map_mul, ha, mul_zero]

theorem mem_span_basisFun {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]
    (z : n → K) : z ∈ Submodule.span O (Set.range (Pi.basisFun K n)) ↔ ∀ i, z i ∈ O := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Pi.basisFun_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, Ne.symm hij]
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
  · intro hz
    have : z = ∑ i, (⟨z i, hz i⟩ : O) • Pi.basisFun K n i := by
      conv_lhs => rw [← (Pi.basisFun K n).sum_repr z]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finMat_apply {D : D7} {W : HSp D} (x : GA D W) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j = finPart D (Formalism.L2.Theta.mt W x i j) := rfl

theorem finMat_sub_one_eq {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D e * (finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j) := by
  have h1ij : (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i j) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1ij, finMat_apply, ← RingHom.map_sub, ← RingHom.map_mul, ← Matrix.sub_apply, hx i j]

theorem finMat_mulVec_fix {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x)
    (y : Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig W.gram x *ᵥ (y - finPart D e • y) = y - finPart D e • y := by
  funext i
  have key : ∀ j, finMat D.sp.cm.sig W.gram x i j * (y - finPart D e • y) j =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j *
        (y - finPart D e • y) j := by
    intro j
    have := finMat_sub_one_eq x hx i j
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y j) * this
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Matrix.one_apply]

theorem inv_mulVec_conj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (β g : GL n K) (w : n → K) :
    (β⁻¹).1 *ᵥ ((β.1 * g.1 * (β⁻¹).1) *ᵥ w) = g.1 *ᵥ ((β⁻¹).1 *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem latIndex_eq_of_chart {D : D7} {W : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    {σ : LP D P →+* LP D P} {π : AE D →+* LP D P} {β : GL (Fin W.rank) (LP D P)}
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hα : finPart D e = α ⊗ₜ[D.host.F] (1 : D.host.E))
    (hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F)
    (hC : Chart e σ π) (hF : Frame W e σ π β) (x : GA D W) (hx : SuppF W e x) (g : GL (Fin W.rank) (LP D P))
    (hxg : (Formalism.L2.Theta.mt W x).map π = β.1 * g.1 * (β⁻¹).1) :
    latIndex W x = ((Submodule.span (P.adicCompletionIntegers D.host.E)
        (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).map
        ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
          (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
  let πf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* LP D P :=
    (RingHom.liftOfSurjective (finPart D) (finPart_surjective D)) ⟨π, ker_finPart_le hC⟩
  have hπf : ∀ a, πf (finPart D a) = π a := fun a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπe : π e = 1 := by
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, hC.1.1, mul_one, sub_self]
    have := (hC.2.2.1 (e - 1)).2 h0
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let T : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig W.gram x).mulVecLin.toAddMonoidHom
  let p : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := DistribMulAction.toAddMonoidHom _ (finPart D e)
  let Φ : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin W.rank → LP D P) :=
    ((β⁻¹).1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.toAddMonoidHom.comp
      (πf.toAddMonoidHom.compLeft (Fin W.rank))
  let h : (Fin W.rank → LP D P) →+ (Fin W.rank → LP D P) :=
    ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
      (P.adicCompletionIntegers D.host.E)).toAddMonoidHom
  have hΦ : ∀ y, Φ y = (β⁻¹).1 *ᵥ (fun k => πf (y k)) := fun y => rfl
  have h1 : ∀ y ∈ Formalism.L2.NTheta.LamHat W, p y ∈ Formalism.L2.NTheta.LamHat W := by
    have hle : Formalism.L2.NTheta.LamHat W ≤ (Formalism.L2.NTheta.LamHat W).comap p := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, z, hz, rfl⟩
      show p _ ∈ Formalism.L2.NTheta.LamHat W
      apply AddSubgroup.subset_closure
      refine ⟨α * a, hαint a ha, z, hz, ?_⟩
      funext i
      show finPart D e * (a ⊗ₜ[D.host.F] z i) = _
      rw [hα, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact fun y hy => hle hy
  have h2 : ∀ y, T (p y) = p (T y) := fun y => by
    show finMat D.sp.cm.sig W.gram x *ᵥ (finPart D e • y) = finPart D e • (finMat D.sp.cm.sig W.gram x *ᵥ y)
    exact Matrix.mulVec_smul _ _ _
  have h3 : ∀ y, T (y - p y) = y - p y := fun y => finMat_mulVec_fix x hx y
  have h4 : ∀ y, Φ y = 0 → p y = 0 := by
    intro y hy
    have h0 : ∀ k, πf (y k) = 0 := by
      intro k
      have := congrArg (fun w => β.1 *ᵥ w) hy
      simp only [hΦ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this k
    funext k
    obtain ⟨a, ha⟩ := finPart_surjective D (y k)
    have hπa : π a = 0 := by rw [← hπf, ha]; exact h0 k
    show finPart D e * y k = 0
    rw [← ha, ← RingHom.map_mul, (hC.2.2.1 a).1 hπa, RingHom.map_zero]
  have h5 : ∀ y, Φ (T y) = h (Φ y) := by
    intro y
    have hmap : (finMat D.sp.cm.sig W.gram x).map πf = β.1 * g.1 * (β⁻¹).1 := by
      rw [← hxg]
      exact Matrix.ext fun i j => hπf _
    have hT : (fun k => πf ((finMat D.sp.cm.sig W.gram x *ᵥ y) k)) =
        (finMat D.sp.cm.sig W.gram x).map πf *ᵥ (fun k => πf (y k)) :=
      funext fun k => RingHom.map_mulVec πf _ y k
    show Φ (finMat D.sp.cm.sig W.gram x *ᵥ y) = g.1 *ᵥ Φ y
    rw [hΦ, hΦ, hT, hmap]
    exact inv_mulVec_conj β g _
  have hmapΦ : (Formalism.L2.NTheta.LamHat W).map Φ =
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine Iff.trans ?_ (mem_span_basisFun _ z).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose a ha using fun k => finPart_surjective D (y k)
      have hpy : (fun i => finPart D (e * a i)) ∈ Formalism.L2.NTheta.LamHat W := by
        have := h1 y hy
        convert this using 1
        funext i
        show finPart D (e * a i) = finPart D e * y i
        rw [RingHom.map_mul, ha]
      have hi := (hF.2 a).1 hpy
      have hz : Φ y = (β⁻¹).1 *ᵥ fun k => π (a k) := by
        rw [hΦ]
        congr 1
        funext k
        rw [← ha, hπf]
      rw [hz]
      exact hi
    · intro hz
      choose a ha using fun k => hC.2.1 ((β.1 *ᵥ z) k)
      have hb : (β⁻¹).1 *ᵥ (fun k => π (a k)) = z := by
        have : (fun k => π (a k)) = β.1 *ᵥ z := funext ha
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      refine ⟨fun i => finPart D (e * a i), (hF.2 a).2 ?_, ?_⟩
      · rw [hb]; exact hz
      · rw [hΦ]
        convert hb using 2
        funext k
        rw [hπf, RingHom.map_mul, hπe, one_mul]
  unfold latIndex
  rw [GlobalTheory.index_transfer_along_projection (Formalism.L2.NTheta.LamHat W) T p Φ h h1 h2 h3 h4 h5, hmapΦ,
    Submodule.map_toAddSubgroup]
  rfl

theorem latIndex_chart_eq : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  intro D W v ε hε P σ π β ι hC hF hG g
  obtain ⟨α, hεα, hα1, hα0⟩ := hε
  have hα : finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    subst hεα; rfl
  have hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F := by
    intro a ha w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [hα1, one_mul]; exact ha w
    · rw [hα0 w hw, zero_mul]; exact zero_mem _
  exact latIndex_eq_of_chart α hα hαint hC hF (ι g) (hG.1 g) g.1 (hG.2.1 g)

end GlobalTheory.InertLatIndex
