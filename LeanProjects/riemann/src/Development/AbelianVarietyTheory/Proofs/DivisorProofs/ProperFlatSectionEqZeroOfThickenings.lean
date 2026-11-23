import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.SpecialConn

theorem eq_zero_of_thickι (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f]
    (s : Γ(Y, ⊤)) (hs : ∀ n, (thickι f n).appTop.hom s = 0) : s = 0 := by
  obtain ⟨P⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f (Inh.trivLB_isLB Y)
  have hid : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id O))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec O (RingHom.id O) Y (𝟙 Y) f hid
  obtain ⟨w, hw⟩ := E.surjective (GlobalTheory.AlgGroup.fnSec (𝟙 Y) s)
  have key : ∀ i, rs Y (le_top : (𝟙 Y) ⁻¹ᵁ P.W i ≤ ⊤) s = loc P (𝟙 Y) f w.1 i := fun i => by
    have e := hE w i
    rw [hw] at e
    exact (rs_rs _ _ s).symm.trans e
  have key₀ : ∀ i, loc₀ P w.1 i = rs Y (le_top : P.W i ≤ ⊤) s := fun i => by
    have := (key i).trans (loc_comp P hid w.1 i)
    exact this.symm
  have hv : ∀ n k, thickQ O n (w.1 k) = 0 := by
    intro n
    have h := thickFib_isPullback f n
    obtain ⟨En, hEn⟩ := P.sec _ (thickQ O n) _ (thickι f n) (thickStr f n) h
    have hk : (P.D₀.map (thickQ O n)).mulVec (thickQ O n ∘ w.1) = 0 := funext fun j => by
      rw [← RingHom.map_mulVec]
      have := congrFun w.2 j
      rw [show P.D₀.mulVec w.1 j = 0 from this, map_zero]
      rfl
    have hz : (P.D₀.map (thickQ O n)).mulVec (0 : Fin P.a → _) = 0 := Matrix.mulVec_zero _
    have hloc : ∀ i, loc P (thickι f n) (thickStr f n) (thickQ O n ∘ w.1) i = 0 := fun i => by
      rw [loc_comp P h, key₀ i]
      have e₃ := congrArg (fun q => q.hom s) ((thickι f n).naturality (homOfLE (le_top : P.W i ≤ ⊤)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₃
      refine e₃.trans ?_
      change rs _ _ ((thickι f n).appTop.hom s) = 0
      rw [hs n, map_zero]
    have hloc₀ : ∀ i, loc P (thickι f n) (thickStr f n) (0 : Fin P.a → _) i = 0 := fun i => by
      simp [loc]
    have heq := En.injective (a₁ := ⟨_, hk⟩) (a₂ := ⟨0, hz⟩) (sec_ext _ _
      (fun i => thickι f n ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull _ _ (P.le i))
      (fun y => exists_mem P (thickι f n y)) fun i => by
        rw [hEn, hEn]
        exact (hloc i).trans (hloc₀ i).symm)
    intro k
    exact congrFun (congrArg Subtype.val heq) k
  have hw0 : ∀ k, w.1 k = 0 := fun k => by
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance (w.1 k) fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq_zero_iff_mem.1 (hv n k))
  refine Y.sheaf.eq_of_locally_eq' (fun i => P.W i) ⊤ (fun i => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_mem P y)) s 0 fun i => ?_
  change rs Y (le_top : P.W i ≤ ⊤) s = rs Y (le_top : P.W i ≤ ⊤) 0
  rw [map_zero, ← key₀ i]
  simp [loc₀, hw0]

end GlobalTheory.SpecialConn
