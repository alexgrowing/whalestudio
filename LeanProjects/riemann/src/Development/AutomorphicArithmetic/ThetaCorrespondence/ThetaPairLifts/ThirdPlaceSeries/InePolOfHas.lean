import Development.DiscreteGroups.GlobalIrreducibility.RegularLocalOfDepthZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
theorem inePol_eq_liftPoly_of_cuspidal {n : ℕ} (hn : 0 < n) (hbig : n = 1 ∨ 16 * n ^ 2 < g) (σ : Irr (w.adicCompletion E) n) (hc : IsCuspidal σ.π) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (σ.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls σ.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  have hc' : IsCuspidal (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap i.symm hi σ.π hc
  let ρ : GLRep g := ⟨n, Rep.of (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))⟩
  have hρ : TameGen.IsSC ρ := ⟨hn, (Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _
      fun y => ⟨_, GlobalTheory.TameRecord.glMap_apply_symm i y⟩), GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal _ _ _ _ hc'⟩
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := TameGen.exists_simple_of_has (sysOf L h5 hA) ρ.2.ρ f hf
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact CategoryTheory.id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  have hτ : FiniteGL.IsCuspidal τ.ρ := fun b hb hb' u hu => hinj (by
    rw [map_zero]
    exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal g ρ hρ hfix b hb hb' _ fun x hx => by rw [← heq, hu x hx])
  refine hDZ E Ω g A w h rc hrc i hi κ L t ht hκ n hbig σ.toIrrRep (IrrGL.isCusp_of.2 ⟨hn, hc⟩) τ f
    (isCuspOf_of_series L h5 hA τ (TameGen.isCusp_character hn τ hs hτ) f he) ⟨_, hφ, fun k u => ?_⟩
  exact (congrArg Subtype.val (heq (red g n k) u)).trans (repK_red ρ.2.ρ k (φ u))
theorem inePol_eq_liftPoly_of_has (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ}
    (π : Irr (w.adicCompletion E) n) (hB : 16 * n ^ 2 < g) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (π.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls π.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  obtain ⟨s, d, σ, hs⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL _ n π
  have h1 := hrc.recSupp n s π d σ hs (ineIncl h ⟨t, ht⟩)
  obtain ⟨-, hc, e, U, T, hT⟩ := hs
  obtain ⟨φ⟩ := GlobalTheory.IndField.multiProd_comp_glMap i.symm hi' hi
    (GlobalTheory.SplitWeil.nabs_map_of_homeomorph i.symm hi' hi) e (fun a => (σ a).π)
  have h2 : IsSubquotient (π.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))
      ((multiProd e fun a => (σ a).π).comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    ⟨⟨U.toSubmodule, fun x _ hv => U.apply_mem_toSubmodule _ hv⟩, ⟨T.toLinearMap, fun x => T.isIntertwining' _⟩, hT⟩
  obtain ⟨fs, hfs, rfl⟩ := series_of_isSubquotient (sysOf L h5 hA) e
    (fun a => (σ a).π.comp (Matrix.GeneralLinearGroup.map (n := Fin (d a)) i.toRingHom))
    (h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)) f hf
  have hbig : ∀ a, d a = 1 ∨ 16 * d a ^ 2 < g := fun a =>
    Or.inr (lt_of_le_of_lt (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (DiscreteGroups.sglob.DzType.Rt.le_of_sigmaEquiv e a) 2)) hB)
  have h3 : ∀ a, (rc (cls (σ a).toIrrRep)).charPol (ineIncl h ⟨t, ht⟩) = TameGen.liftPoly L.teich (fs a) := fun a => by
    rw [← WD.inePol_of_mem_Ine _ ht]
    exact _root_.DiscreteGroups.sglob.DzType.Rt.inePol_eq_liftPoly_of_cuspidal i hi hrc hDZ κ L h5 hA ht hκ (hc a).1 (hbig a) (σ a) (hc a).2.2 _ (hfs a)
  have h4 : ∀ u : Finset (Fin s), TameGen.liftPoly L.teich (∏ a ∈ u, fs a) = ∏ a ∈ u, TameGen.liftPoly L.teich (fs a) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [TameGen.liftPoly_one]
    | insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, TameGen.liftPoly_mul _ (TameGen.Has.monic (hfs a)).ne_zero
        (monic_prod_of_monic _ _ fun b _ => TameGen.Has.monic (hfs b)).ne_zero, ih]
  rw [WD.inePol_of_mem_Ine _ ht, h4]
  exact h1.trans (Finset.prod_congr rfl fun a _ => h3 a)
end Loc
end DiscreteGroups.sglob.DzType.Rt
end
end
