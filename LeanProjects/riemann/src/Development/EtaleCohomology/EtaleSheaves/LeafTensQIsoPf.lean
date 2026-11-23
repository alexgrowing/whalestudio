import Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoPf

def LeafSecInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), Injective F → ∀ U : Scheme.{0},
  Module.Injective (ULift.{1} R) (Sec F U)

def LeafZModInjFlat : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

def LeafTensQIsoGen : Prop := ∀ (R : Type) [CommRing R] {I I' J S T : Cx R} (f : I ⟶ I'), QuasiIso f →
  I.IsStrictlyGE 0 → I'.IsStrictlyGE 0 → J.IsStrictlyGE 0 →
  (∀ (n : ℤ) (U : Scheme.{0}), Module.Flat (ULift.{1} R) (Sec (J.X n) U)) →
  ∀ (σ : Pair I J S) (τ : Pair I' J T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map (f.f s) a) b) →
  QuasiIso ι

theorem resAug_quasiIso (R : Type) [CommRing R] (F : Shv R) : QuasiIso (resAug F) := by
  unfold resAug; exact @InjectiveResolution.instQuasiIsoIntι' _ _ _ _ _

theorem res_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

theorem sgl_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (sgl F).IsStrictlyGE 0 := by
  infer_instance

theorem LeafTensQIso_of (hgen : LeafTensQIsoGen) (hinj : LeafSecInj) (hflat : LeafZModInjFlat) :
    LateralTheory.E.LeafExtTensPf.LeafTensQIso := by
  intro q _ i S T σ τ hσ hτ ι hι
  exact hgen (ZMod q) (resAug (tw q 0)) (resAug_quasiIso _ _) (sgl_strictlyGE _ _) (res_strictlyGE _ _)
    (res_strictlyGE _ _) (fun n U => hflat q _ (hinj _ _ (LateralTheory.E.LeafExtTensPf.res_injective _ _ n) U)) σ τ hσ hτ ι hι

end LateralTheory.E.LeafTensQIsoPf
