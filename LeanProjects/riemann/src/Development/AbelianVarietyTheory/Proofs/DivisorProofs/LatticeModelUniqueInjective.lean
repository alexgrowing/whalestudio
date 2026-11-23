import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

theorem latSec_map {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (M : X → AddSubgroup V)
    (φ : V →+ V') (hφ : Function.Injective φ) (U : X.Opens) (h : genericPoint X ∈ U) :
    (latSec M U).map φ = latSec (fun y => (M y).map φ) U := by
  ext w
  simp only [latSec, AddSubgroup.mem_map, AddSubgroup.mem_iInf]
  constructor
  · rintro ⟨v, hv, rfl⟩ y hy
    exact ⟨v, hv y hy, rfl⟩
  · intro hw
    obtain ⟨v, -, hv⟩ := hw _ h
    refine ⟨v, fun y hy => ?_, hv⟩
    obtain ⟨u, hu, hu'⟩ := hw y hy
    rwa [hφ (hu'.trans hv.symm)] at hu

def LatModel.mapLin {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V']
    [Module X.functionField V'] {M : X → AddSubgroup V} {F : X.Modules} (L : LatModel M F)
    (φ : V →ₗ[X.functionField] V') (hφ : Function.Injective φ) :
    LatModel (fun y => (M y).map φ.toAddMonoidHom) F where
  val U h := φ.toAddMonoidHom.comp (L.val U h)
  inj U h := hφ.comp (L.inj U h)
  range U h := by
    rw [AddMonoidHom.range_comp, L.range U h]
    exact latSec_map M φ.toAddMonoidHom hφ U h
  res U W e h s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.res U W e h s]
  smul U h r s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.smul U h r s, LinearMap.toAddMonoidHom_coe,
      LinearMap.map_smul]

def LatModel.transfer {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U)
    (s : Γ(F, U)) : Γ(F', U) :=
  Classical.choose (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

theorem LatModel.val_transfer {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.transfer L' U h s) = L.val U h s :=
  Classical.choose_spec (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

def LatModel.secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) where
  toFun := L.transfer L' U h
  map_add' s t := L'.inj U h (by simp only [map_add, LatModel.val_transfer])
  map_smul' r s := L'.inj U h (by
    simp only [RingHom.id_apply, LatModel.val_transfer, L'.smul U h, L.smul U h])
  invFun := L'.transfer L U h
  left_inv s := L.inj U h (by simp only [LatModel.val_transfer])
  right_inv s := L'.inj U h (by simp only [LatModel.val_transfer])

theorem LatModel.val_secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.secEquiv L' U h s) = L.val U h s :=
  L.val_transfer L' U h s

theorem subsingleton_sec_of_not_gen (F : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) :
    Subsingleton Γ(F, U) := by
  haveI : Subsingleton Γ(X, U) := ⟨fun a b => fn_ext fun h => absurd h hU⟩
  exact Module.subsingleton Γ(X, U) Γ(F, U)

open Classical in

def LatModel.secEquiv' {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) :=
  if h : genericPoint X ∈ U then L.secEquiv L' U h else
    haveI := subsingleton_sec_of_not_gen F h
    haveI := subsingleton_sec_of_not_gen F' h
    LinearEquiv.ofSubsingleton _ _

def LatModel.iso {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') : F ≅ F' :=
  GlobalTheory.LB.isoOfLinear (L.secEquiv' L') fun {U W} e s => by
    by_cases hW : genericPoint X ∈ W
    · have hU : genericPoint X ∈ U := e hW
      apply L'.inj W hW
      simp only [LatModel.secEquiv', dif_pos hW, dif_pos hU]
      rw [L.val_secEquiv L' W hW, L'.res U W e hW, L.res U W e hW, L.val_secEquiv L' U hU]
    · haveI := subsingleton_sec_of_not_gen F' hW
      exact Subsingleton.elim _ _

theorem latModel_map_and_unique : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  intro X _ V V' _ _ _ _ M F F' φ hφ L
  exact ⟨⟨L.mapLin φ hφ⟩, fun L' => ⟨L.iso L'⟩⟩

end GlobalTheory.LogDR
