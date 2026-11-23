import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts

noncomputable section
namespace GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

section Sum
variable {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L)

def sumEquiv (h : IsSumLat i i') : (T.V × T'.V) ≃ₗ[LL] T''.V :=
  LinearEquiv.ofBijective (i.f.coprod i'.f) h.1

theorem sumEquiv_apply (h : IsSumLat i i') (x : T.V) (y : T'.V) :
    sumEquiv i i' h (x, y) = i.f x + i'.f y := rfl

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : _root_.Formalism.BasicNotions.LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} in
variable {T T' T'' : _root_.Formalism.BasicNotions.LocLat G Qp LL O} (i : _root_.Formalism.WeaklyAdmissibleFiltrations.LatHom T.L T''.L) (i' : _root_.Formalism.WeaklyAdmissibleFiltrations.LatHom T'.L T''.L) in
theorem _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.symm_act (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat i i') (g : G) (z : T''.V) :
    (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm (T''.ρ g z) =
      (T.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).1,
        T'.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).2) := by
  apply (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).injective
  rw [LinearEquiv.apply_symm_apply, _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply, i.equiv, i'.equiv, ← map_add,
    ← _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply i i' h, Prod.mk.eta, LinearEquiv.apply_symm_apply]

def pr₁ (h : IsSumLat i i') : LatHom T''.L T.L where
  f := LinearMap.fst LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hx

def pr₂ (h : IsSumLat i i') : LatHom T''.L T'.L where
  f := LinearMap.snd LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hy

end Sum

theorem latHom_ext {T T' : LocLat G Qp LL O} {f g : LatHom T.L T'.L} (h : ∀ x, f.f x = g.f x) :
    f = g := by
  cases f; cases g
  congr 1
  exact LinearMap.ext h

theorem map_of_zero {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (h : ∀ x, f.f x = 0)
    (x : W.DD T) : W.map f x = 0 := by
  have : f = latComp (latSmul T' (0 : O)) f := latHom_ext fun y => by
    simp [latComp, latSmul, h]
  rw [this, W.map_comp, W.map_latSmul, zero_smul]

theorem sum_N {T T' T'' : LocLat G Qp LL O} (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hT'' : IsCrys PD T''.ρ)
    (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) (h : IsSumLat i i') (x : W.DD T) (y : W.DD T') :
    W.map i x + W.map i' y ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T') := by
  have e1 : ∀ a, (pr₁ i i' h).f (i.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₁, this]
  have e2 : ∀ a, (pr₁ i i' h).f (i'.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₁, this]
  have e3 : ∀ a, (pr₂ i i' h).f (i.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₂, this]
  have e4 : ∀ a, (pr₂ i i' h).f (i'.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₂, this]
  constructor
  · intro hz
    have h1 := W.map_N (pr₁ i i' h) hT'' hT _ hz
    have h2 := W.map_N (pr₂ i i' h) hT'' hT' _ hz
    rw [map_add, ← W.map_comp, ← W.map_comp] at h1 h2
    rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext e1, W.map_id,
      map_of_zero (latComp (pr₁ i i' h) i') e2, add_zero] at h1
    rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext e4, W.map_id,
      map_of_zero (latComp (pr₂ i i' h) i) e3, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hx, hy⟩
    exact (W.N T'').add_mem (W.map_N i hT hT'' x hx) (W.map_N i' hT' hT'' y hy)

theorem sumFor_of_crys
    (hc : ∀ (T T' T'' : LocLat G Qp LL O) (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L),
      IsSumLat i i' → IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ) : SumFor W := by
  intro T T' T'' hT hT' i i' h
  have key : ∀ a b, (pr₁ i i' h).f (i.f a + i'.f b) = a ∧ (pr₂ i i' h).f (i.f a + i'.f b) = b :=
    fun a b => by
      have := (sumEquiv i i' h).symm_apply_apply (a, b)
      rw [sumEquiv_apply] at this
      simp only [pr₁, pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      simp
  have hbij : Function.Bijective ((W.map i).coprod (W.map i')) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨x, y⟩ hxy
      simp only [LinearMap.coprod_apply] at hxy
      have h1 := congrArg (W.map (pr₁ i i' h)) hxy
      have h2 := congrArg (W.map (pr₂ i i' h)) hxy
      rw [map_add, ← W.map_comp, ← W.map_comp, map_zero] at h1 h2
      rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext fun a => by
          simpa [latComp, latId] using (key a 0).1, W.map_id,
        map_of_zero (latComp (pr₁ i i' h) i') (fun a => by simpa [latComp] using (key 0 a).1),
        add_zero] at h1
      rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext fun a => by
          simpa [latComp, latId] using (key 0 a).2, W.map_id,
        map_of_zero (latComp (pr₂ i i' h) i) (fun a => by simpa [latComp] using (key a 0).2),
        zero_add] at h2
      simp [h1, h2]
    · intro z
      refine ⟨(W.map (pr₁ i i' h) z, W.map (pr₂ i i' h) z), ?_⟩
      simp only [LinearMap.coprod_apply]
      rw [← W.map_comp, ← W.map_comp, ← W.map_latAdd,
        show latAdd (latComp i (pr₁ i i' h)) (latComp i' (pr₂ i i' h)) = latId T'' from
          latHom_ext fun a => by
            obtain ⟨⟨x, y⟩, rfl⟩ := (sumEquiv i i' h).surjective a
            rw [sumEquiv_apply]
            change i.f ((pr₁ i i' h).f _) + i'.f ((pr₂ i i' h).f _) = _
            rw [(key x y).1, (key x y).2]
            rfl, W.map_id]
  refine ⟨LinearEquiv.ofBijective _ hbij, fun x y => rfl, fun x y => ?_, fun g x y => ?_,
    fun x y => sum_N hT hT' (hc T T' T'' i i' h hT hT') i i' h x y⟩
  · change W.φD T'' (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add, ← W.map_φ, ← W.map_φ]
    rfl
  · change W.γD T'' g (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add, ← W.map_γ, ← W.map_γ]
    rfl

end GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
