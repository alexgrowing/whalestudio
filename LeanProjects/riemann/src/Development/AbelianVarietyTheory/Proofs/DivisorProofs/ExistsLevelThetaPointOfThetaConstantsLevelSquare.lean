import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem nonempty_level_algClosed (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (M : ℕ)
    (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) : Nonempty (Level P M ze) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let z' : Kˣ := Units.map e.hom.hom.toMonoidHom ze
  have hz' : IsPrimitiveRoot z' M := hz.map_of_injective (f := Units.map e.hom.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso e.hom).1)
  have hze : unitOn z' = ze := Units.ext (e.hom_inv_id_apply (ze : Γ(Sp K, ⊤)))
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P M hM z' hz'
  rw [hze] at hw
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P M ze hz
    (fun F _ s => by
      have := nt F
      refine ⟨?_, ?_⟩
      · rw [← map_natCast (Spec.preimage s).hom]; exact (map_ne_zero _).2 hM
      · rw [← hze]
        exact hz'.map_of_injective (f := Units.map (s.appTop.hom.comp e.inv.hom).toMonoidHom)
          (Units.map_injective (RingHom.injective _)))
    pt hpt hw
  exact ⟨lev⟩

theorem exists_level_isThetaPt_of_hasTh : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (rig : LB.Gen (P.L.pull (eSec P.A))) (g m N : ℕ) (hg : P.g = g) (c : Fin N → K) (ze : Γ(Sp K, ⊤)ˣ), rig.IsGen → Odd m → (m : K) ≠ 0 → IsPrimitiveRoot ze (m ^ 2) → HasTh P.A P.L rig m (𝟙 (Sp K)) c → ∃ (lev : Out.Level P (m ^ 2) ze) (β : (Fin (2 * g) → ZMod (m ^ 2)) → Fin N), ∀ mu : K, mu ≠ 0 → IsThetaPt P m (levelPoint lev hg) (fun a => GlobalTheory.ZH.fn (mu * c (β a))) := by
  intro K _ _ P rig g m N hg c ze hrig hm hK hze hc
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hK2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hK
  obtain ⟨lev⟩ := nonempty_level_algClosed hL K P (m ^ 2) hK2 ze hze
  obtain ⟨v, hv⟩ := ThetaPtDet.exists_thetaPt_of_level hL K P hg m hm hK lev
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let v' : (Fin (2 * g) → ZMod (m ^ 2)) → K := fun a => e.hom.hom (v a)
  have hvv : v = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => (e.hom_inv_id_apply (v a)).symm
  rw [hvv] at hv
  obtain ⟨th, hth, hthG⟩ :=
    exists_gen_thG_of_isThetaPt K P rig hrig m _ (levelPoint lev hg) v' (ThetaPtDet.levelPoint_pow lev hg) hv
  obtain ⟨θ, pt, hgen, hinj, hG, hall⟩ := hc
  have hβ : ∀ a, ∃ b, pt b = levelPoint lev hg a := fun a => by
    let u : Over.mk (spMap (RingHom.id K) ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap (RingHom.id K)) rfl
    obtain ⟨b, hb⟩ := hall K (RingHom.id K) (u ≫ levelPoint lev hg a) (by
      rw [← MonObj.comp_pow, ThetaPtDet.levelPoint_pow, MonObj.comp_one])
    exact ⟨b, TorsionFieldExt.comp_injective u _ (Over.OverMorphism.ext hb.symm)⟩
  choose β hβ using hβ
  refine ⟨lev, β, fun mu hmu => ?_⟩
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast e.inv.hom]
    exact (IsUnit.mk0 _ hK2).map _
  obtain ⟨s, hs⟩ := hth θ
  have e₁ : SecM.ofSec P.A θ = s • SecM.ofSec P.A th := Subtype.ext (funext hs)
  obtain ⟨r, hr⟩ := hgen th
  have e₂ : SecM.ofSec P.A th = r • SecM.ofSec P.A θ := Subtype.ext (funext hr)
  have k₁ : ∀ a, c (β a) = e.hom.hom s * v' a := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun q₁ (ThG.smul P.isLB e₁ (hthG a)))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  have k₂ : ∀ a, v' a = e.hom.hom r * c (β a) := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun (hthG a) (ThG.smul P.isLB e₂ q₁))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  by_cases hs₀ : e.hom.hom s = 0
  · have h0 : ∀ a, c (β a) = 0 := fun a => by rw [k₁, hs₀, zero_mul]
    have : (fun a => GlobalTheory.ZH.fn (mu * c (β a))) = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => by
      rw [k₂, h0, mul_zero, mul_zero]
    rw [this]
    exact hv
  · refine GenericObject.isThetaPt_unit_mul P m (levelPoint lev hg) _ _ (e.inv.hom (mu * e.hom.hom s))
      ((IsUnit.mk0 _ (mul_ne_zero hmu hs₀)).map _) (fun a => ?_) hv
    rw [k₁, ← _root_.mul_assoc]
    exact map_mul e.inv.hom _ _

end GlobalTheory.UMin
