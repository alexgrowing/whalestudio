import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.SemiDivisible

theorem pow_surj_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hq : Function.Surjective q) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : ∀ t : T, ∃ s, s ^ n = t) (hB : ∀ b : B, ∃ c, c ^ n = b) (y : G) :
    ∃ x : G, x ^ n = y := by
  obtain ⟨c, hc⟩ := hB (q y)
  obtain ⟨z, rfl⟩ := hq c
  obtain ⟨t, ht⟩ := hk (y * (z ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hc, mul_inv_cancel])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨i s * z, ?_⟩
  rw [mul_pow, ← map_pow, ht, inv_mul_cancel_right]

theorem pow_surj_chars (X : Type) [AddCommGroup X] [Module.Free ℤ X] (U : Type) [CommGroup U]
    (n : ℕ) (hU : ∀ u : U, ∃ v, v ^ n = u) (t : Multiplicative X →* U) :
    ∃ s : Multiplicative X →* U, s ^ n = t := by
  choose r hr using hU
  let b := Module.Free.chooseBasis ℤ X
  let φ : X →ₗ[ℤ] Additive U :=
    b.constr ℤ fun j => Additive.ofMul (r (t (Multiplicative.ofAdd (b j))))
  let ψ : X →ₗ[ℤ] Additive U := (MonoidHom.toAdditiveRight t).toIntLinearMap
  have h : n • φ = ψ := b.ext fun j => by
    rw [LinearMap.smul_apply, b.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨AddMonoidHom.toMultiplicativeLeft φ.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun h x.toAdd)

theorem pow_surj_units (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (u : Γ(Sp k, ⊤)ˣ) : ∃ v : Γ(Sp k, ⊤)ˣ, v ^ n = u := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (show 0 < n by omega)
  have h : e.symm z ^ n = u.val := by rw [← map_pow, hz, e.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega)).1 (h ▸ u.isUnit)
  exact ⟨hu.unit, Units.ext h⟩

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left]
    (y : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left
      = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x)
    ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem pow_surj_abelian (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B]
    (hB : IsAbelianScheme B) {n : ℕ} (hn : 1 ≤ n) (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = y := by
  have := hB.comm
  have hf : IsFinite ((𝟙 B) ^ n : B ⟶ B).left := GlobalTheory.MulFiniteAny.isFinite_mulA k B hB n hn
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k B hB _ hm hf).2
  obtain ⟨x, hx⟩ := exists_lift_point ((𝟙 B) ^ n : B ⟶ B) y
  exact ⟨x, by rw [← hx, MonObj.comp_pow, Category.comp_id]⟩

end GlobalTheory.SS.SemiDivisible

open GlobalTheory.SS.SemiDivisible in

theorem GlobalTheory.SS.torusExtension_points_divisible : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ (n : ℕ), 1 ≤ n → ∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ n = y := by
  rintro k _ _ G _ _ ⟨E⟩ n hn
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  refine pow_surj_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k))))
    (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) (fun b => exists_lift_point E.q b) ?_ n ?_
    (pow_surj_abelian k E.B E.isAbelian hn)
  · intro x hx
    have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · intro t
    let e := GlobalTheory.splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
    obtain ⟨s, hs⟩ := pow_surj_chars E.X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ n
      (pow_surj_units k hn) (e t)
    exact ⟨e.symm s, e.injective (by rw [map_pow, e.apply_symm_apply, hs])⟩
