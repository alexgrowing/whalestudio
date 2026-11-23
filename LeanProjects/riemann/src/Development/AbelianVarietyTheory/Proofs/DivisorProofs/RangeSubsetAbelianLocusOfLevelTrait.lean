import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegTh

def isPowGrpOfUniv {T : Scheme.{0}} {P C : Over T} [GrpObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C))
    (hpr : ∀ a, IsMonHom (pr a)) (hu : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ P, ∀ a, x ≫ pr a = y a) :
    IsPowGrp P C 8 where
  pr := pr
  hom := hpr
  lim := Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s a => (hu s.pt s.proj).choose_spec.1 a)
    (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)

theorem range_subset_abLocus_of_levelTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
    SysAt F W β S ρ u → ∀ (Y M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (Zh : ZHOut ρ M U₀ EE), LevAt F β u Y q → S.Over₀ M U₀ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z)
      (κ : Ω →+* FractionRing V), spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt →
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt → Set.range ξ ⊆ abLocus Zh.G := by
  intro g n F W o Ω _ _ _ _ β S ρ u hSys Y M q U₀ EE Zh hLev hO V _ _ _ ξ τ κ hξ hτ
  obtain ⟨c, hc, pr, hpr, hu, -⟩ := hSys.2.2.2.1
  obtain ⟨ψ, -, hψ, -⟩ := hc
  obtain ⟨α, hα, -⟩ := PowFibre.exists_pow_pullback (powIsPowGrp F.univ.A 8) (isPowGrpOfUniv pr hpr hu) hψ
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x' : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx' : x' ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x' ≫ Zh.u₀ = spMap S.R.val.toRingHom := Zh.u₀_gen x' hx'
  let a : Sp (FractionRing V) ⟶ U₀.toScheme := spMap κ ≫ x'
  have ha1 : a ≫ U₀.ι = spMap (algebraMap V (FractionRing V)) ≫ ξ := by
    rw [hξ, Category.assoc, hx']
  have ha2 : a ≫ (Zh.u₀ ≫ u) = spMap (algebraMap V (FractionRing V)) ≫ (τ ≫ q) := by
    calc a ≫ (Zh.u₀ ≫ u) = spMap κ ≫ ((x' ≫ Zh.u₀) ≫ u) := by simp only [a, Category.assoc]
      _ = spMap κ ≫ (Y.pt ≫ q) := by rw [hxu, hLev.2.2.2.2]
      _ = _ := by rw [← Category.assoc, ← hτ, Category.assoc]
  have hA := isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) a
  have h₂ := (hA.comp Zh.cart).congr ha1 rfl
  have h₃ := (hA.comp ((isGrpPullback_pullback ρ.P.A Zh.u₀).comp hα)).congr ha2 rfl
  obtain ⟨φ₁, h₁⟩ := GoodVal.exists_isGrpPullback_of_comp (powObj F.univ.A 8) (τ ≫ q) _ h₃
  have hab : IsAbelianScheme ((Over.pullback (τ ≫ q)).obj (powObj F.univ.A 8)) :=
    isAbelianScheme_pullback_obj (τ ≫ q) _ (AbelianSchemeGerms.isAbelianScheme_powObj F.univ.A F.univ.ab 7)
  have hz : LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
    have := M.lft
    haveI := ArithBase.ft (o := o) (Ω := Ω)
    have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    infer_instance
  exact range_subset_abLocus_of_goodReduction
    (existsUnique_hom_extension_semiAbelian_dvr (AbelianSubgroupFinite.finite_of_no_torsion abMulN_holds))
    M.Z _ Zh.G V (FractionRing V) ξ _ _ _ _ hz Zh.semi hab h₁ h₂

end GlobalTheory.SiegTh

end
