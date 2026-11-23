import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSectionExtendsNonzeroOfIntegralThetaConstanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtFrac

theorem thList_pull_of_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {m N : ℕ} {K K' : Type} [Field K] [Field K']
    (i : K →+* K') {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') {θ : SecAt G L x}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x θ pt c) :
    ∃ pt' : Fin N → (Over.mk x' ⟶ G),
      ThList G L ρ m x' (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) θ) pt'
        (fun a => i (c a)) := by
  subst h
  obtain ⟨pt', -, H'⟩ := ThPull.thList_pull S G L ρ hL hρ m N K K' i x θ pt c H
  exact ⟨pt', H'⟩

theorem ext_any_frac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R K) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R K) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R K (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R K)) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ K _ _ _ χ θ pt c hm h3 hu hP hT hc
  let φ : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let i : K →+* FractionRing R := φ.symm.toRingEquiv.toRingHom
  let j : FractionRing R →+* K := φ.toRingEquiv.toRingHom
  have hi : ∀ r, i (algebraMap R K r) = algebraMap R (FractionRing R) r := fun r => φ.symm.commutes r
  have hi' : i.comp (algebraMap R K) = algebraMap R (FractionRing R) := RingHom.ext hi
  have hj' : j.comp (algebraMap R (FractionRing R)) = algebraMap R K := RingHom.ext fun r => φ.commutes r
  have hji : j.comp i = RingHom.id K := RingHom.ext fun r => φ.apply_symm_apply r
  have e₁ : spMap i ≫ spMap (algebraMap R K) ≫ χ = spMap (algebraMap R (FractionRing R)) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hi']
  have e₂ : spMap j ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap R K) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have hp : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  have hLL : LBIso t.PP.L (t.PP.L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl t.PP.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  have hP' := (FibMove.polFib_move S S t.G t.PP.L t.G t.PP.L (𝟙 _) (𝟙 _) t.PP.isLB t.PP.isLB hp hLL g K _).2 _ i hP
  rw [e₁] at hP'
  obtain ⟨pt', hT'⟩ := thList_pull_of_eq t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen i e₁ hT
  simp only [hi] at hT'
  obtain ⟨σ, hσ, hz⟩ := GlobalTheory.T.fibreSection_extends_nonzero_of_integral_thetaConstants E H S t g m N R χ _ pt' c hm h3 hu hP' hT' hc
  refine ⟨σ, ?_, hz⟩
  let β : Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    Over.homMk (spMap j) e₂
  have q := congrArg (VVRank.pullM t.G t.PP.L _ β) hσ
  have a₁ : β ≫ (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) = Over.homMk (spMap (algebraMap R K)) rfl := by
    ext
    change spMap j ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R K)
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have a₂ : β ≫ (Over.homMk (spMap i) e₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶
      Over.mk (spMap (algebraMap R K) ≫ χ)) = 𝟙 _ := by
    ext
    change spMap j ≫ spMap i = 𝟙 _
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hji]
    exact Spec.map_id _
  have b₁ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) (SecM.ofSec t.G σ)
  have b₂ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap i) e₁ :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk (spMap (algebraMap R K) ≫ χ)) (SecM.ofSec t.G θ)
  rw [a₁] at b₁
  rw [a₂, VVRank.pullM_id t.G t.PP.isLB] at b₂
  exact b₁.symm.trans (q.trans b₂)

end GlobalTheory.UMin.ExtFrac
