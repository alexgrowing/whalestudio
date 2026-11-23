import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomainStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.PoincTop

theorem poinSt : PoinSt := by
  intro g hg n hn hodd F Z z i hth OZ hOZ hamp φ hφ
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ := hth
  obtain ⟨d, J, hd, hJ, hval⟩ :=
    GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification g hg n hn hodd F Z z i ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ φ hφ
  haveI := hoi
  let W : Z.Opens := i.opensRange
  have hWset : (W : Set Z) = Set.range i := by simp [W]
  obtain ⟨S, π, BD, hbl, hpS, hBD, hiso, hdS⟩ :=
    GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective n Z z hproj (GlobalTheory.IsNormalScheme.pred Z) J W (by rw [hWset]; exact hdense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : F.X ⟶ (π ⁻¹ᵁ W).toScheme := i.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : F.X ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = i := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range i := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  refine ⟨d, J, S, π, j, BD, hd, hJ, hval, hbl, hpS, inferInstance, ?_, hjπ, hrj.symm, hBD, ?_, ?_⟩
  · rw [hrj, ← hWset]; exact hdS
  · intro T ξ hξ
    obtain ⟨a, ha, hid⟩ := hval T (ξ ≫ π) (by rw [← Category.assoc, hξ, Category.assoc, hjπ])
    refine ⟨a, ha, ?_⟩
    rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]
    exact hid
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
    haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
    obtain ⟨T₀, hT⟩ := GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain (cycAway n) Z S₀ S z J π₀ ν BD hproj hb hfin
      (by rw [hνπ]; exact hBD) OZ hamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h

end GlobalTheory.PoincTop
