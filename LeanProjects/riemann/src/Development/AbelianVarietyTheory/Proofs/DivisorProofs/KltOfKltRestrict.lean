import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModelStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.FieldPair.klt_of_klt_restrict : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  classical
  intro hP L K _ _ cL cK n T hT ψ f w θ hic hconst hker hf0 hRng hTr hsupp hEff hKlt
  obtain ⟨S, hS, ψS, hsurj, hcK, hcomp, hirr⟩ :=
    GlobalTheory.T.exists_dvrPlace_of_prime_element_of_normal_localModel cL cK n T hT ψ f hic hconst hker hf0 hRng

  let ι : T → S.ring := fun t => ⟨t, hS.1 t t.2⟩
  have hw : (fun i => ψS (ι (w i))) = fun i => ψ (w i) := funext fun i => hcomp (w i)
  have hTr' : TrBasis cK (fun i => ψS (ι (w i))) := by rw [hw]; exact hTr
  obtain ⟨hTrL, hform, hord, hord0⟩ :=
    GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts cL cK n S ψS (ι f) (fun i => ι (w i)) hsurj hcK hirr hTr'
  have hmapS : Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ) = Finsupp.mapDomain ψ θ := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext t
    exact hcomp t
  have hmapL : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.mapDomain ι θ) =
      Finsupp.mapDomain (fun g : T => (g : L)) θ := by
    rw [← Finsupp.mapDomain_comp]
    rfl
  have hsuppS : ∀ g ∈ (Finsupp.mapDomain ι θ).support, ψS g ≠ 0 := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    intro h
    exact hsupp t ht ((hcomp t).symm.trans h)
  have hrange : ∀ a ∈ ψ.range, ∃ t : T, ψS ⟨t, hS.1 t t.2⟩ = a := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, hcomp t⟩
  have hKlt' : Klt cK n ψ.range (dForm cK (fun i => ψS (ι (w i))))
      (Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ)) := by
    rw [hw, hmapS]
    exact hKlt
  have hadj := GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring cL cK n T S hS.1 ψS (ι f) (fun i => ι (w i))
    (Finsupp.mapDomain ι θ) ψ.range hsurj hcK hirr hTr' hsuppS hrange hKlt'
  have hadj' : AdjKlt cL (n + 1) T S
      (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ + Finsupp.single (f : L) 1) := by
    rw [← hmapL]
    exact hadj
  have hTrL' : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := hTrL
  have hform' : S.formOrd (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 :=
    hform
  have hord' : S.ord (f : L) = 1 := hord
  have hfL : (f : L) ≠ 0 := fun h => hf0 (Subtype.ext h)

  have hq : S.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun t ht => ?_
    have h0 : S.ord (t : L) = 0 :=
      hord0 (ι t) (fun h => hsupp t ht ((hcomp t).symm.trans h))
    simp [Function.comp, h0]
  have hdisc : S.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.disc, hform', hq]
    simp
  exact GlobalTheory.T.klt_of_adjunctionKlt_localModel hP cL (n + 1) T _ _ (f : L) S hT hic hTrL' f.2 hfL hS hord' hdisc hEff hadj'
