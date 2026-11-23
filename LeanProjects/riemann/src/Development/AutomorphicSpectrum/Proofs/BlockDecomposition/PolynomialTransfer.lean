import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.PolyTfCon

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

section Thickening

variable (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hT : TF l s T)

include hT in

theorem tr_facts : fil (trD T s) s = ⊥ ∧
    (∀ (r : ℕ) (x : trB T s), (l : trB T s) * x ∈ fil (trD T s) r → x ∈ fil (trD T s) r) ∧
    IsNilpotent (trJ T s) :=
  GlobalTheory.CompanionTheory.SiteTr.tr_tf T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2

abbrev pT : Thick (nlFun γ 0 X q κ) :=
  polyTr T s ⟨fun h => absurd rfl h, fun _ => (tr_facts T hT).2.2⟩

abbrev jT : T ⟶ pT T hT := homOf _ _ _ _ _ _ _

theorem pT_tf : TF l s (pT T hT) := ⟨(tr_facts T hT).1, (tr_facts T hT).2.1⟩

abbrev xT : trB T s := Ideal.Quotient.mk (trI T s) ((pq T.B).e 1)

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem xT_mem : xT (s := s) T ∈ trJ T s := Ideal.mem_map_of_mem _ (e_mem _ _)

theorem sum_eq (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.dpow_comp _ (e_mem _ _)]
  rfl

theorem toNat_sub (r : ℤ) (k : ℕ) : (r - k).toNat = r.toNat - k := by omega

theorem fil_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈ fil (trD T s) r.toNat ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) 0).1

theorem std_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) (c : R) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈
        fil (trD T s) r.toNat ⊔ Ideal.span {Ideal.Quotient.mk (trI T s) (algebraMap T.B (pq T.B).P (T.i c))} ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat ⊔ Ideal.span {T.i c} := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) (T.i c)).2

theorem univ_tr {T' : Thick (nlFun γ 0 X q κ)} (hT' : T'.pdPow s = ⊥) (φ : T ⟶ T') (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : pT T hT ⟶ T', jT T hT ≫ ψ = φ ∧ ψ.φ (xT (s := s) T) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hk : trI T s ≤ RingHom.ker F := by
    intro z hz
    have h1 : F z ∈ fil T'.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hF3 _ (Ideal.mem_map_of_mem F hz)
    have h2 : fil T'.δ (max s 1) ≤ fil T'.δ s := GlobalTheory.Cris.ExpBij.dpFil_anti T'.δ (le_max_left _ _)
    have h3 : F z ∈ T'.pdPow s := h2 h1
    rw [hT'] at h3
    exact h3
  let g : trB T s →+* T'.B := Ideal.Quotient.lift (trI T s) F fun a ha => hk ha
  have hgF : g.comp (Ideal.Quotient.mk (trI T s)) = F := by
    refine RingHom.ext fun z => ?_
    exact Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha
  have hg : g.comp (trF T s) = φ.φ := by
    rw [← RingHom.comp_assoc, hgF, hF1]
  have hdp : IsDPMorphism (trD T s) T'.δ g := (trD_spec T s).2 _ _ _ g (by rw [hgF]; exact hF3)
  have hle : trJ T s ≤ T'.J.comap g := Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf φ g hg hdp hle, ⟨hom_ext hg, (Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha).trans hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = g
  have e := hFu (ψ.φ.comp (Ideal.Quotient.mk (trI T s))) ⟨?_, h2, ?_⟩
  · refine Ideal.Quotient.ringHom_ext ?_
    rw [e, hgF]
  · have := congrArg Thick.Hom.φ h1
    exact this
  · exact IsDPMorphism.comp _ ψ.dp (trD_spec T s).1

end Thickening

section Site

variable (l s : ℕ) (𝒱 : Set X.Opens)

abbrev Qc : ObjectProperty (Thick (nlFun γ 0 X q κ)) := St (TF l s) 𝒱

variable {l s 𝒱}

theorem pT_mem (T : (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱).FullSubcategory) : Qc l s 𝒱 (pT T.obj T.property.1) := by
  obtain ⟨V, hV, h⟩ := T.property.2
  exact ⟨pT_tf _ _, V, hV, inU_hom (jT T.obj T.property.1) h⟩

variable (l s 𝒱)

def polyQ : Poly (sP (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱)) where
  P T := ⟨pT T.obj T.property.1, pT_mem T⟩
  j T := ObjectProperty.homMk (jT T.obj T.property.1)
  X T := xT (s := s) T.obj
  X_mem T := xT_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_tr T.obj T.property.1 T'.property.1.1 φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (show trB T.obj s from z)
    obtain ⟨b, rfl⟩ := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ w
    exact ⟨b, (sum_eq T.obj b).symm⟩

theorem crit_fil (r : ℤ) (hr : r ≤ s) : (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (sFil _) r :=
  fun T b => fil_coeff T.obj b r hr

theorem crit_std (r : ℤ) (hr : r ≤ s) (c : R) :
    (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (fun r => stdI _ (some r) c) r :=
  fun T b => std_coeff T.obj b r hr c

end Site

theorem polyTf : KH.PolyTf := by
  intro O R _ _ I γ X q κ l s 𝒱
  exact ⟨polyQ l s 𝒱, fun r hr => ⟨crit_fil l s 𝒱 r hr, crit_std l s 𝒱 r hr⟩⟩

end GlobalTheory.CompanionTheory.PolyTfCon
