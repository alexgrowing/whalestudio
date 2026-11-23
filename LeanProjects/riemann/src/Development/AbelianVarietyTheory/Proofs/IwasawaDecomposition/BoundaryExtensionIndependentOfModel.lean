import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEigBasisPull
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  [Algebra c.F K]

theorem exists_genPt (Z : Model Xo c β) (φ : c.F →+* V) (hφ : (algebraMap V K).comp φ = algebraMap c.F K)
    (y : FrPt Xo c K) : ∃ χ : Sp V ⟶ gen Z, χ ≫ genStr Z = spMap φ ∧ GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap φ) (GlobalTheory.AllWt.ptF y ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp, hφ]
    exact pullback.lift_snd _ _ _)
  exact ⟨χ, h2, h1.symm⟩

theorem exists_genIdent (Z : Model Xo c β) {χ : Sp V ⟶ gen Z} {y : FrPt Xo c K}
    (hχ : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)) {t : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap V K))) (mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) (GlobalTheory.AllWt.ptF y)
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) (GlobalTheory.AllWt.ptF y) Z.m mF
  have hj : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap V K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F}

theorem mem_genBd_of_mem_genBd {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'}
    {t t' : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) (m' : SABMap t' Z'.t (χ' ≫ genι Z'))
    (ψ : SABMap t t' (𝟙 (Sp V))) (p : Sp V) (h : χ' p ∈ genBd Z') : χ p ∈ genBd Z := by
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z.t.semi m.cart.1 p]
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z'.t.semi m'.cart.1 p] at h
  have e := abLocus_pullback abLocusOne t'.semi ψ.cart.1 p
  have e0 : (𝟙 (Sp V)) p = p := rfl
  rw [e0] at e
  exact fun hp => h (e.2 hp)

section Chain

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {x : Sp V ⟶ Z.X} {x' : Sp V ⟶ Z'.X} {t t' : SAB H (Sp V)}
  (m : SABMap t Z.t x) (m' : SABMap t' Z'.t x') (ψ : SABMap t t' (𝟙 (Sp V))) {φ : c.F →+* V}

theorem exists_isEigBasis_chain {τ : E →+* ℂ} {n : ℕ} {v' : Fin n → (Sp (DualNumber V) ⟶ Z'.t.G.left)}
    (h : IsEigBasis Z'.t φ x' τ v') : ∃ v : Fin n → (Sp (DualNumber V) ⟶ t.G.left),
      (∀ i, (v i ≫ ψ.φ) ≫ m'.φ = v' i) ∧ (∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) ∧
        IsEigBasis Z.t φ x τ (fun i => v i ≫ m.φ) := by
  have h1 : IsEigBasis Z'.t φ (𝟙 _ ≫ x') τ v' := by rwa [Category.id_comp]
  obtain ⟨v₁, hv₁, h₁⟩ := isEigBasis_pull m' h1
  have h2 : IsEigBasis t' φ (𝟙 _ ≫ 𝟙 _) τ v₁ := by rwa [Category.id_comp]
  obtain ⟨v₂, hv₂, h₂⟩ := isEigBasis_pull ψ h2
  refine ⟨v₂, fun i => by rw [hv₂, hv₁], fun i => by rw [(h₂.1 i).1, Category.comp_id], ?_⟩
  have := isEigBasis_push m h₂
  rwa [Category.id_comp] at this

end Chain

section Frame

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'} {y : FrPt Xo c K}
  {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)} {t t' : SAB H (Sp V)}
  {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Z'.t (χ' ≫ genι Z')} {ψ : SABMap t t' (𝟙 (Sp V))}
  {a : SABMap tK t (spMap (algebraMap V K))} {a' : SABMap tK t' (spMap (algebraMap V K))}
  {mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)} {mF' : SABMap tK Z'.oF.t (GlobalTheory.AllWt.ptF y)}

theorem exists_lift_frameVec (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Z'.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Z'.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber V) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    {u' : Sp (DualNumber K) ⟶ Xo.univ.t.G.left} (hu' : u' ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ y.x)
    {w' : Sp (DualNumber K) ⟶ Z'.oF.t.G.left}
    (hw1 : w' ≫ Z'.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y)
    (hw2 : w' ≫ Z'.m0.toSABMap.φ = u') (hw3 : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = u' ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ v ≫ m.φ := by
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  obtain ⟨u, hu1, hu2⟩ := exists_lift mK (spMap (algebraMap K (DualNumber K))) u' (by rw [hu', ← hx])
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) =
      spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp, PullbackSections.dualMap_comp_alg]
  have e1 : u ≫ mF'.φ = w' := by
    apply Z'.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hF0', hu2, hw2]
    · rw [Category.assoc, mF'.cart.1.w, ← Category.assoc, hu1, hw1]
  have e2 : u ≫ a.φ = spMap (dualMap (algebraMap V K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3]
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  refine ⟨u ≫ mF.φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  · rw [Category.assoc, hF0, hu2]
  · rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]

end Frame

theorem bdExt_of_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z O' _ β' Z' V K _ _ _ _ _ _ _ φ y hφ h
  obtain ⟨χ', g', e1', e2', hw', hb'⟩ := h
  obtain ⟨χ, e1, e2⟩ := exists_genPt Z φ hφ y
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ' ≫ genι Z') Z'.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_genIdent Z e2 mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_genIdent Z' e2' mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map V K t t' tK a a'
  choose v hv1 hv2 hv3 using fun τ => exists_isEigBasis_chain m m' ψ (EigFrame.isEigBasis g' τ)
  refine ⟨χ, eigFrameOf (fun τ i => v τ i ≫ m.φ) hv3, e1, e2, fun τ i => ?_,
    mem_genBd_of_mem_genBd m m' ψ _ hb'⟩
  obtain ⟨w', hw1, hw2, hw3⟩ := hw' τ i
  rw [← hv1 τ i] at hw3
  exact exists_lift_frameVec hψ hF0 hFm hF0' hFm' (hv2 τ i) (y.tan τ i).1 hw1 hw2 hw3

end GlobalTheory.CuspFrom
