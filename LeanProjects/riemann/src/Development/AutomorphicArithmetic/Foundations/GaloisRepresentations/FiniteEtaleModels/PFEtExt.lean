import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem card_of_pb {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y)
    (x : Spec (CommRingCat.of K) ⟶ Y) (B : Type) [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (f : Spec (CommRingCat.of B) ⟶ Y')
    (h : IsPullback f (Spec.map (CommRingCat.ofHom (algebraMap K B))) s x) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Module.finrank K B := by
  have hcomp : ∀ g : B →ₐ[K] K, Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := by
    intro g
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (g : B →+* K).comp (algebraMap K B) = RingHom.id K := by
      ext z; simp
    rw [this]
    exact Spec.map_id _
  let F : (B →ₐ[K] K) → {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} := fun g =>
    ⟨Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f, by
      rw [Category.assoc, h.w, ← Category.assoc, hcomp, Category.id_comp]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro g g' e
      have e1 : Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = Spec.map (CommRingCat.ofHom (g' : B →+* K)) ≫ f :=
        congrArg Subtype.val e
      have e2 : Spec.map (CommRingCat.ofHom (g : B →+* K)) = Spec.map (CommRingCat.ofHom (g' : B →+* K)) :=
        h.hom_ext e1 ((hcomp g).trans (hcomp g').symm)
      have e3 := Spec.map_injective e2
      have e4 : (g : B →+* K) = (g' : B →+* K) := by
        simpa using congrArg CommRingCat.Hom.hom e3
      exact AlgHom.coe_ringHom_injective e4
    · rintro ⟨y, hy⟩
      let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) := h.lift y (𝟙 _) (by rw [hy, Category.id_comp])
      have ht1 : t ≫ f = y := h.lift_fst _ _ _
      have ht2 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := h.lift_snd _ _ _
      let g0 : CommRingCat.of B ⟶ CommRingCat.of K := Spec.preimage t
      have hg0 : Spec.map g0 = t := Spec.map_preimage t
      have hc : CommRingCat.ofHom (algebraMap K B) ≫ g0 = 𝟙 _ := by
        apply Spec.map_injective
        rw [Spec.map_comp, hg0, ht2, Spec.map_id]
      let g : B →ₐ[K] K := { g0.hom with
        commutes' := fun r => by
          have := congrArg (fun u => u.hom r) hc
          simpa using this }
      have hgg : CommRingCat.ofHom (g : B →+* K) = g0 := by
        ext z; rfl
      refine ⟨g, Subtype.ext ?_⟩
      change Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = y
      rw [hgg, hg0, ht1]
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  obtain ⟨hfin, hsp⟩ := UpperTheory.Gal.crystallineComparison.splitsField_of K B K inferInstance
  haveI := Fintype.ofFinite (B →ₐ[K] K)
  let e : (TensorProduct K K B) ≃ₗ[K] ((B →ₐ[K] K) → K) :=
    LinearEquiv.ofBijective (UpperTheory.Gal.crystallineComparison.splitMap (fun z : B →ₐ[K] K => z)).toLinearMap hsp
  have e1 := e.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, (TensorProduct.lid K B).finrank_eq] at e1
  exact e1.symm

private theorem card_lifts {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) [IsFinite s] [Etale s]
    (x : Spec (CommRingCat.of K) ⟶ Y) (z : Spec (CommRingCat.of K)) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Scheme.Hom.finrank s (x z) := by
  haveI : Etale (pullback.snd s x) := inferInstance
  haveI : IsAffine (pullback s x) := isAffine_of_isAffineHom (pullback.snd s x)
  let e := (pullback s x).isoSpec
  let φ : CommRingCat.of K ⟶ Γ(pullback s x, ⊤) := Spec.preimage (e.inv ≫ pullback.snd s x)
  have hφ : Spec.map φ = e.inv ≫ pullback.snd s x := Spec.map_preimage _
  have hfinφ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hetφ : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Algebra K Γ(pullback s x, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback s x, ⊤) := ((IsFinite.SpecMap_iff φ).mp hfinφ : φ.hom.Finite)
  haveI : Algebra.Etale K Γ(pullback s x, ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hetφ : φ.hom.Etale)
  have hpb : IsPullback (e.inv ≫ pullback.fst s x) (Spec.map φ) s x := by
    rw [hφ]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm (by simp) (by simp)
  rw [card_of_pb s x Γ(pullback s x, ⊤) _ hpb]
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb z
  rw [← h1]
  have h2 := Scheme.Hom.finrank_SpecMap_algebraMap K Γ(pullback s x, ⊤) z
  rw [Module.rankAtStalk_eq_finrank_of_free] at h2
  exact h2.symm

theorem UpperTheory.Gal.FiniteEtaleModels.fEtExt_holds :
    FEtExt := by
  intro O E _ _ _ _ _ Y Y' pY s d hfl hfin het hd
  have key : ∀ y₀ : Y, Scheme.Hom.finrank s y₀ = d := by
    intro y₀
    have hg := Flat.generalizingMap pY
    have hsp : (⊥ : PrimeSpectrum O) ⤳ pY y₀ := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    obtain ⟨y₁, h1, h2⟩ := hg hsp
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point Y y₁
    let pt : Spec (CommRingCat.of k) := (⊥ : PrimeSpectrum k)
    have ha1 : a pt = y₁ := by
      have : a pt ∈ Set.range a := ⟨pt, rfl⟩
      rw [ha] at this
      exact this
    let f : CommRingCat.of O ⟶ CommRingCat.of k := Spec.preimage (a ≫ pY)
    have hf : Spec.map f = a ≫ pY := Spec.map_preimage _
    have hpt : (Spec.map f) pt = (⊥ : PrimeSpectrum O) := by
      rw [hf, Scheme.Hom.comp_apply, ha1, h2]
    have hinj : Function.Injective f.hom := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      have h3 : r ∈ (PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k)).asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using hr
      have h4 : PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k) = (⊥ : PrimeSpectrum O) := hpt
      rw [h4] at h3
      simpa using h3
    let g : E →+* k := IsFractionRing.lift hinj
    let σ : sp k ⟶ sp E := Spec.map (CommRingCat.ofHom g)
    have hσ : a ≫ pY = σ ≫ gen O E := by
      rw [← hf, gen, ← Spec.map_comp]
      congr 1
      ext z
      simp [g]
    have h3 := hd k a σ hσ
    rw [card_lifts s a pt, ha1] at h3
    have h5 := h1.map (Scheme.Hom.isLocallyConstant_finrank s).continuous
    rw [← h3]
    exact (specializes_iff_eq.mp h5).symm
  refine ⟨hfin, het, fun K _ _ x => ?_⟩
  rw [card_lifts s x (⊥ : PrimeSpectrum K), key]
