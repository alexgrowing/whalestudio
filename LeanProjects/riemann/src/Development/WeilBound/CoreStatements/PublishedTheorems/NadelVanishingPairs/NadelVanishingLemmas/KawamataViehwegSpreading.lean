import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChangeStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegModPSquared
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingSpecializes
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncBaseChange
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToModPSquared

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem vanishing_charZero_fibre_of_finiteType : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  intro R k _ _ _ φ X X' f f' π d _ _ hR hφ hpb s L σ h K M A hM hA r b hAmp hr hb hrel q hq
  haveI : IsDomain R := Function.Injective.isDomain φ hφ
  haveI : CharZero R := (RingHom.charZero_iff hφ).mpr inferInstance
  haveI := hR
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI hstab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Flat f := inferInstance
  let KR := FractionRing R
  let ι : KR →+* k := IsFractionRing.lift hφ
  have hφι : φ = ι.comp (algebraMap R KR) := by
    ext x
    simp [ι, IsFractionRing.lift_algebraMap]
  have hsp : spMap φ = spMap ι ≫ spMap (algebraMap R KR) := by
    rw [hφι]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have hAπ : (A.pull π).IsLB := LB.isLB_pull hA π
  have hrelK' : Out.RelAmple (Over.mk f') (A.pull π) :=
    haveI : IsProper (Over.mk f').hom := (inferInstance : IsProper f')
    (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f') hAπ).mpr hAmp
  have hgenPb := IsPullback.of_hasPullback f (spMap (algebraMap R KR))
  have hA1 : (A.pull (pullback.fst f (spMap (algebraMap R KR)))).IsLB := LB.isLB_pull hA _
  have hgen : Out.RelAmple (Over.mk (pullback.snd f (spMap (algebraMap R KR))))
      (A.pull (pullback.fst f (spMap (algebraMap R KR)))) :=
    FibreAmple.relAmple_of_fieldExtension hA ι hgenPb (hsp ▸ hpb) hA1 ((cls_eq_iff hA1 hA1).mp rfl) hrelK'
  obtain ⟨a, ha, hspread⟩ := AmpleSpread.relAmple_spread R KR (Over.mk f) A ‹IsProper f› hA hgen
  obtain ⟨p, hp, hdp, χ, hχ⟩ := exists_ringHom_zmod_prime_sq_isUnit_of_finiteType R hR a ha d
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hY := IsPullback.of_hasPullback f (spMap χ)
  haveI : SmoothOfRelativeDimension d (pullback.snd f (spMap χ)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hY inferInstance
  have h1 := IsPullback.of_hasPullback (pullback.snd f (spMap χ)) (spMap c)
  haveI : SmoothOfRelativeDimension d (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h1 inferInstance
  haveI : IsProper (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) := inferInstance
  have hsp2 : spMap c ≫ spMap χ = spMap (c.comp χ) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hρ : IsPullback (pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ))
      (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) f (spMap (c.comp χ)) :=
    hsp2 ▸ h1.paste_horiz hY
  set ρ := pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ) with hρdef
  set f₁ := pullback.snd (pullback.snd f (spMap χ)) (spMap c) with hf₁
  have hspec := hspread (ZMod p) (c.comp χ) (hχ.map c)
  have hid : spMap (RingHom.id (ZMod p)) ≫ spMap (c.comp χ) = spMap (c.comp χ) := by
    simp [spMap]
  have hAρ : (A.pull ρ).IsLB := LB.isLB_pull hA ρ
  have hamp1 : Out.RelAmple (Over.mk f₁) (A.pull ρ) :=
    FibreAmple.relAmple_of_fieldExtension hA (RingHom.id (ZMod p)) hρ
      (hid.symm ▸ IsPullback.of_hasPullback f (spMap (c.comp χ))) hAρ ((cls_eq_iff hAρ hAρ).mp rfl) hspec
  haveI : IsProper (Over.mk f₁).hom := (inferInstance : IsProper f₁)
  have hampX : IsAmpleLB (A.pull ρ) := (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hAρ).mp hamp1
  have hproj : IsProjOver f₁ := (isProjOver_iff_isProper_and_exists_isAmpleLB f₁).mpr ⟨inferInstance, _, hampX⟩
  have hL := LogPair.relSnc_baseChange R (ZMod (p ^ 2)) χ X _ f _ _ d s L σ hY h
  let K₁ : CanonLB f₁ d := CanonLB.baseChange hρ K
  have hMρ : (M.pull ρ).IsLB := LB.isLB_pull hM ρ
  have hrel1 : r • cls (M.pull ρ) hMρ = r • cls K₁.bundle K₁.isLB +
      ∑ i, b i • pull (pullback.fst (pullback.snd f (spMap χ)) (spMap c))
        (cls ((L i).pull (pullback.fst f (spMap χ))) (LB.isLB_pull (h.isLB i) _)) + cls (A.pull ρ) hAρ := by
    have e := congrArg (pull ρ) hrel
    simp only [map_add, map_nsmul, map_sum] at e
    have eK : cls K₁.bundle K₁.isLB = pull ρ (cls K.bundle K.isLB) := cls_pull K.isLB ρ K₁.isLB
    rw [cls_pull hM ρ, eK, cls_pull hA ρ]
    convert e using 4
    rw [cls_pull (h.isLB _) _, ← pull_comp]
  have hvan := charp_vanishing_liftable p _ _ (pullback.snd f (spMap χ)) f₁
    (pullback.fst (pullback.snd f (spMap χ)) (spMap c)) d h1 hproj hdp s
    (fun i => (L i).pull (pullback.fst f (spMap χ))) (fun i => Cartier.secPull (σ i) _) hL K₁
    (M.pull ρ) (A.pull ρ) hMρ hampX r b hr hb hrel1 q hq
  have hker : RingHom.ker φ ≤ RingHom.ker (c.comp χ) := by
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact SemicontLB.subsingleton_coh_pull_of_ker_le R X f M hM (ZMod p) k (c.comp χ) φ _ X' f₁ f' ρ π hρ hpb hker q hvan

end GlobalTheory
