import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumModuliFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuativeLiftGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegelMapProper

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isQProjOver_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'} {X T : Scheme.{0}}
    {s : X ⟶ Sp R} {sT : T ⟶ Sp R'} {f : T ⟶ X} (h : IsPullback f sT s (spMap j)) (hs : IsQProjOver s) :
    IsQProjOver sT := by
  obtain ⟨N, i, h1, h2, h3⟩ := (GlobalTheory.isQProjOver_baseChange_and_finite_restrict R R' j X s).1 hs
  refine ⟨N, h.isoPullback.hom ≫ i, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, h3, h.isoPullback_hom_snd]

theorem injective_of_generic {O K : Type} [CommRing O] [IsDomain O] [Field K] {T : Scheme.{0}} (sT : T ⟶ Sp O)
    [Flat sT] (x : Sp K ⟶ T) (hx : Set.range x ⊆ genericPoints T) (δ : O →+* K) (h : x ≫ sT = spMap δ) :
    Function.Injective δ := by
  let pt : Sp K := (⊥ : PrimeSpectrum K)
  have hs : x pt ∈ genericPoints T := hx ⟨pt, rfl⟩
  obtain ⟨s', hs', e⟩ := Flat.generalizingMap sT (genericPoint_specializes (sT (x pt)))
  have h1 : closure {x pt} ⊆ closure ({s'} : Set T) := specializes_iff_closure_subset.mp hs'
  have h2 := hs.2 isIrreducible_singleton.closure h1
  have h3 : sT (x pt) = genericPoint (Sp O) := by
    rw [← e, (hs'.antisymm (specializes_iff_closure_subset.mpr h2)).eq]
  rw [← Scheme.Hom.comp_apply, h, genericPoint_eq_bot_of_affine] at h3
  rw [RingHom.injective_iff_ker_eq_bot]
  exact congrArg PrimeSpectrum.asIdeal h3

theorem isProper_toSiegel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → IsNoetherianRing O → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → IsProper u := by
  intro L1 L2 L3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl k o _ b em ρ _ _ hk hρ _ har X s t τ hrep hpel
    p Ag _ _ hS bas' hbas' O _ i z bb hi _ hbb hO T sT f hT tT c u htT hc hu hcu
  have : IsDomain O := hi.isDomain i
  have : CharZero O := i.charZero
  have hbbi : Function.Injective bb := fun x y e => har.2.2 (by rw [← hbb x, ← hbb y, e])
  have := hrep.flat
  have : Flat sT := MorphismProperty.of_isPullback (P := @Flat) hT inferInstance
  have := hS.1
  have := Ag.smooth
  have : Smooth Ag.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) Ag.s
  refine GlobalTheory.T.valuative_lift_generic_point O T _ u (pullback.snd Ag.s (spMap z)) (hu ▸ isQProjOver_of_isPullback hT hrep.qproj)
    inferInstance inferInstance ?_
  intro V K _ _ _ _ _ _ x y hx hxy
  obtain ⟨δ', hδ⟩ := Spec.map_surjective (y ≫ pullback.snd Ag.s (spMap z))
  obtain ⟨δ, rfl⟩ : ∃ δ : O →+* V, CommRingCat.ofHom δ = δ' := ⟨δ'.hom, rfl⟩
  change spMap δ = _ at hδ
  have hxs : x ≫ sT = spMap (algebraMap V K) ≫ spMap δ := by
    rw [← hu, ← Category.assoc, hxy, Category.assoc, hδ]
  have hinj : Function.Injective ((algebraMap V K).comp δ) :=
    injective_of_generic sT x hx _ (by rw [hxs, spMap_comp_spMap])
  have : CharZero K := charZero_of_injective_ringHom hinj
  have hδi : Function.Injective δ := Function.Injective.of_comp (f := algebraMap V K) hinj
  have hxf : (x ≫ f) ≫ s = spMap (algebraMap V K) ≫ spMap (δ.comp bb) := by
    rw [Category.assoc, hT.w, ← Category.assoc, hxs, Category.assoc, spMap_comp_spMap]
  have hid : spMap (RingHom.id (ZP p k)) = 𝟙 _ := Spec.map_id _

  have hV := GlobalTheory.T.siegelPre_pullback_principal_ringChange g k _ _ (zetaZP p k) (zetaZP p k) (RingHom.id _) _ _ Ag.s
    ((y ≫ pullback.fst _ _) ≫ Ag.s) (y ≫ pullback.fst Ag.s (spMap z)) rfl (by rw [hid, Category.comp_id])
  obtain ⟨cV, hcV⟩ := hV.1 Ag.univ
  have hpr : cV.Principal := hV.2.1 _ _ hcV Ag.princ

  obtain ⟨cK, hcK⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange g k _ _ (zetaZP p k) (zetaZP p k) (RingHom.id _) _ _ (sT ≫ spMap z)
    (x ≫ sT ≫ spMap z) x rfl (by rw [hid, Category.comp_id])).1 c
  obtain ⟨tK, htK⟩ := GlobalTheory.tObj_pull o g k J b _ _ (sT ≫ spMap bb) ((x ≫ f) ≫ s) x tT
    (by rw [Category.assoc, hT.w])
  have htKf : TMap tK t (x ≫ f) := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t tT tK).2 f x htT).1 htK
  obtain ⟨τK, hτK⟩ := GlobalTheory.exists_isPEL_of_tmap E H D g J a bas k o b ρ _ _ _ _ t tK τ (x ≫ f) rfl htKf hpel
  have hsK : TSieg bas bas' tK cK :=
    (GlobalTheory.T.siegel_structure_pullback g k J _ bas bas' o _ b _ _ _ _ _ _ _ tT c tK cK x hc htK).1 hcK
  have hcKV : SiegPB cK cV (spMap (algebraMap V K)) := by
    refine ((GlobalTheory.SiegelPullComp.id_comp_cancel g k _ _ _ _ _ _ _ _ _ _ _ _ Ag.univ cV cK _ _).2 hcV).2 ?_
    rw [← Category.assoc (spMap (algebraMap V K)), ← hxy, Category.assoc x u]
    exact ((GlobalTheory.SiegelPullComp.id_comp_cancel g k _ _ _ _ _ _ _ _ _ _ _ _ Ag.univ c cK _ _).2 hcu).1 hcK
  obtain ⟨tV, τV, hτV, htV⟩ := GlobalTheory.T.symplectic_datum_moduli_family L1 L2 L3 E H D g J a w w' bas hpq hbas hw hw' hcl bas' hbas' k o _ b em ρ _
    V K (δ.comp bb) _ _ _ cV cK tK τK hk hρ har hxf hpr hcKV hsK hτK
  obtain ⟨fV, hfV, hmV⟩ := hrep.rep V (δ.comp bb) tV τV (hδi.comp hbbi) hτV
  have he : spMap (algebraMap V K) ≫ fV = x ≫ f :=
    hrep.inj K _ _ _ tK (by rw [hxf, Category.assoc, hfV])
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t tV tK).2 fV _ hmV).1 htV) htKf
  refine ⟨hT.lift fV (spMap δ) (by rw [hfV, spMap_comp_spMap]), hT.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hT.lift_fst, he]
  · rw [Category.assoc, hT.lift_snd, hxs]

end GlobalTheory.SiegelMapProper
