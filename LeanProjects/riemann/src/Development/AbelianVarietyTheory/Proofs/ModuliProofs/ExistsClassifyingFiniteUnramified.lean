import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevelExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegelClassify

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isReduced_pullback_localization {o O : Type} [CommRing o] [CommRing O] [Algebra o O] (M : Submonoid o)
    [IsLocalization M O] {X : Scheme.{0}} (s : X ⟶ Sp o) [IsReduced X] :
    IsReduced (pullback s (spMap (algebraMap o O))) := by
  have h1 : IsPreimmersion (spMap (algebraMap o O)) := IsPreimmersion.of_isLocalization M
  have h2 : Flat (spMap (algebraMap o O)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat O M)
  let π := pullback.fst s (spMap (algebraMap o O))
  have h3 : IsPreimmersion π := inferInstance
  have h4 : Flat π := inferInstance
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap o O))).presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (π.stalkMap x) := π.stalkMap_surjective x
    have hf := Flat.stalkMap π x
    have hi : Function.Injective (π.stalkMap x) := by
      algebraize [(π.stalkMap x).hom]
      have : IsLocalHom (algebraMap (X.presheaf.stalk (π x)) ((pullback s (spMap (algebraMap o O))).presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π x))
        (B := (pullback s (spMap (algebraMap o O))).presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (π x)) _
    exact isReduced_of_injective (RingEquiv.ofBijective (π.stalkMap x).hom ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk _

theorem dense_generic {B O : Type} [CommRing B] [CommRing O] [IsDomain O] (z : B →+* O) (hz : Function.Injective z)
    {T : Scheme.{0}} (sT : T ⟶ Sp O) [Flat sT] : Dense {x : T | ((sT ≫ spMap z) x).asIdeal = ⊥} := by
  intro x
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ sT x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap sT hη
  refine closure_mono (Set.singleton_subset_iff.2 ?_) hx'.mem_closure
  change ((sT ≫ spMap z) x').asIdeal = ⊥
  rw [Scheme.Hom.comp_apply, e]
  change Ideal.comap z ⊥ = ⊥
  exact Ideal.comap_bot_of_injective z hz

theorem exists_localization (p k : ℕ) (hp : p.Prime) {o : Type} [CommRing o] [IsNoetherianRing o] (em : o →+* ℂ)
    (hem : Function.Injective em) (ζ : o) (hζ : em ζ = zeta k) :
    ∃ (M : Submonoid o) (i₀ : Localization M →+* ℂ) (z₀ : ZP p k →+* Localization M), Function.Injective i₀ ∧
      GlobalTheory.Models.IsInc (ZP p k).subtype i₀ z₀ ∧ GlobalTheory.Models.IsInc em i₀ (algebraMap o _) ∧
      ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i →
        GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb →
        ∃ ga : Localization M →+* O, ga.comp (algebraMap o _) = bb ∧ ga.comp z₀ = z := by
  let M : Submonoid o :=
    { carrier := {x | ∃ n : ℕ, n.Coprime p ∧ x = n}
      one_mem' := ⟨1, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨n * m, Nat.Coprime.mul_left hn hm, by simp⟩ }
  have h0 : ∀ n : ℕ, n.Coprime p → (n : ℂ) ≠ 0 := fun n hn h => by
    have : n = 0 := by exact_mod_cast h
    subst this
    exact hp.one_lt.ne' (by simpa using hn)
  have hu : ∀ y : M, IsUnit (em y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using h0 n hn
  let i₀ : Localization M →+* ℂ := IsLocalization.lift hu
  have hi₀ : ∀ x, i₀ (algebraMap o _ x) = em x := IsLocalization.lift_eq hu
  have hinj : Function.Injective i₀ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    exact ⟨fun h => by rw [← hi₀, ← hi₀, h], fun h => by rw [hem h]⟩
  have hle : ZP p k ≤ i₀.range := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨algebraMap o _ ζ, (hi₀ ζ).trans hζ⟩
    · obtain ⟨v, hv⟩ := (IsLocalization.map_units (Localization M) (⟨n, n, hn, rfl⟩ : M)).exists_right_inv
      refine ⟨v, ?_⟩
      have := congrArg i₀ hv
      rw [map_mul, hi₀, map_one, map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
  let e : Localization M ≃+* i₀.range := RingEquiv.ofBijective i₀.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), i₀.rangeRestrict_surjective⟩
  let z₀ : ZP p k →+* Localization M := e.symm.toRingHom.comp (Subring.inclusion hle)
  have hz₀ : ∀ x, i₀ (z₀ x) = (ZP p k).subtype x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))
  refine ⟨M, i₀, z₀, hinj, hz₀, hi₀, fun O _ i z bb hi hz hb => ?_⟩
  have hv : ∀ y : M, IsUnit (bb y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine IsUnit.of_mul_eq_one (z ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨n, hn, rfl⟩)⟩) (hi ?_)
    rw [map_mul, hz, hb, map_one]
    simpa using mul_inv_cancel₀ (h0 n hn)
  have hga : i.comp (IsLocalization.lift (S := Localization M) hv) = i₀ :=
    IsLocalization.ringHom_ext M (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, IsLocalization.lift_eq]
      exact (hb x).trans (hi₀ x).symm)
  refine ⟨IsLocalization.lift hv, IsLocalization.lift_comp hv, RingHom.ext fun x => hi ?_⟩
  rw [hz, ← hz₀, ← hga]; rfl

theorem exists_classifying_finite_unramified : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)), TMap tT t f → ∃ (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TSieg bas bas' tT c ∧ u ≫ pullback.snd _ _ = sT ∧ SiegPB c Ag.univ (u ≫ pullback.fst _ _) ∧ IsFinite u ∧ FormallyUnramified u := by
  intro hL hL2 hTh E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' ha k o _ b em ρ hodd h3 hsq hρ hζ hem X s t τ hrep hpel
    p Ag hp hkp hS bas' hbas' O _ i z bb hi hz hb T sT f hf tT htT
  obtain ⟨hded, hft, heminj⟩ := id hem
  obtain ⟨M, i₀, z₀, hi₀, hz₀, hb₀, hfac⟩ := exists_localization p k hp em heminj (b.ζ : o) hζ
  obtain ⟨ga, hgb, hgz⟩ := hfac O i z bb hi hz hb
  have hdom : IsDomain (Localization M) := hi₀.isDomain i₀
  have hnoeth : IsNoetherianRing (Localization M) := IsLocalization.isNoetherianRing M _ inferInstance
  have hz₀inj : Function.Injective z₀ := fun x y h => Subtype.ext ((hz₀ x).symm.trans ((congrArg i₀ h).trans (hz₀ y)))
  have := hrep.red
  have := hrep.flat
  have hred := isReduced_pullback_localization (O := Localization M) M s
  have hf₀ := IsPullback.of_hasPullback s (spMap (algebraMap o (Localization M)))
  generalize hT₀ : pullback.fst s (spMap (algebraMap o (Localization M))) = f₀ at hf₀
  generalize hs₀ : pullback.snd s (spMap (algebraMap o (Localization M))) = s₀ at hf₀
  clear hT₀ hs₀
  generalize pullback s (spMap (algebraMap o (Localization M))) = T₀ at hred f₀ s₀ hf₀
  have hflat : Flat s₀ := MorphismProperty.of_isPullback (P := @Flat) hf₀ inferInstance
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b X T₀ s (s₀ ≫ spMap (algebraMap o (Localization M))) f₀ t hf₀.w
  have hζ₀ : algebraMap o (Localization M) (b.ζ : o) = z₀ (zetaZP p k) := hi₀ (by rw [hb₀, hz₀, hζ]; rfl)
  obtain ⟨c₀, hc₀, hts₀⟩ := GlobalTheory.T.symplectic_form_basis_change hL hL2 hTh g k J D.La (fun x y => D.EF x y) bas bas' (by simp) (by simp) hbas hbas'
    o (ZP p k) b (zetaZP p k) T₀ _ (s₀ ≫ spMap z₀) t₀ (by omega) (by
      intro K _ x β β' h h'
      obtain ⟨δ, hδ⟩ := Spec.map_surjective (x ≫ s₀)
      have hδ' : x ≫ s₀ = spMap δ.hom := hδ.symm
      rw [← Category.assoc, hδ', spMap_spMap] at h h'
      have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
      have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
      simp only [CommRingCat.hom_ofHom] at e e'
      rw [← e, ← e', RingHom.comp_apply, RingHom.comp_apply, hζ₀])
  obtain ⟨v₀, hv₀, hpb₀⟩ := hS.2 T₀ _ c₀ hred (dense_generic z₀ hz₀inj s₀) hc₀
  let u₀ : T₀ ⟶ pullback Ag.s (spMap z₀) := pullback.lift v₀ s₀ hv₀
  have hu₁ : u₀ ≫ pullback.fst _ _ = v₀ := pullback.lift_fst _ _ _
  have hu₂ : u₀ ≫ pullback.snd _ _ = s₀ := pullback.lift_snd _ _ _
  have hprop := GlobalTheory.T.symplectic_datum_torsion_level_ext hL hL2 hTh E H D g J a w w' bas hpq hbas hw hw' ha k o b em ρ hodd h3 hsq hρ hζ hem X s t τ
    hrep hpel p Ag hp hkp hS bas' hbas' _ i₀ z₀ _ hi₀ hz₀ hb₀ hnoeth T₀ s₀ f₀ hf₀ t₀ c₀ u₀ ht₀ hts₀ hu₂ (hu₁ ▸ hpb₀)
  have hqf := (GlobalTheory.T.symplectic_datum_torsion_level hL hL2 hTh E H D g J a w w' bas hpq hbas hw hw' ha k o b em ρ hodd h3 hsq hρ hζ hem X s t τ
    hrep hpel p Ag hp hkp hS bas' hbas' _ i₀ z₀ _ hi₀ hz₀ hb₀ T₀ s₀ f₀ hf₀ t₀ c₀ u₀ ht₀ hts₀ hu₂ (hu₁ ▸ hpb₀)).2
  have hfin : IsFinite u₀ := IsFinite.of_isProper_of_locallyQuasiFinite u₀
  have eb : spMap ga ≫ spMap (algebraMap o (Localization M)) = spMap bb := by rw [spMap_spMap, hgb]
  have ez : spMap ga ≫ spMap z₀ = spMap z := by rw [spMap_spMap, hgz]
  let r : T ⟶ T₀ := hf₀.lift f (sT ≫ spMap ga) (by rw [Category.assoc, eb, hf.w])
  have hr₁ : r ≫ f₀ = f := hf₀.lift_fst _ _ _
  have hr₂ : r ≫ s₀ = sT ≫ spMap ga := hf₀.lift_snd _ _ _
  have hr : IsPullback r sT s₀ (spMap ga) := IsPullback.of_right (by rw [hr₁, eb]; exact hf) hr₂ hf₀
  have htr : TMap tT t₀ r := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b X T₀ T _ _ _ t t₀ tT).2 f₀ r ht₀).2 (hr₁ ▸ htT)
  have hrz : r ≫ s₀ ≫ spMap z₀ = sT ≫ spMap z := by rw [← Category.assoc, hr₂, Category.assoc, ez]
  obtain ⟨c, hc⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange g k (ZP p k) (ZP p k) (zetaZP p k) (zetaZP p k) (RingHom.id _) T₀ T (s₀ ≫ spMap z₀)
    (sT ≫ spMap z) r rfl (by rw [hrz, Category.assoc, spMap_spMap, RingHom.comp_id])).1 c₀
  have hts : TSieg bas bas' tT c := (GlobalTheory.T.siegel_structure_pullback g k J D.La bas bas' o _ b _ T₀ T _ _ _ _ t₀ c₀ tT c r hts₀ htr).1 hc
  let u : T ⟶ pullback Ag.s (spMap z) := pullback.lift (r ≫ v₀) sT (by rw [Category.assoc, hv₀, hrz])
  have hv₁ : u ≫ pullback.fst _ _ = r ≫ v₀ := pullback.lift_fst _ _ _
  have hv₂ : u ≫ pullback.snd _ _ = sT := pullback.lift_snd _ _ _
  have hpb : SiegPB c Ag.univ (u ≫ pullback.fst _ _) :=
    hv₁ ▸ ((GlobalTheory.T.siegelPullback_id_comp_cancel g k _ _ _ _ _ _ _ _ _ _ _ _ Ag.univ c₀ c v₀ r).2 hpb₀).1 hc
  let q : pullback Ag.s (spMap z) ⟶ pullback Ag.s (spMap z₀) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap ga) (by rw [Category.assoc, ez, pullback.condition])
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap ga := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd _ _) (spMap ga) :=
    IsPullback.of_right (by rw [hq₁, ez]; exact IsPullback.of_hasPullback _ _) hq₂ (IsPullback.of_hasPullback _ _)
  have huq : r ≫ u₀ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu₁, Category.assoc, hq₁, hv₁]
    · rw [Category.assoc, hu₂, Category.assoc, hq₂, ← Category.assoc, hv₂, hr₂]
  have hu : IsPullback r u u₀ q := IsPullback.of_bot (by rw [hv₂, hu₂]; exact hr) huq hq
  exact ⟨c, u, hts, hv₂, hpb, MorphismProperty.of_isPullback (P := @IsFinite) hu hfin,
    (GlobalTheory.T.symplectic_datum_torsion_level hL hL2 hTh E H D g J a w w' bas hpq hbas hw hw' ha k o b em ρ hodd h3 hsq hρ hζ hem X s t τ
      hrep hpel p Ag hp hkp hS bas' hbas' O i z bb hi hz hb T sT f hf tT c u htT hts hv₂ hpb).1⟩

end GlobalTheory.SiegelClassify
