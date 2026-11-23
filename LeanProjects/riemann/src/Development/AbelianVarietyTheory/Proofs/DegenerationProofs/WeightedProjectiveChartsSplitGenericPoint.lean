import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedChartsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericSplit

theorem split_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] (C : Charts G.left) {d : ℕ} (c : Fin d → C.Cl)
    {K K' : Type} [Field K] [Field K'] {H : Over (Sp K)} [GrpObj H] {H' : Over (Sp K')} [GrpObj H']
    {t : Sp K ⟶ S} {t' : Sp K' ⟶ S} (f : Sp K' ⟶ Sp K) (hf : f ≫ t = t') {φ : H.left ⟶ G.left}
    {ψ : H'.left ⟶ G.left} [IsAffineHom φ] [IsAffineHom ψ] (hφ : IsGrpPullback H G t φ)
    (hψ : IsGrpPullback H' G t' ψ) (h : Charts.Split (C.pull φ) c) : Charts.Split (C.pull ψ) c := by
  subst hf
  have w : ψ ≫ G.hom = (H'.hom ≫ f) ≫ t := by rw [hψ.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : H'.left ⟶ H.left, l ≫ φ = ψ ∧ l ≫ H.hom = H'.hom ≫ f :=
    ⟨hφ.1.lift _ _ w, hφ.1.lift_fst _ _ w, hφ.1.lift_snd _ _ w⟩
  subst h₁
  have hl : IsGrpPullback H' H f l := hφ.cancel hψ h₂
  have : IsAffineHom l := MorphismProperty.of_isPullback (P := @IsAffineHom) hl.1.flip inferInstance
  exact SplitPull.pull_pull_and_split_pull.2 K K' H H' f l hl (C.pull φ) d c h

theorem mem_basicOpen_of_mem {X : Scheme.{0}} (C : Charts X) (a a' : {i // C.wt i = C.c₀}) (j : C.I) (x : X)
    (ha : x ∈ C.W a) (h : x ∈ X.basicOpen (C.r a' j)) : x ∈ X.basicOpen (C.r a j) := by
  have hx : x ∈ C.W a ⊓ C.W a' := ⟨ha, X.basicOpen_le _ h⟩
  have e : ∀ (V : X.Opens) (k : C.W a ⊓ C.W a' ≤ V) (u : Γ(X, V)),
      X.basicOpen (resG X k u) = (C.W a ⊓ C.W a') ⊓ X.basicOpen u := fun V k u => X.basicOpen_res u (homOfLE k).op
  have h₁ : x ∈ X.basicOpen (resG X (inf_le_left : C.W a ⊓ C.W a' ≤ C.W a) (C.r a j)) := by
    rw [C.trans a a' j, Scheme.basicOpen_mul, e, e, ← C.inter]
    exact ⟨⟨hx, hx⟩, hx, h⟩
  rw [e] at h₁
  exact h₁.2

theorem exists_open {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (C : Charts G.left) {d : ℕ}
    (c : Fin d → C.Cl) (Sg : Set (Sp R)) (hd : Dense Sg) (hs : C.SplitOn c Sg) :
    ∃ (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) (b : R), b ≠ 0 ∧ (∀ n, C.wt (j n) = c n) ∧
      ∀ x : PrimeSpectrum R, b ∉ x.asIdeal →
        eSec G x ∈ C.W a ∧ ∀ n, eSec G x ∈ G.left.basicOpen (C.r a (j n)) := by
  let e : Sp R ⟶ G.left := eSec G
  obtain ⟨a, ha⟩ : ∃ a, e (⊥ : PrimeSpectrum R) ∈ C.W a :=
    TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ _))
  obtain ⟨x, hxa, hx⟩ := hd.inter_open_nonempty _ (e ⁻¹ᵁ C.W a).isOpen ⟨_, ha⟩
  obtain ⟨K, _, t, _, ht, -, i, hT⟩ := hs x hx
  have hp := isGrpPullback_pullback G t
  have he : (eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t = t ≫ e :=
    eSec_comp_of_isGrpPullback hp
  let y : Sp K := (⊥ : PrimeSpectrum K)
  have hy : t y = x := ht.le ⟨y, rfl⟩
  have hj : ∀ n, ∃ j, C.wt j = c n ∧ e x ∈ G.left.basicOpen (C.r a j) := by
    intro n
    obtain ⟨a', j, hj, hm⟩ := hT.bpf n (eSec ((Over.pullback t).obj G) y)
    refine ⟨j, hj, mem_basicOpen_of_mem C a a' j _ hxa ?_⟩
    have hm' : eSec ((Over.pullback t).obj G) y ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a' j) := by
      rw [Scheme.preimage_basicOpen]
      exact hm
    have h2 : ((eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t) y ∈
      G.left.basicOpen (C.r a' j) := hm'
    rw [he] at h2
    rw [← hy]
    exact h2
  choose j hj hjx using hj
  let U : Set (PrimeSpectrum R) := (e ⁻¹ᵁ C.W a : Set (Sp R)) ∩ ⋂ n, (e ⁻¹ᵁ G.left.basicOpen (C.r a (j n)) : Set (Sp R))
  have hU : IsOpen U := (e ⁻¹ᵁ C.W a).isOpen.inter (isOpen_iInter_of_finite fun n => (e ⁻¹ᵁ _).isOpen)
  have hxU : x ∈ U := ⟨hxa, Set.mem_iInter.2 hjx⟩
  obtain ⟨_, ⟨b, rfl⟩, hb, hbU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  refine ⟨a, j, b, ?_, hj, fun z hz => ⟨(hbU hz).1, fun n => Set.mem_iInter.1 (hbU hz).2 n⟩⟩
  rintro rfl
  exact hb (Ideal.zero_mem _)

theorem split_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hd hs
  obtain ⟨a, j, b, hb, hj, hU⟩ := exists_open G C c Sg hd hs
  let R' := Localization.Away b
  have hle : Submonoid.powers b ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hb
  haveI : IsDomain R' := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers b) R' inferInstance
  let u : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  haveI : IsOpenImmersion u := IsOpenImmersion.of_isLocalization b
  have hu : Set.range u = (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) := PrimeSpectrum.localization_away_comap_range R' b
  let G' : Over (Sp R') := (Over.pullback u).obj G
  let π : G'.left ⟶ G.left := pullback.fst G.hom u
  have hp : IsGrpPullback G' G u π := isGrpPullback_pullback G u
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.1.flip inferInstance
  haveI : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom u))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd G.hom u))
  haveI : QuasiCompact G'.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom u))
  have hd' : Dense (u ⁻¹' Sg) := hd.preimage u.isOpenEmbedding.isOpenMap
  have hs' : (C.pull π).SplitOn c (u ⁻¹' Sg) := by
    intro x hx
    obtain ⟨K, _, t, _, ht, hsp⟩ := hs _ hx
    have hr : Set.range t ⊆ Set.range u := by
      rw [ht]
      rintro _ rfl
      exact ⟨x, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' ≫ u = t := ⟨_, IsOpenImmersion.lift_fac u t hr⟩
    haveI : IsAffineHom (pullback.fst G'.hom t') :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
    refine ⟨K, inferInstance, t', this, ?_, ?_⟩
    · have h1 : ∀ y, t' y = x := fun y => u.isOpenEmbedding.injective (by
        have : t y = u x := ht.le ⟨y, rfl⟩
        rw [← this, ← ht']; rfl)
      ext z
      exact ⟨fun ⟨y, hy⟩ => hy ▸ h1 y, fun hz => ⟨(⊥ : PrimeSpectrum K), (h1 _).trans hz.symm⟩⟩
    · exact split_transport C c (𝟙 _) (by rw [Category.id_comp, ht']) (isGrpPullback_pullback G t)
        ((isGrpPullback_pullback G' t').comp hp) hsp
  have he : ∀ x : Sp R', π (eSec G' x) = eSec G (u x) := fun x =>
    congrArg (fun q => q x) (eSec_comp_of_isGrpPullback hp)
  have hb' : ∀ x : Sp R', b ∉ (u x).asIdeal := fun x => hu.le ⟨x, rfl⟩
  have hB : (C.pull π).Based c a j := by
    refine ⟨fun x _ => ?_, fun n => ⟨hj n, fun x _ => ?_⟩⟩
    · change π (eSec G' x) ∈ C.W a
      rw [he]
      exact (hU _ (hb' x)).1
    · change eSec G' x ∈ G'.left.basicOpen ((π.app (C.W a)).hom (C.r a (j n)))
      rw [← Scheme.preimage_basicOpen]
      change π (eSec G' x) ∈ G.left.basicOpen (C.r a (j n))
      rw [he]
      exact (hU _ (hb' x)).2 n
  haveI : IsAffineHom (pullback.fst G'.hom (Out.jK R')) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have h := GlobalTheory.T.split_generic_of_based_weightedCharts R' G' (C.pull π) d c _ hd' hs' a j hB
  have hun : IsUnit (algebraMap R (FractionRing R) b) :=
    IsLocalization.map_units (FractionRing R) (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors R)
  let g : R' →+* FractionRing R := IsLocalization.Away.lift b hun
  have hg : Function.Injective g := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective R' hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  let g' : FractionRing R' →+* FractionRing R := IsFractionRing.lift hg
  refine split_transport C c (spMap g') ?_ ((isGrpPullback_pullback G' (Out.jK R')).comp hp)
    (isGrpPullback_pullback G (Out.jK R)) h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change g' (algebraMap R' _ (algebraMap R R' x)) = algebraMap R _ x
  rw [IsFractionRing.lift_algebraMap]
  exact IsLocalization.Away.lift_eq b hun x

end GlobalTheory.ZJ.GenericSplit
end
