import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended

noncomputable section

namespace GlobalTheory.MulDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_eq_one_of_kTriv_pull {S S' : Scheme.{0}} {f : S' ⟶ S}
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L')
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A)
    (hx : ∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen)
    {R' : CommRingCat.{0}} (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S') (sq : g ≫ t = t' ≫ f) :
    g ≫ x.left = g ≫ (1 : Over.mk t ⟶ A).left := by
  obtain ⟨w, hw⟩ := hw
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact congrArg (fun q => q.left) e₂

theorem kTriv_of_locally {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (H : ∀ s : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S), IsOpenImmersion f ∧ IsAffineHom f ∧ s ∈ Set.range f ∧
      KTriv ((Over.pullback f).obj A) (L.pull (pullback.fst A.hom f))) : KTriv A L := by
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨S', f, h₁, h₂, ⟨s, hs⟩, hK⟩ := H (t p)
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let g := (pullback t f).isoSpec.inv ≫ pullback.fst t f
  have e := comp_eq_one_of_kTriv_pull (isGrpPullback_pullback A f) hL (pull_isLB hL _)
    (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK t x hx g ((pullback t f).isoSpec.inv ≫ pullback.snd t f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have e' : pullback.fst t f ≫ x.left = pullback.fst t f ≫ (1 : Over.mk t ⟶ A).left := by
    rw [← cancel_epi (pullback t f).isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact e
  refine ⟨(pullback.fst t f).opensRange, ?_, ?_⟩
  · show p ∈ Set.range (pullback.fst t f)
    rw [Scheme.Pullback.range_fst]
    exact ⟨s, hs⟩
  · rw [← cancel_epi (pullback.fst t f).isoOpensRange.hom, ← Category.assoc, ← Category.assoc]
    erw [Scheme.Hom.isoOpensRange_hom_ι]
    exact e'

theorem kTriv_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {L L' : LB A.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso L L') (hK : KTriv A L) : KTriv A L' := by
  obtain ⟨w, hw⟩ : LBIso L' (L.pull (Iso.refl A).hom.left) :=
    h.symm.chartPull (Geo.Tor.chartPullId L') (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl)
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  exact kTriv_pull (isGrpPullback_of_iso (Iso.refl A)) hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.MulDescent

namespace GlobalTheory.MulDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_polarisation_of_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro h₁ h₂ R _ _ _ A _ g m M P pt hA hg hm hu hM hamp hP hpt hbas hfib
  obtain ⟨L, hL, hrig, hsym, hLa, hiso⟩ := GlobalTheory.OddDescent.exists_descended h₁ h₂ R A g m M pt hA hg hm hu hM hamp hpt hbas (by
    intro f hf
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    by_contra hn
    obtain ⟨p, hp, hp', -, hfp⟩ := hP q f hq hn
    exact hfp (hf p (hfib p hp) hp'))
  refine ⟨L, hL, hrig, hsym, hLa, kTriv_of_locally hL fun s => ?_, hiso⟩
  have hs : (s : PrimeSpectrum R).asIdeal.IsPrime := (s : PrimeSpectrum R).isPrime
  obtain ⟨p, hp, -, hle, -⟩ := hP (s : PrimeSpectrum R).asIdeal 1 hs
    (fun h => hs.ne_top ((Ideal.eq_top_iff_one _).2 h))
  obtain ⟨K, _, _, x, Pl, φ, hker, hφ, hw⟩ := hfib p hp
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x Pl.A φ hA hL hLa hφ
    (kTriv_of_lbIso Pl.isLB (pull_isLB hL _) (hiso K x Pl φ hφ hw) Pl.ktriv)
  have hfs : f ∉ (s : PrimeSpectrum R).asIdeal := fun h => hf (by
    have := hle h
    rwa [← hker, RingHom.mem_ker] at this)
  have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨_, spMap (algebraMap R (Localization.Away f)), ho, inferInstance, ?_,
    H (Localization.Away f) (algebraMap R _) _ _ (IsLocalization.Away.algebraMap_isUnit f)
      (isGrpPullback_pullback A _)⟩
  have : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hfs
  exact this

end GlobalTheory.MulDescent
