import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MkTensorLe
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomNeZeroOfCountable
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDominantComponent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrimeDimensionLEOneAvoiding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSmoothNormalisation
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusPullOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBScale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.ThetaFrameSpec

theorem key_descends (hL : Out.Laws) (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (x : KeyIn S) (u : S) :
    ∃ (R : Subring S) (y : KeyIn R), u ∈ R ∧ Algebra.FiniteType ℤ R ∧ KeyPB x y R.subtype := by
  classical
  obtain ⟨R₀, P₀, φ, hfg, hg, hφ, hiso⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring S x.P
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨r, hr, hnear⟩ := GlobalTheory.KeyNear.main hL R₀ P₀ (hg ▸ x.g_pos)
    (PrimeSpectrum.comap R₀.subtype (IsLocalRing.closedPoint S))
  have hru : IsUnit (r : S) := by
    by_contra h
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨R₁, h₁, hF₁, hfg₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin S R₀ {((hru.unit⁻¹ : Sˣ) : S)} hfg
  have hm : ((hru.unit⁻¹ : Sˣ) : S) ∈ R₁ := hF₁ (by simp)
  obtain ⟨y, π, hyg, hπ, hπiso⟩ := hnear R₁ (Subring.inclusion h₁)
    (IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext hru.mul_val_inv))
  have hcomp : spMap R₁.subtype ≫ spMap (Subring.inclusion h₁) = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  let ψ : x.P.A.left ⟶ y.P.A.left := hπ.1.lift φ (x.P.A.hom ≫ spMap R₁.subtype)
    (by rw [Category.assoc, hcomp]; exact hφ.1.w)
  have hψ₁ : ψ ≫ π = φ := hπ.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ y.P.A.hom = x.P.A.hom ≫ spMap R₁.subtype := hπ.1.lift_snd _ _ _
  have hψ : IsGrpPullback x.P.A y.P.A (spMap R₁.subtype) ψ :=
    hπ.cancel (by rw [hcomp, hψ₁]; exact hφ) hψ₂
  have hψiso : LBIso x.P.L (y.P.L.pull ψ) :=
    LBIso.trans x.P.isLB (pull_isLB P₀.isLB φ) (pull_isLB y.P.isLB ψ) hiso
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hπiso ψ hψ₁.symm).symm
  obtain ⟨rig, hrig, th, hth, v, hv, hpb⟩ := GlobalTheory.KeyTf.exists_keyPB_on R₁ S R₁.subtype y x.P ψ x.g_pos (hg.symm.trans hyg.symm) hψ hψiso
  obtain ⟨a, t, ht, hta, hid⟩ := (GlobalTheory.KeyOnPol.main hL S).2 ⟨x.P, x.g_pos, rig, hrig, th, hth, v, hv⟩
    x.rig x.rig_gen x.th x.th_ne x.v x.basis
  haveI := x.P.isAb.comm
  choose M hM using fun i => (hv.2 (x.v i) (x.basis.1 i)).exists
  have hdet : IsUnit (Matrix.det (Matrix.of M)) :=
    ((GlobalTheory.LieComb.lieComb_algebra S x.P.A x.P.g v hv.1).2.2.2.2 (Matrix.of M) x.v hv hM).1 x.basis
  obtain ⟨R₂, h₂, hF₂, hfg₂⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin S R₁
    ({u, (a : S), ((a⁻¹ : Sˣ) : S), ((hdet.unit⁻¹ : Sˣ) : S)} ∪ Finset.univ.image fun p : Fin x.P.g × Fin x.P.g => M p.1 p.2) hfg₁
  have m₁ : u ∈ R₂ := hF₂ (by simp)
  have m₂ : (a : S) ∈ R₂ := hF₂ (by simp)
  have m₃ : ((a⁻¹ : Sˣ) : S) ∈ R₂ := hF₂ (by simp)
  have m₄ : ((hdet.unit⁻¹ : Sˣ) : S) ∈ R₂ := hF₂ (by simp)
  have m₅ : ∀ i k, M i k ∈ R₂ := fun i k => hF₂ (by
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union]
    exact Or.inr ⟨(i, k), by simp, rfl⟩)
  obtain ⟨y₂, hy₂⟩ := exists_keyPB_ring y (Subring.inclusion h₂)
  have hpb₂ := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ (Subring.inclusion h₂) R₂.subtype hy₂ hpb
  let a₂ : R₂ˣ := ⟨⟨a, m₂⟩, ⟨_, m₃⟩, Subtype.ext a.mul_inv, Subtype.ext a.inv_mul⟩
  let M₂ : Matrix (Fin x.P.g) (Fin x.P.g) R₂ := Matrix.of fun i k => ⟨M i k, m₅ i k⟩
  have hdet₂ : IsUnit M₂.det := by
    refine IsUnit.of_mul_eq_one ⟨_, m₄⟩ (Subtype.ext ?_)
    have e : (M₂.det : S) = (Matrix.of M).det := R₂.subtype.map_det M₂
    show (M₂.det : S) * _ = 1
    rw [e]
    exact hdet.mul_val_inv
  obtain ⟨y₃, hy₃⟩ := GlobalTheory.KeyScaleLift.exists_keyPB_scale R₂ S R₂.subtype y₂ ⟨x.P, x.g_pos, rig, hrig, th, hth, v, hv⟩ a₂ M₂ hpb₂ hdet₂
  exact ⟨R₂, y₃, m₁, hfg₂, GlobalTheory.keyPB_trans _ _ _ _ _ _ R₂.subtype (RingHom.id S) (hy₃ t ht x.v x.basis hta hM) hid⟩

theorem exists_smooth_through (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [Countable R]
    (g : R →+* ℂ) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ),
      Algebra.Smooth ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  obtain ⟨E, _, _, _, ρ, e, hft, hρ, he⟩ := GlobalTheory.KeyCx.exists_dominant_component R g
  obtain ⟨Q, hQ, hle, hT, hdim⟩ := GlobalTheory.LineThrough.exists_prime_dimensionLEOne_avoiding E e (ρ '' {0}ᶜ) ((Set.to_countable _).image _) (by
    rintro ⟨r, hr, h⟩
    exact hr (hρ (h.trans (map_zero ρ).symm)))
  obtain ⟨E', _, _, _, ρ', e', hs, hρ', he'⟩ := GlobalTheory.CurveNorm.exists_smooth_normalisation (E ⧸ Q) (Ideal.Quotient.liftₐ Q e fun a ha => hle ha)
  refine ⟨E', inferInstance, inferInstance, inferInstance, (ρ'.toRingHom.comp (Ideal.Quotient.mk Q)).comp ρ, e', hs,
    ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h
    refine hT _ ⟨r, h, rfl⟩ (Ideal.Quotient.eq_zero_iff_mem.1 (hρ' ?_))
    rw [map_zero]; exact hr
  · rw [← he]
    ext r
    exact AlgHom.congr_fun he' (Ideal.Quotient.mk Q (ρ r))

def IsVal (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

theorem exists_isVal (hT : ThetaUnifAV) (x : KeyIn ℂ) : ∃ t, IsVal x t := by
  obtain ⟨τ, M, a, b, c, h₁, h₂, -, h₃⟩ := (GlobalTheory.KeyNormalExists.exists_normalAt hT x).1
  exact ⟨_, τ, M, a, b, c, h₁, h₂, h₃, rfl⟩

theorem isVal_injective (hT : ThetaUnifAV)
    (hE : ∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → IsVal x t → IsVal x' t' → t' = f t)
    {R : Type} [CommRing R] [IsDomain R] (y : KeyIn R) (g g' : R →+* ℂ) (hg : Function.Injective g)
    (hg' : Function.Injective g') (u : R) {x x' : KeyIn ℂ} (hx : KeyPB x y g) (hx' : KeyPB x' y g')
    (ht : IsVal x (g u)) {t' : ℂ} (ht' : IsVal x' t') : t' = g' u := by
  obtain ⟨σ, σ', h⟩ := GlobalTheory.EmbC.exists_comp_eq R g g' hg hg'
  obtain ⟨z, hz⟩ := exists_keyPB_ring x σ
  obtain ⟨s, hs⟩ := exists_isVal hT z
  have hz' : KeyPB z x' σ' := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ g' σ' hx'
    (h ▸ GlobalTheory.keyPB_trans _ _ _ _ _ _ g σ hx hz)
  refine σ'.injective ((hE σ' x' z t' s hz' ht' hs).symm.trans ((hE σ x z _ s hz ht hs).trans ?_))
  exact RingHom.congr_fun h u

theorem value_specialises : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x' τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t' = f t) → (∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsPrincipalIdealRing S] (x₀ : KeyIn S) (f f' : S →+* ℂ) (u : S) (x x' : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ) (τ' M' : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a' b' : Fin x'.P.g → ℂ) (c' : ℂ), Function.Injective f → KeyPB x x₀ f → KeyPB x' x₀ f' → charHalf _ a b → charHalf _ a' b' → c ≠ 0 → c' ≠ 0 → NormalAt x τ M a b c → NormalAt x' τ' M' a' b' c' → M.det ^ 4 / c ^ 8 = f u → M'.det ^ 4 / c' ^ 8 = f' u) := by
  intro hL hT hI hN hE S _ _ _ _ x₀ f f' u x x' τ M a b c τ' M' a' b' c' hf hx hx' hab hab' hc hc' hn hn' hu
  obtain ⟨N, hN, hK⟩ := hN
  obtain ⟨R, y, huR, hfg, hy⟩ := key_descends hL S x₀ u
  haveI : Countable R := by
    obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hfg
    haveI : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max_lift.trans (by simp)
    exact hp.countable
  obtain ⟨E, _, _, _, ρ, e, hs, hρ, he⟩ := exists_smooth_through R (f'.comp R.subtype)
  obtain ⟨z, hz⟩ := exists_keyPB_ring y ρ
  obtain ⟨κ, hκ⟩ := GlobalTheory.KeySmoothBase.exists_unit_of_smooth hT hL.polBaseChange N hK ℂ E z
  choose w hw using fun s : E →ₐ[ℂ] ℂ => exists_keyPB_ring z s.toRingHom
  choose t ht using fun s : E →ₐ[ℂ] ℂ => exists_isVal hT (w s)
  have hxy : KeyPB x y (f.comp R.subtype) := GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hy hx
  have gen : ∀ s : E →ₐ[ℂ] ℂ, (∀ r ∈ ρ '' {0}ᶜ, s r ≠ 0) → t s = s (ρ ⟨u, huR⟩) := fun s h =>
    isVal_injective hT hE y (f.comp R.subtype) (s.toRingHom.comp ρ) (hf.comp Subtype.val_injective)
      ((injective_iff_map_eq_zero _).2 fun r hr => by_contra fun h' => h _ ⟨r, h', rfl⟩ hr) ⟨u, huR⟩ hxy
      (GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hz (hw s)) ⟨τ, M, a, b, c, hab, hc, hn, hu.symm⟩ (ht s)
  have hc₀ : (ρ '' {0}ᶜ).Countable := (Set.to_countable _).image _
  have h₀ : (0 : E) ∉ ρ '' {0}ᶜ := by
    rintro ⟨r, hr, h⟩
    exact hr (hρ (h.trans (map_zero ρ).symm))
  have hpow : ρ ⟨u, huR⟩ ^ N z.P.g = κ := by
    by_contra h
    obtain ⟨s, hs⟩ := GlobalTheory.exists_algHom_ne_zero_of_countable E (insert (ρ ⟨u, huR⟩ ^ N z.P.g - κ) (ρ '' {0}ᶜ)) (hc₀.insert _) (by
      rintro (h' | h')
      exacts [h (sub_eq_zero.1 h'.symm), h₀ h'])
    refine hs _ (Set.mem_insert _ _) ?_
    rw [map_sub, map_pow, ← gen s fun r hr => hs r (Set.mem_insert_of_mem _ hr),
      hκ s.toRingHom (w s) (t s) (hw s) (ht s)]
    exact sub_self _
  have hunit : IsUnit (ρ ⟨u, huR⟩) :=
    (isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 (hN z.P.g))).1 (hpow ▸ κ.isUnit)
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.exists_algHom_ne_zero_of_countable E _ hc₀ h₀
  have key := GlobalTheory.RootConst.value_eq_unit_of_pow_eq hL hT hI E z (N z.P.g) hunit.unit t s₀ (hN _) (fun s => ⟨w s, hw s, ht s⟩)
    (fun s => by
      rw [hκ s.toRingHom (w s) (t s) (hw s) (ht s), ← map_pow, IsUnit.unit_spec, hpow]; rfl)
    (gen s₀ hs₀) e
  have hwe : KeyPB (w e) y (f'.comp R.subtype) := he ▸ GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hz (hw e)
  have hid : KeyPB x' (w e) (RingHom.id ℂ) := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ _ (RingHom.id ℂ) hwe
    (GlobalTheory.keyPB_trans _ _ _ _ _ _ R.subtype f' hy hx')
  refine (hE _ _ _ (t e) _ hid (ht e) ⟨τ', M', a', b', c', hab', hc', hn', rfl⟩).trans (key.trans ?_)
  exact RingHom.congr_fun he ⟨u, huR⟩

end GlobalTheory.ThetaFrameSpec
end
