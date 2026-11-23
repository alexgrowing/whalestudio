import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackTorsionPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyDecompositionProduct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.IntBasis

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    (dualMap b).comp (dualMap a) = dualMap (b.comp a) := by
  ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]

end GlobalTheory.CompanionTheory.Ggeo.IntBasis

open GlobalTheory.CompanionTheory.Ggeo.IntBasis in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X N b a V _ hN hspan hV hNu
  classical
  let f : 𝓞 X.K →+* V := (algebraMap (𝓞 X.K) X.K).codRestrict V hV
  have hf : (algebraMap V X.K).comp f = algebraMap (𝓞 X.K) X.K := by ext; rfl
  obtain ⟨T', m0, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap f) X.B
  have hψ : ∀ k, IsMonHom (X.ψ (b k) (a k)) := fun k => ((X.fam (b k)).1 (a k)).isMonHom
  obtain ⟨hon, hker⟩ := GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points E H D l Xo c g ty FU i Z P hP X N b a hN hspan
  obtain ⟨χ, hχ, hψχ, hoff⟩ := GlobalTheory.T.isogeny_product_decomposition X.K (algebraMap X.K ℂ) g N (fun k => (X.C (b k)).P) X.B.pol
    (fun k => X.ψ (b k) (a k)) hψ hN hon hker
  obtain ⟨uV, huV, htan, hbasis⟩ := GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product (𝓞 X.K) V f g N (fun k => (X.C (b k)).P) (fun k => (X.C (b k)).v)
    X.B.pol (fun k => X.ψ (b k) (a k)) χ T'.t.G m0.φ X.dim (fun k => (X.C (b k)).basis) hψ hχ hψχ hoff hNu m0.cart
  have hy : spMap (algebraMap V X.K) ≫ spMap f = spMap (algebraMap (𝓞 X.K) X.K) := by rw [spectrumMap_comp, hf]
  obtain ⟨m'', hm''⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 X.K) V X.K f (algebraMap V X.K)).2
    (Sp (𝓞 X.K)) (spMap f) (spMap (algebraMap (𝓞 X.K) X.K)) X.B.t T'.t X.t m0 X.m' hy
  refine ⟨T'.t, m'', uV, htan, hbasis, fun k u hu => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := hu
  refine ⟨r, hr1, ?_⟩
  apply m0.cart.1.hom_ext
  · rw [Category.assoc, hm'', hr2, Category.assoc, huV k]
    simp only [← Category.assoc]
    congr 2
    rw [spectrumMap_comp, dualMap_comp_alt, hf]
  · have w1 := m''.cart.1.w
    have w2 := X.m'.cart.1.w
    have hmono : Mono (spMap (algebraMap (𝓞 X.K) X.K)) := by
      have : Epi (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)) := IsLocalization.epi (nonZeroDivisors (𝓞 X.K)) X.K
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)).op))
    have hbase : r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
      apply hmono.right_cancellation
      rw [Category.assoc, ← w2, ← Category.assoc, hr2]
      simp only [Category.assoc]
      rw [Over.w (X.ψ (b k) (a k)), Over.w ((X.C (b k)).v)]
      simp only [Over.mk_hom, spectrumMap_comp]
      congr 1
      ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
    rw [Category.assoc, w1, ← Category.assoc, hbase, Category.assoc, Over.w (uV k)]
    simp only [Over.mk_hom, Category.comp_id]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spectrumMap_comp, spectrumMap_comp]
    congr 1
    ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
