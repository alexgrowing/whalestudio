import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFramesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.Frames

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp (f : R →+* R') (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem polPB_comp {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h' : ∃ φ', PolPB P'' P' (spMap f') φ')
    (h : ∃ φ, PolPB P' P (spMap f) φ) : ∃ ψ, PolPB P'' P (spMap g) ψ := by
  obtain ⟨φ', hc', hg', w', hw'⟩ := h'
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  obtain ⟨w'', T⟩ := exists_comp P'.isLB w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') P.isLB P''.isLB
  exact ⟨φ' ≫ φ, (hc'.comp hc).congr (spMap_comp f f').symm rfl, hg'.trans hg, w'',
    (isGen_iff w'').2 (T.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem polPB_cancel {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h : ∃ φ, PolPB P' P (spMap f) φ)
    (h'' : ∃ ψ, PolPB P'' P (spMap g) ψ) : ∃ φ', PolPB P'' P' (spMap f') φ' := by
  obtain ⟨φ'', hc'', hg'', w'', hw''⟩ := h''
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  have hsp := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : P''.A.left ⟶ P'.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ P'.A.hom = P''.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (P''.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' g g'' P'.isLB P''.isLB
  exact ⟨φ', hc.cancel (hc''.congr hsp rfl) hw0, hg''.trans hg.symm, w',
    (isGen_iff w').2 (T.pgen_cancel P.isLB g g'')⟩

theorem polPB_exists (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ (spMap f) P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_of_keyPB {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} (h : KeyPB x' x f) :
    ∃ φ, PolPB x'.P x.P (spMap f) φ :=
  let ⟨φ, _, w, hg, _, hc, hw, _⟩ := h
  ⟨φ, hc, hg, w, hw⟩

theorem exists_points (K K' R : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [CommRing R] [Algebra K R] (s : R →+* ℂ) (s₀ : R →ₐ[K] K) :
    ∃ (i : R →+* K' ⊗[K] R) (s' : K' ⊗[K] R →+* ℂ) (s₀' : K' ⊗[K] R →ₐ[K'] K'),
      s'.comp i = s ∧ s₀'.toRingHom.comp i = (algebraMap K K').comp s₀.toRingHom := by
  letI : Algebra K ℂ := (s.comp (algebraMap K R)).toAlgebra
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let e : K' →ₐ[K] ℂ := IsAlgClosed.lift
  let sA : R →ₐ[K] ℂ := { s with commutes' := fun _ => rfl }
  refine ⟨Algebra.TensorProduct.includeRight.toRingHom,
    (Algebra.TensorProduct.lift e sA fun _ _ => Commute.all _ _).toRingHom,
    Algebra.TensorProduct.lift (AlgHom.id K' K') ((Algebra.ofId K K').comp s₀) fun _ _ => Commute.all _ _,
    RingHom.ext fun r => ?_, RingHom.ext fun r => ?_⟩
  · simp [sA]
  · simp

end GlobalTheory.KeyFam.Frames

namespace GlobalTheory.KeyFam
open Frames

theorem connFam_of_polFam : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  intro hL hL2 hF x
  obtain ⟨K, _, _, R, _, _, Q, s, s₀, φ, hG, hP, hK⟩ := hF x.P x.g_pos
  obtain ⟨P₀, φ₀, hP₀⟩ := polPB_exists hL.polBaseChange Q s₀.toRingHom
  obtain ⟨K', _, _, j, hKn⟩ := hK P₀ φ₀ hP₀
  letI : Algebra K K' := j.toAlgebra
  obtain ⟨i, s', s₀', hs', hs₀'⟩ := exists_points K K' R s s₀
  obtain ⟨Q', ψ, hQ'⟩ := polPB_exists hL.polBaseChange Q i
  have hG' : GeomInt K' (K' ⊗[K] R) := (GlobalTheory.T.geom_integral_base_change_and_localization K K' R hG).1
  haveI := hG'.1
  haveI : IsNoetherianRing (K' ⊗[K] R) := Algebra.FiniteType.isNoetherianRing K' _
  obtain ⟨r, hr, hr₀, y, χ, hy⟩ := GlobalTheory.T.exists_keyData_near_two_primes hL hL2 (K' ⊗[K] R) Q' ⟨RingHom.ker s', RingHom.ker_isPrime _⟩
    ⟨RingHom.ker s₀'.toRingHom, RingHom.ker_isPrime _⟩ (by rw [hQ'.2.1, ← hP.2.1]; exact x.g_pos)
  have hu : IsUnit (s' r) := isUnit_iff_ne_zero.2 hr
  have hu₀ : IsUnit (s₀'.toRingHom r) := isUnit_iff_ne_zero.2 hr₀
  have hS : GeomInt K' (Localization.Away r) :=
    (GlobalTheory.T.geom_integral_base_change_and_localization K' K' _ hG').2 r fun h => hr (h ▸ Ideal.zero_mem _)
  let t : Localization.Away r →+* ℂ := IsLocalization.Away.lift r hu
  have ht : t.comp (algebraMap _ _) = s' := IsLocalization.Away.lift_comp r hu
  let u : Localization.Away r →+* K' := IsLocalization.Away.lift r hu₀
  have hu' : u.comp (algebraMap _ _) = s₀'.toRingHom := IsLocalization.Away.lift_comp r hu₀
  let t₀ : Localization.Away r →ₐ[K'] K' :=
    { u with
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply K' (K' ⊗[K] R) (Localization.Away r)]
        exact (RingHom.congr_fun hu' _).trans (s₀'.commutes a) }
  have hyQ := polPB_comp rfl ⟨χ, hy⟩ ⟨ψ, hQ'⟩
  obtain ⟨φ₁, hφ₁⟩ := polPB_cancel (f' := t) (by rw [← RingHom.comp_assoc, ht, hs']) hyQ ⟨φ, hP⟩
  obtain ⟨S', _, _, j', y', v, v₀, ψ', hS', hx, hy', hv₀⟩ := GlobalTheory.T.exists_thetaKeyFamily_universal_frames hL K' _ y x t φ₁ t₀ hS hφ₁
  obtain ⟨y₀, hy₀⟩ := exists_keyPB_ring y' v₀.toRingHom
  have e₁ : v₀.toRingHom.comp j'.toRingHom = u := congrArg AlgHom.toRingHom hv₀
  have h₁ := polPB_comp e₁ (polPB_of_keyPB hy₀) ⟨ψ', hy'⟩
  have h₂ := polPB_comp (g := ((RingHom.id K').comp j).comp s₀.toRingHom)
    (by rw [← RingHom.comp_assoc, hu', hs₀']; rfl) h₁ hyQ
  obtain ⟨φ₂, hφ₂⟩ := polPB_cancel rfl ⟨φ₀, hP₀⟩ h₂
  obtain ⟨c, hc⟩ := hKn K' (RingHom.id K') y₀ φ₂ hφ₂
  exact ⟨K', _, ‹_›, S', _, _, y', v, v₀, c, hS'.1, hS'.2, hx, fun e x₀ h =>
    hc e x₀ (KeyCancel.keyPB_cancel _ _ _ y' y₀ x₀ _ _ hy₀ h)⟩

end GlobalTheory.KeyFam
