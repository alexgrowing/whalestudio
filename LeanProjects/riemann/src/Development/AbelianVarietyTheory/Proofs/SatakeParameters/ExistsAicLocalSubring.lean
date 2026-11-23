import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueFieldOfAic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidueStatement

noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem exists_aic_local_subring (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] (φ : k →+* K) :
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  obtain ⟨D, m₀, hD, hm₀, hres, hint⟩ := GlobalTheory.T.exists_polynomialSubring_maximal_integral k K φ
  obtain ⟨R, 𝔪, hR, h𝔪, hres', hfr, hic⟩ := GlobalTheory.T.integralClosure_maximal_residue_of_algClosed k K φ D m₀ hD hm₀ hres hint
  exact GlobalTheory.T.exists_local_subring_monic_roots_residue k K φ R 𝔪 hR h𝔪 hres' hfr hic

section Eqv
variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_trans {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_of_eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := by
  intro n
  have h : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun x y hxy => (hfg n).1 (by rw [h, h, hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hfg n).2 (pull R f F n y)
  exact ⟨x, (hf n).1 (by rw [← h, hx])⟩

variable {X Y W S : Scheme.{0}} (p : X ⟶ S) (d : Y ⟶ S) (g : W ⟶ Y)

theorem fst_comp_eq : pullback.fst p (g ≫ d) =
    (pullbackLeftPullbackSndIso p d g).inv ≫ pullback.fst (pullback.snd p d) g ≫ pullback.fst p d := by
  rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_fst]

theorem eqv_fst_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p d)) F) : Eqv R (sch.map (pullback.fst p (g ≫ d))) F := by
  rw [fst_comp_eq, Functor.map_comp, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) (eqv_trans F h1 h2)

theorem eqv_fst_of_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p (g ≫ d))) F) : Eqv R (sch.map (pullback.fst p d)) F := by
  refine eqv_of_eqv_comp F h1 ?_
  have : pullback.fst (pullback.snd p d) g ≫ pullback.fst p d =
      (pullbackLeftPullbackSndIso p d g).hom ≫ pullback.fst p (g ≫ d) := by
    rw [pullbackLeftPullbackSndIso_hom_fst]
  rw [← Functor.map_comp, this, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) h2

end Eqv

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem eqv_fieldChange (hE2 : E2) (hE3 : E3) (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K]
    [IsAlgClosed K] (φ : k →+* K) (hq : IsUnit (q : k)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) (tw q i) := by
  obtain ⟨T, hφT, ⟨hloc, hT, hres⟩, hfr⟩ := exists_aic_local_subring k K φ
  let α : k →+* T := φ.codRestrict T (fun c => hφT ⟨c, rfl⟩)
  have hqT : IsUnit (q : T) := by simpa using hq.map α
  let a := Spec.map (CommRingCat.ofHom α)

  have hb : Function.Bijective ((IsLocalRing.residue T).comp α) := by
    refine ⟨(IsLocalRing.residue T).comp α |>.injective, fun y => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, h, hc⟩ := hres t
    refine ⟨c, ?_⟩
    change IsLocalRing.residue T (α c) = IsLocalRing.residue T t
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have e : α c - t = -(t - ⟨φ c, h⟩) := by rw [neg_sub]; rfl
    rw [e]
    exact (IsLocalRing.maximalIdeal T).neg_mem hc
  haveI : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue T))
  have hra : r ≫ a = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) := (spec_comp _ _).symm
  have hsp : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a) r)) (tw q i) :=
    eqv_spInc hE2 hT q hqT (pullback.snd p a) i
  have hXT : Eqv (ZMod q) (sch.map (pullback.fst p a)) (tw q i) := by
    refine eqv_fst_of_comp _ p a r hsp ?_
    rw [hra]
    exact eqv_iso _ _

  let e := IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K
  have hφ : φ = (e.toRingEquiv.toRingHom).comp ((algebraMap T (FractionRing T)).comp α) := by
    ext c
    simp only [RingHom.comp_apply]
    rw [show e.toRingEquiv.toRingHom (algebraMap T (FractionRing T) (α c)) = e (algebraMap T (FractionRing T) (α c)) from rfl,
      AlgEquiv.commutes]
    rfl
  haveI : IsIso (CommRingCat.ofHom (e.toRingEquiv.toRingHom)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have hgen : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a)
      (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i) :=
    eqv_genInc hE3 hT q hqT (pullback.snd p a) i
  rw [hφ, spec_comp, spec_comp]
  refine eqv_fst_comp _ p _ _ (eqv_iso _ _) (eqv_fst_comp _ p a _ hgen hXT)

end GlobalTheory.GenusTwoPureComparison.Cmp
