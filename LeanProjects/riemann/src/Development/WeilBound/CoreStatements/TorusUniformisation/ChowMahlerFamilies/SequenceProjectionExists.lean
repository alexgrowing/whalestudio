import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceProjection

section Loc

variable {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
  {V : Type} [AddCommGroup V] [Module Ω V] [Module R V] [IsScalarTower R Ω V]

def locAt (Ω : Type) [Field Ω] [Algebra R Ω] (𝔮 : Ideal R) [h : 𝔮.IsPrime] : Subalgebra R Ω where
  carrier := {x | ∃ u v : R, v ∉ 𝔮 ∧ x * algebraMap R Ω v = algebraMap R Ω u}
  mul_mem' := by
    rintro a b ⟨u, v, hv, e⟩ ⟨u', v', hv', e'⟩
    refine ⟨u * u', v * v', fun hh => (h.mem_or_mem hh).elim hv hv', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']; ring
  add_mem' := by
    rintro a b ⟨u, v, hv, e⟩ ⟨u', v', hv', e'⟩
    refine ⟨u * v' + u' * v, v * v', fun hh => (h.mem_or_mem hh).elim hv hv', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← e, ← e']; ring
  algebraMap_mem' := fun r => ⟨r, 1, (Ideal.ne_top_iff_one 𝔮).1 h.ne_top, by simp⟩

theorem inv_mem (hinj : Function.Injective (algebraMap R Ω)) (𝔮 : Ideal R) [h : 𝔮.IsPrime] {v : R} (hv : v ∉ 𝔮) :
    algebraMap R Ω v ≠ 0 ∧ (algebraMap R Ω v)⁻¹ ∈ locAt Ω 𝔮 := by
  have h0 : algebraMap R Ω v ≠ 0 := fun e => hv (by
    have : v = 0 := hinj (by rw [e, map_zero])
    rw [this]; exact 𝔮.zero_mem)
  exact ⟨h0, 1, v, hv, by rw [inv_mul_cancel₀ h0, map_one]⟩

theorem isLoc (hinj : Function.Injective (algebraMap R Ω)) (𝔮 : Ideal R) [h : 𝔮.IsPrime] :
    IsLocalization.AtPrime (locAt Ω 𝔮) 𝔮 := by
  refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {x y} e => ?_⟩
  · obtain ⟨h0, h1⟩ := inv_mem hinj 𝔮 y.2
    exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  · obtain ⟨u, v, hv, e⟩ := z.2
    exact ⟨(u, ⟨v, hv⟩), Subtype.ext e⟩
  · have : x = y := hinj (congrArg Subtype.val e)
    exact ⟨1, by rw [this]⟩

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
theorem proj_transfer {R M Rp Mp : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing Rp] [Algebra R Rp]
    [AddCommGroup Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [IsLocalizedModule S f] (h : Module.Projective Rp Mp) :
    Module.Projective (Localization S) (LocalizedModule S M) := by
  letI : Algebra Rp (Localization S) := (IsLocalization.algEquiv S Rp (Localization S)).toRingHom.toAlgebra
  haveI : IsScalarTower R Rp (Localization S) :=
    IsScalarTower.of_algebraMap_eq fun r => ((IsLocalization.algEquiv S Rp (Localization S)).commutes r).symm
  letI : Module (Localization S) Mp := Module.compHom Mp (IsLocalization.algEquiv S Rp (Localization S)).symm.toRingHom
  haveI : IsScalarTower R (Localization S) Mp := IsScalarTower.of_algebraMap_smul fun r x => by
    change (IsLocalization.algEquiv S Rp (Localization S)).symm (algebraMap R _ r) • x = r • x
    rw [AlgEquiv.commutes, algebraMap_smul]
  haveI : Module.Projective (Localization S) Mp :=
    Module.Projective.of_equiv (M := Mp) (R := Rp) (σ := (IsLocalization.algEquiv S Rp (Localization S)).toRingEquiv)
      { __ := AddEquiv.refl Mp
        map_smul' := fun r x => by
          change r • x = (IsLocalization.algEquiv S Rp (Localization S)).symm
            (IsLocalization.algEquiv S Rp (Localization S) r) • x
          rw [AlgEquiv.symm_apply_apply] }
  exact Module.Projective.of_equiv
    ((IsLocalizedModule.iso S f).symm.extendScalarsOfIsLocalization S (Localization S))

theorem proj_of_loc [IsNoetherianRing R] (hinj : Function.Injective (algebraMap R Ω)) (M : Submodule R V) (hM : M.FG)
    (H : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], Module.Projective (locAt Ω 𝔮) (Submodule.span (locAt Ω 𝔮) (M : Set V))) :
    Module.Projective R M := by
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 hM
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  refine Module.projective_of_localization_maximal fun P hP => ?_
  haveI : IsLocalization.AtPrime (locAt Ω P) P := isLoc hinj P
  haveI : IsLocalizedModule P.primeCompl (LinearMap.id : V →ₗ[R] V) :=
    isLocalizedModule_id P.primeCompl V (locAt Ω P)
  refine proj_transfer P.primeCompl (Rp := locAt Ω P) (M.toLocalized' (locAt Ω P) P.primeCompl LinearMap.id) ?_
  have h := H P
  have e : Submodule.span (locAt Ω P) (M : Set V) = M.localized' (locAt Ω P) P.primeCompl LinearMap.id := by
    rw [Submodule.localized'_eq_span]; simp
  rw [e] at h
  exact h

theorem loc_of_proj (hinj : Function.Injective (algebraMap R Ω)) (M : Submodule R V) [Module.Projective R M]
    (P : Ideal R) [P.IsPrime] : Module.Projective (locAt Ω P) (Submodule.span (locAt Ω P) (M : Set V)) := by
  haveI : IsLocalization.AtPrime (locAt Ω P) P := isLoc hinj P
  haveI : IsLocalizedModule P.primeCompl (LinearMap.id : V →ₗ[R] V) :=
    isLocalizedModule_id P.primeCompl V (locAt Ω P)
  have e : Submodule.span (locAt Ω P) (M : Set V) = M.localized' (locAt Ω P) P.primeCompl LinearMap.id := by
    rw [Submodule.localized'_eq_span]; simp
  rw [e]
  exact Module.projective_of_isLocalizedModule P.primeCompl (M.toLocalized' (locAt Ω P) P.primeCompl LinearMap.id)

omit [Module R V] [IsScalarTower R Ω V] in
theorem proj_of_frame (B : Subring Ω) (S : Subalgebra R Ω) (hB : ∀ x, x ∈ B ↔ x ∈ S) (M : Set V) {r : ℕ}
    (b : Fin r → V) (hb : LinearIndependent Ω b) (e : Submodule.span B (Set.range b) = Submodule.span B M) :
    Module.Projective S (Submodule.span S M) := by
  have hBS : B = S.toSubring := Subring.ext hB
  subst hBS
  have e' : Submodule.span S (Set.range b) = Submodule.span S M := e
  rw [← e']
  have hb' : LinearIndependent S b := hb.restrict_scalars' S
  haveI := Module.Free.of_basis (Module.Basis.span hb')
  infer_instance

end Loc

section Chart

open GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  (D : HTChart A K c p R N V)

theorem pow_mem {x : V} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩; exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩; exact D.om.smul_mem _ hx

theorem om'_stable (a : 𝓞 E) {x : V} (hx : x ∈ D.om') : D.ρΩ a x ∈ D.om' := by
  have : D.om' ≤ D.om'.comap ((D.ρΩ a).restrictScalars A) := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw, e⟩ := D.h_lin a z
      have e' : D.ρΩ a (D.h z) = D.h (a • z) - ((p : A) ^ R) • w := by
        rw [e, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; abel
      change D.ρΩ a (D.h z) ∈ D.om'
      rw [e']
      exact D.om'.sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)) (pow_mem D hw)
    · rintro _ ⟨z, hz, rfl⟩
      change D.ρΩ a (((p : A) ^ R) • z) ∈ D.om'
      rw [LinearMap.map_smul_of_tower]
      exact pow_mem D (D.om_stable a z hz)
  exact this hx

theorem omHT_proj (σ : E →+* K) (hσ : ∀ k, ∃ a : A, algebraMap A K a = σ (dualInt E k))
    [Module.Projective A D.om'] : Module.Projective A (D.omHT σ) := by
  have hle : D.omHT σ ≤ D.om' := by
    rintro _ ⟨x, hx, rfl⟩
    change eigProj D.ρΩ σ x ∈ D.om'
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨a, ha⟩ := hσ k
    rw [← ha, algebraMap_smul]
    exact D.om'.smul_mem a (om'_stable D _ hx)
  refine Module.Projective.of_split (Submodule.inclusion hle)
    (((eigProj D.ρΩ σ).restrictScalars A).restrict (p := D.om') (q := D.omHT σ) fun x hx => ⟨x, hx, rfl⟩) ?_
  ext z
  exact LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp D.ρΩ σ D.om' z.2)

theorem span_eq_of_notMem (hinj : Function.Injective (algebraMap A K)) (𝔮 : Ideal A) [h : 𝔮.IsPrime]
    (hp : (p : A) ∉ 𝔮) :
    Submodule.span (locAt K 𝔮) (D.om' : Set V) = Submodule.span (locAt K 𝔮) (D.om : Set V) := by
  refine le_antisymm (Submodule.span_mono (om'_le D)) (Submodule.span_le.2 fun x hx => ?_)
  obtain ⟨h0, h1⟩ := inv_mem hinj 𝔮 (v := (p : A) ^ R) fun hh => hp (h.mem_of_pow_mem _ hh)
  have h2 := Submodule.smul_mem (Submodule.span (locAt K 𝔮) (D.om' : Set V)) ⟨_, h1⟩
    (Submodule.subset_span (pow_mem D hx))
  have e : (⟨_, h1⟩ : locAt K 𝔮) • ((p : A) ^ R) • x = x := by
    change (algebraMap A K ((p : A) ^ R))⁻¹ • ((p : A) ^ R) • x = x
    rw [← algebraMap_smul K ((p : A) ^ R) x, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [e] at h2
  exact h2

end Chart

end PositivityTheory.Xgn.SequenceProjection

open PositivityTheory.Xgn.SequenceProjection in
theorem PositivityTheory.Xgn.sequence_projection_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hfree hp A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' _ P
    hN hpt hloc
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have h1 : Module.Projective (CR O y c') P.Dh.om' := by
    refine proj_of_loc hinj _ (by
      haveI := isNoetherian_of_fg_of_noetherian _ P.Dh.om_lat.fg
      exact isNoetherian_submodule.1 this _ (om'_le P.Dh)) fun 𝔮 h𝔮 => ?_
    by_cases hq : (p : CR O y c') ∈ 𝔮
    · obtain ⟨q, hc, hO, hr⟩ := hpt 𝔮 h𝔮
      have hf : InFibre 𝔐.ξ p q := by
        rintro ⟨h0, -, hi⟩
        obtain ⟨u, v, hv, e⟩ := (hr _).1 hi
        apply hv
        have : v = (p : CR O y c') * u := by
          apply Subtype.ext
          have e1 : (((p : CR O y c') * u : CR O y c') : Ω) = (p : Ω) * (u : Ω) := by simp
          rw [e1, ← e, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
        rw [this]
        exact 𝔮.mul_mem_right _ hq
      obtain ⟨U, hU, b, -, hb⟩ := hfree.1 q hf
      obtain ⟨hli, hsp⟩ := hb q hf hU
      exact proj_of_frame (regAt 𝔐.ξ q) (locAt Ω 𝔮) hr _ b hli (hsp.symm.trans (hloc q hc hO))
    · rw [span_eq_of_notMem P.Dh hinj 𝔮 hq]
      haveI := P.Dh.om_proj
      exact loc_of_proj hinj _ 𝔮
  refine ⟨h1, fun t σ _ => omHT_proj P.Dh σ fun k => ?_⟩
  obtain ⟨hint, x, hx, o, ho⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
  obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x hx k
  obtain ⟨o', ho'⟩ := hint z
  refine ⟨algebraMap O _ (o * o'), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, map_mul, ho', hz, map_mul, ← _root_.mul_assoc, ho, _root_.one_mul]
