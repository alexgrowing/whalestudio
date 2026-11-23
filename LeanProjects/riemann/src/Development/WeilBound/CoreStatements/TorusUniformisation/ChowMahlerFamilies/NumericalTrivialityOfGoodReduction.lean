import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGenericAgree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullbackStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AdaptedEigenbasisExists

noncomputable section

namespace PositivityTheory.Xgn.NumericalTriviality

section Germ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

theorem germ_degZero_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [Algebra O Ω] (O' : Type) [CommRing O'] (s : X ⟶ Sp O') [IsSeparated s] [LocallyOfFiniteType s] (p : ℕ) (σ : E →+* Ω), p.Prime → Function.Injective (algebraMap O Ω) → (∀ (q : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ q) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (p : Ω) := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ 𝓗 O _ _ O' _ s _ _ p σ hp hinj hreg hξ hpow hgive hfib hcard hrange
    u hu hsp Γ
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ : ∀ (q : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ q := fun q a => by
    obtain ⟨o, ho⟩ := hrange σ a
    exact ho ▸ hreg q o
  let τ : ∀ q : Cpt ξ, 𝓞 E →+* X.presheaf.stalk q.1 := fun q =>
    (GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q).symm.toRingHom.comp
      ((σ.comp (algebraMap (𝓞 E) E)).codRestrict (regAt ξ q) (hσ q))
  have hτ : ∀ (q : Cpt ξ) (a : 𝓞 E), genMap ξ q (τ q a) = σ (a : E) := fun q a => by
    have := GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv_coe ξ hξ q (τ q a)
    rw [← this]
    simp [τ]
  let q0 : Cpt ξ := ⟨centre Γ.η, Γ.η_spec⟩
  let qi : Γ.C.I → Cpt ξ := fun i => ⟨centre (Γ.z i), FibreCurve.z_spec Γ i⟩
  let v0 : X.presheaf.stalk q0.1 →+* Γ.κ := (Scheme.stalkClosedPointTo Γ.η).hom
  let vi : ∀ i, X.presheaf.stalk (qi i).1 →+* (Γ.C.v i).valuationSubring :=
    fun i => (Scheme.stalkClosedPointTo (Γ.z i)).hom
  have hpκ : (p : Γ.κ) = 0 := by
    obtain ⟨hh, s0, hs0, hs1⟩ := Γ.η_zero
    have e : (p : X.presheaf.stalk q0.1) = s0 := hξ.inj q0 ((map_natCast _ p).trans hs0.symm)
    have h3 := congrArg v0 e
    rw [map_natCast] at h3
    exact h3.trans hs1
  haveI : CharP Γ.κ p := (CharP.charP_iff_prime_eq_zero hp).2 hpκ
  obtain ⟨F, hF0, hFi⟩ := GlobalTheory.T.fibre_curve_germ_powers E H hstar X t Ω ξ d M S O' s _ p Γ hξ hpow hfib
  choose hFB φ' ψ' lam' he hφ hψ hlam using hFi
  choose xs A hxs hfr hpr using GlobalTheory.T.hodge_lattice_germ_eigen E H X t Ω ξ d r M S ρ 𝓗 σ u hξ hgive hσ hu hsp
  have hdet := fun q => (GlobalTheory.T.hodge_lattice_span_independent X Ω ξ E (Fin d → Ω) M.lat ρ H.bar r 𝓗 σ u hσ hu hsp).2.2 q (A q) (hfr q)
  choose Mt hAM hMt using fun i => exists_trans S hgive σ (qi i) q0 (FibreCurve.generic_centre_specializes Γ i) (τ q0) (hτ q0)
    (he i) (hxs q0) hu (hpr (qi i)) (hpr q0)
  let χ : 𝓞 E →+* Γ.κ := v0.comp (τ q0)
  have hsq : ∀ i, ((Γ.C.v i).valuationSubring.subtype).comp (vi i) =
      v0.comp (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom := fun i => by
    have key := ProjectiveLinePlaces.stalk_square (FibreCurve.generic_centre_specializes Γ i) (Scheme.stalkClosedPointTo (Γ.z i))
      (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
        (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
    exact RingHom.ext fun s => (congrArg (fun g => g.hom s) key).symm
  have hτs : ∀ i a, (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom (τ (qi i) a) = τ q0 a :=
    fun i a => hξ.inj q0 ((ProjectiveLinePlaces.genMap_specializes (FibreCurve.generic_centre_specializes Γ i) q0.2 (qi i).2 _).trans
      ((hτ (qi i) a).trans (hτ q0 a).symm))
  have hχ : ∀ i a, Γ.C.v i (χ a) ≤ 1 := fun i a => by
    have e : χ a = ((vi i (τ (qi i) a) : (Γ.C.v i).valuationSubring) : Γ.κ) :=
      (congrArg v0 (hτs i a).symm).trans (RingHom.congr_fun (hsq i) (τ (qi i) a)).symm
    rw [e]
    exact (vi i (τ (qi i) a)).2
  let x₀ : Fin r → (Fin d → Γ.κ) × (Fin d → Γ.κ) := fun l => vmap v0 (xs q0 l)
  let x : ∀ i : Γ.C.I, Fin r → (Fin d → (Γ.C.v i).valuationSubring) × (Fin d → (Γ.C.v i).valuationSubring) :=
    fun i j => vmap (vi i) (xs (qi i) j)
  let N : Γ.C.I → Matrix (Fin r) (Fin r) Γ.κ := fun i => (Mt i).map v0
  have hx₀ : IsHBasis F.B x₀ := GlobalTheory.T.intersection_second E _ _ v0 d r _ _ _ hF0 (hxs q0)
  have hx : ∀ i, IsHBasis (F.Bi i) (x i) := fun i => GlobalTheory.T.intersection_second E _ _ (vi i) d r _ _ _ (hFB i) (hxs (qi i))
  have hrel : ∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (Γ.C.v i).valuationSubring.subtype (x i j)) -
      ∑ l, N i j l • x₀ l ∈ eigW F.B χ := fun i j => by
    have h1 := vmap_mem_eigW hF0 (τ q0) (hMt i j)
    have h2 := vmap_rel v0 (vi i) (Γ.C.v i).valuationSubring.subtype _ (hsq i) (φ' i) (ψ' i) (lam' i)
      (xs (qi i) j) (Mt i j) (xs q0)
    rw [hφ i, hψ i, hlam i]
    exact h2 ▸ h1
  obtain ⟨hne, hfin, hsum⟩ := GlobalTheory.T.valuation_bounded_frame E Γ.κ Γ.C p d r F χ
    (GlobalTheory.T.charpoly_splits_of_embeddings E Ω O Γ.κ (v0.comp ((GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q0).symm.toRingHom.comp
      ((algebraMap O Ω).codRestrict (regAt ξ q0) (hreg q0)))) hinj hcard hrange) hχ x₀ x N hx₀ hx hrel
  have hNdet : ∀ i, (N i).det = v0 (Mt i).det := fun i => (RingHom.map_det v0 (Mt i)).symm
  have hAdet : ∀ i, (A (qi i)).det = genMap ξ q0 (Mt i).det * (A q0).det := fun i => by
    rw [hAM i, Matrix.det_mul]
    exact congrArg (· * (A q0).det) (RingHom.map_det (genMap ξ q0) (Mt i)).symm
  have hunit : ∀ i, IsUnit (Mt i).det := fun i => by
    have h1 : IsUnit (v0 (Mt i).det) := isUnit_iff_ne_zero.2 (hNdet i ▸ hne i)
    haveI : IsLocalHom v0 := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo Γ.η).hom)
    exact (isUnit_map_iff v0 _).1 h1
  refine ⟨(A q0).det, fun i => (A (qi i)).det, fun i => ((N i).det)⁻¹, hdet q0,
    fun i => ⟨FibreCurve.z_spec Γ i, hdet (qi i)⟩, fun i => ⟨inv_ne_zero (hne i), ?_⟩, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hunit i
    have hw0 : genMap ξ q0 (w : X.presheaf.stalk q0.1) * genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hv0 : v0 (w : X.presheaf.stalk q0.1) * v0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨Γ.η_spec, ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1), ?_, ?_⟩
    · have e0 := (hdet q0).1
      have e1 : (A (qi i)).det = genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det :=
        (hAdet i).trans (congrArg (fun z => genMap ξ q0 z * (A q0).det) hw.symm)
      have e2 : genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) =
          (A q0).det / (genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det) := by
        generalize genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = b at hw0
        generalize genMap ξ q0 (w : X.presheaf.stalk q0.1) = a at hw0
        have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hw0
        rw [eq_div_iff (mul_ne_zero ha e0)]
        linear_combination (A q0).det * hw0
      exact e2.trans (congrArg ((A q0).det / ·) e1.symm)
    · have e3 : (N i).det = v0 (w : X.presheaf.stalk q0.1) := (hNdet i).trans (congrArg v0 hw.symm)
      exact (eq_inv_of_mul_eq_one_right hv0).trans (congrArg (·⁻¹) e3.symm)
  · refine hfin.subset fun i hi h1 => hi ?_
    rw [map_inv₀, h1, inv_one]
  · have : ∀ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i ((N i).det)⁻¹)) =
        (Γ.C.w i : ℤ) * WithZero.log (Γ.C.v i (N i).det) := fun i => by
      rw [map_inv₀, WithZero.log_inv, neg_neg]
    simp only [this]
    exact hsum

end Germ

section Agree

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.QuotEig GlobalTheory.CompanionTheory.Ar.Flat.GenAgree

theorem eigProj_mem_dual {K : Type} [Field K] {A : Subring K} {W : Type} [AddCommGroup W] [Module K W]
    {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K W} {Y : Submodule A W} {N : ℕ} {t : Fin N → W}
    (h : HT.IsFreeOn ρ Y t) (σ : E →+* K) (hσ : ∀ k, σ (HT.dualInt E k) ∈ A) {y : W} (hy : y ∈ Y) :
    HT.eigProj ρ σ y ∈ Y := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Y.smul_mem (⟨_, hσ k⟩ : A) (act_mem_of_free h _ hy)

theorem quot_eig_dual : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (x : Cpt ξ), (∀ k, σ (HT.dualInt E k) ∈ regAt ξ x) → (∀ y, y ∈ 𝓗.quot σ x ↔ y ∈ 𝓗.HL x ∧ y ∈ HT.eigSp 𝓗.ρH σ) ∧ (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) ∧ (𝓗.quot σ x).map ((LinearMap.fst Ω V (Module.Dual Ω V)).restrictScalars (regAt ξ x)) = (L.inter (HT.eigSp ρ σ)) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ x hσ
  obtain ⟨U, hU, t, ht⟩ := 𝓗.free x
  have hfree := ht x hU
  have hstab : ∀ {h}, h ∈ 𝓗.HL x → HT.eigProj 𝓗.ρH σ h ∈ 𝓗.HL x := fun hh =>
    eigProj_mem_dual hfree σ hσ hh
  refine ⟨fun y => ⟨?_, ?_⟩, fun z hz => ?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hstab hh, HT.LatBasic.eigProj_mem _ _ _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, HT.LatBasic.eigProj_of_mem h2⟩
  · obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
    exact (mem_L_iff 𝓗 x).2 ⟨_, hstab hh, fst_eigProj 𝓗 σ h⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      have e : (HT.eigProj 𝓗.ρH σ h).1 = HT.eigProj ρ σ h.1 := fst_eigProj 𝓗 σ h
      refine ⟨(mem_L_iff 𝓗 x).2 ⟨_, hstab hh, rfl⟩, ?_⟩
      change (HT.eigProj 𝓗.ρH σ h).1 ∈ HT.eigSp ρ σ
      rw [e]
      exact HT.LatBasic.eigProj_mem _ _ _
    · rintro ⟨hz, hz'⟩
      obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
      refine ⟨HT.eigProj 𝓗.ρH σ h, ⟨h, hh, rfl⟩, ?_⟩
      exact (fst_eigProj 𝓗 σ h).trans (HT.LatBasic.eigProj_of_mem hz')

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Key
variable [CharZero Ω] {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  [FiniteDimensional Ω V] {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {p q : ℕ}

theorem key_dual (𝓗 : HodgeLat L ρ bar (p + q)) {σ σ' : E →+* Ω} {v : Fin p → V} {w : Fin q → V}
    {u : Fin (p + q) → V × Module.Dual Ω V} {x : Cpt ξ}
    (h1 : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (h2 : ∀ a, bar (bar a) = a)
    (hreg : ∀ k, σ (HT.dualInt E k) ∈ regAt ξ x ∧ σ' (HT.dualInt E k) ∈ regAt ξ x)
    (hv : LinearIndependent Ω v) (hvs : Submodule.span Ω (Set.range v) = HT.eigSp ρ σ)
    (hw : LinearIndependent Ω w) (hws : Submodule.span Ω (Set.range w) = HT.eigSp ρ σ')
    (had : IsAdapted 𝓗.ρH σ v w u) {P : Matrix (Fin p) (Fin p) Ω} {Q : Matrix (Fin q) (Fin q) Ω}
    (hP : (L.inter (HT.eigSp ρ σ)).IsFrameAt (fun i => ∑ j, P i j • v j) x)
    (hQ : (L.inter (HT.eigSp ρ σ')).IsFrameAt (fun i => ∑ j, Q i j • w j) x) :
    ∃ A : Matrix (Fin (p + q)) (Fin (p + q)) Ω, (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) x ∧
      A.det = P.det / Q.det := by
  classical
  obtain ⟨huli, husp, hinv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  obtain ⟨hq, -, hmap⟩ := quot_eig_dual X Ω ξ E V L ρ bar (p + q) 𝓗 σ x (fun a => (hreg a).1)
  obtain ⟨-, hL', -⟩ := quot_eig_dual X Ω ξ E V L ρ bar (p + q) 𝓗 σ' x (fun a => (hreg a).2)
  have hP0 := det_ne_zero_of_li hv hP.1
  have hQ0 := det_ne_zero_of_li hw hQ.1
  have hdual : ∀ φ : Module.Dual Ω V, ((0 : V), φ) ∈ 𝓗.HL x ↔ φ ∈ L.dual x := fun φ => by
    rw [← congrFun 𝓗.comap_inr x]
    rfl
  let C : Matrix (Fin q) (Fin q) Ω := (Q.transpose)⁻¹
  have hCQ : C * Q.transpose = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hQ0)
  have hCd : C.det * Q.det = 1 := by
    have := congrArg Matrix.det hCQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hC0 : C.det ≠ 0 := left_ne_zero_of_mul_eq_one hCd
  let φ : Fin q → Module.Dual Ω V := fun k => (u (Fin.natAdd p k)).2
  let ψ : Fin q → Module.Dual Ω V := fun j => ∑ k, C j k • φ k
  let b : Fin q → V := fun l => ∑ m, Q l m • w m
  let c : Fin q → V × Module.Dual Ω V := fun j => ∑ k, C j k • u (Fin.natAdd p k)
  have hc : ∀ j, c j = ((0 : V), ψ j) := fun j => by
    refine Prod.ext ?_ ?_
    · simp only [c, Prod.fst_sum, Prod.smul_fst, (had.2.2 _).1, smul_zero, Finset.sum_const_zero]
    · simp only [c, ψ, φ, Prod.snd_sum, Prod.smul_snd]
  have hceig : ∀ j, c j ∈ HT.eigSp 𝓗.ρH σ := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (had.1 _)
  have hψinv : ∀ j, ψ j ∘ₗ HT.eigProj ρ σ' = ψ j := fun j => hinv (ψ j) (hc j ▸ hceig j)
  have hψb : ∀ j l, ψ j (b l) = if j = l then 1 else 0 := fun j l => by
    have e1 : ∀ k, φ k (b l) = Q l k := fun k => by
      simp only [b, map_sum, map_smul, φ, (had.2.2 k).2, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp
    have e2 : ψ j (b l) = (C * Q.transpose) j l := by
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, e1, smul_eq_mul, Matrix.mul_apply,
        Matrix.transpose_apply]
    rw [e2, hCQ, Matrix.one_apply]
  have hbsp : Submodule.span Ω (Set.range b) = HT.eigSp ρ σ' := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hws ▸ Submodule.subset_span ⟨m, rfl⟩)
    · rw [finrank_span_eq_card hQ.1, ← hws, finrank_span_eq_card hw]
  have hbL : ∀ l, b l ∈ L x := fun l => by
    have : b l ∈ (L.inter (HT.eigSp ρ σ')) x := hQ.2 ▸ Submodule.subset_span ⟨l, rfl⟩
    exact this.1
  have hcH : ∀ j, c j ∈ 𝓗.quot σ x := fun j => by
    refine (hq _).2 ⟨?_, hceig j⟩
    rw [hc j, hdual]
    intro z hz
    have e1 : ψ j z = ψ j (HT.eigProj ρ σ' z) := (LinearMap.congr_fun (hψinv j) z).symm
    have e2 : HT.eigProj ρ σ' z ∈ (L.inter (HT.eigSp ρ σ')) x := ⟨hL' z hz, HT.LatBasic.eigProj_mem ρ σ' z⟩
    rw [hQ.2] at e2
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 e2
    rw [e1, ← hr, map_sum]
    refine sum_mem fun l _ => ?_
    have e3 : ψ j ((r l) • b l) = (r l : Ω) * ψ j (b l) := by
      change ψ j ((r l : Ω) • b l) = _
      rw [map_smul, smul_eq_mul]
    rw [e3, hψb]
    split_ifs
    · simpa using (r l).2
    · simp
  have hker : ∀ y ∈ 𝓗.quot σ x, LinearMap.fst Ω V (Module.Dual Ω V) y = 0 →
      y ∈ Submodule.span (regAt ξ x) (Set.range c) := by
    rintro ⟨y₁, θ⟩ hy hy0
    obtain rfl : y₁ = 0 := hy0
    obtain ⟨hyH, hye⟩ := (hq _).1 hy
    have hθ := hinv θ hye
    have hθL := (hdual θ).1 hyH
    have hreg' : ∀ j, θ (b j) ∈ regAt ξ x := fun j => hθL _ (hbL j)
    have e : ((0 : V), θ) = ∑ j, (⟨θ (b j), hreg' j⟩ : regAt ξ x) • c j := by
      have e0 : ∀ j, (⟨θ (b j), hreg' j⟩ : regAt ξ x) • c j = θ (b j) • c j := fun j => rfl
      simp only [e0, hc]
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        refine LinearMap.ext fun z => ?_
        have hz : HT.eigProj ρ σ' z ∈ Submodule.span Ω (Set.range b) := hbsp ▸ HT.LatBasic.eigProj_mem ρ σ' z
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
        have e1 : θ z = θ (HT.eigProj ρ σ' z) := (LinearMap.congr_fun hθ z).symm
        have e2 : ∀ j, ψ j z = d j := fun j => by
          have : ψ j z = ψ j (HT.eigProj ρ σ' z) := (LinearMap.congr_fun (hψinv j) z).symm
          rw [this, ← hd, map_sum]
          simp [hψb]
        rw [e1, ← hd, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [LinearMap.smul_apply, map_smul, e2, smul_eq_mul]
        exact mul_comm _ _
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨A, hAd, hAl, hAs⟩ := GlobalTheory.CompanionTheory.Ggeo.ext_frame_of_quotient_kernel Ω (V × Module.Dual Ω V) V (regAt ξ x) (𝓗.quot σ x)
    (LinearMap.fst Ω V (Module.Dual Ω V)) p q u v P C huli hv (fun y hy => husp ▸ ((hq y).1 hy).2)
    (fun i => had.2.1 i) (fun j => (had.2.2 j).1) hP0 hC0 (hmap.trans hP.2) hcH hker
  refine ⟨A, ⟨hAl, hAs⟩, ?_⟩
  rw [hAd, eq_div_iff hQ0, mul_assoc, hCd, mul_one]

end Key

end Agree

section Line

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.GenAgree

theorem dualInt_mem {K E : Type} [Field K] [Field E] [NumberField E] (A : Subring K) (σ : E →+* K)
    (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ A) (hd : ((NumberField.discr E : ℤ) : K)⁻¹ ∈ A) (k) : σ (HT.dualInt E k) ∈ A := by
  classical
  let T := Algebra.traceMatrix ℤ (RingOfIntegers.basis E)
  have h1 : ∀ j, (integralBasis E j : E) = ∑ l, ((T j l : ℤ) : E) * HT.dualInt E l := fun j => by
    conv_lhs => rw [← ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)).sum_repr
      (integralBasis E j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.smul_def]
    congr 1
    have : (Algebra.traceForm ℚ E) (integralBasis E j) (integralBasis E l) = ((T j l : ℤ) : ℚ) := by
      simp only [T, Algebra.traceMatrix_apply, Algebra.traceForm_apply, integralBasis_apply]
      rw [Algebra.coe_trace_int, ← map_mul]
    rw [this, map_intCast]
  have h2 : ((NumberField.discr E : ℤ) : E) * HT.dualInt E k =
      ∑ j, ((T.adjugate k j : ℤ) : E) * integralBasis E j := by
    simp only [h1, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← Int.cast_mul, ← Int.cast_sum, ← Matrix.mul_apply, Matrix.adjugate_mul]
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rfl
    · intro l _ hl
      simp [Matrix.one_apply_ne hl.symm]
    · simp
  have h0 : ((NumberField.discr E : ℤ) : K) ≠ 0 := by
    rw [← map_intCast σ, map_ne_zero]
    exact_mod_cast NumberField.discr_ne_zero E
  have h3 := congrArg σ h2
  rw [map_mul, map_intCast, map_sum] at h3
  rw [← inv_mul_cancel_left₀ h0 (σ (HT.dualInt E k)), h3]
  refine mul_mem hd (sum_mem fun j _ => ?_)
  rw [map_mul, map_intCast, integralBasis_apply]
  exact mul_mem (intCast_mem A _) (hσ _)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_of_not_dvd {p : ℕ} (hp : p.Prime) {x : Cpt ξ} (hx : InFibre ξ p x) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    unitAt ξ x (n : Ω) := by
  haveI : IsLocalRing (regAt ξ x) := EigSplit.isLocalRing_regAt x
  have key : ∀ m : ℤ, IsUnit (m : regAt ξ x) → unitAt ξ x (m : Ω) := fun m hm => by
    obtain ⟨c, hc⟩ := hm.exists_right_inv
    have h1 : (m : Ω) * (c : Ω) = 1 := by simpa using congrArg (regAt ξ x).subtype hc
    exact ⟨left_ne_zero_of_mul_eq_one h1, intCast_mem _ _, by rw [← eq_inv_of_mul_eq_one_right h1]; exact c.2⟩
  obtain ⟨u, v, h⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hn)
  have h' : (u : regAt ξ x) * ((p : ℤ) : regAt ξ x) + (v : regAt ξ x) * (n : regAt ξ x) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ x) h
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h' with h1 | h1
  · exact absurd (by simpa using key _ (isUnit_of_mul_isUnit_right h1)) hx
  · exact key _ (isUnit_of_mul_isUnit_right h1)

variable {V : Type} [AddCommGroup V] [Module Ω V]

theorem lineLat_gen {A B : Lat ξ V} {p q : ℕ} {a : ⋀[Ω]^p V} {b : ⋀[Ω]^q V} (ha : a ≠ 0) (hb : b ≠ 0) {x : Cpt ξ}
    {f : Ω} (h : IsCoeffAt A B p q a b x f) : (lineLat A B p q a b).IsGenAt x f⁻¹ := by
  have h' := h
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  have hf : f ≠ 0 := left_ne_zero_of_mul (e ▸ hβ)
  refine ⟨inv_ne_zero hf, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f', ⟨α', β', hα', hβ', hA', hB', e'⟩, rfl⟩
    obtain ⟨y, hy, e1⟩ := ZUnit.exists_of_span_eq (p := x) (smul_ne_zero hα' ha) (hA'.symm.trans hA)
    obtain ⟨z, hz, e2⟩ := ZUnit.exists_of_span_eq (p := x) (smul_ne_zero hβ' hb) (hB'.symm.trans hB)
    rw [smul_smul] at e1 e2
    have e3 := smul_left_injective Ω ha e1
    have e4 := smul_left_injective Ω hb e2
    have hf' : f' ≠ 0 := left_ne_zero_of_mul (e' ▸ hβ')
    refine Submodule.mem_span_singleton.2 ⟨⟨y * z⁻¹, mul_mem hy.2.1 hz.2.2⟩, ?_⟩
    change y * z⁻¹ * f⁻¹ = f'⁻¹
    have hz0 := hz.1
    have : f' * y = z * f := by
      apply mul_right_cancel₀ hα
      rw [mul_assoc, mul_assoc, ← e3, e', e, e4]
    field_simp
    linear_combination this
  · exact Submodule.span_mono (by rintro _ rfl; exact ⟨f, h', rfl⟩)

theorem exists_frame_matrix {A : Lat ξ V} {r : ℕ} {W : Submodule Ω V} (hA : A.IsVB r W) {v : Fin r → V}
    (hv : Submodule.span Ω (Set.range v) = W) (x : Cpt ξ) :
    ∃ P : Matrix (Fin r) (Fin r) Ω, A.IsFrameAt (fun i => ∑ j, P i j • v j) x := by
  obtain ⟨U, hU, b, hb, h⟩ := hA x trivial
  have h1 : ∀ i, b i ∈ Submodule.span Ω (Set.range v) := fun i => by
    rw [hv, ← hb]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h1 i)
  exact ⟨Matrix.of P, by simpa only [Matrix.of_apply, hP] using h x trivial hU⟩

theorem exists_basis_of_wedge {A : Lat ξ V} {r : ℕ} {W : Submodule Ω V} (hA : A.IsVB r W) {a : ⋀[Ω]^r V} (ha : a ≠ 0)
    {x : Cpt ξ} {α : Ω} (hα : α ≠ 0) (h : A.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ (v : Fin r → V) (c : Ω), LinearIndependent Ω v ∧ Submodule.span Ω (Set.range v) = W ∧ c ≠ 0 ∧
      exteriorPower.ιMulti Ω r v = c • a := by
  obtain ⟨U, hU, v, hv, h1⟩ := hA x trivial
  have h2 := h1 x trivial hU
  rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ V _ r _ x h2] at h
  obtain ⟨y, hy, e⟩ := ZUnit.exists_of_span_eq (p := x) (smul_ne_zero hα ha) h.symm
  refine ⟨v, y⁻¹ * α, h2.1, hv, mul_ne_zero (inv_ne_zero hy.1) hα, ?_⟩
  rw [mul_smul, e, inv_smul_smul₀ hy.1]

theorem numTriv_of_degZero [CharZero Ω] {E : Type} [Field E] [NumberField E] {L A B : Lat ξ V}
    {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {p q : ℕ} (𝓗 : HodgeLat L ρ bar (p + q)) {σ σ' : E →+* Ω}
    (hξ : IsCptGen ξ) (h1 : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (h2 : ∀ a, bar (bar a) = a)
    (hσ : ∀ x (a : 𝓞 E), σ (a : E) ∈ regAt ξ x) {r : ℕ} (hr : r.Prime) (hd : ¬ (r : ℤ) ∣ NumberField.discr E)
    (hA : A.IsVB p (HT.eigSp ρ σ)) (hB : B.IsVB q (HT.eigSp ρ σ'))
    (eA : ∀ x, InFibre ξ r x → A x = L.inter (HT.eigSp ρ σ) x)
    (eB : ∀ x, InFibre ξ r x → B x = L.inter (HT.eigSp ρ σ') x)
    (hz : 𝓗.DegZero σ (r : Ω)) {a : ⋀[Ω]^p V} {b : ⋀[Ω]^q V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∃ x f, IsCoeffAt A B p q a b x f) : NumTrivMod (lineLat A B p q a b) (r : Ω) := by
  haveI := 𝓗.finiteDimensional
  obtain ⟨x₀, -, α, β, hα, hβ, hwA, hwB, -⟩ := hc
  obtain ⟨v, c, hv, hvs, hc0, ev⟩ := exists_basis_of_wedge hA ha hα hwA
  obtain ⟨w, d, hw, hws, hd0, ew⟩ := exists_basis_of_wedge hB hb hβ hwB
  obtain ⟨u, had, hu, hus⟩ := PositivityTheory.Xgn.adapted_eigenbasis_exists E Ω V ρ 𝓗.ρH bar σ σ' p q v w 𝓗.act_fst 𝓗.act_inr
    h1 h2 hv hvs hw hws
  have key : ∀ x, InFibre ξ r x → ∀ s, (detLat (𝓗.quot σ) u).IsGenAt x s →
      (lineLat A B p q a b).IsGenAt x (c / d * s) := by
    intro x hx s hs
    have hdu := (unitAt_of_not_dvd hr hx hd).2.2
    obtain ⟨P, hP⟩ := exists_frame_matrix hA hvs x
    obtain ⟨Q, hQ⟩ := exists_frame_matrix hB hws x
    obtain ⟨N, hN, hNd⟩ := key_dual 𝓗 h1 h2 (x := x)
      (fun k => ⟨dualInt_mem _ σ (hσ x) hdu k, dualInt_mem _ σ' (fun a => h1 a ▸ hσ x _) hdu k⟩)
      hv hvs hw hws had (P := P) (Q := Q) ⟨hP.1, (eA x hx).symm.trans hP.2⟩ ⟨hQ.1, (eB x hx).symm.trans hQ.2⟩
    have hP0 := det_ne_zero_of_li hv hP.1
    have hQ0 := det_ne_zero_of_li hw hQ.1
    refine HodgeDeterminantLattice.isGenAt_mul (HodgeDeterminantLattice.detLat_of_frame hu hN) ?_ hs
    have hco : IsCoeffAt A B p q a b x (c / d * N.det)⁻¹ := by
      refine ⟨P.det * c, Q.det * d, mul_ne_zero hP0 hc0, mul_ne_zero hQ0 hd0, ?_, ?_, ?_⟩
      · rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ V _ p _ x hP, iotaMulti_rows, ev, mul_smul]
      · rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ V _ q _ x hQ, iotaMulti_rows, ew, mul_smul]
      · rw [hNd]; field_simp
    simpa only [inv_inv] using lineLat_gen ha hb hco
  intro Γ
  obtain ⟨e, f, t, he, hf, ht, hfin, hs⟩ := hz u hu hus Γ
  have hη : InFibre ξ r ⟨centre Γ.η, Γ.η_spec⟩ := fun h => by
    obtain ⟨s, hs⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec h
    exact s.ne_zero (CoordModel.valAt_unique hξ hs Γ.η_zero)
  have hzi : ∀ i, InFibre ξ r ⟨centre (Γ.z i), Γ.z_spec i⟩ := fun i h => by
    obtain ⟨s, hs, hv⟩ := Γ.exists_val_of_unitAt i h
    rw [CoordModel.valAt_unique hξ hs Γ.η_zero, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨c / d * e, fun i => c / d * f i, t, key _ hη _ he, fun i => ⟨(hf i).1, key _ (hzi i) _ (hf i).2⟩,
    fun i => by rw [mul_div_mul_left _ _ (div_ne_zero hc0 hd0)]; exact ht i, hfin, hs⟩

end Line

section Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem mem_abLocus_of_map {X Y : Scheme.{0}} {G : Over X} {G' : Over Y} {f : X ⟶ Y} {φ : G.left ⟶ G'.left}
    (h : IsPullback φ G.hom G'.hom f) {x : X} (hx : f x ∈ abLocus G') : x ∈ abLocus G := by
  intro K _ _ t hxt
  obtain ⟨u, rfl⟩ := hxt
  have hp : IsProper (pullback.snd G'.hom (t ≫ f)) := hx K (t ≫ f) ⟨u, by simp⟩
  have sq : IsPullback (pullback.fst G.hom t ≫ φ) (pullback.snd G.hom t) G'.hom (t ≫ f) :=
    (IsPullback.of_hasPullback G.hom t).paste_horiz h
  rw [← sq.isoPullback_hom_snd]
  infer_instance

theorem genPt_max {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (z : X)
    (hz : z ⤳ genPt ξ) : z = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have h1 : z ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hz
  obtain ⟨w, rfl⟩ := h1
  have h2 : w = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    letI := hF.toField
    exact Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) _ _
  rw [h2, Scheme.fromSpecStalk_closedPoint]

theorem eigSp_eq {E : Type} [Field E] [NumberField E] {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : 𝓞 E →+* Module.End Ω V) (s : E →+* Ω) (χ : 𝓞 E →+* Ω) (hχ : ∀ a : 𝓞 E, χ a = s (a : E)) :
    eigSp ρ χ = HT.eigSp ρ s := by
  simp only [eigSp, HT.eigSp, hχ]
  rfl

theorem finrank_of_isVB {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A : Lat ξ V} {r : ℕ} {W : Submodule Ω V} (hA : A.IsVB r W) :
    Module.finrank Ω W = r := by
  obtain ⟨U, hU, b, hb, h⟩ := hA ⟨genPt ξ, specializes_rfl⟩ trivial
  rw [← hb, finrank_span_eq_card (h _ trivial hU).1, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem emb_inl (𝔐 : HodgeCpt Y S y) (τ : CMType H) : 𝔐.emb (.inl τ) = 𝔐.cst.comp (tauIn c τ.1) := rfl

theorem emb_inr (𝔐 : HodgeCpt Y S y) (τ : CMType H) :
    𝔐.emb (.inr τ) = 𝔐.cst.comp (tauIn c (ComplexEmbedding.conjugate τ.1)) :=
  RingHom.ext fun a => congrArg 𝔐.cst (CptHodge.tauIn_conj c τ.1 a).symm

theorem cst_mem (𝔐 : HodgeCpt Y S y) (q : Cpt 𝔐.ξ) (o : 𝓞 c.F) : 𝔐.cst (o : c.F) ∈ regAt 𝔐.ξ q := by
  letI algΩ : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  exact GlobalTheory.T.base_constants_regular 𝔐.X Ω 𝔐.ξ (𝓞 c.F) (𝔐.f ≫ Y.s) 𝔐.cst_over q o

open CptHodge in

theorem exists_hodgeLat (𝔐 : HodgeCpt Y S y)
    (hFibY : ∀ (p : ℕ), p.Prime → ∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z) (p : ℕ) (hp : p.Prime) :
    ∃ 𝓗 : HodgeLat 𝔐.M.lat 𝔐.ρ H.bar (D.p + D.q), ∀ σ : E →+* Ω, 𝓗.DegZero σ (p : Ω) := by
  classical
  letI : StarRing (𝓞 E) := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hgen := 𝔐.tie.gen
  obtain ⟨s₀, hft, hqc, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie
  haveI hprop : IsProper s₀ := LocModel.isProper_of_coordTie 𝔐.all 𝔐.tie s₀
  haveI hLN : IsLocallyNoetherian 𝔐.X := LocallyOfFiniteType.isLocallyNoetherian s₀
  have hFib : ∀ (p : ℕ), p.Prime → ∀ z : 𝔐.X, (p : 𝔐.X.residueField z) = 0 → FibPF 𝔐.t z := fun p hp z hz =>
    (GlobalTheory.T.fibre_power_free_pullback E H _ _ _ 𝔐.t 𝔐.f 𝔐.m z).2 (hFibY p hp _ (by
      rwa [← map_natCast (𝔐.f.residueFieldMap z).hom p, map_eq_zero] at hz))
  haveI : ∀ x : 𝔐.X, _root_.IsReduced (𝔐.X.presheaf.stalk x) := fun x => by
    have := (𝔐.normal x).1
    infer_instance
  have hred : AlgebraicGeometry.IsReduced 𝔐.X := isReduced_of_isReduced_stalk 𝔐.X
  have hf0 : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := by
    have h1 : (𝔐.ξ ≫ 𝔐.f) (IsLocalRing.closedPoint Ω) =
        (Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀) (IsLocalRing.closedPoint Ω) := by rw [𝔐.fn_over]
    exact ((Scheme.Hom.comp_apply 𝔐.ξ 𝔐.f _).symm.trans h1).trans ((Scheme.Hom.comp_apply _ 𝔐.ξ₀ _).trans
      (congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)))
  have hPow : PowFns 𝔐.t := GlobalTheory.T.powFns_of_abelian_generic E H 𝔐.X 𝔐.t hred hLN (fun z hz => by
    rw [← hz _ (𝔐.all z)]
    refine mem_abLocus_of_map 𝔐.m.cart.1 ?_
    rw [hf0]
    exact generic_mem_abLocus (O := 𝓞 c.F) Y _ (genPt_max 𝔐.gen₀))
  obtain ⟨hcard, hfac⟩ := emb_factor (E := E) c 𝔐.cst
  have facts : ∀ τ' : E →+* ℂ, τ' (H.rt : E) = H.rt0 →
      Module.finrank Ω (eigSp 𝔐.ρ (𝔐.cst.comp (tauIn c τ'))) = D.p ∧
      Module.finrank Ω (eigSp 𝔐.ρ (𝔐.cst.comp (tauIn c (ComplexEmbedding.conjugate τ')))) = D.q := fun τ' h =>
    ⟨finrank_of_isVB (𝔐.vb (.inl ⟨τ', h⟩)), by
      rw [← emb_inr 𝔐 ⟨τ', h⟩]
      exact finrank_of_isVB (𝔐.vb (.inr ⟨τ', h⟩))⟩
  obtain ⟨d, M, ⟨G⟩⟩ := GlobalTheory.T.exists_germ_system E H hstar 𝔐.X 𝔐.t Ω 𝔐.ξ hPow hgen
  obtain ⟨e, he, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv 𝔐.X 𝔐.t.G Ω 𝔐.ξ (Fin d → Ω) 𝔐.Li M 𝔐.M
  let ρ' : 𝓞 E →+* Module.End Ω (Fin d → Ω) := (e.symm.conjRingEquiv : _ ≃+* _).toRingHom.comp 𝔐.ρ
  have hρ' : ∀ a v, e (ρ' a v) = 𝔐.ρ a (e v) := fun a v => by
    simp [ρ', LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
  have hact : M.IsActOf 𝔐.t.act.act ρ' := fun a v => by
    rw [← he, hρ', 𝔐.act a (e v), he]
  have hrho : ∀ a v, ρ' a v = (rho G.g₀.B a).mulVec v := fun a v => M.inj (by rw [G.act₀, hact a v])
  have hsum : ∀ s s' : E →+* Ω, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) →
      Module.finrank Ω (HT.eigSp ρ' s) + Module.finrank Ω (HT.eigSp ρ' s') = D.p + D.q := by
    intro s s' hss
    obtain ⟨τ', hτ'⟩ := hfac s
    have h1 := finrank_eig e ρ' 𝔐.ρ hρ' s (𝔐.cst.comp (tauIn c τ')) fun a => (hτ' a).symm
    have h2 := finrank_eig e ρ' 𝔐.ρ hρ' s' (𝔐.cst.comp (tauIn c (ComplexEmbedding.conjugate τ'))) fun a => by
      rw [hss, hτ', hstar, RingHom.comp_apply, tauIn_conj]
    rw [h1, h2]
    rcases rt_cases (H := H) τ' with h | h
    · obtain ⟨e1, e2⟩ := facts τ' h
      rw [e1, e2]
    · obtain ⟨e1, e2⟩ := facts _ h
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ') = τ' := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [hcc] at e2
      rw [e1, e2, add_comm]
  have hC : HChar G.g₀.B (D.p + D.q) := GlobalTheory.T.hermitian_signature_character E Ω d (D.p + D.q) G.g₀.B ρ' hrho hcard hsum
  have hfree := GlobalTheory.T.germ_system_height_free E H hstar 𝔐.X 𝔐.t Ω 𝔐.ξ d (D.p + D.q) M G hPow hgen hC
    (fun q p' hp' h => hFib p' hp' q.1 h)
  obtain ⟨𝓗, hG⟩ := GlobalTheory.T.exists_hodge_lattice_germ_system E H hstar 𝔐.X 𝔐.t Ω 𝔐.ξ d (D.p + D.q) M G ρ' hgen hact hfree
  letI algΩ : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hint : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap (𝓞 c.F) Ω).range := by
    intro s' a
    obtain ⟨τ', hτ'⟩ := hfac s'
    have h1 : IsIntegral ℤ (tauIn c τ' a) :=
      (RingOfIntegers.isIntegral a).map (tauIn c τ').toIntAlgHom
    exact ⟨⟨tauIn c τ' a, h1⟩, (hτ' a).symm⟩
  have hdeg : ∀ σ : E →+* Ω, 𝓗.DegZero σ (p : Ω) := fun σ =>
    germ_degZero_prime E H hstar 𝔐.X 𝔐.t Ω 𝔐.ξ d (D.p + D.q) M G ρ' 𝓗 (𝓞 c.F) ℤ s₀ p σ hp
      (𝔐.cst.injective.comp RingOfIntegers.coe_injective) (cst_mem 𝔐) hgen
      hPow hG (fun q h => hFib p hp q.1 h) hcard hint
  have htr := GlobalTheory.T.hodge_lattice_transport_equiv 𝔐.X Ω 𝔐.ξ E (Fin d → Ω) 𝔐.Li e M.lat ρ' 𝔐.ρ H.bar (D.p + D.q) 𝓗 hρ'
  rw [lat_map M 𝔐.M e he] at htr
  obtain ⟨𝓗', h'⟩ := htr
  exact ⟨𝓗', fun σ => h' σ _ (hdeg σ)⟩

end Model

end PositivityTheory.Xgn.NumericalTriviality

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open PositivityTheory.Xgn.NumericalTriviality in
theorem PositivityTheory.Xgn.numerical_triviality_of_good_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (τ : CMType H) (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) → NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω) := by
  intro E _ _ _ H D Xo Yl hY l c hg Y hdom S Ω _ K _ J _ y 𝔐 p hp hpS hdisc τ a b ha hb hc
  obtain ⟨-, hFib⟩ := GlobalTheory.T.global_model_power_free E H D Xo Yl hY l c hg Y hdom
  obtain ⟨𝓗, hz⟩ := exists_hodgeLat 𝔐 hFib p hp
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F.toSubfield (c.conj τ.1))
  let σ' : E →+* Ω := 𝔐.cst.comp ((ComplexEmbedding.conjugate τ.1).codRestrict c.F.toSubfield (c.conj _))
  have e1 : GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (.inl τ)) = HT.eigSp 𝔐.ρ σ := eigSp_eq _ _ _ fun _ => rfl
  have e2 : GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (.inr τ)) = HT.eigSp 𝔐.ρ σ' := eigSp_eq _ _ _ fun a => by
    rw [emb_inr]
    rfl
  have hV : ∀ s x, InFibre 𝔐.ξ p x → 𝔐.V s x = 𝔐.M.lat.inter (GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb s)) x := fun s x hx =>
    Lat.patch_of_not S _ _ fun r hr h => h (by
      have := unitAt_of_not_dvd hp hx (n := (r : ℤ)) fun hd => hpS
        (((Nat.prime_dvd_prime_iff_eq hp (𝔐.S_prime r hr)).1 (by exact_mod_cast hd)) ▸ hr)
      simpa using this)
  refine numTriv_of_degZero 𝓗 (σ := σ) (σ' := σ') 𝔐.tie.gen
    (fun a => congrArg 𝔐.cst (CptHodge.tauIn_conj c τ.1 a)) (fun a => ?_) (fun x a => ?_) hp hdisc
    (e1 ▸ 𝔐.vb (.inl τ)) (e2 ▸ 𝔐.vb (.inr τ)) (fun x hx => e1 ▸ hV _ x hx) (fun x hx => e2 ▸ hV _ x hx) (hz σ) ha hb hc
  · apply RingOfIntegers.coe_injective
    change ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  · exact cst_mem 𝔐 x ⟨GlobalTheory.CompanionTheory.Ar.Fl.tauIn c τ.1 a,
      (RingOfIntegers.isIntegral a).map (GlobalTheory.CompanionTheory.Ar.Fl.tauIn c τ.1).toIntAlgHom⟩
