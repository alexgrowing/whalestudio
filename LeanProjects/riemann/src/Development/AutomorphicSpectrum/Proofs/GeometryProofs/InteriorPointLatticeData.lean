import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEmbLabel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannLatticeOverPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodRiemannLatticeFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinates
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnif
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx

open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx GlobalTheory.CompanionTheory.Ar.Flat.PerGram

section Tangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem surjective_of_add_mem {g₀ : ℕ} (Λ : Submodule ℤ (Fin g₀ → ℂ)) (hd : DiscreteTopology Λ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g₀ → ℂ)) (h : ∀ y, ∃ z, y - F z ∈ Λ) : Function.Surjective F := by
  have hc : (Λ : Set (Fin g₀ → ℂ)).Countable := by
    haveI := hd
    have : Countable Λ := countable_of_Lindelof_of_discrete
    exact Set.countable_coe_iff.1 this
  intro y
  have h0 : (LinearMap.range F).mkQ y = 0 := by
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hc.image (LinearMap.range F).mkQ) fun s => ?_
    obtain ⟨z, hz⟩ := h (s • y)
    refine ⟨_, hz, ?_⟩
    simp only [map_sub, map_smul, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range F)).2 ⟨z, rfl⟩, sub_zero]
  simpa using h0

theorem exists_isDiff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} (t' : SAB H (Sp ℂ)) (m : SABMap t' t z) (hP : IsProper t'.G.hom)
    (hA : Out.RelAmple t'.G t'.PP.L) {φ : A.left ⟶ t.G.left} (hp : IsGrpPullback A t.G z φ) (u : HolUnif A L g)
    {x : epsR ℂ ⟶ A} (hx : IsTangent x) : ∃ w, u.IsDiff w x := by
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g₀, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif t'.G t'.PP.L g₀ hab hA hg
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ _ g₀ u₀ hc
  obtain ⟨e, hmon, -⟩ := grpPullback_iso hp m.cart
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun w => (u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo t'.G hab _ g₀ g u₀ ht₁ ht₂
    (fun w => u.ex w ≫ e.hom) (fun p q => by rw [u.ex_add, MonObj.mul_comp]) hol
  have hF' : ∀ w, u₀.ex (F w) = u.ex w ≫ e.hom := hF
  have hsurj : Function.Surjective F := surjective_of_add_mem u₀.Λ u₀.discrete F fun y => by
    obtain ⟨w, hw⟩ := u.ex_onto (u₀.ex y ≫ e.inv)
    refine ⟨w, (u₀.ker _).1 ?_⟩
    have h1 : u₀.ex (F w) = u₀.ex y := by rw [hF', hw, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h2 := u₀.ex_add (y - F w) (F w)
    rw [sub_add_cancel, h1] at h2
    have h3 : u₀.ex (y - F w) * u₀.ex y = 1 * u₀.ex y := by rw [← h2, _root_.one_mul]
    exact mul_right_cancel h3
  have hxe : IsTangent (x ≫ e.hom) := by
    have h₁ : η[A] ≫ e.hom = η[t'.G] := IsMonHom.one_hom e.hom
    unfold IsTangent at hx ⊢
    rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₁]
  obtain ⟨w₀, hw₀, -⟩ := ht₁ (x ≫ e.hom) hxe
  obtain ⟨w, rfl⟩ := hsurj w₀
  refine ⟨w, ?_⟩
  have a := isDerivAt0_of_isDiff u₀ hxe hw₀
  have b := GlobalTheory.FibreDeriv.isDerivAt0_comp a e.inv.left
  have hol' : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (u₀.ex z).left ≫ e.inv.left) :=
    GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u₀) e.inv.left
  have c := isDerivAt0_comp_linMap hol' F b
  have back : ∀ {T : Over (Sp ℂ)} (q : T ⟶ A), (q ≫ e.hom).left ≫ e.inv.left = q.left := fun q => by
    rw [← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
  have e1 : (fun z => (u₀.ex (F z)).left ≫ e.inv.left) = fun z => (u.ex z).left :=
    funext fun z => by rw [hF', back]
  rw [e1, back] at c
  exact fun U h f => c.2 U h f

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem fibreLatVec_of_fibreLat {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} (hz : HodgeMetric.PolarisedAt t z) (hF : FibreLat t z R) {A₀ : Type}
    (v : A₀ → (epsAt z ⟶ t.G)) (hv : ∀ i, IsTanAt t.G z (v i)) : ∃ x : A₀ → Fin g → ℂ, FibreLatVec t z R x v := by
  obtain ⟨t', m, hP, hA⟩ := hz
  obtain ⟨A, _, φ, u, χ, hp, hAH, hact, hinj, hmem, -⟩ := hF
  have key : ∀ i, ∃ (x : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = (v i).left ∧ u.IsDiff x v' := fun i => by
    let Φ := HodgeLin.tanEquiv hp
    have hl : (Φ.symm (v i)).left ≫ φ = (v i).left := congrArg (fun q => q.left) (Φ.apply_symm_apply (v i))
    have ht : IsTangent (Φ.symm (v i)) := (HodgeLin.isTangent_iff hp _).2 (by
      change IsTanAt t.G z (Φ (Φ.symm (v i)))
      rw [Φ.apply_symm_apply]
      exact hv i)
    obtain ⟨w, hw⟩ := exists_isDiff t' m hP hA hp u ht
    exact ⟨w, _, hl, hw⟩
  choose x v' h1 h2 using key
  exact ⟨x, A, inferInstance, φ, u, χ, hp, hAH, hact, hinj, hmem, fun i => ⟨v' i, h1 i, h2 i⟩⟩

theorem hodgeInnerProduct_eq_pi_mul_riemannForm {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

theorem val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
    [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (hg : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r)
    (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hg.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

theorem exists_fibreLat_rank : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z →
    ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ)
      (R : RiemLat E g Λ), IsOver 𝔐 z κ p ∧ FibreLat 𝔐.t z R ∧
        ∀ s, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c s))) = labelRk D s := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz
  obtain ⟨κ, p, hO⟩ := exists_isOver E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hN : N1c := hG.1.2.2.1
  let j : KA l →+* c.F := (IntermediateField.inclusion c.le).toRingHom
  let ρF : c.F := j (baseKA l).ρ
  have hρF : (ρF : ℂ) = H.rt0 := rfl
  have hσ : p ≫ Xo.s = spMap (κ.comp j) := by
    obtain ⟨x, -, h1, h2⟩ := hO
    rw [← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, Chg.spMap_comp']
  have hsq : (κ ρF) ^ 2 = H.rt0 ^ 2 := by
    have e : ρF ^ 2 = -((H.d : ℕ) : c.F) := Subtype.ext (by
      push_cast
      rw [hρF]
      exact H.sqrt_neg_disc_sq)
    rw [← map_pow, e, H.sqrt_neg_disc_sq]
    simp
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by
      have : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
      simpa using this
    have h1 := H.sqrt_neg_disc_sq
    rw [h0] at h1
    have h2 : ((H.d : ℕ) : ℂ) = 0 := by simpa using h1.symm
    exact H.d_prime.pos.ne' (by exact_mod_cast h2)
  by_cases hρ : κ ρF = H.rt0
  · obtain ⟨FU⟩ := hN E H D l Xo (κ.comp j) g ty hD hρ hty
    obtain ⟨i, P, hP, hu⟩ := FU.onto p hσ
    obtain ⟨⟨R, -, hF, hr⟩, -⟩ := GlobalTheory.T.period_riemann_lattice_fibre E H D l Xo (κ.comp j) g ty FU i P hty hP
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      GlobalTheory.T.riemann_lattice_over_point E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO (hu ▸ hF), fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = H.rt0 := h.trans hρ
      simp [h']
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans (by simp [hρ])
      simp [h', hne.symm]
  · have hneg : κ ρF = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hρ
    have hρ₁ : ((starRingEnd ℂ).comp (κ.comp j)) (baseKA l).ρ = H.rt0 := by
      show starRingEnd ℂ (κ ρF) = H.rt0
      rw [hneg, map_neg, hconj, neg_neg]
    obtain ⟨FU⟩ := hN E H D l Xo ((starRingEnd ℂ).comp (κ.comp j)) g ty hD hρ₁ hty
    have hσ₁ : (spMap (starRingEnd ℂ) ≫ p) ≫ Xo.s = spMap ((starRingEnd ℂ).comp (κ.comp j)) := by
      rw [Category.assoc, hσ]
      exact (Chg.spMap_comp' _ _).symm
    obtain ⟨i, P, hP, hu⟩ := FU.onto _ hσ₁
    obtain ⟨-, R, -, hF, hr⟩ := GlobalTheory.T.period_riemann_lattice_fibre E H D l Xo _ g ty FU i P hty hP
    have hcc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ p = p := by
      have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun x => by simp
      rw [← Category.assoc, ← Chg.spMap_comp', e]
      simp [spMap]
    rw [hu, hcc] at hF
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      GlobalTheory.T.riemann_lattice_over_point E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO hF, fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans hneg
      simp [h', hne.symm]
    · have h' : τ (H.rt : E) = H.rt0 := h.trans (by simp [hneg])
      simp [h']

theorem exists_riemLat_of_interior : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz hG A₀ v hv
  obtain ⟨κ, p, g, Λ, i₁, i₂, R, hO, hF, hr⟩ := exists_fibreLat_rank hG E H D l Xo c Y S Ω K J y 𝔐 z hD hz
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hpol := HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨x, hx⟩ := fibreLatVec_of_fibreLat hpol hF v hv
  refine ⟨g, Λ, i₁, i₂, R, x, hx, fun i j => hodgeInnerProduct_eq_pi_mul_riemannForm hx hv i j, fun σ hσ s => ?_⟩
  have e : σ s = κ.comp (labelEmb c s) := RingHom.ext fun a =>
    val_unique 𝔐.tie.gen (hσ s a) (val_cst E H D l Xo c Y S Ω K J y 𝔐 z κ p hO (labelEmb c s a))
  rw [e]
  exact hr s

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx
