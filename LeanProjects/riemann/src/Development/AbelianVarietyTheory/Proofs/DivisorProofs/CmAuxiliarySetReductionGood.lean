import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.HalfFormUnit

theorem conj_mem_orderC {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} {x : E} (hx : x ∈ orderC c) :
    IsCMField.complexConj E x ∈ orderC c := by
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
  refine mem_orderC.2 ⟨a, IsCMField.ringOfIntegersComplexConj E b, ?_, ?_⟩
  · have : c.map (algebraMap (OF E) (𝓞 E)) ≤
        (c.map (algebraMap (OF E) (𝓞 E))).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hz
    exact this hb
  · rw [map_add]
    congr 1
    exact (IsCMField.complexConj E).commutes (a : FR E)

theorem span_bcMap {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' (algebraMap R R') (spMap (algebraMap R R')) φ} (hm : m.IsBC)
    [Module.Finite R (primDR A)] [Module.Projective R (primDR A)] (lam : HdR A' →ₗ[R'] R')
    (h : ∀ x, lam (hm.bcMap x) = 0) : lam = 0 := by
  haveI : Module.Free R (primDR A) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R (primDR A)
  refine LinearMap.ext fun y ↦ ?_
  have : y = ∑ k, y (m.pull (b k)) • hm.bcMap (b.coord k) := by
    refine LinearMap.ext fun c ↦ ?_
    obtain ⟨z, rfl⟩ := hm.2 c
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      rw [liftSemi_tmul, map_smul, map_smul]
      congr 1
      rw [LinearMap.sum_apply]
      conv_lhs => rw [← b.sum_repr c, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [LinearMap.smul_apply, hm.corr_iff.2 rfl c, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
  rw [this, map_sum]
  simp [h]

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem exists_coord {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) {L : LB X.A.left}
    (u : HolUnif X.A L (Module.finrank ℚ F)) :
    ∃ D : X.Lie →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), Function.Surjective D ∧ ∀ v w, u.IsDiff w v.hom ↔ D v = w := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  choose D hD hu using fun v : X.Lie ↦ h1 v.hom v.isTangent
  refine ⟨{ toFun := D, map_add' := fun v v' ↦ ?_, map_smul' := fun c v ↦ ?_ }, fun w ↦ ?_,
    fun v w ↦ ⟨fun h ↦ (hu v w h).symm, fun h ↦ h ▸ hD v⟩⟩
  · refine (hu _ _ ?_).symm
    have := GlobalTheory.UnifLieBasis.isDiff_add u ((isTan_iff _).2 v.isTangent) ((isTan_iff _).2 v'.isTangent) (hD v) (hD v')
    rw [Serre.Lie.hom_add]
    exact this
  · refine (hu _ _ ?_).symm
    have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 v.isTangent) (hD v) c
    convert this using 1
    all_goals rfl
  · obtain ⟨v, ⟨hv, hw⟩, -⟩ := h2 w
    exact ⟨Serre.Lie.mk X.rm v hv, (hu (Serre.Lie.mk X.rm v hv) w hw).symm⟩

theorem periodGen_eigen (P : GlobalTheory.Published.AbelianDeRham) {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    {𝔠 : FracId (FR E)} {R : Subring ℂ} [IsLocalRing R] {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {L : Set E}
    {U : Unif φ L 0 X} {p : X.A.left ⟶ X₀.A.left} (hp : X.IsPullBy X₀ (spMap R.subtype) p) (hL : LieExact X₀.A)
    {i : I} {e : X₀.Lie →ₗ[R] R} {a : ℂ} (ha : a ≠ 0) (he : IsPeriodGen X₀ U p i e a) :
    (∃ x, e (hL.toLie X₀.rm x) ≠ 0) ∧
    ∀ (β : X₀.A ⟶ X₀.A) [IsMonHom β] (α : X.A ⟶ X.A) [IsMonHom α] (c : Fin (Module.finrank ℚ (FR E)) → ℂ),
      α.left ≫ p = p ≫ β.left → (∀ w, U.u.ex (fun j ↦ c j * w j) = U.u.ex w ≫ α) → ∀ x,
      (e (hL.toLie X₀.rm (push (dp0 R) (𝟙 _) β x)) : ℂ) = c (U.e.symm i) * e (hL.toLie X₀.rm x) := by
  have hφ : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hp.grp
  obtain ⟨hm, -⟩ := P.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hφ
  have hL' := (P.2.1 ℂ X.A _ X.ab X.dim).1
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.1 X₀.ab X₀.dim
  obtain ⟨D, hDs, hD⟩ := exists_coord X U.u
  have key : ∀ x y, (GlobalTheory.Published.AbelianDeRham.bcMor hφ).Corr x y →
      (e (hL.toLie X₀.rm x) : ℂ) = a * D (hL'.toLie X.rm y) (U.e.symm i) := fun x y hxy ↦
    he _ _ _ (Obj.lieCorr_of_isLieImage P R.subtype hp (GlobalTheory.Published.AbelianDeRham.bcMor hφ) hxy
      ((hL.toLie_eq_iff _).1 rfl) ((hL'.toLie_eq_iff _).1 rfl)) ((hD _ _).2 rfl)
  refine ⟨?_, fun β _ α _ c hαβ hα x ↦ ?_⟩
  · by_contra h0
    push_neg at h0
    have := span_bcMap hm (LinearMap.proj (U.e.symm i) ∘ₗ D ∘ₗ hL'.toLie X.rm) fun x ↦ by
      have h1 := key x _ (hm.corr_iff.2 rfl)
      rw [h0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left ha
    obtain ⟨v, hv⟩ := hDs fun _ ↦ 1
    obtain ⟨y, rfl⟩ := hL'.toLie_surjective X.rm v
    have h2 := LinearMap.congr_fun this y
    simp [hv] at h2
  · have hx := hm.corr_iff.2 (rfl : hm.bcMap x = _)
    rw [key _ _ hx, key _ _ (GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor hφ) β α hαβ.symm hx),
      hL'.toLie_push hL' X.rm X.rm]
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j => c j * w j
        map_add' := fun w w' => by funext j; simp [mul_add]
        map_smul' := fun r w => by funext j; simp; ring }
    have h3 := GlobalTheory.UnifLieBasis.isDiff_comp U.u α (LinearMap.toContinuousLinearMap M) hα
      (hL'.toLie X.rm (hm.bcMap x)).isTangent ((hD _ _).2 rfl)
    rw [(hD (Serre.Lie.map X.rm X.rm α (hL'.toLie X.rm (hm.bcMap x))) _).1 h3]
    change a * (c _ * _) = _
    ring

theorem mem_eigLat {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} {R K : Type} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {H : Type*} [AddCommGroup H] [Module R H] {H' : Type} [AddCommGroup H'] [Module R H']
    (eH : H ≃ₗ[R] H') (ρ : orderC c →+* Module.End R H) (σ : E →+* K) (h : H) {r : R} (hr : r ≠ 0)
    (hh : ∀ a : orderC c, ∃ s : R, algebraMap R K s = σ a * algebraMap R K r ∧ r • ρ a h = s • h) :
    eH h ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp ρ) σ := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro a
  obtain ⟨s, h2, h1⟩ := hh a
  have hr0 : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  refine smul_right_injective _ hr0 ?_
  have h3 : LinearMap.baseChange K ((eH.conjRingEquiv.toRingHom.comp ρ) a) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H' (eH h)) =
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H' (eH (ρ a h)) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK]
  dsimp only
  rw [h3, smul_smul, mul_comm, ← h2, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul, h1, map_smul, map_smul]

theorem exists_factor {R : Type} [CommRing R] [IsDomain R] {H M : Type*} [AddCommGroup H] [Module R H] [AddCommGroup M]
    [Module R M] (π : H →ₗ[R] M) (hπ : Function.Surjective π) (f : H →ₗ[R] R) (e : M →ₗ[R] R) {s : R} (hs : s ≠ 0)
    (h : ∀ x, s * f x = e (π x)) : ∃ ℓ : M →ₗ[R] R, ∀ x, ℓ (π x) = f x := by
  have hker : LinearMap.ker π ≤ LinearMap.ker f := fun x hx ↦ by
    have := h x
    rw [LinearMap.mem_ker.1 hx, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hs
  refine ⟨(LinearMap.ker π).liftQ _ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun x ↦ ?_⟩
  simp

set_option maxHeartbeats 800000 in

theorem halfForm_eq_unit_mul : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
      (c₀ : FR E) ≠ 0 → IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) → Function.Bijective ψ₀ →
      (∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h')) →
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  intro _ P _ E _ _ _ _ I _ d φ _ 𝔣 _ l _ Q _ _ y _ lam 𝔠 R _ _ X₀ X U p cm hp _ hcm j hj φK hφK e a he hL n eH c₀ ψ₀ _ _
    hψ hadj _ i g hg
  obtain ⟨ha, hper, huniq⟩ := he i
  obtain ⟨⟨x₀, hx₀⟩, heig⟩ := periodGen_eigen P hp hL ha hper
  obtain ⟨h, hh⟩ := hψ.2 (e i ∘ₗ hL.toLie X₀.rm)
  have hh' : ∀ x, ψ₀ h x = e i (hL.toLie X₀.rm x) := fun x ↦ LinearMap.congr_fun hh x
  have heig' : ∀ (b : orderC (condQ 𝔣 Q)) x,
      (e i (hL.toLie X₀.rm (act (dp0 R) (𝟙 _) cm b x)) : ℂ) = φ i b * e i (hL.toLie X₀.rm x) := fun b x ↦ by
    obtain ⟨α, hα, h1, h2⟩ := hcm b
    haveI := cm.hom b
    have := heig (cm.act b) α (fun j ↦ φ (U.e j) (b : E)) h1 h2 x
    rwa [Equiv.apply_symm_apply] at this
  have hmem : eH h ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
    refine mem_eigLat eH _ _ h hx₀ fun c ↦ ?_
    let b : orderC (condQ 𝔣 Q) := ⟨_, conj_mem_orderC c.2⟩
    refine ⟨e i (hL.toLie X₀.rm (act (dp0 R) (𝟙 _) cm b x₀)), j.injective ?_, hψ.1 (LinearMap.ext fun x ↦ ?_)⟩
    · rw [map_mul, hj, hj, heig', ← hφK i]
      rfl
    · rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hadj c b rfl, hh', hh']
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul]
      rw [heig', heig']
      ring
  rw [hg] at hmem
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
  have hsg : ∀ x, s * ψ₀ (eH.symm g) x = e i (hL.toLie X₀.rm x) := fun x ↦ by
    have h1 : h = s • eH.symm g := by rw [← LinearEquiv.map_smul, hs, eH.symm_apply_apply]
    rw [← hh', h1, LinearMap.map_smul₂, smul_eq_mul]
  have hs0 : s ≠ 0 := fun h0 ↦ hx₀ (by rw [← hsg, h0, zero_mul])
  obtain ⟨ℓ, hℓ⟩ := exists_factor (hL.toLie X₀.rm) (hL.toLie_surjective X₀.rm) (ψ₀ (eH.symm g)) (e i) hs0 hsg
  have hs0' : (s : ℂ) ≠ 0 := fun h0 ↦ hs0 (Subtype.ext h0)
  obtain ⟨t, ht⟩ := huniq ℓ (a i / s) fun v v' W h1 h2 ↦ by
    have h3 := hper v v' W h1 h2
    obtain ⟨x, rfl⟩ := hL.toLie_surjective X₀.rm v
    rw [← hsg, Subring.coe_mul] at h3
    rw [hℓ, div_mul_eq_mul_div, ← h3, mul_div_cancel_left₀ _ hs0']
  have hst : t * s = 1 := by
    have := hsg x₀
    rw [← hℓ, ht, LinearMap.smul_apply, smul_eq_mul, ← _root_.mul_assoc] at this
    rw [mul_comm]
    exact mul_right_cancel₀ hx₀ (this.trans (_root_.one_mul _).symm)
  refine ⟨Units.mkOfMulEqOne t s hst, fun x ↦ ?_⟩
  rw [← hℓ, ht]
  rfl

end GlobalTheory.LatModel.HalfFormUnit
