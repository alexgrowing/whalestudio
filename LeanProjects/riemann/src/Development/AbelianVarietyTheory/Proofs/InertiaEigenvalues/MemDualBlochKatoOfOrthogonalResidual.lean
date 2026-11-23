import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLatticeStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual.Perp

theorem ker_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x : O) :
    algebraMap O K x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O := by
  refine ⟨fun hx => ?_, h x⟩
  by_contra hn
  have hu : IsUnit x := by simpa using hn
  exact (hu.map (algebraMap O K)).ne_zero hx

theorem eq_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ algebraMap O K x = algebraMap O K y := by
  rw [← ker_iff h, map_sub, sub_eq_zero]

def divMap {O : Type} [CommRing O] [IsDomain O] (ϖ : O) : O →ₗ[O] Formalism.BasicNotions.KmodO O :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹) ∘ₗ Algebra.linearMap O (FractionRing O)

theorem divMap_apply {O : Type} [CommRing O] [IsDomain O] (ϖ a : O) :
    divMap ϖ a = Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem divMap_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : divMap ϖ a = 0 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  rw [divMap_apply, Submodule.Quotient.mk_eq_zero, map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨b, rfl⟩

theorem continuous_algebraMap {O K : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Field K] [Algebra O K] [TopologicalSpace K]
    (ha : IsAdic (IsLocalRing.maximalIdeal O))
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) : Continuous (algebraMap O K) := by
  have ho : IsOpen (IsLocalRing.maximalIdeal O : Set O) := by simpa using (isAdic_iff.1 ha).1 1
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (IsLocalRing.maximalIdeal O : Set O), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  exact (eq_iff h y x).1 hy

theorem repOn_one_map {G O K : Type} [Group G] [CommRing O] [Field K] [Algebra O K] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (g : G) (y : Fin r → O) (a : Fin r) :
    repOn ρ (1 : G →* Kˣ) K g (fun b => algebraMap O K (y b)) a =
      algebraMap O K (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).mulVec y a) := by
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem mem_bkOn_of_orthogonal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  intro D N X bkP i s hG K _ _ _ _ hK hs ρ hρ v hv y H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  choose lift hlift using hs
  have hy : ∀ g, y.1 g = fun b => algebraMap (X.O0 i) K (lift (y.1 g b)) := fun g => funext fun b => (hlift _).symm
  have hact : ∀ (g h : DecV N v) a, ((red i K ρ).comp (DecV N v).subtype) g (y.1 h) a =
      algebraMap (X.O0 i) K ((Tdual i s g.1).mulVec (fun b => lift (y.1 h b)) a) := fun g h a => by
    rw [← hρ g.1, ← repOn_one_map ρ g.1, ← hy]
    rfl
  have key := (GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice D N X bkP i s hG ρ hρ v hv ϖ hϖ (fun g a => lift (y.1 g a)) (fun a => ?_)
    (fun g h a => ?_)).2 ?_
  · obtain ⟨y', hy', e⟩ := key
    obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hy'
    unfold bkOn
    rw [dif_pos hv]
    refine Submodule.subset_span ⟨y, c, y', 1, hc, hc', fun g a => ?_, rfl⟩
    rw [smul_eq_mul, mul_one, (eq_iff hK _ _).1 (e g a), hlift]
  · have : IsLocallyConstant fun g => y.1 g a :=
      (IsLocallyConstant.iff_continuous _).2 ((continuous_apply a).comp y.2.1)
    exact this.comp fun k => IsLocalRing.residue (X.O0 i) (lift k)
  · rw [eq_iff hK, map_add, hlift, hlift, ← hact, y.2.2 g h]
    rfl
  · intro d hd
    let x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype) :=
      ⟨fun g a => algebraMap (X.O0 i) K (d g a),
        continuous_pi fun a => (continuous_algebraMap (X.twistBaseCoefficientRing_isAdic i) hK).comp ((continuous_apply a).comp hd.continuous),
        fun g h => funext fun a => by
          beta_reduce
          rw [hd.cocycle g h, Pi.add_apply, map_add, ← repOn_one_map]
          rfl⟩
    have hx : Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v := by
      obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hd
      unfold bkOn
      rw [dif_pos hv]
      exact Submodule.subset_span ⟨x, c, d, 1, hc, hc', fun g a => by rw [smul_eq_mul, mul_one], rfl⟩
    obtain ⟨f, hf, e⟩ := H x hx
    refine ⟨fun g => divMap ϖ (lift (f g)), hf.comp fun k => divMap ϖ (lift k), fun g h => ?_⟩
    rw [← divMap_apply, ← map_smul, ← map_sub, ← map_add, ← sub_eq_zero, ← map_sub]
    apply divMap_eq_zero hϖ
    rw [eq_iff hK, map_add, map_sub, smul_eq_mul, map_mul, hlift, hlift, hlift, ← e g h]
    simp only [dotProductBilin_apply_apply, dotProduct, map_sum, map_mul, hact]
    rfl

end GlobalTheory.ResDual.Perp
