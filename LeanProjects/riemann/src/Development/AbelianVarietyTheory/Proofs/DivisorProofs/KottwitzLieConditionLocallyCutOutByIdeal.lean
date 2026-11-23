import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdLieMatrixSmoothCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionAtIffKottwitzModuleCondiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankSimultaneousEigenSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionModuleIffIdealLeKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealGeometricRankIffOfLieConditionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

section Transport

variable {O T V W : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]
  (ψ : O →+* Module.End T V) (ν : O →+* Module.End T W) (e : V ≃ₗ[T] W) (he : ∀ c v, e (ψ c v) = ν c (e v))
include he

theorem mem_eigSub_transport (τ : O →+* T) (v : V) : e v ∈ eigSub ν τ ↔ v ∈ eigSub ψ τ := by
  simp only [mem_eigSub]
  refine forall_congr' fun c => ?_
  rw [← he, ← map_smul, e.injective.eq_iff]

theorem eigSub_transport (τ : O →+* T) : (eigSub ψ τ).map (e : V →ₗ[T] W) = eigSub ν τ := by
  ext w
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, ← mem_eigSub_transport ψ ν e he]
  simp

theorem finrank_eigSub_transport (τ : O →+* T) :
    Module.finrank T (eigSub ψ τ) = Module.finrank T (eigSub ν τ) := by
  rw [← eigSub_transport ψ ν e he τ]
  exact (e.submoduleMap (eigSub ψ τ)).finrank_eq

theorem lieMod_transport (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) :
    LieMod ψ ω ρ τ ↔ LieMod ν ω ρ τ := by
  constructor
  · intro h w hw
    obtain ⟨u, hu, hs⟩ := h (e.symm w) (by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, hw])
    refine ⟨fun i => e (u i), fun i => (mem_eigSub_transport ψ ν e he _ _).2 (hu i), ?_⟩
    rw [← map_sum, ← hs, LinearEquiv.apply_symm_apply]
  · intro h v hv
    obtain ⟨u, hu, hs⟩ := h (e v) (by rw [← he, hv, map_smul])
    refine ⟨fun i => e.symm (u i), fun i => ?_, ?_⟩
    · rw [← mem_eigSub_transport ψ ν e he, LinearEquiv.apply_symm_apply]
      exact hu i
    · apply e.injective
      rw [map_sum, hs]
      simp

end Transport

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_baseMap {R : Type} [CommRing R] {S : Scheme.{0}} (s : S ⟶ Sp R) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ βB : R →+* Γ(S, U), ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'),
      spMap f ≫ hU.fromSpec ≫ s = spMap β → β = f.comp βB := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, fun R' _ f β h => ?_⟩
  have h2 : spMap (f.comp (Spec.preimage (hU.fromSpec ≫ s)).hom) = spMap β := by
    rw [← h, ← spMap_comp_spMap']
    congr 1
    show Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h3 := Spec.map_injective h2
  exact (congrArg CommRingCat.Hom.hom h3).symm

theorem lieHer_iff_mat {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {S : Scheme.{0}}
    {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {U : S.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) Γ(S, U))
    (hM : ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
      ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
        ∀ (c : 𝓞 D.F) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
          e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') (act.toF D) c v) = matAct M f c (e v))
    {R' : Type} [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R') :
    LieHer b act β (spMap f ≫ hU.fromSpec) ↔ LieHerMat b M f β := by
  unfold LieHer LieHerMat LieRankAt
  refine forall_congr' fun T' => forall_congr' fun _ => forall_congr' fun g => ?_
  have hx : spMap g ≫ spMap f ≫ hU.fromSpec = spMap (g.comp f) ≫ hU.fromSpec := by
    rw [← Category.assoc, spMap_comp_spMap']
  rw [hx]
  obtain ⟨e, he⟩ := hM T' (g.comp f)
  refine and_congr ?_ ?_
  · rw [GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition]
    exact lieMod_transport _ _ e he _ _ _
  · refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h =>
      forall_congr' fun i => ?_
    have hx2 : spMap h ≫ spMap (g.comp f) ≫ hU.fromSpec = spMap (h.comp (g.comp f)) ≫ hU.fromSpec := by
      rw [← Category.assoc, spMap_comp_spMap']
    rw [hx2]
    obtain ⟨e2, he2⟩ := hM k (h.comp (g.comp f))
    haveI : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (h.comp (g.comp f)) ≫ hU.fromSpec) A) :=
      Module.Finite.equiv e2.symm
    rw [GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule _ _ _ _ _ _ _ _ inferInstance, finrank_eigSub_transport _ _ e2 he2]

theorem lieHerMat_iff_le {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {B : Type}
    [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K₂ : Ideal B)
    (hK₂ : ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f))
    {T : Type} [CommRing T] (f : B →+* T) :
    LieHerMat b M f (f.comp βB) ↔ lieIdeal b βB M ⊔ K₂ ≤ RingHom.ker f := by
  constructor
  · intro h
    obtain ⟨hL, hR⟩ := h T (RingHom.id T)
    have hJ : lieIdeal b βB M ≤ RingHom.ker f := (GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T f).1 hL
    exact sup_le hJ ((hK₂ T f hJ).1 hR)
  · intro hK T' _ g
    have hker : RingHom.ker f ≤ RingHom.ker (g.comp f) := fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, hx, map_zero]
    have hJ : lieIdeal b βB M ≤ RingHom.ker (g.comp f) := le_sup_left.trans (hK.trans hker)
    have h2 : K₂ ≤ RingHom.ker (g.comp f) := le_sup_right.trans (hK.trans hker)
    exact ⟨(GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T' (g.comp f)).2 hJ, (hK₂ T' (g.comp f) hJ).2 h2⟩

theorem lieHer_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  intro p _ D R _ b S s A _ _ hA act z
  obtain ⟨U, hU, hz, n, M, hM⟩ := GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group (𝓞 D.F) S A hA (act.toF D) z
  obtain ⟨βB, hβB⟩ := exists_baseMap s hU
  obtain ⟨K₂, hK₂⟩ := GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition p D R b Γ(S, U) βB n M
  refine ⟨U, hU, hz, lieIdeal b βB M ⊔ K₂, fun R' _ f β hc => ?_⟩
  obtain rfl := hβB R' f β hc
  rw [lieHer_iff_mat b act hU M hM f]
  exact lieHerMat_iff_le b βB M K₂ hK₂ f

end GlobalTheory.UPel.HT.LieLin
