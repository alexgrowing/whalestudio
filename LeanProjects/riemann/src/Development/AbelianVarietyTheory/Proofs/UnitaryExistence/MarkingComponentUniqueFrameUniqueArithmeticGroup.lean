import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVarietyStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.MarkUniq

lemma nsmul_cancel (F : Type) [Field F] {M : Type} [AddCommGroup M] [Module F M] {N : ℕ} (hN : (N : F) ≠ 0)
    {x y : M} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

lemma sub_eq_nsmul_sub {M : Type} [AddCommGroup M] {N : ℕ} {x y z w w' : M} (h : x - z = N • w) (h' : y - z = N • w') :
    x - y = N • (w - w') := by
  rw [smul_sub, ← h, ← h']; abel

lemma exists_of_finVec_eq_nsmul {D : D7} (V : HSp D) (g : GA D V) (N : ℕ) (hN : N ≠ 0)
    (u : Fin V.rank → D.host.E) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V g)
    (h : finVec V u = N • w) : ∃ x ∈ latG V g, u = N • x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hu : u = N • ((N : D.host.E)⁻¹ • u) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  refine ⟨(N : D.host.E)⁻¹ • u, ?_, hu⟩
  refine ((GlobalTheory.T.adelicCompletion_rational_points_and_approximation D.host.F D.host.E V.rank (latG V g) h1 h2).1 _).1 ?_
  have e : N • finVec V ((N : D.host.E)⁻¹ • u) = N • w := by
    rw [← h]
    conv_rhs => rw [hu]
    funext i
    simp only [finVec, Pi.smul_apply]
    exact (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) N _).symm
  have e' := nsmul_cancel D.host.F hNF e
  rw [h5, ← e'] at hw
  exact hw

lemma finVec_sub {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    finVec V (u - v) = finVec V u - finVec V v := by
  funext i
  simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]

lemma half_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (t : A →ₗ[𝓞 E] B) (ht : ∀ b, ∃ a e, b = t a + l.M • e) (b : B)
    (hb : b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) B)) :
    ∃ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) A), ∃ e, b = t a + l.M • e := by
  obtain ⟨a, e, hae⟩ := ht b
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have h2 : x • b ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) B) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hx hb
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨e', -, he'⟩ := h2
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, e' + y • e, ?_⟩
  rw [Nat.cast_smul_eq_nsmul] at he'
  have : b = x • b + y • b := by rw [← add_smul, hxy, one_smul]
  rw [this, ← he', map_smul, smul_add, smul_comm l.M y e]
  conv_lhs => rw [hae]
  rw [smul_add]
  abel

lemma matched {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} (C : Ctx Xo c σ V V.rank) (h : GA D V) (k k' : Fin C.F.n)
    (γ γ' : GA D V) (hm : C.Mark h k γ) (hm' : C.Mark h k' γ') :
    ∃ δ : GL (Fin V.rank) D.host.E, IsRat V (γ' * γ⁻¹) δ ∧
      (∀ v, v ∈ (C.M.X k).Λ ↔ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ (C.M.X k').Λ) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ (C.M.X k').Λ,
          (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) =
            (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) + l.M • w := by
  obtain ⟨r1, -, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨hγ, hΛ, hk⟩ := hm
  obtain ⟨hγ', hΛ', hk'⟩ := hm'
  obtain ⟨δ, hδ⟩ := (r1 _).1 ((GQ V).mul_mem hγ' ((GQ V).inv_mem hγ))
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 _ δ (γ * h) hδ
  have hg : γ' * γ⁻¹ * (γ * h) = γ' * h := by group
  rw [hg] at m1 m2
  have hL : (C.M.X k).Λ = latG V (γ * h) := SetLike.ext' (hΛ.trans (Set.image_id _))
  have hL' : (C.M.X k').Λ = latG V (γ' * h) := SetLike.ext' (hΛ'.trans (Set.image_id _))
  refine ⟨δ, hδ, fun v => by rw [hL, hL']; exact m1 v, fun a ha => ?_⟩
  obtain ⟨w, hw, e⟩ := hk a ha
  obtain ⟨w', hw', e'⟩ := hk' a ha
  change finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _ at e
  change finVec V (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) - _ = _ at e'
  have e2 := congrArg (fun z => (finHom V (γ' * γ⁻¹)).1 *ᵥ z) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
  rw [(r5 _ δ hδ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hg] at e2
  obtain ⟨x, hx, hx'⟩ := exists_of_finVec_eq_nsmul V (γ' * h) l.M (by have := l.three_le; omega)
    ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
      (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E)) ((finHom V (γ' * γ⁻¹)).1 *ᵥ w - w')
    (sub_mem ((m2 w).1 hw) hw') ((finVec_sub V _ _).trans (sub_eq_nsmul_sub e2 e'))
  exact ⟨x, hL' ▸ hx, by rw [← hx']; abel⟩

theorem mark_unique : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, r2, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  have hG : ∀ k, (C.M.X k).Gm = -V.gramᵀ := fun k => (hC.modelW k).1
  refine ⟨fun k k' γ γ' hm hm' => ?_, fun k γ γ' hm hm' => ?_⟩
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k' γ γ' hm hm'
    refine GlobalTheory.ClassUniq.eq_of_matched GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.firstFiveLaws.1 _ H Dw l Xo _ C.g _ C.F _ C.M k k' δ
      hC.pos hC.good ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hC.good).2.2.2 Dw C.g C.e) hC.base
      ((hG k').trans (hG k).symm) ((hC.modelW k').2.trans (hC.modelW k).2.symm)
      (by rw [hG k]; exact r2 _ δ hδ) hΛ hmk (fun a => ?_)
    refine ⟨_ - _, sub_mem ((hΛ _).1 (C.M.φ k (C.F.t k a)).2) (C.M.φ k' (C.F.t k' a)).2, ?_⟩
    rw [hC.lA, one_smul]; abel
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k γ γ' hm hm'
    have hφ : ∀ w ∈ (C.M.X k).Λ, ∃ b, (C.M.φ k b : Fin V.rank → D.host.E) = w := fun w hw =>
      ⟨(C.M.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    refine ⟨δ, (hC.base.gam k δ).2 ⟨⟨by rw [hG k]; exact r2 _ δ hδ, hΛ⟩, fun b hb => ?_, fun a => ?_⟩, ?_⟩
    · have hM : l.M' = l.M := by rw [Level.M', hC.lA, Nat.lcm_one_right]
      obtain ⟨a, ha, e, rfl⟩ := half_surj l (C.F.t k) (fun b => hM ▸ C.F.t_surj k b) b hb
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      obtain ⟨b', hb'⟩ := hφ _ (sub_mem (add_mem hw ((hΛ _).1 (C.M.φ k e).2)) (C.M.φ k e).2)
      refine ⟨b', ?_⟩
      rw [hb', map_add, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul, Matrix.mulVec_add,
        Matrix.mulVec_smul, hw', smul_sub, smul_add]
      abel
    · obtain ⟨b', hb'⟩ := hφ _ (sub_mem ((hΛ _).1 (C.M.φ k a).2) (C.M.φ k a).2)
      refine ⟨b', ?_⟩
      rw [hb', hC.lA, one_smul]; abel
    · funext τ
      have hg : γ' * h = γ' * γ⁻¹ * (γ * h) := by group
      have e := ((GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf).1 τ.1).2.1 (γ' * γ⁻¹) (γ * h)
      rw [← hg, (r5 _ δ hδ).2 τ.1 _ (hC.inf τ.1)] at e
      change archM V (C.θ τ.1) (γ' * h) * C.x₀ τ.1 =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [e, Matrix.mul_assoc]

end GlobalTheory.MarkUniq
