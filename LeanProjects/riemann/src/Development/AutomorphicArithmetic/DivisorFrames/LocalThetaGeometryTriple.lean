import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.SymplecticShiftFixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem cA_cA (hcm : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
    rw [GlobalTheory.XTermSupp.invol hcm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem symp_shiftB (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁) (hH : form σ JX H.x H.y = 1)
    (hH' : form σ JW H'.x H'.y = 1) (l : (AE F E)ˣ) (a : AF F) (c : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW)
      (a • inclR (F := F) (AF F) c • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (shiftB σ H H' l) =
      a * Algebra.trace (AF F) (AE F E) ((l : AE F E) * inclR (F := F) (AF F) c) := by
  rw [← smul_assoc, symp, shiftB, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc, hH,
    GlobalTheory.XTermSupp.form_skew hcm hJ, hH', cA_cA hcm, ← smul_eq_mul a, ← map_smul (Algebra.trace (AF F) (AE F E))]
  congr 1
  simp [mul_comm]

private theorem rho_om_fixed {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil ψ χX χW om)
    {C : Set (UA σ X.J × UA σ W.J)} (hC : IsCompact C)
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ᶠ a in 𝓝 (0 : Af F), ∀ p ∈ C, M.co.rho ψ (pairA F 0 a • u) (om p Φ) = om p Φ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hm : Continuous fun g : UA σ X.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have hm' : Continuous fun g : UA σ W.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun p : UA σ X.J × UA σ W.J => M.co.e (mat p.1⁻¹ * u * (mat p.2⁻¹)ᵀ) :=
    he.comp (((hm.comp continuous_fst).matrix_mul continuous_const).matrix_mul
      (hm'.comp continuous_snd).matrix_transpose)
  filter_upwards [GlobalTheory.XTermSupp.schA_fixed_smul ψ hψ Φ hΦ hC _ hg] with a ha p hp
  obtain ⟨k, h⟩ := p
  have h1 := (IsUWeilPair.isUSplitting hom).impl (k, h) (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) Φ hΦ
  have h2 : actAB (cA σ) (k, h) (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) = pairA F 0 a • u := by
    show mat k * (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) * (mat h)ᵀ = _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, GlobalTheory.StabHaar.mat_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [h2] at h1
  rw [← h1, Darboux.rho, map_smul, ha (k, h) hp]

end UpperTheory.SymplecticShiftFixed

end

open UpperTheory.SymplecticShiftFixed in
theorem UpperTheory.local_theta_geometry_triple :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
        (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
        ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
        ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
        ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), ∀ C : Set (UA σ G.V'.J × UA σ G.W.J), IsCompact C →
        ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ p ∈ C, ∀ l : (AE F E)ˣ,
          (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U → e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ)) = 0 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e he X om om' om₁ om₁' hT _ Φ hΦ' C hKc
  have hstd := hT.base.std
  choose c hc using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  have hO := fun i => rho_om_fixed G.M' B.ψ hstd.1 hT.weil' hKc Φ hΦ'
    (inclR (F := F) (AF F) (c i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun p hp l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun t ht => ?_
  have hfix := ht i p hp
  have hΨ : om' p Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    (IsUWeilPair.isUSplitting hT.weil').pres _ _ hΦ'
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm G.M'.co B.ψ (pairA F 0 t • inclR (F := F) (AF F) (c i) •
    Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (shiftB σ H H' l) (om' p Φ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 t • inclR (F := F) (AF F) (c i) • incV F H'.y, by
      rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hstd _ _ hΨ),
    symp_shiftB hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 t * GlobalTheory.XTermMaj.crd F E (l : AE F E) i = pairA F 0 (t * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))
