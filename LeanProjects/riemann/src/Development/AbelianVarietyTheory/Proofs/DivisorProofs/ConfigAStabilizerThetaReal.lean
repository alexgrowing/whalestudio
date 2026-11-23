import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPureTensorFixedByOpenFiniteHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermSupp

theorem rho_comm {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}
    {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (s u : W) (φ : (κ → R) → ℂ) :
    d.rho ψ s (d.rho ψ u φ) = ψ (B s u) • d.rho ψ u (d.rho ψ s φ) := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, d.form, ← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [add_right_comm x (d.e s).1]
  congr 2
  simp only [add_dotProduct]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem schA_fixed (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ)
    (hΦ : Φ ∈ schA F κ) : ∀ᶠ m in 𝓝 (0 : (κ → Af F) × (κ → Af F)), schr ψ (GlobalTheory.WeilAdm.finE2 F m) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨M, hMo, hM⟩ := GlobalTheory.WeilAdm.pureA_fixed_fin F ψ hψ κ g hg
    filter_upwards [hMo.mem_nhds M.zero_mem] with m hm using hM m hm f
  | zero => exact .of_forall fun m => by funext x; simp [schr]
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with m e1 e2
    funext z
    have hx1 := congrFun e1 z
    have hy1 := congrFun e2 z
    simp only [schr, Pi.add_apply, mul_add] at hx1 hy1 ⊢
    rw [hx1, hy1]
  | smul c x _ hx =>
    filter_upwards [hx] with m e1
    funext z
    have hx1 := congrFun e1 z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at hx1 ⊢
    rw [mul_left_comm, hx1]

theorem schA_fixed_smul (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ)
    (hΦ : Φ ∈ schA F κ) {T : Type} [TopologicalSpace T] {C : Set T} (hC : IsCompact C)
    (g : T → (κ → AF F) × (κ → AF F)) (hg : Continuous g) :
    ∀ᶠ a in 𝓝 (0 : Af F), ∀ k ∈ C, schr ψ (pairA F 0 a • g k) Φ = Φ := by
  let m : Af F × T → (κ → Af F) × (κ → Af F) := fun p => (fun i => p.1 * ((g p.2).1 i).2, fun i => p.1 * ((g p.2).2 i).2)
  have hs : Continuous fun z : AF F => (z.2 : Af F) := continuous_snd
  have hm : Continuous m := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_fst.mul (hs.comp ?_))
      (continuous_pi fun i => continuous_fst.mul (hs.comp ?_))
    · exact (continuous_apply i).comp (continuous_fst.comp (hg.comp continuous_snd))
    · exact (continuous_apply i).comp (continuous_snd.comp (hg.comp continuous_snd))
  have e : ∀ a k, pairA F 0 a • g k = GlobalTheory.WeilAdm.finE2 F (m (a, k)) := fun a k =>
    Prod.ext (funext fun i => Prod.ext (zero_mul _) rfl) (funext fun i => Prod.ext (zero_mul _) rfl)
  simp only [e]
  refine hC.eventually_forall_of_forall_eventually fun k _ => ?_
  have h0 : m (0, k) = 0 := Prod.ext (funext fun i => zero_mul _) (funext fun i => zero_mul _)
  exact (hm.tendsto' _ _ h0).eventually (schA_fixed ψ hψ Φ hΦ)

theorem trace_mul_dual (i : Fin (Module.finrank F E)) : ∃ c : E, ∀ x : AE F E,
    Algebra.trace (AF F) (AE F E) (x * inclR (F := F) (AF F) c) = GlobalTheory.XTermMaj.crd F E x i := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨(Module.finBasis F E).traceDual i, fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [GlobalTheory.XTermMaj.crd]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy, GlobalTheory.XTermMaj.crd, Pi.add_apply]
  | tmul r x =>
    have h1 := Module.Basis.traceDual_repr_apply (Module.finBasis F E).traceDual x i
    rw [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply] at h1
    have h2 : (r ⊗ₜ[F] x : AE F E) * inclR (F := F) (AF F) ((Module.finBasis F E).traceDual i) =
        r • ((1 : AF F) ⊗ₜ[F] (x * (Module.finBasis F E).traceDual i)) := by
      simp [inclR, TensorProduct.smul_tmul']
    rw [h2, map_smul, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply,
      ← h1]
    simp [GlobalTheory.XTermMaj.crd]

theorem form_inc {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ j, ∑ l, incV F x j * incM F J j l * cA σ (incV F y l) = inclR (F := F) (AF F) (form σ J x y) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]

theorem hTens_vv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (l t : A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (l • Matrix.vecMulVec a x) (t • Matrix.vecMulVec a' x') =
      l * c t * ((∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l)) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_skew (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (x y : Fin n → E) : form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, invol h, hJ, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rho_om_fixed {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil ψ χX χW om) {C : Set (UA σ X.J)} (hC : IsCompact C) (h : UA σ W.J)
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ᶠ a in 𝓝 (0 : Af F), ∀ k ∈ C, M.co.rho ψ (pairA F 0 a • u) (om (k, h) Φ) = om (k, h) Φ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hm : Continuous fun g : UA σ X.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun k : UA σ X.J => M.co.e (mat k⁻¹ * u * (mat h⁻¹)ᵀ) :=
    he.comp ((hm.matrix_mul continuous_const).matrix_mul continuous_const)
  filter_upwards [schA_fixed_smul ψ hψ Φ hΦ hC _ hg] with a ha k hk
  have h1 := (IsUWeilPair.isUSplitting hom).impl (k, h) (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) Φ hΦ
  have h2 : actAB (cA σ) (k, h) (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) = pairA F 0 a • u := by
    show mat k * (pairA F 0 a • (mat k⁻¹ * u * (mat h⁻¹)ᵀ)) * (mat h)ᵀ = _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, GlobalTheory.StabHaar.mat_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [h2] at h1
  rw [← h1, Darboux.rho, map_smul, ha k hk]

theorem symp_shiftA (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁) (hH : form σ JX H.x H.y = 1)
    (hH' : form σ JW H'.x H'.y = 1) (l : (AE F E)ˣ) (a : AF F) (c : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW) (shiftA H H' l)
      (a • inclR (F := F) (AF F) (σ c) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) =
      a * Algebra.trace (AF F) (AE F E) ((l : AE F E) * inclR (F := F) (AF F) c) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  rw [← smul_assoc, symp, shiftA, hTens_vv, form_inc, form_inc, hH, form_skew hcm hJ, hH', map_smul, hc, invol hcm,
    ← smul_eq_mul a, ← map_smul (Algebra.trace (AF F) (AE F E))]
  congr 1
  simp

theorem finsupp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧
      ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U → e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) = 0 := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h
  have hstd := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := by
    refine (Submodule.span_le.2 ?_ : PolData B G.M ≤ _) hΦ
    rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
  choose c hc using trace_mul_dual (F := F) (E := E)
  have hO := fun i => rho_om_fixed G.M B.ψ hstd.1 hT.weil hCc h Φ hΦ'
    (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun k hk l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun a ha => ?_
  have hfix := ha i k (hsub ((hK k).1 hk))
  have hΨ : om (k, h) Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (IsUWeilPair.isUSplitting hT.weil).pres _ _ hΦ'
  have h1 := congrArg e (rho_comm G.M.co B.ψ (shiftA H H' l) (pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) •
    Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (k, h) Φ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) • incV F H.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ),
    symp_shiftA hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 a * GlobalTheory.XTermMaj.crd F E (l : AE F E) i = pairA F 0 (a * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))

end GlobalTheory.XTermSupp

end
