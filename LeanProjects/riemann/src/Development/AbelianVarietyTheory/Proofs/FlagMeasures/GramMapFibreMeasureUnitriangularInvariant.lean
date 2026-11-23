import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitiaStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreUnitri
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gramR_comb {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (fun b => ∑ c, u c b • X c) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  simp only [gramR, hR, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, d, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, d]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def cgr {a : ℕ} (m A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) : Matrix (Fin a) (Fin a) (R ⊗[F] E) :=
  (m.map (sigR R σ)).transpose * A * m

theorem cgr_cgr {a : ℕ} (u w A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (huw : u * w = 1) :
    cgr R σ w (cgr R σ u A) = A := by
  have e1 : (w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, huw,
      map_one, Matrix.transpose_one]
  unfold cgr
  calc (w.map (sigR R σ)).transpose * ((u.map (sigR R σ)).transpose * A * u) * w
      = ((w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose) * A * (u * w) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [e1, huw, Matrix.one_mul, Matrix.mul_one]

theorem cgr_mem (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (S : HermR R σ a) : cgr R σ m (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) ∈ HermR R σ a := by
  have hS : ∀ p q, sigR R σ ((S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) q p) =
      (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) p q := S.2
  intro p q
  simp only [cgr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    sigR_invol R σ hσ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hS]
  ring

def cgrH (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (S : HermR R σ a) :
    HermR R σ a :=
  ⟨cgr R σ m S, cgr_mem R σ hσ m S⟩

theorem comb_comb {M a : ℕ} (u w : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ c, w c b • ∑ d, u d c • X d) = fun b => ∑ d, (u * w) d b • X d := by
  funext b
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem comb_one {M a : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ d, (1 : Matrix (Fin a) (Fin a) (R ⊗[F] E)) d b • X d) = X := by
  funext b
  simp [Matrix.one_apply]

theorem linIndep_comb {M a : ℕ} (m m' : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (h : m' * m = 1)
    (X : Fin a → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (fun b => ∑ c, m c b • X c) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg
  have h0 : ∑ c, (m *ᵥ g) c • X c = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hv : m *ᵥ g = 0 := funext (hX _ h0)
  have : g = m' *ᵥ (m *ᵥ g) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  intro i
  rw [this, hv, Matrix.mulVec_zero]
  rfl

end Alg

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem isFibreFamily_transport (e : V ≃ₜ V) (r : X ≃ₜ X) {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} {ν : Measure X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hν : ν.map r.toMeasurableEquiv = ν)
    (hf : ∀ x b, f (e x) = ι (r b) ↔ f x = ι b) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν Set.univ
      (fun b => (fib (r.symm b)).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  set rm := r.toMeasurableEquiv with hrm
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (r.symm b)} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      have hb := hf x (r.symm b)
      rw [r.apply_symm_apply] at hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι (r.symm b) ∧ x ∈ U)
      rw [hb, hx]
    rw [this]
    exact hfib.1 _
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    have h2 : ∀ c, ∫⁻ x, φ (em x) ∂(fib c) = ∫⁻ x, φ x ∂((fib (r.symm (rm c))).map em) := by
      intro c
      rw [lintegral_map_equiv]
      change _ = ∫⁻ x, φ (em x) ∂(fib (r.symm (r c)))
      rw [r.symm_apply_apply]
    simp_rw [h2]
    conv_rhs => rw [← hν]
    exact (lintegral_map_equiv (fun b => ∫⁻ x, φ x ∂((fib (r.symm b)).map em)) rm).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b _ => (integrable_map_equiv em φ).2 (h1 _ (Set.mem_univ _)), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib (r.symm b)).map em)) =
        (fun c => ∫ x, (φ ∘ e) x ∂(fib c)) ∘ r.symm :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    have h3 : Continuous fun c => ∫ x, (φ ∘ e) x ∂(fib c) := continuousOn_univ.1 h2
    exact (h3.comp r.symm.continuous).continuousOn

end Abstract
end GlobalTheory.FibreUnitri

namespace GlobalTheory.FibreUnitri
open Matrix

theorem fibre_unitri_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib hfib S u hdiag htri hS
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  obtain ⟨hring, -, -, hsc, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hE n J hJ v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩

  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => htri i j hij)]
    simp [hdiag]
  have hu : IsUnit u.det := by rw [hdet]; exact isUnit_one
  set w := u⁻¹ with hw
  have huw : u * w = 1 := Matrix.mul_nonsing_inv u hu
  have hwu : w * u = 1 := Matrix.nonsing_inv_mul u hu

  have hcont : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      Continuous (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, m c b • X c) := by
    intro m
    refine continuous_pi fun b => continuous_finset_sum _ fun c _ => ?_
    exact (continuous_apply c).const_smul (m c b)
  let e : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X b => ∑ c, u c b • X c
      invFun := fun X b => ∑ c, w c b • X c
      left_inv := fun X => by
        show (fun b => ∑ c, w c b • ∑ d, u d c • X d) = X
        rw [comb_comb, huw, comb_one]
      right_inv := fun X => by
        show (fun b => ∑ c, u c b • ∑ d, w d c • X d) = X
        rw [comb_comb, hwu, comb_one]
      continuous_toFun := hcont u
      continuous_invFun := hcont w }

  have hcontH : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), Continuous (cgrH (Fv F v) σ hσ m) := by
    intro m
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let r : HermR (Fv F v) σ a ≃ₜ HermR (Fv F v) σ a :=
    { toFun := cgrH (Fv F v) σ hσ u
      invFun := cgrH (Fv F v) σ hσ w
      left_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ u w _ huw)
      right_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ w u _ hwu)
      continuous_toFun := hcontH u
      continuous_invFun := hcontH w }
  obtain ⟨hμu, hνu⟩ := GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian F E σ hE n J hJ v a u hdiag htri
  have hμe : μ.map e.toMeasurableEquiv = μ := hμu μ hμ
  have hνr : ν.map r.toMeasurableEquiv = ν := hνu ν hν r (fun T => rfl)
  have hf : ∀ X T, gramR (Fv F v) σ J (e X) = ((r T : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ↔
      gramR (Fv F v) σ J X = (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    intro X T
    have h1 : gramR (Fv F v) σ J (e X) = cgr (Fv F v) σ u (gramR (Fv F v) σ J X) :=
      gramR_comb (Fv F v) σ J u X
    have h2 : ((r T : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
        cgr (Fv F v) σ u T := rfl
    rw [h1, h2]
    constructor
    · intro h
      have := congrArg (cgr (Fv F v) σ w) h
      rwa [cgr_cgr _ _ _ _ _ huw, cgr_cgr _ _ _ _ _ huw] at this
    · intro h
      rw [h]
  have hU : e ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    constructor
    · intro h
      have h' := linIndep_comb (Fv F v) w u huw _ h
      have e2 : (fun b => ∑ c, w c b • (e X) c) = X := e.left_inv X
      rw [e2] at h'
      exact h'
    · intro h
      exact linIndep_comb (Fv F v) u w hwu X h
  have hfam := isFibreFamily_transport e r hfib hμe hνr hf hU
  have heq := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hE n J hJ v a μ ν hμ hν fib hfib _ hfam
  have hrS : r.symm S = S := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hS.symm
  have := congrFun heq S
  simp only [hrS] at this
  exact this.symm

end GlobalTheory.FibreUnitri
