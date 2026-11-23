import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreInducedUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsInhabitant

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Published.LeviCentreModel

namespace GlobalTheory.Published.LeviInducedModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_conj (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    piInf τ (cA σ a) = starRingEnd ℂ (piInf τ a) := by
  change _ = starRingEnd ℂ (infEmb τ _)
  rw [infEmb_sigR hσ]
  change infEmb τ _ = _
  congr 1
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem cont_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F) (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
    change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
    rw [infEmb_tmul, map_one, mul_one]; rfl

def chi (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) : Chr F E where
  toFun t := ⟨piInf τ (t.1 * cA σ (t⁻¹).1), by
    have : piInf τ t.1 * piInf τ (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg norm this
    simpa [Submonoid.unitSphere, piInf_conj hσ] using h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change piInf τ ((a * b).1 * cA σ ((a * b)⁻¹).1) = piInf τ (a.1 * cA σ (a⁻¹).1) * piInf τ (b.1 * cA σ (b⁻¹).1)
    simp only [mul_inv_rev, Units.val_mul, map_mul]; ring)

theorem detA_levi_torus (δ : E) (t : (AE F E)ˣ) (m : UA σ (big F δ).J)
    (hm : IsLevi (W₁ := small F δ) (pl E) t 1 m) : detA (big F δ).J m = t.1 * cA σ (t⁻¹).1 := by
  obtain ⟨h1, h2, h3⟩ := hm
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  have c1 := congrFun (congrFun h3 1) 0
  have c2 := congrFun (congrFun h3 2) 0
  have e : mat (1 : UA σ (small F δ).J) = 1 := rfl
  rw [e] at c1 c2
  generalize cA σ (t⁻¹).1 = s at *
  simp [pl, incV, incM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply] at a0 a1 a2 b0 b1 b2 c1 c2
  rw [detA_apply, Matrix.det_fin_three]
  simp [a0, a1, a2, b0, b1, b2, c1, c2]

theorem exists_inhabitant (hσ : IsCMExt F E σ) :
    ∃ (Y : Spc F E 3) (Y₁ : Spc F E 1) (H : Plane E 3 1) (ψ : UA σ Y.J → ℂ) (χ : Chr F E) (c : E)
      (φ : GAd σ (c • Y.J.map σ) → ℂ) (V : Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ)) (Kc : Set (UA σ Y.J)),
      (∀ i j, σ (Y.J j i) = -Y.J i j) ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
      (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
      (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) ∧ Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) ∧
      (∀ t m, IsLevi (W₁ := Y₁) H t 1 m → ∀ x, ψ (m * x) = (χ t : ℂ) * ψ x) ∧
      c ≠ 0 ∧ IsHermND σ (c • Y.J.map σ) ∧ IsHermND σ (c • Y₁.J.map σ) ∧
      (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) ∧ GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
      FiniteDimensional ℂ V ∧ (∀ v ∈ V, GlobalTheory.UAut.IsSm σ (c • Y₁.J.map σ) v) ∧
      (∀ v ∈ V, ∀ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z → GlobalTheory.UAut.dop z v ∈ V) ∧
      (∀ x : UA σ Y.J, ∃ u ∈ unip σ Y H, ∃ t h₁ m, IsLevi (W₁ := Y₁) H t h₁ m ∧ ∃ k ∈ Kc, x = u * m * k) ∧
      (∀ k ∈ Kc, ∃ v ∈ V, ∀ (h₁ : UA σ Y₁.J) (m : UA σ Y.J) (g' : GAd σ (c • Y₁.J.map σ)),
        IsLevi (W₁ := Y₁) H 1 h₁ m → h₁.1 = g'.1 → v g' = ψ (m * k)) ∧
      ψ 1 = 1 ∧ (∃ t, χ t ≠ 1) ∧ (∃ v ∈ V, ∃ a, v a ≠ v 1) ∧
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨δ, h0, hδ⟩ := exists_anti hσ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine ⟨big F δ, small F δ, pl E, fun g => piInf τ (detA _ g), chi hσ τ, δ, fun g' => piInf τ (g'.1.1.det),
    Submodule.span ℂ {fun g => piInf τ (g.1.1 0 0)}, Set.univ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro u; simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i j; fin_cases i; fin_cases j; simp [big, small, pl, Matrix.mul_apply, Fin.sum_univ_three]
  · intro u hu x; simp only [map_mul, detA_unip δ u hu, one_mul]
  · change Continuous fun t : (AE F E)ˣ => piInf τ (t.1 * cA σ (t⁻¹).1)
    simp only [map_mul, piInf_conj hσ]
    exact ((cont_piInf τ).comp Units.continuous_val).mul
      (Complex.continuous_conj.comp ((cont_piInf τ).comp Units.continuous_coe_inv))
  · intro t m hm x
    change piInf τ (detA _ (m * x)) = piInf τ (t.1 * cA σ (t⁻¹).1) * piInf τ (detA _ x)
    rw [map_mul, detA_levi_torus δ t m hm, map_mul]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [big, Matrix.det_fin_three, h0, hδ]
  · intro i j; fin_cases i; fin_cases j; simp [small, hδ]
  · simp [small, h0, hδ]
  · intro g g' hg
    exact congrArg (fun x : GL (Fin 3) (AE F E) => piInf τ x.1.det) hg.symm
  · intro k γ hγ g
    have e := fun i j => GlobalTheory.UAut.Model.isSm_entry (J := δ • (big F δ).J.map σ) hσ τ i j k γ hγ g
    simp only [arch_entry] at e
    simp only [Matrix.det_fin_three, map_add, map_sub, map_mul]
    fun_prop
  · intro v hv k γ hγ g
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have e := GlobalTheory.UAut.Model.isSm_entry (J := δ • (small F δ).J.map σ) hσ τ 0 0 k γ hγ g
    simp only [arch_entry] at e
    exact e.const_smul a
  · intro v hv z _
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    choose c hc using GlobalTheory.UAut.foldr_lineDer_char (φ := fun g' : GAd σ (δ • (small F δ).J.map σ) => piInf τ (g'.1.1 0 0))
      (fun g h => by
        rw [← map_mul]
        change piInf τ ((g.1.1 * h.1.1) 0 0) = _
        simp [Matrix.mul_apply]) a
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
      simp only [GlobalTheory.UAut.dop, hc]; simp [Finsupp.sum, Finset.sum_mul, mul_assoc]⟩
  · intro x
    refine ⟨1, one_mem _, 1, 1, 1, ⟨?_, ?_, ?_⟩, x, trivial, by simp⟩
    · change (1 : Matrix _ _ _) *ᵥ _ = _; simp
    · change (1 : Matrix _ _ _) *ᵥ _ = _; simp
    · change (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _); simp
  · intro k _
    refine ⟨piInf τ (detA _ k) • fun g => piInf τ (g.1.1 0 0), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    intro h₁ m g' hm e
    simp only [map_mul, detA_levi δ h₁ m hm, mat, e, Pi.smul_apply, smul_eq_mul, mul_comm]
  · simp
  · refine ⟨Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom (Units.mk0 δ h0), fun e => ?_⟩
    have e1 : piInf τ (inclR (F := F) (AF F) δ * inclR (F := F) (AF F) (σ δ⁻¹)) = 1 := congrArg Subtype.val e
    rw [← map_mul, map_inv₀, hδ, inv_neg, mul_neg, mul_inv_cancel₀ h0, map_neg, map_one, map_neg, map_one] at e1
    norm_num at e1
  · refine ⟨_, Submodule.mem_span_singleton_self _, ⟨-1, show _ * _ * _ = _ by
      ext i j; fin_cases i; fin_cases j; simp [Formalism.UG.cT, Matrix.mul_apply]⟩, ?_⟩
    change piInf τ ((-1 : Matrix (Fin 1) (Fin 1) _) 0 0) ≠ piInf τ ((1 : Matrix (Fin 1) (Fin 1) _) 0 0)
    simp only [Matrix.neg_apply, Matrix.one_apply_eq, map_neg, map_one]
    norm_num
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ
      {fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det)}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, -, rfl⟩
    choose c hc using GlobalTheory.UAut.Model.foldr_char (φ := fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det))
      fun g h => by rw [← map_mul, ← Matrix.det_mul]; rfl
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
      simp [GlobalTheory.UAut.dop, hc, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩

example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (big F δ).J.map σ)) :
    ∃ φ : GAd σ (δ • (big F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (big F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviInducedModel

end
