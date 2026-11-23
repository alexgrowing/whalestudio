import Development.WeilBound.ThetaLifts.LatticeBasics.RankPolData
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Cardinal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele Dense

namespace Herm

theorem ode_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (h0 : f 0 = 0) (x : V) (c : ℂ)
    (h : ∀ t : ℝ, fderiv ℝ f (t • x) x = t * c * f (t • x)) : f x = 0 := by
  have d : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) * t * c / 2))) 0 t := fun t => by
    have h1 := (f.hasFDerivAt (t • x)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    refine (h1.mul (((h2.mul h2).mul_const c).div_const 2).neg.cexp).congr_deriv ?_
    simp only [one_smul, h, Function.comp, id, Pi.neg_apply, Pi.mul_apply]
    ring
  have := is_const_of_deriv_eq_zero (fun t => (d t).differentiableAt) (fun t => (d t).deriv) 1 0
  simpa [h0] using this

theorem exists_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Countable ι] (D : ι → Module.End ℂ M) (G : Submodule ℂ M)
    [FiniteDimensional ℂ G] : ∃ N : Submodule ℂ M, G ≤ N ∧ Module.rank ℂ N ≤ ℵ₀ ∧ ∀ i, ∀ x ∈ N, D i x ∈ N := by
  obtain ⟨s, rfl⟩ := Module.Finite.iff_fg.1 ‹_›
  refine ⟨Submodule.span ℂ (Set.range fun z : List ι × s => (z.1.map D).prod z.2),
    Submodule.span_mono fun x hx => ⟨([], ⟨x, hx⟩), rfl⟩,
    (rank_span_le _).trans (Cardinal.mk_range_le.trans Cardinal.mk_le_aleph0), fun i => ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem _ h => obtain ⟨⟨l, x⟩, rfl⟩ := h; exact Submodule.subset_span ⟨(i :: l, x), by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dL (p : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : Module.End ℂ (SInf F κ) where
  toFun := dOp p.1 p.2
  map_add' f g := by simp only [dOp, LineDeriv.lineDerivOp_add, map_add, smul_add]; abel
  map_smul' c f := by
    rw [dOp, dOp, LineDeriv.lineDerivOp_smul, smul_add, RingHom.id_apply]
    congr 1
    ext y
    simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (linForm p.2).hasTemperateGrowth, smul_eq_mul,
      Complex.real_smul]
    ring

theorem dL_apply (p) (f : SInf F κ) (y) :
    dL p f y = fderiv ℝ f y p.1 + (-(2 * Real.pi * Complex.I)) * ((tr κ y p.2 : ℝ) : ℂ) * f y := dOp_apply _ _ _ _

theorem actsD_dL (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (dL (fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) f) := fun r hr x => by
  have hab : ∀ t, evI F t = 0 → t • M.co.e u = 0 := fun t ht => by rw [← map_smul, hu t ht, map_zero]
  simp only [Model.heisLine, Darboux.rho, map_smul]
  exact hasDerivAt_dOp ψ hψ _ _ (fun t ht => congrArg Prod.fst (hab t ht)) (fun t ht => congrArg Prod.snd (hab t ht)) f r hr x

theorem exists_vac (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (ε : InfinitePlace F → ℤˣ) : ∃ G : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ G ∧ ∀ f₀ : SInf F (Fin n × Fin d),
      (∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ∀ f f' : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f₀ f → ActsD (evI F) (M.heisLine B.ψ u') f₀ f' →
          f' = Complex.I • f) → f₀ ∈ G := by
  have h := hB.cm
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h B.emb M.co.e fun w => ((ε w : ℤ) : ℝ) • cs (X.θ w) (W.θ w)
  have hA : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← h.2.2.2, hX.herm]
  have hC : ∀ w, (Complex.I • W.J.map (B.emb w).1)ᴴ = Complex.I • W.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2, hW.skew]
    simp
  have sj : Function.Surjective (LinearMap.fst ℝ _ _ ∘ₗ J ∘ₗ LinearMap.inr ℝ _ _) := by
    refine LinearMap.injective_iff_surjective.1 ((injective_iff_map_eq_zero _).2 fun b hb => ?_)
    have hb : (J (0, b)).1 = 0 := hb
    let e : AF F := (fun w => ((ε w : ℤ) : w.Completion), 0)
    have he : ∀ w, (e • S (0, b)).map (piInf (B.emb w)) = ((ε w : ℤ) : ℝ) • (S (0, b)).map (piInf (B.emb w)) := fun w => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def, map_mul, show algebraMap (AF F) (AE F E) e = e ⊗ₜ 1 from rfl, piInf_tmul]
      simp [e]
    have es : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b =>
      map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    have t := trace_symp (X := X) (W := W) h B.emb (e • S (0, b)) (S (J (0, b)))
    rw [M.co.form, es, map_smul] at t
    simp only [dotProduct, evI_sum, evI_mul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, congrFun (sev _).1, hb, Pi.zero_apply,
      mul_zero, zero_mul, Finset.sum_const_zero, sub_zero, map_zero, he, sJ] at t
    have q : ∀ w x, hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (((ε w : ℤ) : ℝ) • x) ((((ε w : ℤ) : ℝ) • cs (X.θ w) (W.θ w)) x) =
        hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) x (cs (X.θ w) (W.θ w) x) := fun w x => by
      rcases Int.units_eq_one_or (ε w) with h | h <;> simp [h, hf, Matrix.map_neg]
    simp only [q] at t
    have nn : ∀ w, 0 ≤ -(2 * (hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((S (0, b)).map (piInf (B.emb w)))
        (cs (X.θ w) (W.θ w) ((S (0, b)).map (piInf (B.emb w))))).re) := fun w => by
      by_cases hv : (S (0, b)).map (piInf (B.emb w)) = 0
      · simp [hv, hf]
      · linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) hv]
    have z : S (0, b) = 0 := eq_of_piInf h B.emb (sAt _) (fun c _ => smul_zero c) fun w => by
      by_contra hv
      have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => nn w).1 t.symm w (Finset.mem_univ _)
      linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) (x := (S (0, b)).map (piInf (B.emb w))) (by simpa using hv)]
    have := (sev (0, b)).2
    rw [z, map_zero] at this
    exact this.symm.trans (funext fun _ => evI_zero)
  refine ⟨⨅ p, LinearMap.ker (dL (J p) - Complex.I • dL p), ?_, fun f₀ H => (Submodule.mem_iInf _).2 fun p => ?_⟩
  · let ev : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ := ⟨⟨fun f => f 0, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    refine Module.Finite.of_injective (ev ∘ₗ Submodule.subtype _) ((injective_iff_map_eq_zero _).2 fun f hf => ?_)
    ext x
    obtain ⟨b, hb⟩ := sj x
    have hb : (J (0, b)).1 = x := hb
    refine ode_zero f.1 hf x (2 * Real.pi * Complex.I * (tr _ x (J (0, b)).2 - Complex.I * tr _ x b)) fun t => ?_
    have : dL (J (0, b)) f.1 (t • x) - Complex.I * dL (0, b) f.1 (t • x) = 0 :=
      DFunLike.congr_fun (show (dL (J (0, b)) - Complex.I • dL (0, b)) f.1 = 0 from (Submodule.mem_iInf _).1 f.2 (0, b)) (t • x)
    simp only [dL_apply, hb, map_zero, map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul] at this
    linear_combination this
  · have := H _ _ (sAt p) (sAt (J p)) (fun w => by rw [sJ]; ext i j; simp [cs, mul_assoc]) _ _
      (actsD_dL M hB.std (sAt p) f₀) (actsD_dL M hB.std (sAt (J p)) f₀)
    rw [(sev p).1, (sev p).2, (sev _).1, (sev _).2] at this
    exact sub_eq_zero.2 this

end Herm

open Herm in
theorem polRank : PolRank := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW
  choose G h1 h2 using exists_vac M hB hX hW
  let b := Module.finBasis ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
  obtain ⟨N, n1, n2, n3⟩ := exists_stable (fun i => dL (b i)) (⨆ ε, G ε)
  have all : ∀ p, ∀ f ∈ N, dL p f ∈ N := fun p f hf => by
    induction b.mem_span p using Submodule.span_induction with
    | mem p h => obtain ⟨i, rfl⟩ := h; exact n3 i f hf
    | zero => convert N.zero_mem; ext y; simp [dL_apply]
    | add p q _ _ hp hq => convert N.add_mem hp hq; ext y; simp [dL_apply]; ring
    | smul t p _ hp => convert N.smul_mem (t : ℂ) hp; ext y; simp [dL_apply]; ring
  refine (Submodule.rank_mono (show M.Pol B.ψ B.emb ≤ N from sInf_le ?_)).trans n2
  refine ⟨fun f₀ ⟨ε, H⟩ => n1 (Submodule.mem_iSup_of_mem ε (h2 ε f₀ H)), fun u hu f hf f₁ H => ?_⟩
  rw [actsD_unique M hB.std hu H]
  exact all (_, _) f hf

end GlobalTheory.ThK.Dbl

end
