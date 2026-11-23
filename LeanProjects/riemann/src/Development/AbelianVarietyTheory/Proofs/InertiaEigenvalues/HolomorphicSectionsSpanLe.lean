import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndependeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CuspDescent

theorem exists_indep_comb {K R V : Type} [Field K] [AddCommGroup R] [Module K R] [AddCommGroup V] [Module ℂ V]
    (σ : K →+* ℂ) (ρ : R →ₛₗ[σ] V) (S : Submodule K R) {P : V} (hP : P ∈ Submodule.span ℂ (ρ '' (S : Set R))) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (f : Fin m → R), (∀ i, f i ∈ S) ∧
      (∀ c : Fin m → K, ∑ i, σ (c i) * e i = 0 → c = 0) ∧ P = ∑ i, e i • ρ (f i) := by
  obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.1 hP
  choose g hg hgv using fun k => (v k).2
  letI : Algebra K ℂ := σ.toAlgebra
  have hsm : ∀ (a : K) (x : ℂ), a • x = σ a * x := fun a x => by rw [Algebra.smul_def]; rfl
  let W : Submodule K ℂ := Submodule.span K (Set.range z)
  have hzW : ∀ k, z k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range z)
  let ζ := Module.finBasis K W
  let β : Fin n → Fin (Module.finrank K W) → K := fun k m => ζ.repr ⟨z k, hzW k⟩ m
  have hzexp : ∀ k, z k = ∑ m, σ (β k m) * (ζ m : ℂ) := by
    intro k
    have h2 := congrArg Subtype.val (ζ.sum_repr ⟨z k, hzW k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h2
    exact h2.symm
  have hlin : LinearIndependent K (fun m => (ζ m : ℂ)) :=
    ζ.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  refine ⟨_, fun m => (ζ m : ℂ), fun m => ∑ k, β k m • g k,
    fun m => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k), fun c hc => ?_, ?_⟩
  · funext m
    exact (Fintype.linearIndependent_iff.1 hlin) c (by simpa only [hsm] using hc) m
  · rw [← hv]
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul, hgv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, hzexp k]
    congr 1
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Geometric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rd_prod {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) (f : Fin (N + 1) → Rul Xo c) :
    rdU U (∏ t, f t) = ∏ t, rdU U (f t) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Fin.prod_univ_castSucc, GlobalTheory.CuspAllEmb.rd_mul, ih, ← Fin.prod_univ_castSucc fun t => rdU U (f t)]

theorem prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (N : ℕ) (f : Fin (N + 1) → Rul Xo c)
    (hf : ∀ t, f t ∈ sec Xo c a n) : ∏ t, f t ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) := by
  induction N with
  | zero => simpa using hf 0
  | succ N ih =>
    rw [succ_nsmul, add_mul _ 1, one_mul, Fin.prod_univ_castSucc]
    exact sec_mul Xo c _ _ _ _ (ih _ fun t => hf _) (hf _)

theorem pow_comb {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) {ι : Type} [Fintype ι] (e : ι → ℂ) (f : ι → Rul Xo c) :
    (∑ i, e i • rdU U (f i)) ^ (N + 1) =
      ∑ p : Fin (N + 1) → ι, (∏ t, e (p t)) • rdU U (∏ t, f (p t)) := by
  classical
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rd_prod, Finset.prod_smul]

theorem isSec_comb (X : Data E r) (la : Wt X.Ψ r) {ι : Type} [Fintype ι] (e : ι → ℂ) (Q : ι → Frame X.Ψ r → ℂ)
    (hQ : ∀ i, X.IsSec la (Q i)) : X.IsSec la (∑ i, e i • Q i) := by
  refine ⟨DifferentiableOn.sum fun i _ => (hQ i).1.const_smul (e i), fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.1 x hx b hb]; ring
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.2 γ hγ x hx]; ring

theorem descent (hf : 1 < Module.finrank ℚ E / 2) {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (N : ℕ)
    (hI : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c ((N + 1) • a) ((N + 1) * n)) →
      LinearIndependent c.F b → LinearIndependent ℂ fun i => rdU U (b i))
    (hspan : holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) ≤ Submodule.span ℂ (rdU U ''
      {g | g ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) ∧ rdU U g ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n))})) :
    holSub0 U.X (laU U a n) ⊓ Submodule.span ℂ (rdU U '' (sec Xo c a n : Set (Rul Xo c))) ≤
      Submodule.span ℂ (rdU U '' {f | f ∈ sec Xo c a n ∧ rdU U f ∈ holSub0 U.X (laU U a n)}) := by
  classical
  rintro P ⟨hP, hPs⟩
  obtain ⟨m, e, f, hfs, he, rfl⟩ := exists_indep_comb σ (rdU U) _ hPs
  have hoff : ∀ e' : Fin m → ℂ, ∑ i, e' i • rdU U (f i) ∈ offZero U.X := fun e' =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  have hpow : (∑ i, e i • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, ?_⟩
    · have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hP.1 k
      rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2]
      rcases N with _ | N
      · simpa using h1
      · have h2 := GlobalTheory.CuspAllEmb.ss_mul _ hf h1 (GlobalTheory.CuspAllEmb.isSec_pow _ h1.1.1 N)
        rw [← pow_succ', ← succ_nsmul'] at h2
        exact h2
    · rw [pow_comb]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  obtain ⟨q, z, v, hv⟩ := Submodule.mem_span_set'.1 (hspan hpow)
  choose g hg hgv using fun k => (v k).2
  have conj : ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) →
      ∑ i, φ (e i) • rdU U (f i) ∈ holSub0 U.X (laU U a n) := by
    intro φ hφ
    have tr := GlobalTheory.CuspAllEmb.transfer (φ : ℂ →+* ℂ) hφ (rdU U) (rdU U) _ hI
      (fun p : Fin (N + 1) → Fin m => ∏ t, f (p t)) g (fun p => prod_mem_sec N _ fun t => hfs _) (fun k => (hg k).1)
      (fun p => ∏ t, e (p t)) z (by rw [← pow_comb, ← hv]; simp only [hgv])
    simp only [map_prod, RingHom.coe_coe] at tr
    rw [← pow_comb U N (fun i => φ (e i)) f] at tr
    have hm : (∑ i, φ (e i) • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
      rw [tr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k).2
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, hoff _⟩
    have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hm.1 k
    rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2] at h1
    refine GlobalTheory.CuspAllEmb.ss_of_pow _ hf ?_ N h1
    have := isSec_comb (U.X k) (laU U a n k) (fun i => φ (e i)) (fun i => rdU U (f i) k)
      (fun i => hU.2.2.2.2.1 a n hd _ (hfs i) k)
    simpa only [Finset.sum_apply, Pi.smul_apply] using this
  haveI := c.fin
  haveI : NumberField c.F := {}
  have htop := GlobalTheory.T.span_automorphismConjugates_of_numberField_independent_eq_top c.F σ (Fin m) e he
  let L : (Fin m → ℂ) →ₗ[ℂ] FDSec U.X := Fintype.linearCombination ℂ fun i => rdU U (f i)
  have hle : (⊤ : Submodule ℂ (Fin m → ℂ)) ≤ (holSub0 U.X (laU U a n)).comap L := by
    rw [← htop, Submodule.span_le]
    rintro _ ⟨φ, hφ, rfl⟩
    exact conj φ hφ
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f i, ⟨hfs i, ?_⟩, rfl⟩)
  have := hle (Submodule.mem_top (x := Pi.single i 1))
  simpa [L] using this

end Geometric

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in

theorem cusp_descends : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ⊓ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (wtA w) w.n : Set (Rul (T.Q.Xo j) T.Q.c))) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T h j hj σ hσ w hw hn
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have h8 := D.eight_le_f
  set N := 8 * D.R.f * D.R.r + 3 with hN
  have hA : wtA (WeightAlgebra.wsmul (N + 1) w) = (N + 1) • wtA w := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold wtA
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [WeightAlgebra.wsmul, ext0]
    split_ifs <;> ring
  have hd : Dom ((N + 1) • wtA w) ((N + 1) * w.n) := hA ▸ dom_wtA (WeightAlgebra.wsmul (N + 1) w)
  refine descent (by omega) (T.U j σ) (h.unf j hj σ hσ) (dom_wtA w) N
    (GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ _ _ hd) ?_
  have key := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj (WeightAlgebra.wsmul (N + 1) w)
    (fun τ i hi => Nat.mul_pos (Nat.succ_pos N) (hw τ i hi)) (Nat.le_mul_of_pos_right _ hn) σ hσ
  rw [hA] at key
  refine key.trans (Submodule.span_mono (Set.image_mono fun g hg => ?_))
  exact ⟨cusp_le_sec _ _ _ _ _ hg, ((mem_cusp _ _ _ _ _ _).1 hg).2 σ hσ, rdU_mem_offZero _ _⟩

end GlobalTheory.CuspDescent
