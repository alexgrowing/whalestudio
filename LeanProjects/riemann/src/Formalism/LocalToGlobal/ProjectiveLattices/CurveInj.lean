import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

namespace CurveInj

section Lin

variable {k V M : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup M] [Module k M]

def evDual (φ : Module.Dual k V) : V ⊗[k] M →ₗ[k] M :=
  TensorProduct.lid k M ∘ₗ TensorProduct.map φ LinearMap.id

theorem evDual_tmul (φ : Module.Dual k V) (v : V) (m : M) : evDual φ (v ⊗ₜ[k] m) = φ v • m := by
  simp [evDual]

end Lin

theorem coeff_eq_zero {K Kl K' C : Type*} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K']
    [AddCommGroup C] [Module K C] {κ : Type*} [Fintype κ] (b : Module.Basis κ K C)
    {ι : Type*} (Ω : ι → Type*) [∀ Z, AddCommGroup (Ω Z)] [∀ Z, Module K (Ω Z)]
    (ev : ∀ Z, C →ₗ[K] Ω Z) (hev : ∀ F : C, (∀ Z, ev Z F = 0) → F = 0)
    (c : κ → K') (hc : ∀ Z, ∑ i, c i ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ev Z (b i)) = 0) : c = 0 := by
  funext i₀
  refine (Module.forall_dual_apply_eq_zero_iff Kl (c i₀)).1 fun φ => ?_
  refine (Module.forall_dual_apply_eq_zero_iff K (φ (c i₀))).1 fun ψ => ?_
  have hF : (∑ i, ψ (φ (c i)) • b i) = 0 := by
    refine hev _ fun Z => ?_
    have h := congrArg (fun t => evDual (M := Ω Z) ψ (evDual (M := Kl ⊗[K] Ω Z) φ t)) (hc Z)
    simp only [map_sum, evDual_tmul, map_zero, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    rw [map_sum]
    simpa only [map_smul] using h
  exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hF i₀

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {ι : Type} (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem vw_inj (u : WeightFamilies.Wt D j) (hinj : ∀ F : B.Cusp j u, (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {g : Rp X la N} (hg : g ∈ Vw X la N u) (h0 : ∀ Z, rzMap X la N (Ω Z) (gF Z) g = 0) : g = 0 := by
  classical
  let b := Module.finBasis B.KO (B.Cusp j u)
  have hs : Submodule.span B.KO (Set.range b) = ⊤ := b.span_eq
  rw [Vw_eq_span_image X la N u hs, ← Set.range_comp] at hg
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (Kp X la N)).1 hg
  have hc : c = 0 := by
    refine coeff_eq_zero (K := B.KO) (Kl := X.Kl la) (K' := Kp X la N) b Ω
      (fun Z => (gF Z).toLinearMap ∘ₗ X.inc u) (fun F hF => hinj F hF) c fun Z => ?_
    refine (Finset.sum_congr rfl fun i _ => ?_).trans ((map_sum _ _ _).symm.trans (h0 Z))
    rw [map_smul, Function.comp_apply, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  simp [hc]

theorem fraction_zero_injective [Finite ι] {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    (f : ↥(Frac0 X la w)) (hf : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) : f = 0 := by
  classical
  cases nonempty_fintype ι
  obtain ⟨k, g, hg, hfg⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 f.2)
  have hZ : ∀ Z, ∃ n : ℕ, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ n * g) = 0 := by
    intro Z
    have h1 := hf Z
    rw [phiZ_apply, hfg, frac_apply, map_mul, map_pow] at h1
    have hu : IsUnit (lwZ X la N (Ω Z) (gF Z) w (w0inv X la w)) := by
      refine IsUnit.of_mul_eq_one (lwZ X la N (Ω Z) (gF Z) w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
      rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]
    rw [(hu.pow k).mul_left_eq_zero, lwZ_alg,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)))] at h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h1
    exact ⟨n, by rw [map_mul, map_pow]; exact hn⟩
  choose n hn using hZ
  have hM : ∀ Z, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ (Finset.univ.sup n) * g) = 0 := by
    intro Z
    have hle : n Z ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ Z)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul, hn Z, mul_zero]
  have h0 := vw_inj X la N Ω gF _ (hinj _) (sec_pow_mul_mem X la w 0 (wt0 D j) k (Finset.univ.sup n) hg) hM
  apply Subtype.ext
  show (f : Lw X la w) = 0
  rw [hfg, frac_eq_zero_iff]
  exact ⟨_, h0⟩

end Gen

end CurveInj

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveInj [Finite (Comp (T.Q.Xo j) T.Q.c)] (hV : GenValInjSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (f : ↥(Frac0 (recPlus h j hj) la G.w))
    (hf : ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) : f = 0 :=
  CurveInj.fraction_zero_injective (recPlus h j hj) la G.N (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) G.w
    (fun u F hF => hV u F fun Z => (formsEvR_single j hG hT Z _ _).symm.trans (hF Z)) f hf

end Inst

end Formalism.L2.Pj
