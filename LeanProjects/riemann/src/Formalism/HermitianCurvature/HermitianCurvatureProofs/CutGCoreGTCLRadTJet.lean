import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Jet

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem jetT_le (j : ℕ) : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)

theorem jetT_mono {N M : ℕ} (hMN : M ≤ N) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r M f g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  exact ⟨U, F, hU, hgU, hF, hfF, fun j hj => hv j (hj.trans hMN)⟩

theorem jetT_val {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (h : ZJ k r N f g₀) : f g₀ = 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  rw [hfF g₀ hgU hg₀]
  have h0 := hv 0 (Nat.zero_le _)
  calc F g₀ = iteratedFDeriv ℝ 0 F g₀ (fun i => Fin.elim0 i) := (iteratedFDeriv_zero_apply _).symm
    _ = 0 := by rw [h0]; rfl

theorem jetT_zero {N : ℕ} {g₀ : Q.Mx k r} : ZJ k r N (fun _ => (0 : E)) g₀ :=
  ⟨Set.univ, fun _ => (0 : E), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl,
    fun j _ => by rw [iteratedFDeriv_zero_fun]; rfl⟩

theorem jetT_add {N : ℕ} {f f₂ : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) (h₂ : ZJ k r N f₂ g₀) :
    ZJ k r N (fun x => f x + f₂ x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hfF₂, hv₂⟩ := h₂
  have hO : IsOpen (U ∩ U₂) := hU.inter hU₂
  have hx : g₀ ∈ U ∩ U₂ := ⟨hgU, hgU₂⟩
  have hF1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (U ∩ U₂) := hF.mono Set.inter_subset_left
  have hF2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (U ∩ U₂) := hF₂.mono Set.inter_subset_right
  refine ⟨U ∩ U₂, fun x => F x + F₂ x, hO, hx, hF1.add hF2, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg.1 hgl, hfF₂ g hg.2 hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (F + F₂) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hO hx,
      iteratedFDerivWithin_add_apply ((hF1 g₀ hx).of_le (jetT_le j)) ((hF2 g₀ hx).of_le (jetT_le j))
        hO.uniqueDiffOn hx,
      iteratedFDerivWithin_of_isOpen j hO hx, iteratedFDerivWithin_of_isOpen j hO hx, hv j hj, hv₂ j hj,
      add_zero]

theorem jetT_smul {N : ℕ} (c : ℂ) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r N (fun x => c • f x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  refine ⟨U, fun x => c • F x, hU, hgU, hF.const_smul c, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (c • F) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hU hgU,
      iteratedFDerivWithin_const_smul_apply ((hF g₀ hgU).of_le (jetT_le j)) hU.uniqueDiffOn hgU,
      iteratedFDerivWithin_of_isOpen j hU hgU, hv j hj, smul_zero]

theorem jetT_fderiv {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {g₀ : D} {i : ℕ} (h : iteratedFDeriv ℝ (i + 1) F g₀ = 0) :
    iteratedFDeriv ℝ i (fderiv ℝ F) g₀ = 0 := by
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] at h
  exact (LinearIsometryEquiv.map_eq_zero_iff _).1 h

theorem jetT_gen {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {U : Set D} (hU : IsOpen U) {g₀ : D} (hgU : g₀ ∈ U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U) (L : D →L[ℝ] D) (N : ℕ)
    (hv : ∀ j ≤ N + 1, iteratedFDeriv ℝ j F g₀ = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fderiv ℝ F x (L x)) U ∧
      ∀ j ≤ N, iteratedFDeriv ℝ j (fun x => fderiv ℝ F x (L x)) g₀ = 0 := by
  have hmn : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have hF' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F y) U := hF.fderiv_of_isOpen hU hmn
  refine ⟨hF'.clm_apply L.contDiff.contDiffOn, ?_⟩
  intro j hj
  let Bl : (D →L[ℝ] G) →L[ℝ] D →L[ℝ] G := (ContinuousLinearMap.apply ℝ G : D →L[ℝ] (D →L[ℝ] G) →L[ℝ] G).flip
  have hfun : (fun x => fderiv ℝ F x (L x)) = fun x => Bl (fderiv ℝ F x) (L x) := rfl
  have hbd := Bl.norm_iteratedFDerivWithin_le_of_bilinear hF' L.contDiff.contDiffOn hU.uniqueDiffOn hgU
    (n := j) (jetT_le j)
  have hzero : ∀ i ∈ Finset.range (j + 1), iteratedFDerivWithin ℝ i (fun y => fderiv ℝ F y) U g₀ = 0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hU hgU]
    exact jetT_fderiv (hv (i + 1) (by simp at hi; omega))
  rw [Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, norm_zero, mul_zero, zero_mul]), mul_zero] at hbd
  have h0 := norm_le_zero_iff.1 hbd
  rw [iteratedFDerivWithin_of_isOpen j hU hgU] at h0
  rw [hfun]
  exact h0

theorem jetT_rd {N : ℕ} {f : Q.Mx k r → E} {g₀ X : Q.Mx k r}
    (hX : Q.inLieLev k r (Fin.last r) X) (h : ZJ k r (N + 1) f g₀) : ZJ k r N (RdV X f) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  let L : Q.Mx k r →L[ℝ] Q.Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := fun x => rfl
  have hG := jetT_gen hU hgU hF L N hv
  refine ⟨U, fun x => fderiv ℝ F x (L x), hU, hgU, hG.1, ?_, hG.2⟩
  intro g hg hgl
  have hd : DifferentiableAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simpa using jetT_le 1)
  show RdV X f g = fderiv ℝ F g (L g)
  rw [hL]
  exact (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hg hgl hX hd hfF).deriv

theorem jetT_EH {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  have hl := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) a b
  exact jetT_add (jetT_rd hl.1 h) (jetT_smul Complex.I (jetT_rd hl.2 h))

theorem jetT_Top {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (u : ℂ) (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  by_cases hab : Q.posL k r (Fin.last r) a = Q.posL k r (Fin.last r) b
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        fun g => u • f g + Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f g := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_true]
    rw [he]
    exact jetT_add (jetT_smul u (jetT_mono (Nat.le_succ N) h)) (jetT_EH a b h)
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_false, zero_add]
    rw [he]
    exact jetT_EH a b h

theorem jetT_foldr {g₀ : Q.Mx k r} (L : List ((Q.Mx k r → E) → (Q.Mx k r → E)))
    (hL : ∀ T ∈ L, ∀ (N : ℕ) (h : Q.Mx k r → E), ZJ k r (N + 1) h g₀ → ZJ k r N (T h) g₀) :
    ∀ (N : ℕ) (f : Q.Mx k r → E), ZJ k r (N + L.length) f g₀ →
      ZJ k r N (L.foldr (fun T h => T h) f) g₀ := by
  induction L with
  | nil =>
    intro N f h
    simpa using h
  | cons T L ih =>
    intro N f h
    simp only [List.foldr_cons]
    apply hL T List.mem_cons_self N
    apply ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) (N + 1) f
    simp only [List.length_cons] at h
    rwa [show N + 1 + L.length = N + (L.length + 1) by omega]

theorem jetT_qminor {N t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (c d : Fin t → Fin (Q.mdim k r (Fin.last r)))
    (u : ℂ) (h : ZJ k r (N + t) f g₀) :
    ZJ k r N (qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f) g₀ := by
  have hG : ∀ σ : Equiv.Perm (Fin t), ZJ k r N
      ((((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (List.ofFn fun i : Fin t => Top (Q.EH k r) (u - ((i : ℕ) : ℂ))
          ((Q.posL k r (Fin.last r) ∘ c) (σ i)) ((Q.posL k r (Fin.last r) ∘ d) i)).foldr
          (fun T h => T h) f)) g₀ := by
    intro σ
    apply jetT_smul
    apply jetT_foldr
    · intro T hT N' h'' h'
      rw [List.mem_ofFn] at hT
      obtain ⟨i, rfl⟩ := hT
      exact jetT_Top _ (c (σ i)) (d i) h'
    · rwa [List.length_ofFn]
  have hsum : ∀ s : Finset (Equiv.Perm (Fin t)), ZJ k r N (∑ σ ∈ s, ((((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (List.ofFn fun i : Fin t => Top (Q.EH k r) (u - ((i : ℕ) : ℂ))
          ((Q.posL k r (Fin.last r) ∘ c) (σ i)) ((Q.posL k r (Fin.last r) ∘ d) i)).foldr
          (fun T h => T h) f))) g₀ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty]
      exact jetT_zero
    · intro σ s hσ ih
      rw [Finset.sum_insert hσ]
      exact jetT_add (hG σ) ih
  exact hsum Finset.univ

theorem jetT_qminor_val {t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (hZ : ZJ k r (Q.mdim k r (Fin.last r)) f g₀) (c d : Fin t → Fin (Q.mdim k r (Fin.last r))) (u : ℂ)
    (ht : t ≤ Q.mdim k r (Fin.last r)) :
    qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f g₀ = 0 :=
  jetT_val hg₀ (jetT_qminor c d u (jetT_mono (by omega) hZ : ZJ k r (0 + t) f g₀))

end Jet

theorem jet_finite_order_along_level : GTCLRJetT := by
  intro E _ _ k r z z' Y a b
  refine ⟨Q.mdim k r (Fin.last r), ?_⟩
  intro f g₀ hg₀ hZ
  have hq : ∀ {t : ℕ} (c d : Fin t → Fin (Q.mdim k r (Fin.last r))) (u : ℂ), t ≤ Q.mdim k r (Fin.last r) →
      qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f g₀ = 0 :=
    fun c d u ht => jetT_qminor_val hg₀ hZ c d u ht
  match a, b with
  | 0, 0 => exact hq id id _ le_rfl
  | 0, 1 =>
    simp only [Q.tL, Pi.neg_apply, Q.chatL, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
  | 1, 0 =>
    simp only [Q.tL, Pi.neg_apply, Q.chatL, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
  | 1, 1 =>
    simp only [Q.tL, Pi.neg_apply, Q.chat2L, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ =>
      Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
    split_ifs
    · rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
    · rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
