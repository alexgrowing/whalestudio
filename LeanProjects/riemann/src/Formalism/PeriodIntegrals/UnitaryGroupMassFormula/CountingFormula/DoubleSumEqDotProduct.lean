import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSC

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel Matrix

section Alg

variable {F : Type} [Field F]

def qmat {n : ℕ} (b : Module.Basis (Fin n) F (Fin n → F)) (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun k i => b k i) * A

theorem pair_basis {n : ℕ} (b : Module.Basis (Fin n) F (Fin n → F)) (A : Matrix (Fin n) (Fin n) F)
    (u w : Fin n → F) : u ⬝ᵥ (A *ᵥ w) = b.equivFun u ⬝ᵥ (qmat b A *ᵥ w) := by
  rw [qmat, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (b.equivFun u)]
  congr 1
  funext i
  have h := congrFun (b.sum_equivFun u) i
  rw [Finset.sum_apply] at h
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  exact h.symm

end Alg

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def amat {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : Matrix (Fin n) (Fin n) F :=
  fun k l => (e (H.h (β k) (β l))).1

private theorem hermSp_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f s

private theorem hermSp_h_sum_right' {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) := by
  rw [H.h_herm, hermSp_h_sum_left, map_sum]
  exact Finset.sum_congr rfl (fun i _ => (H.h_herm (f i) x).symm)

private theorem hermSp_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]

theorem form_fst {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap) {n : ℕ} (β : Module.Basis (Fin n) E V)
    (x y : V) : (e (H.h x y)).1 = (sig e β x).1 ⬝ᵥ (amat H e β *ᵥ (sig e β y).2) := by
  conv_lhs => rw [← β.sum_repr x, ← β.sum_repr y]
  simp only [hermSp_h_sum_left, hermSp_h_sum_right', H.h_smul_left, hermSp_h_smul_right, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, he,
    Prod.fst_swap]
  simp only [amat, sig, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem form_snd {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap) {n : ℕ} (β : Module.Basis (Fin n) E V)
    (x y : V) : (e (H.h x y)).2 = (sig e β y).1 ⬝ᵥ (amat H e β *ᵥ (sig e β x).2) := by
  have hs : ∀ k l, (e (H.h (β k) (β l))).2 = (e (H.h (β l) (β k))).1 := fun k l => by
    rw [H.h_herm (β l) (β k), he]; rfl
  conv_lhs => rw [← β.sum_repr x, ← β.sum_repr y]
  simp only [hermSp_h_sum_left, hermSp_h_sum_right', H.h_smul_left, hermSp_h_smul_right, map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, he,
    Prod.snd_swap, hs]
  simp only [amat, sig, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem tau_zero (e : E ≃ₐ[F] F × F) {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (β : Module.Basis (Fin n) E V) : tau e β 0 = 0 := by
  simp only [tau, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Prod.mk_zero_zero, map_zero, zero_smul,
    Finset.sum_const_zero]

theorem one_sum {n : ℕ} (u w : Fin n → F) :
    ∑ k, ∑ l, u k * (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) k l : 𝒪[F]) : F) * w l = u ⬝ᵥ w := by
  simp only [Matrix.one_apply, apply_ite (fun z : 𝒪[F] => (z : F)), OneMemClass.coe_one, ZeroMemClass.coe_zero,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]

theorem coord_of_basis (M : Loc.Model F E) (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) {n : ℕ} (β : Module.Basis (Fin n) E V) :
    ∃ (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]), IsSplitCoord e H Λ π Ph := by
  classical
  have hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F] := fun x => integral_split_count F E M.L hl e x
  set A := amat H e β with hA
  set ε₁ : E := e.symm (1, 0) with hε₁
  set ε₂ : E := e.symm (0, 1) with hε₂
  have he₁ : e ε₁ = (1, 0) := by simp [ε₁]
  have he₂ : e ε₂ = (0, 1) := by simp [ε₂]
  have hε₁O : ε₁ ∈ M.L.O := (hO _).2 (by rw [he₁]; exact ⟨one_mem _, zero_mem _⟩)
  have hε₂O : ε₂ ∈ M.L.O := (hO _).2 (by rw [he₂]; exact ⟨zero_mem _, one_mem _⟩)
  have h1 : ∀ x, tau e β ((sig e β x).1, 0) = ε₁ • x := by
    intro x
    have := tau_smul e β ε₁ (sig e β x)
    rw [he₁, tau_sig] at this
    simpa using this
  have h2 : ∀ x, tau e β (0, (sig e β x).2) = ε₂ • x := by
    intro x
    have := tau_smul e β ε₂ (sig e β x)
    rw [he₂, tau_sig] at this
    simpa using this
  have memΛ : ∀ x, x ∈ Λ ↔ tau e β ((sig e β x).1, 0) ∈ Λ ∧ tau e β (0, (sig e β x).2) ∈ Λ := by
    intro x
    constructor
    · intro hx
      rw [h1, h2]
      exact ⟨Λ.smul_mem (⟨ε₁, hε₁O⟩ : M.L.O) hx, Λ.smul_mem (⟨ε₂, hε₂O⟩ : M.L.O) hx⟩
    · rintro ⟨ha, hb⟩
      have : x = tau e β ((sig e β x).1, 0) + tau e β (0, (sig e β x).2) := by
        rw [← tau_add, Prod.mk_add_mk, add_zero, zero_add]
        exact (tau_sig e β x).symm
      rw [this]
      exact Λ.add_mem ha hb

  let S₁ : Submodule 𝒪[F] (Fin n → F) :=
    { carrier := {u | tau e β (u, 0) ∈ Λ}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_ofPred_eq] at hu hv ⊢
        have : ((u + v, 0) : (Fin n → F) × (Fin n → F)) = (u, 0) + (v, 0) := by simp
        rw [this, tau_add]
        exact Λ.add_mem hu hv
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        have : ((0, 0) : (Fin n → F) × (Fin n → F)) = 0 := rfl
        rw [this, tau_zero]
        exact Λ.zero_mem
      smul_mem' := by
        intro c u hu
        simp only [Set.mem_ofPred_eq] at hu ⊢
        set a : E := algebraMap F E (c : F) with ha
        have hea : e a = ((c : F), (c : F)) := by simp [a]
        have haO : a ∈ M.L.O := (hO a).2 (by rw [hea]; exact ⟨c.2, c.2⟩)
        have := tau_smul e β a (u, 0)
        rw [hea] at this
        have hcu : ((c • u, 0) : (Fin n → F) × (Fin n → F)) = ((c : F) • u, (c : F) • (0 : Fin n → F)) := by
          rw [smul_zero]
          rfl
        rw [hcu, this]
        exact Λ.smul_mem (⟨a, haO⟩ : M.L.O) hu }
  have hS₁ : ∀ u, u ∈ S₁ ↔ tau e β (u, 0) ∈ Λ := fun u => Iff.rfl
  have hsigS : ∀ y ∈ Λ, (sig e β y).1 ∈ S₁ := by
    intro y hy
    rw [hS₁, h1]
    exact Λ.smul_mem (⟨ε₁, hε₁O⟩ : M.L.O) hy
  have hfg : S₁.FG := by
    obtain ⟨s, hs⟩ := hΛ.1
    refine ⟨s.image (fun g => (sig e β g).1), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, Finset.coe_image]
      rintro _ ⟨g, hg, rfl⟩
      exact hsigS g (hs ▸ Submodule.subset_span hg)
    · intro u hu
      rw [Finset.coe_image]
      have hu' : tau e β (u, 0) ∈ Submodule.span M.L.O (s : Set V) := by rw [hs]; exact hu
      have key : ∀ y ∈ Submodule.span M.L.O (s : Set V),
          (sig e β y).1 ∈ Submodule.span 𝒪[F] ((fun g => (sig e β g).1) '' (s : Set V)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
        | zero => rw [sig_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [sig_add]; exact Submodule.add_mem _ hx hy
        | smul a x _ hx =>
          have hs' : (sig e β (a • x)).1 = (e (a : E)).1 • (sig e β x).1 := by
            rw [show a • x = (a : E) • x from rfl, sig_smul]
          rw [hs']
          exact Submodule.smul_mem _ (⟨(e (a : E)).1, ((hO a).1 a.2).1⟩ : 𝒪[F]) hx
      have := key _ hu'
      rwa [sig_tau] at this
  have hsp : Submodule.span F (S₁ : Set (Fin n → F)) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have key : ∀ y ∈ Submodule.span E (Λ : Set V),
        (sig e β y).1 ∈ Submodule.span F (S₁ : Set (Fin n → F)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact Submodule.subset_span (hsigS g hg)
      | zero => rw [sig_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [sig_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        rw [sig_smul]
        exact Submodule.smul_mem _ _ hx
    have := key (tau e β (u, 0)) (by rw [hΛ.2.1]; trivial)
    rwa [sig_tau] at this
  obtain ⟨bF, hbS, hbmem⟩ := latBasis_exists F n S₁ hfg hsp
  set Qm := qmat bF A with hQm

  have hpair : ∀ (x : V) (w : Fin n → F), e (H.h x (tau e β (0, w))) =
      (bF.equivFun (sig e β x).1 ⬝ᵥ (Qm *ᵥ w), 0) := by
    intro x w
    ext
    · rw [form_fst H e he, sig_tau, pair_basis bF]
    · rw [form_snd H e he, sig_tau]
      simp
  have hpair' : ∀ (y : V) (w : Fin n → F), e (H.h (tau e β (0, w)) y) =
      (0, bF.equivFun (sig e β y).1 ⬝ᵥ (Qm *ᵥ w)) := by
    intro y w
    rw [H.h_herm y (tau e β (0, w)), he, hpair]
    rfl
  have hinj : Function.Injective (Matrix.mulVecLin Qm) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply] at hw
    have hz : ∀ x, H.h x (tau e β (0, w)) = 0 := by
      intro x
      apply e.injective
      rw [hpair, hw, dotProduct_zero, map_zero]
      rfl
    have hy : tau e β (0, w) = 0 := by
      apply H.nondeg
      intro z
      rw [H.h_herm z, hz, map_zero]
    have := congrArg (fun v => (sig e β v).2) hy
    simpa [sig_tau, sig_zero] using this
  let Qe : (Fin n → F) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin Qm) hinj
  let σ : V ≃+ (Fin n → F) × (Fin n → F) :=
    { toFun := sig e β
      invFun := tau e β
      left_inv := tau_sig e β
      right_inv := sig_tau e β
      map_add' := sig_add e β }
  let π : V ≃+ (Fin n → F) × (Fin n → F) :=
    σ.trans (AddEquiv.prodCongr bF.equivFun.toAddEquiv Qe.toAddEquiv)
  have hπ : ∀ x, π x = (bF.equivFun (sig e β x).1, Qm *ᵥ (sig e β x).2) := fun x => rfl

  have hdual : ∀ w, tau e β (0, w) ∈ Λ ↔ ∀ k, (Qm *ᵥ w) k ∈ 𝒪[F] := by
    intro w
    rw [hΛ.2.2]
    constructor
    · intro hall k
      have hy : tau e β (bF k, 0) ∈ Λ := hbS k
      have := ((hO _).1 (hall _ hy)).2
      rw [hpair', sig_tau] at this
      have hsingle : bF.equivFun (bF k) = Pi.single k 1 := by
        ext j
        rw [Module.Basis.equivFun_self]
        simp [Pi.single_apply, eq_comm]
      simpa [hsingle, single_dotProduct] using this
    · intro hq y hy
      rw [hO, hpair']
      refine ⟨zero_mem _, ?_⟩
      have hc := (hbmem _).1 (hsigS y hy)
      simp only [dotProduct, Module.Basis.equivFun_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hc k) (hq k)
  refine ⟨π, 1, ?_, ?_, by simp, ?_⟩
  · intro a x
    rw [hπ, hπ, sig_smul]
    simp only [map_smul, Matrix.mulVec_smul]
  · intro x
    rw [memΛ, ← hS₁, hbmem, hdual, hπ]
    simp only [Module.Basis.equivFun_apply]
  · intro x y
    rw [hπ, hπ, one_sum, one_sum]
    ext
    · rw [form_fst H e he, pair_basis bF]
    · rw [form_snd H e he, pair_basis bF]

theorem adapted_coords_self_dual : CoordData := by
  intro F E _ _ _ _ _ _ _ M hl _ e he V _ _ H Λ hΛ
  haveI := H.free
  haveI := H.fin
  haveI : Nontrivial E := e.toEquiv.nontrivial
  exact coord_of_basis M hl e he V H Λ hΛ (Module.finBasis E V)

end Main

end PI.UnitaryGroupMassFormula.CntFormula
