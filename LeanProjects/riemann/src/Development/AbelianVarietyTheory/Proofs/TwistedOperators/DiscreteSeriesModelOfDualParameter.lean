import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjDS

open Matrix Formalism.REAL Formalism.QuantumDeterminants

section Conj

def Cj (H : Type) : Type := H

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : NormedAddCommGroup (Cj H) := inferInstanceAs (NormedAddCommGroup H)

instance : Module ℂ (Cj H) := Module.compHom H (starRingEnd ℂ)

instance : InnerProductSpace ℂ (Cj H) where
  norm_smul_le a x := by
    change ‖(starRingEnd ℂ a) • (show H from x)‖ ≤ ‖a‖ * ‖(show H from x)‖
    rw [norm_smul]; simp
  inner x y := ⟪(show H from y), (show H from x)⟫_ℂ
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) (show H from x)
  conj_inner_symm x y := inner_conj_symm (𝕜 := ℂ) (show H from y) (show H from x)
  add_left x y z := inner_add_right (𝕜 := ℂ) (show H from z) (show H from x) (show H from y)
  smul_left x y r := inner_smul_right (𝕜 := ℂ) (show H from y) (show H from x) (starRingEnd ℂ r)

def cj : Cj H ≃ₗᵢ⋆[ℂ] H where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

variable {H}

def cjOp (A : H →L[ℂ] H) : Cj H →L[ℂ] Cj H where
  toFun x := (cj H).symm (A (cj H x))
  map_add' x y := by simp
  map_smul' a x := by simp [map_smulₛₗ]
  cont := (cj H).symm.continuous.comp (A.continuous.comp (cj H).continuous)

theorem cj_cjOp (A : H →L[ℂ] H) (x : Cj H) : cj H (cjOp A x) = A (cj H x) := rfl

end Conj

section Rev

variable {n : ℕ}

def rv (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.revPerm Fin.revPerm

theorem rv_rv (g : Matrix (Fin n) (Fin n) ℂ) : rv (rv g) = g := by
  ext i j
  simp [rv]

theorem rv_mul (g h : Matrix (Fin n) (Fin n) ℂ) : rv (g * h) = rv g * rv h := by
  unfold rv
  rw [submatrix_mul_equiv]

theorem rv_one : rv (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold rv
  exact submatrix_one_equiv _

theorem rv_ct (g : Matrix (Fin n) (Fin n) ℂ) : rv gᴴ = (rv g)ᴴ := rfl

theorem rv_diag (d : Fin n → ℂ) : rv (diagonal d) = diagonal fun a => d a.rev := by
  unfold rv
  rw [submatrix_diagonal_equiv]
  rfl

theorem rv_cont : Continuous (rv : Matrix (Fin n) (Fin n) ℂ → _) := by
  unfold rv
  exact continuous_id.matrix_submatrix _ _

variable {ε ε' : Fin n → Bool}

theorem sg_symm (he : ∀ a, ε' a = ε a.rev) : ∀ a, ε a = ε' a.rev := fun a => by rw [he, Fin.rev_rev]

theorem rv_Jm (he : ∀ a, ε' a = ε a.rev) : rv (Formalism.REAL.Jm ε') = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [rv_diag]
  congr 1
  funext a
  simp [he]

theorem rv_UJ (he : ∀ a, ε' a = ε a.rev) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε') : rv g ∈ UJset ε := by
  have h0 : gᴴ * Formalism.REAL.Jm ε' * g = Formalism.REAL.Jm ε' := hg
  show (rv g)ᴴ * Formalism.REAL.Jm ε * rv g = Formalism.REAL.Jm ε
  rw [← rv_ct, ← rv_Jm he, ← rv_mul, ← rv_mul, h0]

theorem rv_K (he : ∀ a, ε' a = ε a.rev) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε') :
    rv g ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← rv_ct, ← rv_mul, hu, rv_one]
  · rw [← rv_Jm he, ← rv_mul, ← rv_mul, hc]

def nr (μ : Fin n → ℝ) : Fin n → ℝ := fun a => -μ a.rev

theorem nr_nr (μ : Fin n → ℝ) : nr (nr μ) = μ := by
  funext a
  simp [nr]

theorem card_rev (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin n => p b.rev).card = (Finset.univ.filter p).card := by
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro a ha <;> simp_all

theorem rhoC_rev (he : ∀ a, ε' a = ε a.rev) : Formalism.REAL.rhoC ε' = nr (Formalism.REAL.rhoC ε) := by
  funext a
  have h1 := card_rev (fun b => a.rev < b ∧ ε b = ε a.rev)
  have h2 := card_rev (fun b => b < a.rev ∧ ε b = ε a.rev)
  simp only [Fin.rev_lt_rev] at h1 h2
  simp only [Formalism.REAL.rhoC, nr, he]
  rw [h1, h2]
  ring

theorem rhoN_rev (he : ∀ a, ε' a = ε a.rev) : Formalism.REAL.rhoN ε' = nr (Formalism.REAL.rhoN ε) := by
  funext a
  have h1 := card_rev (fun b => a.rev < b ∧ ε b ≠ ε a.rev)
  have h2 := card_rev (fun b => b < a.rev ∧ ε b ≠ ε a.rev)
  simp only [Fin.rev_lt_rev] at h1 h2
  simp only [Formalism.REAL.rhoN, nr, he]
  rw [h1, h2]
  ring

theorem lowK_rev (he : ∀ a, ε' a = ε a.rev) (lam : Fin n → ℝ) :
    Formalism.QuantumDeterminants.lowK ε' (nr lam) = nr (Formalism.QuantumDeterminants.lowK ε lam) := by
  funext a
  simp only [Formalism.QuantumDeterminants.lowK, rhoN_rev he, rhoC_rev he, nr, Pi.add_apply, Pi.sub_apply]
  ring

theorem vNormSq_rev (he : ∀ a, ε' a = ε a.rev) (μ : Fin n → ℝ) : vNormSq ε' (nr μ) = vNormSq ε μ := by
  simp only [vNormSq, Formalism.REAL.nsq, Formalism.REAL.dot, rhoC_rev he]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun a => by simp [nr]; ring)

private theorem sum_rev_smul_root_apply (c : Fin n → Fin n → ℕ) (x : Fin n) :
    (∑ a, ∑ b, ((c b.rev a.rev : ℕ) : ℝ) • Formalism.REAL.root a b) x =
      -((∑ a, ∑ b, ((c a b : ℕ) : ℝ) • Formalism.REAL.root a b) x.rev) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun b => ?_)
  rw [← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun a => ?_)
  simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, Fin.revPerm_apply, Fin.rev_inj]
  split_ifs <;> ring

theorem cdom_rev (he : ∀ a, ε' a = ε a.rev) {μ Λ : Fin n → ℝ} (h : CDom ε' μ Λ) : CDom ε (nr μ) (nr Λ) := by
  obtain ⟨c, hc, hsum⟩ := h
  refine ⟨fun a b => c b.rev a.rev, fun a b hab => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ hab
    refine ⟨Fin.rev_lt_rev.mp h1, ?_⟩
    rw [he, he, Fin.rev_rev, Fin.rev_rev] at h2
    exact h2.symm
  · funext x
    have hx := congrFun hsum x.rev
    rw [sum_rev_smul_root_apply c x]
    simp only [nr, Pi.sub_apply] at hx ⊢
    rw [← hx]
    ring

def rvU (he : ∀ a, ε' a = ε a.rev) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨⟨rv g.1.1, rv g.1.2, by rw [← rv_mul, g.1.3, rv_one], by rw [← rv_mul, g.1.4, rv_one]⟩, rv_UJ he g.2⟩
  invFun g := ⟨⟨rv g.1.1, rv g.1.2, by rw [← rv_mul, g.1.3, rv_one], by rw [← rv_mul, g.1.4, rv_one]⟩,
    rv_UJ (sg_symm he) g.2⟩
  left_inv g := Subtype.ext (Units.ext (rv_rv _))
  right_inv g := Subtype.ext (Units.ext (rv_rv _))
  map_mul' g h := Subtype.ext (Units.ext (rv_mul _ _))

theorem rvU_cont (he : ∀ a, ε' a = ε a.rev) : Continuous (rvU he) := by
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact rv_cont.comp (Units.continuous_val.comp continuous_subtype_val)
  · exact rv_cont.comp (Units.continuous_coe_inv.comp continuous_subtype_val)

theorem memLp_rev (he : ∀ a, ε' a = ε a.rev) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ rvU he) 2 (Formalism.REAL.muG ε') := by
  have hc : Continuous (rvU he) := rvU_cont he
  have hcs : Continuous (rvU he).symm := rvU_cont (sg_symm he)
  have : (Measure.map (rvU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (rvU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (rvU he) (Formalism.REAL.muG ε') =
      Measure.haarScalarFactor (Measure.map (rvU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul _ _
  refine MemLp.comp_of_map ?_ hc.measurable.aemeasurable
  rw [hmap]
  exact hF.smul_measure ENNReal.coe_ne_top

end Rev

section Transfer

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem symm_inter (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v)) :
    ∀ g v, T.symm (σ g v) = σ' (rv g) (T.symm v) := by
  intro g v
  apply T.injective
  rw [T.apply_symm_apply, h, rv_rv, T.apply_symm_apply]

theorem inner_conj_map (T : H' ≃ₗᵢ⋆[ℂ] H) (x y : H') : ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ := by
  have hre : ∀ u w : H', RCLike.re ⟪T u, T w⟫_ℂ = RCLike.re ⟪u, w⟫_ℂ := by
    intro u w
    rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
      T.norm_map, T.norm_map, T.norm_map]
  have h1 := hre x y
  have h2 := hre x (Complex.I • y)
  rw [LinearIsometryEquiv.map_smulₛₗ, inner_smul_right, inner_smul_right] at h2
  have s1 := inner_re_symm (𝕜 := ℂ) y x
  have s2 := inner_im_symm (𝕜 := ℂ) y x
  apply Complex.ext
  · simp only [RCLike.re_to_complex] at h1 s1 ⊢
    rw [h1, s1]
  · simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.conj_I, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h2 s2 ⊢
    linarith

theorem wt_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {μ : Fin n → ℝ} {v : H'} (hv : IsWtOn (Formalism.REAL.Kset ε') σ' μ v) :
    IsWtOn (Formalism.REAL.Kset ε) σ (nr μ) (T v) := by
  intro θ hθ
  have hK := rv_K (sg_symm he) hθ
  rw [rv_diag] at hK
  have h1 := hv (fun a => θ a.rev) hK
  have h2 := h (diagonal fun a => Complex.exp ((θ a.rev : ℂ) * Complex.I)) v
  rw [h1, rv_diag] at h2
  simp only [Fin.rev_rev] at h2
  rw [← h2, LinearIsometryEquiv.map_smulₛₗ]
  congr 1
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  have hs : ∑ a, nr μ a * θ a = -∑ a, μ a * θ a.rev := by
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun a => by simp [nr])
  rw [hs]
  push_cast
  ring

theorem finite_comap (T : H ≃ₗᵢ⋆[ℂ] H') (S : Submodule ℂ H') [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (S.comap (T.toLinearEquiv : H →ₗ⋆[ℂ] H')) := by
  have hS : S.FG := Module.Finite.iff_fg.mp inferInstance
  rw [Submodule.comap_equiv_eq_map_symm]
  exact Module.Finite.iff_fg.mpr (hS.map _)

theorem ktype_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {Λ : Fin n → ℝ} {S : Submodule ℂ H'} (hS : IsKTypeOf ε' σ' Λ S) :
    IsKTypeOf ε σ (nr Λ) (S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H')) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  have hinv := symm_inter T h
  refine ⟨finite_comap T.symm S, ?_, ?_, ?_, ?_⟩
  · intro g hg w hw
    show T.symm (σ g w) ∈ S
    rw [hinv]
    exact hst _ (rv_K (sg_symm he) hg) _ hw
  · intro S' hle hst'
    have hst'' : IsKStableOn ε' σ' (S'.comap (T.toLinearEquiv : H' →ₗ⋆[ℂ] H)) := by
      intro g hg v hv
      show T (σ' g v) ∈ S'
      rw [h]
      exact hst' _ (rv_K he hg) _ hv
    have hle' : S'.comap (T.toLinearEquiv : H' →ₗ⋆[ℂ] H) ≤ S := by
      intro v hv
      have : T v ∈ S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := hle hv
      simpa using this
    rcases hirr _ hle' hst'' with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have : T.symm w ∈ S'.comap (T.toLinearEquiv : H' →ₗ⋆[ℂ] H) := by
        show T (T.symm w) ∈ S'
        simpa using hw
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      simpa using this
    · right
      apply le_antisymm hle
      intro w hw
      have hw' : T.symm w ∈ S'.comap (T.toLinearEquiv : H' →ₗ⋆[ℂ] H) := by
        rw [h0]
        exact hw
      have : T (T.symm w) ∈ S' := hw'
      simpa using this
  · refine ⟨T v, ?_, ?_, wt_transfer he T h hvw⟩
    · show T.symm (T v) ∈ S
      simpa using hvS
    · simpa using hv0
  · intro μ w hw hw0 hww
    have hv' := wt_transfer (sg_symm he) T.symm hinv hww
    have hd := hdom (nr μ) (T.symm w) hw (by simpa using hw0) hv'
    have := cdom_rev he hd
    rwa [nr_nr] at this

theorem isDS_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) : IsDS ε' (nr lam) σ' := by
  obtain ⟨hcomp, hnt, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := hσ
  have key : ∀ g v, σ' g v = T.symm (σ (rv g) (T v)) := fun g v => by
    rw [← h, T.symm_apply_apply]
  have hinv := symm_inter T h
  refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := hcomp
    exact T.toIsometryEquiv.completeSpace
  · have := hnt
    exact T.toLinearEquiv.toEquiv.nontrivial
  · ext v
    rw [key, rv_one, h1]
    simp
  · intro a ha b hb
    ext v
    rw [ContinuousLinearMap.comp_apply, key, key, key, rv_mul, hmul _ (rv_UJ he ha) _ (rv_UJ he hb),
      ContinuousLinearMap.comp_apply, T.apply_symm_apply]
  · intro g hg v
    rw [key, LinearIsometryEquiv.norm_map, hnorm _ (rv_UJ he hg), LinearIsometryEquiv.norm_map]
  · intro v
    have hfun : (fun g => σ' g v) = fun g => T.symm (σ (rv g) (T v)) := funext fun g => key g v
    rw [hfun]
    exact T.symm.continuous.comp_continuousOn
      ((hcont (T v)).comp rv_cont.continuousOn (fun g hg => rv_UJ he hg))
  · intro S hcl hst
    have hcl' : IsClosed ((S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') : Submodule ℂ H) : Set H) :=
      hcl.preimage T.symm.continuous
    have hst' : ∀ g ∈ UJset ε, ∀ w ∈ S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H'),
        σ g w ∈ S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
      intro g hg w hw
      show T.symm (σ g w) ∈ S
      rw [hinv]
      exact hst _ (rv_UJ (sg_symm he) hg) _ hw
    rcases hirr _ hcl' hst' with h0 | h0
    · left
      rw [eq_bot_iff]
      intro v hv
      have : T v ∈ S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
        show T.symm (T v) ∈ S
        simpa using hv
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      simpa using this
    · right
      rw [eq_top_iff]
      intro v _
      have : T v ∈ S.comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
        rw [h0]
        exact Submodule.mem_top
      have : T.symm (T v) ∈ S := this
      simpa using this
  · intro v w
    have hm := memLp_rev he (hsq (T v) (T w))
    have hfun : coefOn (ε := ε') σ' v w =
        fun g => starRingEnd ℂ ((coefOn (ε := ε) σ (T v) (T w) ∘ rvU he) g) := by
      funext g
      simp only [coefOn, Function.comp]
      conv_lhs => rw [← T.symm_apply_apply w, key]
      rw [inner_conj_map T.symm, inner_conj_symm]
      rfl
    rw [hfun]
    exact hm.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hm.1)
      (Filter.Eventually.of_forall fun g => by simp)
  · obtain hK := ktype_transfer (sg_symm he) T.symm hinv hS0
    exact ⟨_, by rw [lowK_rev he]; exact hK⟩
  · intro μ S' hS'
    have hK := ktype_transfer he T h hS'
    have hle := hmin _ _ hK
    rw [lowK_rev he, vNormSq_rev he, ← nr_nr μ, vNormSq_rev he]
    exact hle

theorem isEnum_dual {S : SPar} {lam : Fin n → ℝ} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (nr lam) (fun a => ε a.rev) := by
  obtain ⟨hanti, q, hq, hS⟩ := h
  refine ⟨fun a b hab => ?_, fun a => -q a.rev, fun a => ?_, ?_⟩
  · simp only [nr]
    exact neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab))
  · simp [nr, hq]
  · rw [hS, dualPar, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, rfl⟩

private theorem rv_revPerm_conj_eq_conj {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) :
    rv (A.submatrix Fin.revPerm (Equiv.refl (Fin n)) * g * (A.submatrix Fin.revPerm (Equiv.refl (Fin n)))⁻¹) =
      A * g * A⁻¹ := by
  rw [inv_submatrix_equiv]
  have e1 : A.submatrix Fin.revPerm (Equiv.refl (Fin n)) * g =
      (A * g).submatrix Fin.revPerm (Equiv.refl (Fin n)) := by
    rw [← submatrix_mul_equiv A g Fin.revPerm (Equiv.refl (Fin n)) (Equiv.refl (Fin n))]
    simp
  rw [e1, submatrix_mul_equiv]
  unfold rv
  ext i j
  simp

end Transfer

def conjModel {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    DSModel V (fun τ => dualPar (S τ)) where
  H τ := Cj (M.H τ)
  σ τ g := cjOp (M.σ τ (rv g))
  lam τ := nr (M.lam τ)
  ε τ a := M.ε τ a.rev
  fr τ := (M.fr τ).submatrix Fin.revPerm (Equiv.refl _)
  enum τ := isEnum_dual (M.enum τ)
  ds τ := isDS_transfer (fun _ => rfl) (cj (M.H τ)) (fun _ _ => rfl) (M.ds τ)
  fr_unit τ := (Matrix.isUnit_submatrix_equiv _ _).2 (M.fr_unit τ)
  fr_gram τ := by
    rw [← M.fr_gram τ, ← rv_Jm (ε := fun a => M.ε τ a.rev) (ε' := M.ε τ) (fun a => by simp), rv,
      conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    rfl

theorem exists_conjModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  intro D V S M
  refine ⟨conjModel M, fun τ => cj (M.H τ), fun τ g _ w => ?_⟩
  simp only [DSModel.rep, conjModel]
  rw [rv_revPerm_conj_eq_conj]
  exact cj_cjOp _ _

end GlobalTheory.ConjDS
