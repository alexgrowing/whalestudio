import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BranchingRankTwo

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem exists_embU_one (τ : E →+* ℂ) (z : ℂ) (hz : ‖z‖ = 1) : ∃ x ∈ embU 1 τ, cEmb τ x 0 0 = z := by
  classical
  let z' : ℂ := if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z
  have hz' : star z' * z' = 1 := by
    have h : ‖z'‖ = 1 := by
      simp only [z']
      split_ifs <;> simp [hz]
    rw [mul_comm]
    change z' * starRingEnd ℂ z' = 1
    rw [Complex.mul_conj', h]
    simp
  let c : Cinf E := Function.update 1 (InfinitePlace.mk τ) z'
  have hc : star c * c = 1 := by
    funext w
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      simpa [c] using hz'
    · simp [c, h]
  let y : GL (Fin 1) (Cinf E) := GeneralLinearGroup.scalar (Fin 1) ⟨c, star c, by rw [mul_comm, hc], hc⟩
  have hy : y.val 0 0 = c := by simp [y]
  have hU : infGL E 1 y ∈ UA E 1 := infGL_mem_UA y (by
    ext1 i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [Matrix.mul_apply, hy, hc])
  have he : ∀ τ' : E →+* ℂ, cEmb τ' ⟨_, hU⟩ 0 0 = coord τ' c := fun τ' => by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E 1 y)) 0 0 = _
    rw [pInf_infGL, ← hy]
    rfl
  refine ⟨⟨_, hU⟩, ⟨pFin_infGL y, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    refine (he τ').trans ?_
    unfold coord
    split_ifs <;> simp [c, h]
  · rw [he]
    unfold coord
    split_ifs with h <;> simp [c, z', h]

theorem weight_eq_zero_of_const (τ : E →+* ℂ) (lam : DomWeight 1)
    (h : HasWeightAt (Submodule.span ℂ {(fun _ => 1 : UA E 1 → ℂ)}) τ lam) : lam.w 0 = 0 := by
  obtain ⟨-, f, h0, h1, h2⟩ := h
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
  by_contra hl
  have hl' : (lam.w 0 : ℂ) ≠ 0 := by exact_mod_cast hl
  obtain ⟨x, hx, e⟩ := exists_embU_one τ _ (Complex.norm_exp_ofReal_mul_I (Real.pi / lam.w 0))
  have h3 := h2 ⟨x, hx⟩ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h1 v)
  have h4 : RU E 1 x (f v) = f v := by rw [← hc]; rfl
  rw [GlobalTheory.Branching.RankTwo.small_act, map_smul] at h3
  change (cEmb τ x 0 0) ^ lam.w 0 • f v = RU E 1 x (f v) at h3
  rw [e, h4, ← Complex.exp_int_mul, show (lam.w 0 : ℂ) * (((Real.pi / lam.w 0 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
    push_cast; field_simp, Complex.exp_pi_mul_I] at h3
  have h5 : (2 : ℂ) • f v = 0 := by linear_combination (norm := module) -h3
  exact hv ((smul_eq_zero.1 h5).resolve_left two_ne_zero)

theorem isCompAlong_const {n : ℕ} (Gv : Subgroup (UA E n)) {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
    (p : Gv →* H) {σ : Representation ℂ H W} (φ : (Representation.trivial ℂ H ℂ).Equiv σ) :
    IsCompAlong (Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}) Gv p σ := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ
    ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩),
    (LinearMap.toSpanSingleton ℂ _ fun _ => 1).comp φ.symm.toLinearMap, fun h => ?_,
    fun v => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun x v => ?_⟩
  · have := congrFun (LinearMap.congr_fun h (φ 1)) 1
    simp at this
  · have : φ.symm (σ (p x) v) = φ.symm v := LinearMap.congr_fun (φ.symm.isIntertwining' (p x)) v
    funext g
    change φ.symm (σ (p x) v) • (1 : ℂ) = φ.symm v • (1 : ℂ)
    rw [this]

theorem hasWeightAt_const (τ : E →+* ℂ) :
    HasWeightAt (Submodule.span ℂ {(fun _ => 1 : UA E 1 → ℂ)}) τ ⟨0, antitone_const⟩ := by
  let lam : DomWeight 1 := ⟨0, antitone_const⟩
  have h0 : GlobalTheory.Branching.RankTwo.one' lam ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  refine isCompAlong_const _ _ (.mk (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ _ (GlobalTheory.Branching.RankTwo.one' lam))
    ⟨smul_left_injective ℂ h0, fun f => ⟨_, (GlobalTheory.Branching.RankTwo.eq_smul_one lam f).symm⟩⟩) fun g => ?_)
  refine LinearMap.ext fun c => ?_
  refine Eq.trans ?_ (GlobalTheory.Branching.RankTwo.small_act lam g _).symm
  simp [lam]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
omit [IsCMField E] in

theorem nonempty_equiv_locProd_triv {n : ℕ} (h : ∑ _ : Fin 1, n = n) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ).Equiv
      (locProd h w fun _ => SmIrr.triv _)) :=
  GlobalTheory.LocGL.nonempty_equiv_multiProd_one (SmIrr.triv _).smooth _ fun a i => Fin.ext (by
    rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp)

end GlobalTheory.UnitaryBC

end
