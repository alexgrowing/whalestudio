import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC.Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

example (γ : latticeGL E n) (g : GA E n) : γ • g = γ.1 * g := rfl

variable (E n) in

abbrev constU : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}

theorem sum_one (n : ℕ) : ∑ _i : Fin 1, n = n := by simp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
omit [IsCMField E] in

theorem equiv_triv (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ).Equiv
      (locProd (N := fun _ : Fin 1 => n) (sum_one n) w fun _ => SmIrr.triv _)) :=
  GlobalTheory.LocGL.nonempty_equiv_multiProd_one (SmIrr.triv _).smooth _
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; simp [Subsingleton.elim a 0]))

section Triv

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ H W}

theorem act_eq (e : (Representation.trivial ℂ H ℂ).Equiv ρ) (g : H) (v : W) : ρ g v = v := by
  obtain ⟨c, rfl⟩ := e.toLinearEquiv.surjective v
  exact (LinearMap.congr_fun (e.isIntertwining' g) c).symm

theorem compAlong_triv (e : (Representation.trivial ℂ H ℂ).Equiv ρ) (Gv : Subgroup (UA E n)) (p : Gv →* H) :
    IsCompAlong (constU E n) Gv p ρ := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv e
    (by letI : TopologicalSpace H := ⊥; exact (SmIrr.triv H).irred),
    (LinearMap.toSpanSingleton ℂ _ (fun _ => 1)).comp e.toLinearEquiv.symm.toLinearMap, fun h => ?_,
    fun v => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun x v => ?_⟩
  · have := congrFun (LinearMap.congr_fun h (e.toLinearEquiv 1)) 1
    have h2 : e.toLinearEquiv.symm (e.toLinearEquiv 1) • (1 : ℂ) = 0 := this
    rw [LinearEquiv.symm_apply_apply] at h2
    simp at h2
  · rw [act_eq e]; rfl

theorem spherical_triv (e : (Representation.trivial ℂ H ℂ).Equiv ρ) (K : Subgroup H) : GlobalTheory.LGrp.IsSpherical ρ K :=
  (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv 1, GlobalTheory.LGrp.mem_fixed.2 fun k _ => act_eq e k _, by simp⟩

end Triv

theorem sat_triv (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin 1) (w.adicCompletion E)) W} (e : (Representation.trivial ℂ _ ℂ).Equiv ρ) :
    GlobalTheory.LFun.HasSatGL w ρ {1} := by
  refine ⟨spherical_triv e _, fun x _ h0 => ?_⟩
  let f : W →ₗ[ℂ] (GL (Fin 1) (w.adicCompletion E) → ℂ) :=
    (LinearMap.toSpanSingleton ℂ _ (fun _ => 1)).comp e.toLinearEquiv.symm.toLinearMap
  have hi : Function.Injective f := fun a b h => by
    have := congrFun h 1
    have h2 : e.toLinearEquiv.symm a • (1 : ℂ) = e.toLinearEquiv.symm b • (1 : ℂ) := this
    exact e.toLinearEquiv.symm.injective (smul_left_injective ℂ one_ne_zero h2)
  refine GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) f (fun g y => by rw [act_eq e]; rfl) hi ?_
  have := GlobalTheory.LFun.isSatVecGL_of_isSpherical (w := w) (α := fun _ : Fin 1 => 1) (φ := f x)
    (fun b g k _ _ => by simp [f, chiDelta]) (fun h => h0 (hi (by rw [h, map_zero])))
  simpa using this

theorem locComp_triv (w : HeightOneSpectrum (𝓞 E)) :
    IsLocCompGL (Submodule.span ℂ {oneFn E n}) w (SmIrr.triv _) :=
  ⟨LinearMap.toSpanSingleton ℂ _ (oneFn E n),
    fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (LinearMap.congr_fun h (1 : ℂ))),
    fun _ => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun _ _ => rfl⟩

def zeroWt (n : ℕ) : DomWeight n := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

theorem infChar_triv (τ : E →+* ℂ) : HasInfCharGL (Submodule.span ℂ {oneFn E n}) τ (infOfWeight (zeroWt n)) := by
  refine ⟨by simp [infOfWeight], fun u φ hφ => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  rw [map_smul, cap_oneFn, smul_comm]
  congr 1
  simp [infOfWeight, zeroWt, Finset.prod, Function.comp_def]

theorem sqRep_one (lam : DomWeight 1) (g : GL (Fin 1) ℂ) (v : nablaSq ℂ 1 lam) :
    GlobalTheory.Branching.sqRep ℂ 1 lam g v = (g.val 0 0) ^ lam.w 0 • v := by
  have h0 : lam.natW = 0 := by
    funext i
    simp [DomWeight.natW, DomWeight.detShift, Subsingleton.elim i 0]
  have hv : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW 1 1) v.1 lam.natW := v.2.1
  rw [h0] at hv
  have hc : v.1 = MvPolynomial.C (MvPolynomial.coeff 0 v.1) := by
    classical
    ext d
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · rw [← h]
    · by_contra hd
      have := congrFun (hv hd) 0
      apply h
      ext i
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.colW, Fintype.sum_prod_type] at this
      rw [Subsingleton.elim i (0, 0)]
      simp [this]
  apply Subtype.ext
  change sqAct ℂ 1 lam g v.1 = _ • v.1
  rw [hc]
  simp [sqAct, detPow, DomWeight.detShift, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algebraMap_eq, Matrix.det_fin_one]

theorem coord_expU (τ : E →+* ℂ) (z : Cinf E) : coord τ (expU z).val = Complex.exp (coord τ z) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm

theorem coord_atEmb_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  unfold coord atEmb
  split_ifs <;> simp [Pi.single_eq_of_ne h]

def rot (τ : E →+* ℂ) (θ : ℝ) : UA E 1 :=
  ⟨infGL E 1 (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))), by
    set g := infGL E 1 (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))) with hg
    have h1 : pInf E (g.val 0 0) = (expU (atEmb τ (θ * Complex.I))).val :=
      congrArg (fun x : GL (Fin 1) (Cinf E) => x.val 0 0) (pInf_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))))
    have h2 : pFin E (g.val 0 0) = 1 :=
      congrArg (fun x : GL (Fin 1) (Af E) => x.val 0 0) (pFin_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))))
    have c1 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => (infEq E).symm_apply_apply _
    have c2 : ∀ y, pFin E (conjAd E y) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E y) := fun y => rfl
    change cT (conjAd E) g.val * 1 * g.val = 1
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp only [Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply_eq]
    refine ad_ext ?_ ?_
    · rw [map_mul, c1, h1, map_one]
      funext w
      classical
      change starRingEnd ℂ (Complex.exp _) * Complex.exp _ = 1
      rw [← Complex.exp_conj, ← Complex.exp_add]
      by_cases h : w = InfinitePlace.mk τ
      · subst h
        unfold atEmb
        split_ifs <;> simp
      · simp [atEmb, Pi.single_eq_of_ne h]
    · rw [map_mul, c2, h2]; simp⟩

theorem cEmb_rot (τ τ' : E →+* ℂ) (θ : ℝ) :
    (cEmb τ' (rot τ θ)).val 0 0 = Complex.exp (coord τ' (atEmb τ (θ * Complex.I))) := by
  rw [← coord_expU]
  exact congrArg (coord τ') (congrArg (fun x : GL (Fin 1) (Cinf E) => x.val 0 0)
    (pInf_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I))))))

theorem rot_mem (τ : E →+* ℂ) (θ : ℝ) : rot τ θ ∈ embU 1 τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => ?_⟩
  rw [MonoidHom.mem_ker]
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, cEmb_rot, coord_atEmb_ne h]
  simp

theorem weight_eq_zero (τ : E →+* ℂ) (lam : DomWeight 1) (h : HasWeightAt (constU E 1) τ lam) : lam.w 0 = 0 := by
  obtain ⟨-, f, h0, hm, hf⟩ := h
  by_contra hk
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h0 (LinearMap.ext hh)
  have h1 := hf ⟨_, rot_mem τ (Real.pi / lam.w 0)⟩ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hm v)
  have h2 : ∀ x, RU E 1 x (f v) = f v := fun x => by rw [← hc]; rfl
  rw [sqRep_one, map_smul, h2] at h1
  have h3 := smul_left_injective ℂ hv (h1.trans (one_smul ℂ _).symm)
  change (cEmb τ (rot τ _)).val 0 0 ^ lam.w 0 = 1 at h3
  have hk' : ((lam.w 0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [cEmb_rot, coord_atEmb, ← Complex.exp_int_mul,
    show ((lam.w 0 : ℤ) : ℂ) * (((Real.pi / lam.w 0 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
      push_cast; field_simp, Complex.exp_pi_mul_I] at h3
  norm_num at h3

theorem hasWeightAt_zero (τ : E →+* ℂ) : HasWeightAt (constU E 1) τ (zeroWt 1) := by
  have hv : ∀ v : nablaSq ℂ 1 (zeroWt 1), v.1 = MvPolynomial.C (MvPolynomial.coeff 0 v.1) := fun v => by
    have h := sqRep_one (zeroWt 1) (CG.oneByOne (Units.mk0 2 two_ne_zero)) v
    have h0 : (zeroWt 1).natW = 0 := by
      funext i
      simp [DomWeight.natW, DomWeight.detShift, zeroWt]
    have hv : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW 1 1) v.1 (zeroWt 1).natW := v.2.1
    rw [h0] at hv
    classical
    ext d
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · rw [← h]
    · by_contra hd
      have := congrFun (hv hd) 0
      apply h
      ext i
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.colW, Fintype.sum_prod_type] at this
      rw [Subsingleton.elim i (0, 0)]
      simp [this]
  let l : nablaSq ℂ 1 (zeroWt 1) →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ 0).comp (Submodule.subtype _)
  have hi : Function.Injective l := fun a b h => Subtype.ext (by rw [hv a, hv b]; exact congrArg _ h)
  obtain ⟨v, hv0⟩ := exists_ne (0 : nablaSq ℂ 1 (zeroWt 1))
  have hl : l v ≠ 0 := fun h => hv0 (hi (by rw [h, map_zero]))
  have hs : Function.Surjective l := fun c => ⟨(c / l v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hl]⟩
  exact compAlong_triv (Representation.Equiv.mk (LinearEquiv.ofBijective l ⟨hi, hs⟩).symm fun g => LinearMap.ext fun c => by
    change _ = GlobalTheory.Branching.sqRep ℂ 1 (zeroWt 1) g _
    rw [sqRep_one]; simp [zeroWt]; exact (one_smul ℂ _).symm) _ _

theorem isBaseChange_const :
    IsBaseChange (constU E 1) (N := fun _ : Fin 1 => 1) (sum_one 1) (fun _ => Submodule.span ℂ {oneFn E 1})
      (fun _ _ => SmIrr.triv _) (fun _ _ => infOfWeight (zeroWt 1)) where
  pos _ := one_pos
  discrete _ := GlobalTheory.IdeleCovolume.isDiscrete_const_one E
  csd _ := isCsdGL_const
  loc _ := locComp_triv
  inf _ := infChar_triv
  unram w _ := (equiv_triv w).elim fun e => spherical_triv e _
  inert w s ϖ q _ _ α _ := (equiv_triv w).elim fun e => by
    have : GlobalTheory.LGrp.bcParam 1 α = {1} := by simp [GlobalTheory.LGrp.bcParam]
    rw [this]; exact sat_triv w e
  split w _ := (equiv_triv w).elim fun e => compAlong_triv e _ _
  weight τ lam h := by
    simp [infOfWeight, zeroWt, weight_eq_zero τ lam h]

theorem split_unram_const (w : HeightOneSpectrum (𝓞 E)) :
    IsCompAlong (constU E n) (locU n w) ((cLoc w).comp (locU n w).subtype)
        (locProd (N := fun _ : Fin 1 => n) (sum_one n) w fun _ => SmIrr.triv _) ∧
      GlobalTheory.LGrp.IsSpherical (locProd (N := fun _ : Fin 1 => n) (sum_one n) w fun _ => SmIrr.triv _) (GlobalTheory.LFun.KGL w n) :=
  (equiv_triv w).elim fun e => ⟨compAlong_triv e _ _, spherical_triv e _⟩

theorem pLoc_conj (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (y : Af E) :
    pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv y) = s (pLoc E w y) := by
  have key : ∀ (u : HeightOneSpectrum (𝓞 E)) (_ : w = u) (φ : u.adicCompletion E →+* w.adicCompletion E),
      Continuous φ → (∀ x : E, φ (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
      φ (pLoc E u y) = s (pLoc E w y) := by
    rintro u rfl φ hφ h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hφ
      (GlobalTheory.Mem.Chr.continuous_of_valued_eq (w.valuedAdicCompletion_surjective E) s hv)
      (funext fun x => (h x).trans (hs x).symm)) _
  rw [pLoc_conjFin]
  refine key _ (eq_conjSrc fun x => ?_) _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans
    ((congrArg Valued.v (hs x).symm).trans ((hv _).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _)))

theorem hasSatAt_const (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (ϖ : w.adicCompletion E) (q : ℕ)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) (hU : IsUnramInv ϖ s q)
    (α : Fin (1 / 2) → ℂˣ) : HasSatAt (constU E 1) w s ϖ q α := by
  have hJ : antiJ (w.adicCompletion E) 1 = 1 := by
    ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp [antiJ]
  have hm : ∀ x : UA E 1, cLoc w x ∈ GU s 1 := fun x => by
    have hx : cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
    change cT s (cLoc w x).val * antiJ _ 1 * (cLoc w x).val = antiJ _ 1
    rw [hJ]
    ext i j : 1
    have := congrArg (fun y => pLoc E w (pFin E y)) (congrFun (congrFun hx 0) 0)
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp only [Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply_eq, map_mul, map_one] at this ⊢
    rw [show pFin E (conjAd E (x.1.val 0 0)) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (x.1.val 0 0))
      from rfl, pLoc_conj w s hs hU.2.1] at this
    exact this
  refine ⟨1, one_mem _, by rw [hJ]; simp [cT_one], (((cLoc w).codRestrict _ hm)).comp (locU 1 w).subtype,
    fun x => by simp, SmIrr.triv _, compAlong_triv (.refl _) _ _, spherical_triv (.refl _) _, fun x _ h0 => ?_⟩
  let f : ℂ →ₗ[ℂ] (GU s 1 → ℂ) := LinearMap.toSpanSingleton ℂ _ (fun _ => 1)
  have hi : Function.Injective f := fun a b h => by simpa [f] using congrFun h 1
  refine GlobalTheory.LFun.IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) f (fun g y => rfl) hi
    (GlobalTheory.LFun.isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (hi (h.trans (map_zero f).symm)))
  have : chiDeltaU q (fun i => (α i : ℂ)) b = 1 := Finset.prod_eq_one fun i _ => absurd i.2 (by simp)
  rw [this, one_mul]; rfl

theorem conclusion_const : IsAutRepU (constU E 1) ∧
    ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = 1) (V : ∀ i, Submodule ℂ (Sm E (N i)))
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (m : Fin c → (E →+* ℂ) → Multiset ℂ), IsBaseChange (constU E 1) h V σ m :=
  ⟨isAutRepU_const, _, _, _, _, _, _, isBaseChange_const⟩

theorem inf_of_isBaseChange {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = 1} {V σ m}
    (H : IsBaseChange (constU E 1) h V σ m) (τ : E →+* ℂ) : ∑ i, m i τ = {0} := by
  rw [H.weight τ _ (hasWeightAt_zero τ)]
  simp [infOfWeight, zeroWt]

end GlobalTheory.UnitaryBC.Model

end
