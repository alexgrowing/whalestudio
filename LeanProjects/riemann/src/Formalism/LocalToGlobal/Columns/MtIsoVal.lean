import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Columns.PolyFn

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.L2.Col

section Map

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K')

theorem mti_map_colAddGen {r n : ℕ} (l j : Fin n) (P : MvPolynomial (Fin r × Fin n) K) :
    map s (Formalism.GradedWeylDivisibility.colAddGen K l j P) = Formalism.GradedWeylDivisibility.colAddGen K' l j (map s P) := by
  have h : (map s).comp (Formalism.GradedWeylDivisibility.colAddGen K (r := r) l j).toRingHom =
      (Formalism.GradedWeylDivisibility.colAddGen K' (r := r) l j).toRingHom.comp (map s) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Formalism.GradedWeylDivisibility.colAddGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
      split_ifs <;> simp
  exact congrArg (fun φ : MvPolynomial (Fin r × Fin n) K →+* MvPolynomial (Option (Fin r × Fin n)) K' => φ P) h

theorem mti_map_rename_some {r n : ℕ} (P : MvPolynomial (Fin r × Fin n) K) :
    map s (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) P) = rename some (map s P) :=
  map_rename s _ P

theorem mti_map_weighted {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) :
    map s P ∈ weightedHomogeneousSubmodule K' (Formalism.GradedWeylDivisibility.colW r n) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hP ⊢
  intro m hm
  rw [coeff_map] at hm
  apply hP
  intro h0
  rw [h0, map_zero] at hm
  exact hm rfl

theorem mti_map_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : map s P ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf] at hP ⊢
  refine ⟨mti_map_weighted s ν hP.1, ?_⟩
  have h2 := hP.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h2 ⊢
  intro l j hlj
  rw [← mti_map_colAddGen, ← mti_map_rename_some, h2 l j hlj]

end Map

section VVMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

theorem mti_dualWeyl_of_map {r m : ℕ} (ν : Fin m → ℕ) {P : MvPolynomial (Fin r × Fin m) K}
    (hP : map s P ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r m ν) : P ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf] at hP ⊢
  refine ⟨?_, ?_⟩
  · have h1 := hP.1
    rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    rw [coeff_map]
    intro h0
    exact hd ((map_eq_zero_iff s s.injective).mp h0)
  · have h2 := hP.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h2 ⊢
    intro l j hlj
    apply map_injective s s.injective
    rw [mti_map_colAddGen, mti_map_rename_some, h2 l j hlj]

theorem mti_map_ten (F : ι → MvPolynomial (Fin n × Fin n) K) :
    map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ)) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K' τ (map s (F τ)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact map_rename s _ (F τ)

theorem mti_map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) : map s F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun τ => map s (G τ), fun τ => ?_, mti_map_ten s G⟩
    exact mti_map_dualWeyl s _ (hG τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

def mtiMapVV (lam : ι → DomWeight n) : VV K lam →ₛₗ[s] VV K' lam where
  toFun F := ⟨map s F.1, mti_map_mem_VV s lam F.2⟩
  map_add' F G := Subtype.ext (map_add _ _ _)
  map_smul' a F := Subtype.ext (by
    show map s (a • F.1) = s a • map s F.1
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul])

theorem mtiMapVV_coe (lam : ι → DomWeight n) (F : VV K lam) : ((mtiMapVV s lam F : VV K' lam) : Pol K' ι n) = map s F.1 := rfl

theorem mti_map_initMinor {r m q : ℕ} (I : Fin q → Fin r) (hq : q ≤ m) :
    map s (Formalism.GradedWeylDivisibility.initMinor K I hq : MvPolynomial (Fin r × Fin m) K) = Formalism.GradedWeylDivisibility.initMinor K' I hq := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem mti_map_bidet {r m Kk : ℕ} (sz : Fin Kk → ℕ) (hsz : ∀ k, sz k ≤ m) (I : ∀ k, Fin (sz k) → Fin r) :
    map s (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I : MvPolynomial (Fin r × Fin m) K) = Formalism.GradedWeylDivisibility.bideterminant K' sz hsz I := by
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => mti_map_initMinor s (I k) (hsz k)

theorem mti_ssB_map (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ P ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν, map s P = ssB K' ν m := by
  obtain ⟨-, -, Kk, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.2 m
  have hb' : ssB K' ν m = Formalism.GradedWeylDivisibility.bideterminant K' sz hsz I := hb
  refine ⟨Formalism.GradedWeylDivisibility.bideterminant K sz hsz I, mti_dualWeyl_of_map s ν ?_, by rw [mti_map_bidet, hb']⟩
  rw [mti_map_bidet, ← hb']
  have hsp := (Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.1.2.1
  show (Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose m ∈ Formalism.GradedWeylDivisibility.dualWeyl K' n n ν
  rw [← hsp]
  exact Submodule.subset_span ⟨m, rfl⟩

theorem mti_span_map (lam : ι → DomWeight n) :
    Submodule.span K' (Set.range fun F : VV K lam => ((mtiMapVV s lam F : VV K' lam) : Pol K' ι n)) = VV K' lam := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact (mtiMapVV s lam F).2
  · intro x hx
    rw [← (bVVfun_spec K' lam).2] at hx
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨i, rfl⟩
    have hP := fun τ => mti_ssB_map s (lam τ).natW (i τ)
    choose P hP1 hP2 using hP
    have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (P τ)) ∈ VV K lam :=
      Submodule.subset_span ⟨P, hP1, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨_, hmem⟩, ?_⟩
    show map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (P τ)) = bVVfun K' lam i
    rw [mti_map_ten, bVVfun, ten]
    exact Finset.prod_congr rfl fun τ _ => by rw [hP2]

end VVMap

section RhoMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

theorem mti_map_blockAct (g : ι → Matrix (Fin n) (Fin n) K) (P : Pol K ι n) :
    map s (Formalism.GradedWeylDivisibility.blockAct K (n := n) g P) = Formalism.GradedWeylDivisibility.blockAct K' (n := n) (fun τ => (g τ).map s) (map s P) := by
  have h : (map s).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) g).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct K' (n := n) (fun τ => (g τ).map s)).toRingHom.comp (map s) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.blockAct, map_sum]
  exact congrArg (fun φ : Pol K ι n →+* Pol K' ι n => φ P) h

theorem mti_map_detPow (g : GL (Fin n) K) (c : ℤ) :
    s (detPow K n g c) = detPow K' n (Matrix.GeneralLinearGroup.map s g) c := by
  unfold detPow
  have e : Units.map s.toMonoidHom (Matrix.GeneralLinearGroup.det g) =
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map s g) := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [← e, ← map_zpow (Units.map s.toMonoidHom) (Matrix.GeneralLinearGroup.det g) c, Units.coe_map]
  rfl

theorem mti_map_detTwK (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    s (detTwK lam g) = detTwK lam (fun τ => Matrix.GeneralLinearGroup.map s (g τ)) := by
  unfold detTwK
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => mti_map_detPow s (g τ) _

theorem mti_map_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (P : Pol K ι n) :
    map s (actP lam g P) = actP lam (fun τ => Matrix.GeneralLinearGroup.map s (g τ)) (map s P) := by
  unfold actP trAct
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [smul_eq_C_mul, map_mul, map_C, mti_map_detTwK, mti_map_blockAct, smul_eq_C_mul]
  congr 3

theorem mti_rhoK_map (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (F : VV K lam) :
    mtiMapVV s lam (rhoK lam g F) = rhoK lam (fun τ => Matrix.GeneralLinearGroup.map s (g τ)) (mtiMapVV s lam F) :=
  Subtype.ext (mti_map_actP s lam g F.1)

end RhoMap

end Formalism.L2.Col
