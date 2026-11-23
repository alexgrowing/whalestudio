import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsCanFam

set_option autoImplicit false

noncomputable section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

namespace GlobalTheory.WH.PullCoc

section Gen

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

theorem wd_comp (φ : E →ₗ[k] E') (w : ι → Module.End k E) (w' : ι → Module.End k E')
    (h : ∀ i, φ ∘ₗ w i = w' i ∘ₗ φ) (c : Finset ι → E) :
    (fun t => φ (wd w c t)) = wd w' (fun t => φ (c t)) := by
  funext t
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearMap.comp_apply φ (w i), h i, LinearMap.comp_apply]

theorem tD_comp (φ : E →ₗ[k] E') (w : ι → Module.End k E) (w' : ι → Module.End k E')
    (κ : Module.End k E) (κ' : Module.End k E')
    (h : ∀ i, φ ∘ₗ w i = w' i ∘ₗ φ) (hκ : φ ∘ₗ κ = κ' ∘ₗ φ) (c : Finset ι → E) :
    (fun t => φ (tD w κ c t)) = tD w' κ' (fun t => φ (c t)) := by
  have h1 := wd_comp φ w w' h c
  funext t
  have h2 := congrFun h1 t
  simp only [tD, LinearMap.add_apply, Pi.add_apply, map_add, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_zsmul] at h2 ⊢
  rw [h2, ← LinearMap.comp_apply φ κ, hκ, LinearMap.comp_apply]

theorem comp_pow (φ : E →ₗ[k] E') (u : Module.End k E) (u' : Module.End k E') (h : φ ∘ₗ u = u' ∘ₗ φ) (n : ℕ) :
    φ ∘ₗ (u ^ n) = (u' ^ n) ∘ₗ φ := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih,
      LinearMap.comp_assoc, h, LinearMap.comp_assoc]

theorem kFam_map {σ : Type} [LinearOrder σ] (φ : E →ₗ[k] E') (Y : σ → Module.End k E) (Y' : σ → Module.End k E')
    (u v : Module.End k E) (u' v' : Module.End k E') (M : Submodule k E) (M' : Submodule k E') (q : ℤ)
    (hY : ∀ i, φ ∘ₗ Y i = Y' i ∘ₗ φ) (hu : φ ∘ₗ u = u' ∘ₗ φ) (hv : φ ∘ₗ v = v' ∘ₗ φ) (hM : M.map φ ≤ M')
    (f : Finset σ → E) (hf : f ∈ kFam Y u v M q) : (fun T => φ (f T)) ∈ kFam Y' u' v' M' q := by
  simp only [kFam, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies, LinearMap.proj_apply] at hf ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨⟨fun T hT => by rw [h1 T hT, map_zero], ?_⟩, fun T => ?_⟩
  · rw [← wd_comp φ Y Y' hY f, h2]; funext t; simp
  · obtain ⟨m, hm, e⟩ := h3 T
    refine ⟨φ m, hM ⟨m, hm, rfl⟩, ?_⟩
    rw [← e, ← LinearMap.comp_apply (u' ^ _ * v'), Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, ← hv, ← LinearMap.comp_assoc, ← comp_pow φ u u' hu, LinearMap.comp_assoc]
    rfl

end Gen

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section J2

variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

theorem mapDR_smul_ιMulti {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      algebraMap K L b • ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  rw [map_smul, algebraMap_smul]
  congr 1
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, mapDR, map1, Function.comp_def,
    KaehlerDifferential.map_D]

theorem mapDR_smul' {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (w : DR ℂ K) :
    mapDR ℂ K L (b • w) = algebraMap K L b • mapDR ℂ K L w := by
  rw [map_smul, algebraMap_smul]

theorem deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD (j2 : K →ₐ[ℂ] K') (b : K) (q : ℕ) (v : Fin q → K) :
    pr2L j2 (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      j2 b • ExteriorAlgebra.ιMulti K' q fun j => D ℂ K' (j2 (v j)) := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul_ιMulti (L := K') b q v

theorem pullback_kahler_smul (j2 : K →ₐ[ℂ] K') (b : K) (w : DR ℂ K) : pr2L j2 (b • w) = j2 b • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' (L := K') b w

end J2

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

theorem gY_tmul (j2 : K →ₐ[ℂ] K') (w w' : DR ℂ K) : gY j2 (w ⊗ₜ w') = mapDR ℂ K K' w * pr2L j2 w' := by
  simp [gY]

theorem gY_smul_tmul (j2 : K →ₐ[ℂ] K') (a b : K) (w w' : DR ℂ K) :
    gY j2 ((a • w) ⊗ₜ (b • w')) = (algebraMap K K' a * j2 b) • gY j2 (w ⊗ₜ w') := by
  rw [gY_tmul, gY_tmul, mapDR_smul', pullback_kahler_smul, smul_mul_smul_comm]

theorem gY_actZ (j2 : K →ₐ[ℂ] K') (y : K ⊗[ℂ] K) :
    gY j2 ∘ₗ actZ K y = (Algebra.lsmul ℂ ℂ (DR ℂ K')) (gz j2 y) ∘ₗ gY j2 := by
  unfold gz
  induction y using TensorProduct.induction_on with
  | zero => ext; simp
  | tmul a b =>
    apply TensorProduct.ext'
    intro w w'
    simp only [LinearMap.comp_apply, actZ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Module.endTensorEndAlgHom_apply, TensorProduct.AlgebraTensorModule.map_tmul, Algebra.lsmul_coe,
      Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.coe_toAlgHom', gY_smul_tmul]
  | add y y' hy hy' =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, hy, hy', LinearMap.add_comp]

theorem gY_XZ (j2 : K →ₐ[ℂ] K') (l : Fin (d + 1)) : gY j2 ∘ₗ XZ F K x l = XY x l ∘ₗ gY j2 := by
  apply TensorProduct.ext'
  intro w w'
  have := gY_smul_tmul j2 (algebraMap F K (x l)) 1 w w'
  rw [one_smul, map_one, mul_one, ← IsScalarTower.algebraMap_apply] at this
  simpa [XZ, XY] using this

theorem gY_YZ (j2 : K →ₐ[ℂ] K') (l : Fin (d + 1)) : gY j2 ∘ₗ YZ F K x l = YY x j2 l ∘ₗ gY j2 := by
  apply TensorProduct.ext'
  intro w w'
  have := gY_smul_tmul j2 1 (algebraMap F K (x l)) w w'
  rw [one_smul, map_one, one_mul] at this
  simpa [YZ, YY] using this

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

theorem ιMulti_append {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (p q : ℕ) (u : Fin p → M) (u' : Fin q → M) :
    ExteriorAlgebra.ιMulti R (p + q) (Fin.append u u') = ExteriorAlgebra.ιMulti R p u * ExteriorAlgebra.ιMulti R q u' := by
  have h : (fun i => ExteriorAlgebra.ι R (Fin.append u u' i)) =
      Fin.append (fun i => ExteriorAlgebra.ι R (u i)) (fun i => ExteriorAlgebra.ι R (u' i)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [h, List.ofFn_fin_append, List.prod_append]

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

theorem mem_RY_left (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) (b : K) (hb : b ∈ rB ℂ K x I) :
    algebraMap K K' b ∈ RY x j2 I J := by
  refine (le_sup_left : rB ℂ K' x I ≤ RY x j2 I J) ?_
  haveI : IsScalarTower (rA ℂ x I) K K' := IsScalarTower.of_algebraMap_eq fun r =>
    IsScalarTower.algebraMap_apply F K K' (r : F)
  simp only [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  exact hb.algebraMap

theorem mem_RY_right (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) (b : K) (hb : b ∈ rB ℂ K x J) :
    j2 b ∈ RY x j2 I J := by
  refine (le_sup_right : R2 x j2 J ≤ RY x j2 I J) ?_
  simp only [R2, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_algebraMap (x := (⟨j2 b, Subalgebra.mem_map.2 ⟨b, hb, rfl⟩⟩ : (rB ℂ K x J).map j2))

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

theorem gY_omB (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) (p q : ℕ) (m : DR ℂ K)
    (hm : m ∈ omB ℂ K (rB ℂ K x I) p) (n : DR ℂ K) (hn : n ∈ omB ℂ K (rB ℂ K x J) q) :
    gY j2 (m ⊗ₜ n) ∈ omB ℂ K' (RY x j2 I J) (p + q) := by
  induction hn using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b', hb', v', hv', rfl⟩ := hy
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hy
      rw [gY_tmul, mapDR_smul_ιMulti, deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD, smul_mul_smul_comm, ← ιMulti_append]
      refine Submodule.subset_span ⟨_, mul_mem (mem_RY_left x j2 I J b hb) (mem_RY_right x j2 I J b' hb'),
        Fin.append (fun j => algebraMap K K' (v j)) (fun j => j2 (v' j)), ?_, ?_⟩
      · intro j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using mem_RY_left x j2 I J _ (hv i)
        · simpa using mem_RY_right x j2 I J _ (hv' i)
      · congr 1
        congr 1
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
    | zero => simp
    | add y z _ _ hy hz => rw [TensorProduct.add_tmul, map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [← TensorProduct.smul_tmul', map_smul]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [TensorProduct.tmul_smul, map_smul]; exact Submodule.smul_mem _ _ hy

theorem omB_eq_zero (hK : IsFinCover ℂ K x) (B : Subalgebra ℂ K) (a : ℕ) (ha : d < a) (n : DR ℂ K)
    (hn : n ∈ omB ℂ K B a) : n = 0 := by
  induction hn using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    obtain ⟨bs, -⟩ := hK.exists_basis
    haveI := Module.Finite.of_basis bs
    have : ExteriorAlgebra.ιMulti K a (fun j => D ℂ K (v j)) = 0 := by
      refine AlternatingMap.map_linearDependent _ _ fun hli => ?_
      have h := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis bs] at h
      simp at h
      omega
    rw [this, smul_zero]
  | zero => rfl
  | add y z _ _ hy hz => rw [hy, hz, add_zero]
  | smul c y _ hy => rw [hy, smul_zero]

theorem gY_MZ (hK : IsFinCover ℂ K x) (j2 : K →ₐ[ℂ] K') (a : ℕ) (I J : Finset (Fin (d + 1))) :
    (MZ F K x a I J).map (gY j2) ≤ MY x j2 I J := by
  rw [Submodule.map_le_iff_le_comap]
  unfold MZ
  rw [Submodule.map₂_le]
  intro m hm n hn
  simp only [Submodule.mem_comap, TensorProduct.mk_apply, MY]
  by_cases ha : a ≤ d
  · have h := gY_omB x j2 I J _ _ m hm n hn
    rwa [Nat.sub_add_cancel ha] at h
  · rw [omB_eq_zero x hK _ a (by omega) n hn, TensorProduct.tmul_zero, map_zero]
    exact zero_mem _

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

theorem TZ_TY (hK : IsFinCover ℂ K x) (j2 : K →ₐ[ℂ] K') {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1)) (a : ℕ)
    (q : ℤ) (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) (f : Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K)
    (hf : f ∈ TZ F K x p1 p2 a q s) : (fun U => gY j2 (f U)) ∈ TY x p1 p2 j2 q s := by
  unfold TZ at hf
  unfold TY
  by_cases h : (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty ∧ 0 < q
  · rw [if_pos h] at hf ⊢
    simp only [Submodule.mem_iInf] at hf ⊢
    intro i hi j hj
    exact kFam_map (gY j2) _ _ _ _ _ _ _ _ q (fun l => gY_YZ x j2 l) (gY_XZ x j2 i)
      (by rw [pow_zero, pow_zero, one_mul, one_mul]; exact gY_YZ x j2 j) (gY_MZ x hK j2 a _ _) f (hf i hi j hj)
  · rw [if_neg h] at hf ⊢
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    funext U
    simp

theorem wZ_wY (j2 : K →ₐ[ℂ] K') {κ : Type} (z : κ → K ⊗[ℂ] K) (t : (Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) :
    LinearMap.compLeft (gY j2) (Finset (Fin (d + 1))) ∘ₗ wZ K (d := d) z t =
      wY (d := d) j2 z t ∘ₗ LinearMap.compLeft (gY j2) (Finset (Fin (d + 1))) := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with l | l
  · simp only [wZ, wY, ofLex_toLex]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  · apply LinearMap.ext
    intro c
    funext U
    simpa [wZ, wY, pw] using LinearMap.congr_fun (gY_actZ j2 (z l)) (c U)

theorem wd_XZ_XY (j2 : K →ₐ[ℂ] K') :
    LinearMap.compLeft (gY j2) (Finset (Fin (d + 1))) ∘ₗ wd (XZ F K x) =
      wd (XY x) ∘ₗ LinearMap.compLeft (gY j2) (Finset (Fin (d + 1))) := by
  apply LinearMap.ext
  intro c
  exact wd_comp (gY j2) _ _ (gY_XZ x j2) c

end Y

end GlobalTheory.WH.PullCoc

open GlobalTheory.WH.PullCoc in

theorem GlobalTheory.WH.pullY_mem_Z : ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'), IsFinCover ℂ K x → IsFinCover ℂ K' x → ∀ {κ : Type} [LinearOrder κ] [Fintype κ] (p1 p2 : κ → Fin (d + 1)) (z : κ → K ⊗[ℂ] K), IsGen F K x p1 p2 z → ∀ (n : ℤ), ∀ c ∈ (totZ F K x p1 p2 a z).Z n, pullY j2 c ∈ (totY x p1 p2 j2 z).Z n := by
  intro d a F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ x j2 hK _ κ _ _ p1 p2 z _ n c hc
  have hpull : pullY j2 c = fun s => LinearMap.compLeft (gY j2) (Finset (Fin (d + 1))) (c s) := rfl
  simp only [Cx.Z, totZ, totY, tcx, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies] at hc ⊢
  refine ⟨fun s => TZ_TY x hK j2 p1 p2 a _ s (c s) (hc.1 s), ?_⟩
  rw [hpull, ← tD_comp _ _ _ _ _ (wZ_wY j2 z) (wd_XZ_XY x j2) c, hc.2]
  funext s
  simp
