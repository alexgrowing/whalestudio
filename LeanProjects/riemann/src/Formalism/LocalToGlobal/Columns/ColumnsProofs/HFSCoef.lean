import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSSplit
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSData

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section VVMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_blockEmb (s : σ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.map ι (Formalism.GradedWeylDivisibility.blockEmb K s f) = Formalism.GradedWeylDivisibility.blockEmb L s (MvPolynomial.map ι f) := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  exact MvPolynomial.map_rename _ _ _

private lemma map_aeval_eq_aeval_map' {α β : Type} (g : α → MvPolynomial β K) (g' : α → MvPolynomial β L)
    (hg : ∀ v, MvPolynomial.map ι (g v) = g' v) (F : MvPolynomial α K) :
    MvPolynomial.map ι (MvPolynomial.aeval g F) = MvPolynomial.aeval g' (MvPolynomial.map ι F) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, hp, hg]

private lemma map_mem_dualWeyl' {r m : ℕ} {ν : Fin m → ℕ} {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν) : MvPolynomial.map ι f ∈ Formalism.GradedWeylDivisibility.dualWeyl L r m ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  constructor
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    rw [MvPolynomial.coeff_map] at hd
    intro h0
    apply hd
    rw [h0, map_zero]
  · simp only [Submodule.mem_iInf] at h2 ⊢
    intro l j hlj
    have h3 := h2 l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h3 ⊢
    simp only [AlgHom.toLinearMap_apply] at h3 ⊢
    rw [← MvPolynomial.map_rename, ← h3]
    unfold Formalism.GradedWeylDivisibility.colAddGen
    refine (map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) f).symm
    split_ifs <;> simp

theorem hfs_map_mem_VV {F : Pol K σ n} (hF : F ∈ VV K lam) : MvPolynomial.map ι F ∈ VV L lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map ι (G s), fun s => ?_, ?_⟩
    · have h1 : G s ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n (lam s).natW := hG s
      exact map_mem_dualWeyl' ι h1
    · rw [map_prod]
      exact Finset.prod_congr rfl fun s _ => hfs_map_blockEmb ι s (G s)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

def hfsJ : VV K lam →+ VV L lam where
  toFun v := ⟨MvPolynomial.map ι (v : Pol K σ n), hfs_map_mem_VV ι lam v.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add _ _ _)

theorem hfsJ_coe (v : VV K lam) : ((hfsJ ι lam v : VV L lam) : Pol L σ n) = MvPolynomial.map ι (v : Pol K σ n) := rfl

theorem hfsJ_smul (a : K) (v : VV K lam) : hfsJ ι lam (a • v) = ι a • hfsJ ι lam v := by
  apply Subtype.ext
  rw [hfsJ_coe, Submodule.coe_smul, Submodule.coe_smul, hfsJ_coe, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem hfsJ_li (F : CoefFrame ι) : LinearIndependent L fun i => hfsJ ι lam (bVV K lam i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpol : ∑ j ∈ s, g j • MvPolynomial.map ι ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    have h0 := congrArg (fun v : VV L lam => (v : Pol L σ n)) hg
    simpa [hfsJ_coe] using h0
  have hK : ∀ k, ∑ j ∈ s, F.c (g j) k • ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    intro k
    ext d
    have h1 := congrArg (MvPolynomial.coeff d) hpol
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      MvPolynomial.coeff_zero] at h1 ⊢
    have h2 := congrArg (fun y => F.c y k) h1
    simp only [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), F.smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hli := (bVV K lam).linearIndependent
  rw [linearIndependent_iff'] at hli
  have hz : ∀ k, F.c (g i) k = 0 := by
    intro k
    refine hli s (fun j => F.c (g j) k) ?_ i hi
    apply Subtype.ext
    simpa using hK k
  rw [F.spec (g i)]
  simp [hz]

theorem hfsJ_span (F : CoefFrame ι) : ⊤ ≤ Submodule.span L (Set.range fun i => hfsJ ι lam (bVV K lam i)) := by
  classical
  haveI : FiniteDimensional L (VV L lam) := Module.Basis.finiteDimensional_of_finite (bVV L lam)
  rw [(hfsJ_li ι lam F).span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV L lam)).symm]

end VVMap

section Act

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_trAct (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (trAct g F) = trAct (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold trAct Formalism.GradedWeylDivisibility.blockAct
  refine map_aeval_eq_aeval_map' ι _ _ (fun v => ?_) F
  simp [map_sum, Formalism.UG.bc, Matrix.transpose_apply]

theorem hfs_detPow_bc (g : GL (Fin n) K) (c : ℤ) : detPow L n (Formalism.UG.bc ι g) c = ι (detPow K n g c) := by
  unfold detPow
  have h : Matrix.GeneralLinearGroup.det (Formalism.UG.bc ι g) =
      Units.map (ι : K →* L) (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [h, ← map_zpow, Units.coe_map]
  rfl

theorem hfs_detTwK_bc (g : σ → GL (Fin n) K) : detTwK lam (fun τ => Formalism.UG.bc ι (g τ)) = ι (detTwK lam g) := by
  unfold detTwK
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => hfs_detPow_bc ι (g τ) _

theorem hfs_map_actP (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (actP lam g F) = actP lam (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold actP
  rw [LinearMap.smul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hfs_map_trAct,
    hfs_detTwK_bc]

theorem hfs_rhoK (g : σ → GL (Fin n) K) (v : VV K lam) :
    rhoK lam (fun τ => Formalism.UG.bc ι (g τ)) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam g v) := by
  apply Subtype.ext
  show actP lam (fun τ => Formalism.UG.bc ι (g τ)) ((hfsJ ι lam v : VV L lam) : Pol L σ n) =
    MvPolynomial.map ι (actP lam g (v : Pol K σ n))
  rw [hfsJ_coe, hfs_map_actP]

variable [NumberField K] [NumberField L] {E : Type} [Field E] [NumberField E]

theorem hfs_embGL (emb : σ → E →+* K) (γ : GL (Fin n) E) :
    embGL (fun τ => ι.comp (emb τ)) γ = fun τ => Formalism.UG.bc ι (embGL emb γ τ) := by
  funext τ
  apply Units.ext
  ext i j
  simp [embGL, Formalism.UG.bc]

theorem hfs_invTrK (g : σ → GL (Fin n) K) : invTrK (fun τ => Formalism.UG.bc ι (g τ)) = fun τ => Formalism.UG.bc ι (invTrK g τ) := by
  funext τ
  apply Units.ext
  show ((((Formalism.UG.bc ι (g τ))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).transpose =
    ((Formalism.UG.bc ι (inside₂ K n (g τ)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [← map_inv]
  ext i j
  simp [Formalism.UG.bc, inside₂]

theorem hfs_rhoV (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoV (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoV emb lam γ v) := by
  show rhoK lam (embGL (fun τ => ι.comp (emb τ)) γ) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam (embGL emb γ) v)
  rw [hfs_embGL]
  exact hfs_rhoK ι lam _ v

theorem hfs_rhoVr (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoVr (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoVr emb lam γ v) := by
  show rhoK lam (invTrK (embGL (fun τ => ι.comp (emb τ)) γ)) (hfsJ ι lam v) =
    hfsJ ι lam (rhoK lam (invTrK (embGL emb γ)) v)
  rw [hfs_embGL, hfs_invTrK]
  exact hfs_rhoK ι lam _ v

end Act

end Formalism.L2.Col
