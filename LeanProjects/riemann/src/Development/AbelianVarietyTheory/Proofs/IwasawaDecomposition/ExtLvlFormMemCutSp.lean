import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section LvlCoord

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} {P : Subgroup G₀} {ψ : P →* Kˣ}

theorem lvlForm_eig (x : Fin (S.lvlDim act P ψ) → K) (p : P) :
    act (p : G₀) (lvlForm S act P ψ x) = ((ψ p : Kˣ) : K) • lvlForm S act P ψ x := by
  have h1 : (S.lvlE act P ψ).mulVec x ∈ LinearMap.range (imE (S.gaMat act (lvlIdem P ψ))).mulVecLin := ⟨x, rfl⟩
  rw [(image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).2, level_part_spec K S G₀ act P ψ] at h1
  have hz : (S.actMat act (p : G₀)).mulVec ((S.lvlE act P ψ).mulVec x) =
      ((ψ p : Kˣ) : K) • (S.lvlE act P ψ).mulVec x := h1 p
  have h4 := S.I_actMat act (p : G₀) ((S.lvlE act P ψ).mulVec x)
  rw [hz, map_smul, CSD.I_apply] at h4
  apply Subtype.ext
  show ((act (p : G₀) (S.basis.equivFun.symm ((S.lvlE act P ψ).mulVec x)) : S.Forms) : S.Cl → S.V) = _
  rw [← h4]
  rfl

theorem exists_lvlForm (f : S.Forms) (hf : ∀ p : P, act (p : G₀) f = ((ψ p : Kˣ) : K) • f) :
    ∃ x, lvlForm S act P ψ x = f := by
  have hI : Function.Injective S.I := by
    intro a b h
    rw [CSD.I_apply, CSD.I_apply] at h
    exact S.basis.equivFun.symm.injective (Subtype.ext h)
  have hzf : S.basis.equivFun.symm (S.basis.equivFun f) = f := S.basis.equivFun.symm_apply_apply f
  have hz : ∀ p : P, (S.actMat act (p : G₀)).mulVec (S.basis.equivFun f) =
      ((ψ p : Kˣ) : K) • S.basis.equivFun f := by
    intro p
    apply hI
    rw [S.I_actMat act (p : G₀) _, map_smul, CSD.I_apply, hzf, hf p]
    rfl
  have h1 : S.basis.equivFun f ∈ LinearMap.range (imE (S.gaMat act (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).2, level_part_spec K S G₀ act P ψ]
    exact hz
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, ?_⟩
  have hx' : (S.lvlE act P ψ).mulVec x = S.basis.equivFun f := hx
  show S.basis.equivFun.symm ((S.lvlE act P ψ).mulVec x) = f
  rw [hx', hzf]

def lvlFormL (S : CSD K) (act : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) :
    (Fin (S.lvlDim act P ψ) → K) →ₗ[K] S.Forms :=
  S.basis.equivFun.symm.toLinearMap ∘ₗ (S.lvlE act P ψ).mulVecLin

theorem lvlFormL_apply (x : Fin (S.lvlDim act P ψ) → K) : lvlFormL S act P ψ x = lvlForm S act P ψ x := rfl

theorem lvlForm_eq_sum (x : Fin (S.lvlDim act P ψ) → K) :
    lvlForm S act P ψ x = ∑ i, ((S.lvlE act P ψ).mulVec x) i • S.basis i := by
  simp only [lvlForm, Module.Basis.equivFun_symm_apply]

open Classical in

def lvlAvgF (act : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (f : S.Forms) : S.Forms :=
  ∑ p : P, ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) • act (p : G₀) f

theorem lvlAvgF_eig (f : S.Forms) (q : P) :
    act (q : G₀) (lvlAvgF act P ψ f) = ((ψ q : Kˣ) : K) • lvlAvgF act P ψ f := by
  classical
  unfold lvlAvgF
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, Equiv.coe_mulLeft, smul_smul, Subgroup.coe_mul]
  congr 1
  have hq : ((ψ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  simp only [mul_inv_rev, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem exists_lvlForm_avg (f : S.Forms) : ∃ x, lvlForm S act P ψ x = lvlAvgF act P ψ f :=
  exists_lvlForm _ (lvlAvgF_eig f)

end LvlCoord

section Avg

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]
  {K : Type} [Field K] {G₀ : Type} [Group G₀] [Fintype G₀]

open Classical in

def cutAvgL {Q : Subgroup G} (ch : Q →* ℂˣ) (red : Q →* G₀) (hred : Function.Surjective red) (σ : K →+* ℂ)
    (P : Subgroup G₀) (ψ : P →* Kˣ) (W : Type) [AddCommGroup W] [Module ℂ W] : (G → W) →ₗ[ℂ] (G → W) :=
  ∑ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) * (((ch (hred (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) •
    LinearMap.funLeft ℂ W (fun h : G => h * ((hred (p : G₀)).choose : G))

open Classical in
theorem cutAvgL_apply {Q : Subgroup G} (ch : Q →* ℂˣ) (red : Q →* G₀) (hred : Function.Surjective red)
    (σ : K →+* ℂ) (P : Subgroup G₀) (ψ : P →* Kˣ) (F : G → W) (h : G) :
    cutAvgL ch red hred σ P ψ W F h = ∑ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) *
      (((ch (hred (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) • F (h * ((hred (p : G₀)).choose : G)) := by
  simp only [cutAvgL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    LinearMap.funLeft_apply]

end Avg

end GlobalTheory.MtIn

namespace GlobalTheory.MtIn

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
  [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (pres : Bridge.ClassPres ι S σ ρ J χ) {Q : Subgroup G} {ch : Q →* ℂˣ} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ)

theorem cutAvgL_ext (f : S.Forms) :
    cutAvgL ch tie.red tie.red_surj σ P ψ W (pres.ext f.1) = pres.ext (lvlAvgF act P ψ f).1 := by
  classical
  funext h
  rw [cutAvgL_apply, ← Bridge.ClassPres.extL_apply pres (lvlAvgF act P ψ f)]
  unfold lvlAvgF
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smulₛₗ, Bridge.ClassPres.extL_apply,
    tie.act_eq (p : G₀) _ (tie.red_surj (p : G₀)).choose_spec f, Pi.smul_apply, Bridge.g0Act, mul_smul]

theorem cutAvgL_of_mem {F : G → W}
    (hF : F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ)) :
    cutAvgL ch tie.red tie.red_surj σ P ψ W F = F := by
  classical
  have hF2 := (Submodule.mem_inf.1 hF).2
  have hF2' : ∀ (κ : Q) (hκ : tie.red κ ∈ P) (h : G),
      F (h * κ) = ((ch κ * ((Units.map σ.toMonoidHom).comp ψ) ⟨tie.red κ, hκ⟩ : ℂˣ) : ℂ) • F h := hF2
  funext h
  rw [cutAvgL_apply]
  have key : ∀ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) *
      (((ch (tie.red_surj (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) • F (h * ((tie.red_surj (p : G₀)).choose : G)) =
      ((Nat.card P : ℂ))⁻¹ • F h := by
    intro p
    have hs := (tie.red_surj (p : G₀)).choose_spec
    have hm : tie.red (tie.red_surj (p : G₀)).choose ∈ P := by rw [hs]; exact p.2
    have hp : (⟨tie.red (tie.red_surj (p : G₀)).choose, hm⟩ : P) = p := Subtype.ext hs
    rw [hF2' _ hm h, hp, smul_smul]
    congr 1
    have h1 : ((ch (tie.red_surj (p : G₀)).choose : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : σ ((ψ p : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_mul, map_inv,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_natCast, RingHom.toMonoidHom_eq_coe]
    field_simp
  rw [Finset.sum_congr rfl fun p _ => key p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

theorem ext_lvlForm_mem_span (x : Fin (S.lvlDim act P ψ) → K) :
    pres.ext (lvlForm S act P ψ x).1 ∈
      Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) := by
  have hx : x = ∑ a, x a • (Pi.single a (1 : K) : Fin (S.lvlDim act P ψ) → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e : pres.ext (lvlForm S act P ψ x).1 =
      ∑ a, σ (x a) • pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
    rw [← lvlFormL_apply, ← Bridge.ClassPres.extL_apply, hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, map_smulₛₗ, Bridge.ClassPres.extL_apply, lvlFormL_apply]
    simp [Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem ext_lvlForm_mem_cutSp (x : Fin (S.lvlDim act P ψ) → K) :
    pres.ext (lvlForm S act P ψ x).1 ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) := by
  refine Submodule.mem_inf.2 ⟨Bridge.ClassPres.extMem_holds pres _, ?_⟩
  intro κ hκ h
  have e1 := tie.act_eq (tie.red κ) κ rfl (lvlForm S act P ψ x)
  have e2 : act (tie.red κ) (lvlForm S act P ψ x) = ((ψ ⟨tie.red κ, hκ⟩ : Kˣ) : K) • lvlForm S act P ψ x :=
    lvlForm_eig x ⟨tie.red κ, hκ⟩
  rw [e2, ← Bridge.ClassPres.extL_apply, map_smulₛₗ, Bridge.ClassPres.extL_apply] at e1
  have e3 := congrFun e1 h
  simp only [Pi.smul_apply, Bridge.g0Act] at e3
  have h1 : ((ch κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_mul, RingHom.id_apply,
    RingHom.toMonoidHom_eq_coe]
  rw [mul_smul, e3, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Pres

end GlobalTheory.MtIn

namespace GlobalTheory.MtIn

section Main

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
  [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (pres : Bridge.ClassPres ι S σ ρ J χ) {Q : Subgroup G} {ch : Q →* ℂˣ} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ)

theorem ext_lvlForm_single (a : Fin (S.lvlDim act P ψ)) :
    pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 = ∑ i, σ (S.lvlE act P ψ i a) • pres.ext (S.basis i).1 := by
  rw [← Bridge.ClassPres.extL_apply, lvlForm_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, Bridge.ClassPres.extL_apply]
  simp [Matrix.mulVec_single_one]

theorem lvlForm_linInd : LinearIndependent ℂ fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hb := Fintype.linearIndependent_iff.1 (Bridge.ClassPres.linInd pres)
  have hsum : ∑ i, (∑ a, g a * σ (S.lvlE act P ψ i a)) • pres.extL (S.basis i) = 0 := by
    have e : ∑ i, (∑ a, g a * σ (S.lvlE act P ψ i a)) • pres.extL (S.basis i) =
        ∑ a, g a • pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
      simp only [ext_lvlForm_single, Finset.smul_sum, smul_smul, Bridge.ClassPres.extL_apply, Finset.sum_smul]
      exact Finset.sum_comm
    rw [e, hg]
  have hc : ((S.lvlE act P ψ).map σ).mulVec g = 0 := by
    ext i
    have := hb _ hsum i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hinj : Function.Injective (S.lvlE act P ψ).mulVec :=
    (image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).1
  obtain ⟨gl, hgl⟩ := LinearMap.exists_leftInverse_of_injective (S.lvlE act P ψ).mulVecLin
    (LinearMap.ker_eq_bot.2 hinj)
  have hLE : LinearMap.toMatrix' gl * S.lvlE act P ψ = 1 := by
    have := congrArg LinearMap.toMatrix' hgl
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLE' : (LinearMap.toMatrix' gl).map σ * (S.lvlE act P ψ).map σ = 1 := by
    rw [← Matrix.map_mul, hLE, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h0 : g = 0 := by
    calc g = ((LinearMap.toMatrix' gl).map σ * (S.lvlE act P ψ).map σ).mulVec g := by
          rw [hLE', Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  intro a
  rw [h0]
  rfl

theorem lvlForm_span :
    Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) =
      cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ext_lvlForm_mem_cutSp pres tie P ψ _
  · intro F hF
    have hFA : F ∈ Submodule.span ℂ (Set.range pres.extL) := by
      rw [Bridge.ClassPres.span_eq]
      exact (Submodule.mem_inf.1 hF).1
    have hle : Submodule.span ℂ (Set.range pres.extL) ≤
        (Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1)).comap
          (cutAvgL ch tie.red tie.red_surj σ P ψ W) := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Bridge.ClassPres.extL_apply, cutAvgL_ext pres tie P ψ f]
      obtain ⟨x, hx⟩ := exists_lvlForm_avg (act := act) (P := P) (ψ := ψ) f
      rw [← hx]
      exact ext_lvlForm_mem_span pres P ψ x
    have := hle hFA
    rwa [Submodule.mem_comap, cutAvgL_of_mem pres tie P ψ hF] at this

theorem lvlForm_of_mem {F : G → W}
    (hF : F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ))
    (hv : ∀ c, F (pres.y c) ∈ Set.range pres.coef) : ∃ x, F = pres.ext (lvlForm S act P ψ x).1 := by
  choose f0 hf0 using hv
  have hA := (Submodule.mem_inf.1 hF).1
  have hfix : ∀ c (g : S.Gam c), S.ρ c g (f0 c) = f0 c := by
    intro c g
    have e : pres.coef (S.ρ c g (f0 c) - f0 c) = 0 := by
      rw [map_sub, pres.coef_act, hf0, Bridge.ClassPres.adForms_fixed pres hA c g, sub_self]
    exact sub_eq_zero.1 (Bridge.ClassPres.coef_inj pres e)
  let f : S.Forms := ⟨f0, hfix⟩
  have hFf : F = pres.ext f.1 := by
    refine Bridge.ClassPres.adForms_ext pres hA (Bridge.ClassPres.extMem_holds pres f) fun c => ?_
    rw [Bridge.ClassPres.ext_rep]
    exact (hf0 c).symm
  obtain ⟨x, hx⟩ := exists_lvlForm_avg (act := act) (P := P) (ψ := ψ) f
  refine ⟨x, ?_⟩
  rw [hx, ← cutAvgL_ext pres tie P ψ f, ← hFf, cutAvgL_of_mem pres tie P ψ hF]

end Main

theorem mem_lvlNab_iff {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {G₀ : Type} [Group G₀]
    [Fintype G₀] {act : Representation K G₀ S.Forms} {P : Subgroup G₀} {ψ : P →* Kˣ} (x : Fin (S.lvlDim act P ψ) → K) :
    x ∈ S.lvlNab act P ψ ↔ ∀ c, (lvlForm S act P ψ x).1 c ∈ S.Nab c := by
  show (S.lvlE act P ψ).mulVec x ∈ S.nabLat ↔ _
  rw [CSD.nabLat, mem_valLatF] <;> rfl

theorem lvlForm_adelic_basis : ∀ (G Γ W K : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (pres : Bridge.ClassPres ι S σ ρ J χ) (Q : Subgroup G) (ch : Q →* ℂˣ) (G₀ : Type) [Group G₀] [Fintype G₀] (act : Representation K G₀ S.Forms) (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ), (LinearIndependent ℂ fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) ∧ Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) = cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) ∧ (∀ F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ), (∀ c, F (pres.y c) ∈ Set.range pres.coef) → ∃ x, F = pres.ext (lvlForm S act P ψ x).1) ∧ (∀ x, x ∈ S.lvlNab act P ψ ↔ ∀ c, (lvlForm S act P ψ x).1 c ∈ S.Nab c) ∧ (∀ (f : S.Forms) c, pres.ext f.1 (pres.y c) = pres.coef (f.1 c)) ∧ Function.Injective pres.coef := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ pres Q ch G₀ _ _ act tie P ψ
  exact ⟨lvlForm_linInd pres P ψ, lvlForm_span pres tie P ψ, fun F hF hv => lvlForm_of_mem pres tie P ψ hF hv,
    fun x => mem_lvlNab_iff x, fun f c => Bridge.ClassPres.ext_rep pres f c,
    fun a b h => sub_eq_zero.1 (Bridge.ClassPres.coef_inj pres (by rw [map_sub, h, sub_self]))⟩

end GlobalTheory.MtIn
