import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainOneFlagTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTripleCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
import Development.AutomorphicArithmetic.LocalEmbeddings.SemiUnfold
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.MidUnfold

open Matrix GlobalTheory.ThK.FlagSemi
open GlobalTheory.SwapShearLines (incM_mulVec' incM_mul' inv_mulVec_of pair_incV incV_add' incV_smul' incV_sub' incV_zero' cA_inclR')

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d d₁ e : ℕ}

variable (F) in

def Spans (H : Plane E d₁ e) : Prop := ∀ z : Fin d₁ → AE F E, ∃ (a b : AE F E) (z₂ : Fin e → AE F E),
  z = a • incV F H.x + incM F H.ι *ᵥ z₂ + b • incV F H.y

theorem spans_of_span (H : Plane E d₁ e)
    (h : Submodule.span E ({H.x, H.y} ∪ Set.range (fun u => H.ι *ᵥ u)) = ⊤) : Spans F H := by
  let S : Submodule (AE F E) (Fin d₁ → AE F E) :=
    { carrier := {z | ∃ (a b : AE F E) (z₂ : Fin e → AE F E), z = a • incV F H.x + incM F H.ι *ᵥ z₂ + b • incV F H.y}
      zero_mem' := ⟨0, 0, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, b, z, rfl⟩ ⟨a', b', z', rfl⟩
        exact ⟨a + a', b + b', z + z', by rw [add_smul, add_smul, mulVec_add]; abel⟩
      smul_mem' := by
        rintro c _ ⟨a, b, z, rfl⟩
        exact ⟨c * a, c * b, c • z, by rw [mul_smul, mul_smul, mulVec_smul, smul_add, smul_add]⟩ }
  have key : ∀ v : Fin d₁ → E, incV F v ∈ S := by
    intro v
    have hv : v ∈ Submodule.span E ({H.x, H.y} ∪ Set.range (fun u => H.ι *ᵥ u)) := h ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (rfl | rfl) | ⟨u, rfl⟩
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, incV F u, by simp [incM_mulVec']⟩
    | zero => rw [incV_zero']; exact S.zero_mem
    | add x y _ _ hx hy => rw [incV_add']; exact S.add_mem hx hy
    | smul c x _ hx => rw [incV_smul']; exact S.smul_mem _ hx
  intro z
  show z ∈ S
  rw [← Finset.univ_sum_single z]
  refine S.sum_mem fun j _ => ?_
  have : (Pi.single j (z j) : Fin d₁ → AE F E) = z j • incV F (Pi.single j (1 : E)) := by
    ext k; by_cases hk : k = j <;> simp [incV, Pi.single_apply, hk]
  rw [this]
  exact S.smul_mem _ (key _)

variable (σ) in

def stabY (W : Spc F E d) (H' : Plane E d d₁) (H₂ : Plane E d₁ e) : Subgroup (UA σ W.J) where
  carrier := {u | u ∈ unip σ W H' ∧ mat u *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x)}
  one_mem' := ⟨one_mem _, by rw [mat_one, one_mulVec]⟩
  mul_mem' := fun hu hv => ⟨mul_mem hu.1 hv.1, by rw [mat_mul, ← mulVec_mulVec, hv.2, hu.2]⟩
  inv_mem' := fun hu => ⟨inv_mem hu.1, inv_mulVec_of _ hu.2⟩

theorem isClosed_stabY (W : Spc F E d) (H' : Plane E d d₁) (H₂ : Plane E d₁ e) :
    IsClosed (stabY σ W H' H₂ : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  exact (GlobalTheory.UnipCT.isClosed_unip σ W H').inter (isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const)

section Shear

variable {W : Spc F E d} {J₁ : Matrix (Fin d₁) (Fin d₁) E} {H' : Plane E d d₁} {H₂ : Plane E d₁ e}
  {π : Matrix (Fin d₁) (Fin d) E} (hF : IsFrame σ W.J J₁ H' π) (hS : Spans F H₂)
  {nn : AE F E → UA σ W.J} (hn : IsShear H' H₂ nn)

include hS hn in
theorem shear_ι (z : Fin d₁ → AE F E) : ∃ a : AE F E, ∀ c,
    mat (nn c) *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + (c * a) • incV F H'.x := by
  obtain ⟨a, b, z₂, rfl⟩ := hS z
  refine ⟨a, fun c => ?_⟩
  obtain ⟨-, n2, n3, -, n5⟩ := hn c
  simp only [mulVec_add, mulVec_smul, incM_mulVec', n2, n3]
  rw [mulVec_mulVec z₂ (incM F H'.ι), ← incM_mul', mulVec_mulVec, n5, smul_add, smul_smul, mul_comm a c]
  abel

include hF hS hn in
theorem shear_apply (v : Fin d → AE F E) : ∃ a b : AE F E, ∀ c,
    mat (nn c) *ᵥ v = v + (c * a) • incV F H'.x + (cA σ c * b) • incV F (H'.ι *ᵥ H₂.y) := by
  obtain ⟨a, ha⟩ := shear_ι hS hn (incM F π *ᵥ v)
  refine ⟨a, incV F (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ v, fun c => ?_⟩
  have hv := hF.decomp v
  generalize incV F (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ v = β at hv ⊢
  generalize incV F (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ v = α at hv
  generalize incM F π *ᵥ v = z at hv ha
  subst hv
  rw [mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul, ha, (hn c).1, (hn c).2.2.2.1, smul_sub, smul_smul,
    mul_comm β]
  abel

include hF hS hn in
theorem shear_add (c c' : AE F E) : nn (c + c') = nn c * nn c' := by
  refine mat_ext (ext_mulVec_single fun j => ?_)
  obtain ⟨a, b, h⟩ := shear_apply hF hS hn (Pi.single j 1)
  rw [mat_mul, ← mulVec_mulVec, h c', mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, (hn c).1, (hn c).2.2.1, h c, h,
    map_add, add_mul, add_mul, add_smul, add_smul]
  abel

def shearHom : Multiplicative (AE F E) →* UA σ W.J :=
  MonoidHom.mk' (fun c => nn c.toAdd) fun c c' => shear_add hF hS hn _ _

theorem shearHom_apply (c : Multiplicative (AE F E)) : shearHom hF hS hn c = nn c.toAdd := rfl

theorem continuous_shearHom : Continuous (shearHom hF hS hn) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hm : Continuous fun c => mat (nn c) := by
    refine continuous_matrix fun i j => ?_
    obtain ⟨a, b, h⟩ := shear_apply hF hS hn (Pi.single j 1)
    have : (fun c => mat (nn c) i j) = fun c => (Pi.single j 1 + (c * a) • incV F H'.x +
        (cA σ c * b) • incV F (H'.ι *ᵥ H₂.y) : Fin d → AE F E) i := by
      funext c; rw [← h, mulVec_single_one]; rfl
    rw [this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  apply Continuous.subtype_mk (f := fun c => (shearHom hF hS hn c).1)
  refine Units.continuous_iff.2 ⟨hm.comp continuous_toAdd, ((hm.comp continuous_toAdd).comp continuous_inv).congr fun c => ?_⟩
  show mat (shearHom hF hS hn c⁻¹) = _
  rw [map_inv]; rfl

include hS hn in
theorem shear_mem (c : AE F E) : nn c ∈ unip σ W H' :=
  mem_unip.2 ⟨(hn c).1, fun z => by obtain ⟨a, ha⟩ := shear_ι hS hn z; exact ⟨_, ha c⟩⟩

theorem stab_mul_shear {u : UA σ W.J} (hu : u ∈ stabY σ W H' H₂) (c : Multiplicative (AE F E)) :
    mat (u * shearHom hF hS hn c) *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x) + c.toAdd • incV F H'.x := by
  rw [mat_mul, ← mulVec_mulVec, shearHom_apply, (hn _).2.1, mulVec_add, mulVec_smul, hu.2, (mem_unip.1 hu.1).1]

theorem shear_conj (u : UA σ W.J) (hu : u ∈ stabY σ W H' H₂) (c : Multiplicative (AE F E)) :
    shearHom hF hS hn c * u * (shearHom hF hS hn c)⁻¹ ∈ stabY σ W H' H₂ := by
  have hm : ∀ c, shearHom hF hS hn c ∈ unip σ W H' := fun c => shear_mem hS hn _
  refine ⟨mul_mem (mul_mem (hm c) hu.1) (inv_mem (hm c)), ?_⟩
  rw [← map_inv, mul_assoc, mat_mul, ← mulVec_mulVec, stab_mul_shear hF hS hn hu, mulVec_add, mulVec_smul,
    shearHom_apply, (hn _).1, (hn _).2.1, toAdd_inv, neg_smul, add_neg_cancel_right]

theorem unip_eq_sup : unip σ W H' = stabY σ W H' H₂ ⊔ (shearHom hF hS hn).range := by
  refine le_antisymm (fun u hu => ?_) (sup_le (fun u hu => hu.1) ?_)
  · obtain ⟨h1, a, ha⟩ := GlobalTheory.SwapShearLines.unip_prop H₂.x hu
    have h2 : u * (shearHom hF hS hn (Multiplicative.ofAdd a))⁻¹ ∈ stabY σ W H' H₂ := by
      refine ⟨mul_mem hu (inv_mem (shear_mem hS hn _)), ?_⟩
      rw [← map_inv, mat_mul, ← mulVec_mulVec, shearHom_apply, (hn _).2.1, mulVec_add, mulVec_smul, ha, h1, toAdd_inv,
        toAdd_ofAdd, neg_smul, add_neg_cancel_right]
    have := mul_mem (Subgroup.mem_sup_left (T := (shearHom hF hS hn).range) h2)
      (Subgroup.mem_sup_right ⟨Multiplicative.ofAdd a, rfl⟩)
    simpa using this
  · rintro _ ⟨c, rfl⟩
    exact shear_mem hS hn _

variable (hxy : form σ W.J H'.x H'.y = 1) (ho : form σ W.J (H'.ι *ᵥ H₂.x) H'.y = 0)
include hxy ho

theorem shear_coef {u : UA σ W.J} (hu : u ∈ stabY σ W H' H₂) (c : Multiplicative (AE F E)) :
    (mat (u * shearHom hF hS hn c) *ᵥ incV F (H'.ι *ᵥ H₂.x)) ⬝ᵥ incV F (W.J *ᵥ fun i => σ (H'.y i)) = c.toAdd := by
  rw [stab_mul_shear hF hS hn hu, add_dotProduct, smul_dotProduct, pair_incV, pair_incV, hxy, ho, map_one, map_zero,
    smul_eq_mul, mul_one, zero_add]

theorem shear_inj : ∀ n ∈ stabY σ W H' H₂, ∀ n' ∈ stabY σ W H' H₂, ∀ h h',
    n * shearHom hF hS hn h = n' * shearHom hF hS hn h' → n = n' ∧ h = h' := by
  intro n h1 n' h2 h h' he
  obtain rfl : h = h' := Multiplicative.toAdd.injective (by
    rw [← shear_coef hF hS hn hxy ho h1, he, shear_coef hF hS hn hxy ho h2])
  exact ⟨mul_right_cancel he, rfl⟩

theorem shear_rat_iff (hr : ∀ c : E, nn (inclR (F := F) (AF F) c) ∈ ratU σ W.J) : ∀ n ∈ stabY σ W H' H₂, ∀ h,
    n * shearHom hF hS hn h ∈ ratU σ W.J ↔ n ∈ ratU σ W.J ∧
      h ∈ AddSubgroup.toSubgroup (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.range := by
  intro n h1 h
  have key : h ∈ AddSubgroup.toSubgroup (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.range →
      shearHom hF hS hn h ∈ ratU σ W.J := by
    rintro ⟨c, hc⟩
    have hc' : inclR (F := F) (AF F) c = h.toAdd := hc
    rw [shearHom_apply, ← hc']
    exact hr c
  refine ⟨fun hm => ?_, fun hm => mul_mem hm.1 (key hm.2)⟩
  obtain ⟨A, hA⟩ := (mem_ratU_iff _).1 hm
  have h2 := shear_coef hF hS hn hxy ho h1 h
  rw [← hA, incM_mulVec', pair_incV] at h2
  have h3 : h ∈ AddSubgroup.toSubgroup (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.range := ⟨_, h2⟩
  exact ⟨(mul_mem_cancel_right (key h3)).1 hm, h3⟩

end Shear

section Swap

variable {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {H₂ : Plane E d₁ e}
  {π : Matrix (Fin d₁) (Fin d) E} (hF : IsFrame σ W.J W₁.J H' π) (hS : Spans F H₂) {w : UA σ W.J} (hw : IsSwap H' H₂ w)

variable (σ W H') in

def capN (w : UA σ W.J) : Subgroup (UA σ W.J) := unip σ W H' ⊓ (unip σ W H').comap (MulAut.conj w).toMonoidHom

theorem mem_capN {u : UA σ W.J} : u ∈ capN σ W H' w ↔ u ∈ unip σ W H' ∧ w * u * w⁻¹ ∈ unip σ W H' := Iff.rfl

theorem isClosed_capN : IsClosed (capN σ W H' w : Set (UA σ W.J)) := by
  haveI := (GlobalTheory.UnipCT.topFacts σ W.J).1
  exact (GlobalTheory.UnipCT.isClosed_unip σ W H').inter ((GlobalTheory.UnipCT.isClosed_unip σ W H').preimage
    (f := fun u => w * u * w⁻¹) (by fun_prop))

variable (H₂ w) in

def leviW : unip σ W₁ H₂ →* UA σ W.J :=
  (MulAut.conj w⁻¹).toMonoidHom.comp (hF.1.levi.comp (unip σ W₁ H₂).subtype)

theorem leviW_apply (h : unip σ W₁ H₂) : leviW H₂ hF w h = w⁻¹ * hF.1.levi h.1 * w := by
  simp [leviW]

theorem conj_leviW (n : UA σ W.J) (h : unip σ W₁ H₂) :
    w * (n * leviW H₂ hF w h) * w⁻¹ = w * n * w⁻¹ * hF.1.levi h.1 := by
  rw [leviW_apply]; group

theorem continuous_leviW : Continuous (leviW H₂ hF w) := by
  haveI := (GlobalTheory.UnipCT.topFacts σ W.J).1
  have := hF.1.continuous_levi
  exact (show Continuous fun h : unip σ W₁ H₂ => w⁻¹ * hF.1.levi h.1 * w by fun_prop).congr
    fun h => (leviW_apply hF h).symm

include hw in
theorem swap_ι (z : Fin e → AE F E) :
    mat w *ᵥ (incM F H'.ι *ᵥ (incM F H₂.ι *ᵥ z)) = incM F H'.ι *ᵥ (incM F H₂.ι *ᵥ z) := by
  rw [mulVec_mulVec z (incM F H'.ι), ← incM_mul', mulVec_mulVec, hw.2.2.2.2.2]

include hS hw in
theorem leviW_mem (h : unip σ W₁ H₂) : leviW H₂ hF w h ∈ stabY σ W H' H₂ := by
  obtain ⟨h1, h2⟩ := mem_unip.1 h.2
  obtain ⟨-, w1, w2, w3, w4, -⟩ := id hw
  have e : ∀ v, mat (leviW H₂ hF w h) *ᵥ v = mat w⁻¹ *ᵥ (mat (hF.1.levi h.1) *ᵥ (mat w *ᵥ v)) := fun v => by
    rw [leviW_apply, mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have e1 : mat (leviW H₂ hF w h) *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x) := by
    rw [e, w3, hF.1.levi_fix _ hF.πx, inv_mulVec_of w w3]
  have e2 : mat (leviW H₂ hF w h) *ᵥ incV F (H'.ι *ᵥ H₂.y) = incV F (H'.ι *ᵥ H₂.y) := by
    rw [e, w4, hF.1.levi_fix _ hF.πy, inv_mulVec_of w w4]
  refine ⟨mem_unip.2 ⟨?_, fun z => ?_⟩, e1⟩
  · rw [e, w1, ← incM_mulVec', hF.1.levi_ι, h1, incM_mulVec', inv_mulVec_of w w1]
  · obtain ⟨a, b, z₂, rfl⟩ := hS z
    obtain ⟨c, hc⟩ := h2 z₂
    refine ⟨c, ?_⟩
    have e3 : mat (leviW H₂ hF w h) *ᵥ (incM F H'.ι *ᵥ (incM F H₂.ι *ᵥ z₂)) =
        incM F H'.ι *ᵥ (incM F H₂.ι *ᵥ z₂) + c • incV F H'.x := by
      rw [e, swap_ι hw, hF.1.levi_ι, hc, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, incM_mulVec',
        inv_mulVec_of w w1, inv_mulVec_of w (swap_ι hw z₂)]
    simp only [mulVec_add, mulVec_smul, incM_mulVec', e1, e2, e3]
    abel

include hS hw in
theorem leviW_conj (n : UA σ W.J) (hn : n ∈ capN σ W H' w) (h : unip σ W₁ H₂) :
    leviW H₂ hF w h * n * (leviW H₂ hF w h)⁻¹ ∈ capN σ W H' w := by
  have h1 := (leviW_mem hF hS hw h).1
  refine mem_capN.2 ⟨mul_mem (mul_mem h1 hn.1) (inv_mem h1), ?_⟩
  have := GlobalTheory.ThK.DescB.FlagTwoDom.levi_conj_mem hF _ (mem_capN.1 hn).2 h.1
  convert this using 1
  rw [leviW_apply]; group

theorem proj_mul_levi {n : UA σ W.J} (hn : n ∈ unip σ W H') (g : UA σ W₁.J) (z : Fin d₁ → AE F E) :
    incM F π *ᵥ (mat (n * hF.1.levi g) *ᵥ (incM F H'.ι *ᵥ z)) = mat g *ᵥ z := by
  have := GlobalTheory.ThK.DescB.FlagTwoDom.proj_unip hF hn (mat g *ᵥ z) 0
  rw [zero_smul, add_zero] at this
  rw [mat_mul, ← mulVec_mulVec, hF.1.levi_ι, this]

theorem leviW_inj : ∀ n ∈ capN σ W H' w, ∀ n' ∈ capN σ W H' w, ∀ h h',
    n * leviW H₂ hF w h = n' * leviW H₂ hF w h' → n = n' ∧ h = h' := by
  intro n hn n' hn' h h' he
  have e := congrArg (fun x => w * x * w⁻¹) he
  simp only [conj_leviW] at e
  obtain rfl : h = h' := Subtype.ext (mat_ext (ext_mulVec_single fun j => by
    rw [← proj_mul_levi hF (mem_capN.1 hn).2 h.1, e, proj_mul_levi hF (mem_capN.1 hn').2 h'.1]))
  exact ⟨mul_right_cancel he, rfl⟩

include hw in
theorem leviW_rat_iff : ∀ n ∈ capN σ W H' w, ∀ h, n * leviW H₂ hF w h ∈ ratU σ W.J ↔
    n ∈ ratU σ W.J ∧ h ∈ (ratU σ W₁.J).subgroupOf (unip σ W₁ H₂) := by
  intro n hn h
  have key : h ∈ (ratU σ W₁.J).subgroupOf (unip σ W₁ H₂) → leviW H₂ hF w h ∈ ratU σ W.J := fun hh => by
    rw [leviW_apply]
    exact mul_mem (mul_mem (inv_mem hw.1) (hF.1.levi_rat (Subgroup.mem_subgroupOf.1 hh))) hw.1
  refine ⟨fun hm => ?_, fun hm => mul_mem hm.1 (key hm.2)⟩
  have h1 := mul_mem (mul_mem hw.1 hm) (inv_mem hw.1)
  rw [conj_leviW] at h1
  have hg : h ∈ (ratU σ W₁.J).subgroupOf (unip σ W₁ H₂) := by
    obtain ⟨A, hA⟩ := (mem_ratU_iff _).1 h1
    refine Subgroup.mem_subgroupOf.2 ((mem_ratU_iff _).2 ⟨π * A * H'.ι, ext_mulVec_single fun j => ?_⟩)
    rw [incM_mul', incM_mul', hA, ← mulVec_mulVec, ← mulVec_mulVec, proj_mul_levi hF (mem_capN.1 hn).2]
  exact ⟨(mul_mem_cancel_right (key hg)).1 hm, hg⟩

include hw in
theorem conj_fix {v : UA σ W.J} (hv : v ∈ stabY σ W H' H₂) : mat (w * v * w⁻¹) *ᵥ incV F H'.x = incV F H'.x := by
  rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_of w hw.2.2.2.1, hv.2, hw.2.2.2.1]

include hS hw in
theorem stabY_eq_sup : stabY σ W H' H₂ = capN σ W H' w ⊔ (leviW H₂ hF w).range := by
  obtain ⟨-, w1, w2, w3, w4, -⟩ := id hw
  refine le_antisymm (fun v hv => ?_) (sup_le (fun u hu => ⟨hu.1, ?_⟩) ?_)
  · obtain ⟨g, hg⟩ := hF.exists_unip _ (conj_fix hw hv)
    obtain ⟨v1, v2⟩ := mem_unip.1 hv.1
    have key := proj_mul_levi hF hg g
    simp only [inv_mul_cancel_right, mat_mul, ← mulVec_mulVec] at key
    have hu : g ∈ unip σ W₁ H₂ := by
      refine mem_unip.2 ⟨?_, fun z => ?_⟩
      · rw [← key, incM_mulVec', inv_mulVec_of w w1, v1, w1, ← incM_mulVec', hF.1.π_ι]
      · obtain ⟨a, ha⟩ := v2 (incM F H₂.ι *ᵥ z)
        refine ⟨a, ?_⟩
        rw [← key, inv_mulVec_of w (swap_ι hw z), ha, mulVec_add, mulVec_smul, swap_ι hw, w1, mulVec_add, mulVec_smul,
          ← incM_mulVec', hF.1.π_ι, hF.1.π_ι]
    have h2 : v * (leviW H₂ hF w ⟨g, hu⟩)⁻¹ ∈ capN σ W H' w := by
      refine mem_capN.2 ⟨mul_mem hv.1 (inv_mem (leviW_mem hF hS hw _).1), ?_⟩
      convert hg using 1
      rw [leviW_apply]; group
    have := mul_mem (Subgroup.mem_sup_left (T := (leviW H₂ hF w).range) h2) (Subgroup.mem_sup_right ⟨⟨g, hu⟩, rfl⟩)
    simpa using this
  · have h1 := (mem_unip.1 (mem_capN.1 hu).2).1
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_of w w3] at h1
    rw [← inv_mulVec_of w h1, inv_mulVec_of w w3]
  · rintro _ ⟨h, rfl⟩
    exact leviW_mem hF hS hw h

end Swap

end GlobalTheory.MidUnfold

end
