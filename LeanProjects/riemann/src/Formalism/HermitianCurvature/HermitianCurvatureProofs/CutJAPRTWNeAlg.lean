import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlgSt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

section lemmas

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qdet_comm {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} (hF : GlRel F) (u : ℂ) (a b : Fin n) :
    qdet F u * F a b = F a b * qdet F u :=
  Formalism.REAL.qDetCentral_of Formalism.REAL.quantumMinorRowSkew_holds Formalism.REAL.quantumMinorColSkew_holds (Module.End ℂ V) n F hF u a b

theorem zvec {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hF : GlRel F) (hy : IsVec F y)
    (u : ℂ) : IsVec F (fun x => qdet F u * y x) := by
  intro a b c
  have e1 : F a b * (qdet F u * y c) = qdet F u * (F a b * y c) := by
    rw [← mul_assoc, ← qdet_comm hF u a b, mul_assoc]
  rw [e1, mul_assoc, ← mul_sub, hy a b c]
  split_ifs <;> simp

theorem cpol_down_self {n : ℕ} (p : Fin n → ℂ) (hp : Function.Injective p) (i : Fin n) :
    cpol (Function.update p i (p i - 1)) (-p i) ≠ 0 := by
  unfold cpol
  rw [Finset.prod_ne_zero_iff]
  intro j _
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    intro h
    have h1 : (-1 : ℂ) = 0 := by linear_combination h
    norm_num at h1
  · rw [Function.update_of_ne hj]
    intro h
    exact hj (hp (by linear_combination h))

theorem cpol_down_other {n : ℕ} (p : Fin n → ℂ) (i j : Fin n) (hji : j ≠ i) :
    cpol (Function.update p j (p j - 1)) (-p i) = 0 := by
  unfold cpol
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Function.update_of_ne (Ne.symm hji)]
  ring

theorem erase_ne_zero {n : ℕ} (p : Fin n → ℂ) (hp : Function.Injective p) (i : Fin n) :
    ∏ j ∈ Finset.univ.erase i, (-p i + p j) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj h
  exact Finset.ne_of_mem_erase hj (hp (by linear_combination h))

theorem z_main (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : Fin (n + 1) → ℂ) (hE : GlRel E)
    (hcap : ∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) (p : Fin n → ℂ) (hp : Function.Injective p) (i : Fin n)
    (hl : ∀ j, p i - 1 ≠ l j) (v : V) (hv : v ∈ CapSp (subA E) p) :
    (∀ x, qdet (subA E) (-p i) (yK E x v) ∈ CapSp (subA E) (Function.update p i (p i - 1))) ∧
      ∃ t : ℂ, t ≠ 0 ∧ ∑ x, etaK E x (qdet (subA E) (-p i) (yK E x v)) = t • v := by
  obtain ⟨hsGl, -, hsVec, -, hyc, -⟩ := Formalism.FourierDecayAlt.P.submodule_relations (Module.End ℂ V) n E hE
  obtain ⟨Φ, hsum, hmemΦ, hrelΦ⟩ :=
    Formalism.FourierDecayAlt.P.vector_descent V n (subA E) (yK E) hsGl hsVec hyc p hp v hv

  have hΦq : ∀ j x, qdet (subA E) (-p i) (Φ j x) =
      if j = i then cpol (Function.update p i (p i - 1)) (-p i) • Φ i x else 0 := by
    intro j x
    rw [(mem_CapSp.mp (hmemΦ j x)) (-p i)]
    split_ifs with hji
    · subst hji
      rfl
    · rw [cpol_down_other p i j hji, zero_smul]
  have hqy : ∀ x, qdet (subA E) (-p i) (yK E x v) =
      cpol (Function.update p i (p i - 1)) (-p i) • Φ i x := by
    intro x
    rw [← hsum x, map_sum, Finset.sum_congr rfl (fun j _ => hΦq j x), Finset.sum_ite_eq']
    simp
  refine ⟨fun x => ?_, ?_⟩
  · rw [hqy x]
    exact Submodule.smul_mem _ _ (hmemΦ i x)
  · set P := ∏ k ∈ Finset.univ.erase i, (-p i + p k) with hPdef
    have hpart : ∀ w : Fin n, ∑ x : Fin n, ((-1 : ℂ) ^ ((w : ℕ) + (x : ℕ))) •
        qminor (subA E) (skip1 w) (skip1 x) (-p i - 1) (yK E x v) = P • Φ i w := by
      intro w
      have e1 : ∀ x, yK E x v = ∑ j, Φ j x := fun x => (hsum x).symm
      simp only [e1, map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      simp only [hrelΦ]
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩) (by ring),
          zero_smul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hS : (∑ w : Fin n, ∑ x : Fin n, ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) *
        (etaK E w * qminor (subA E) (skip1 w) (skip1 x) (-p i - 1) * yK E x))) v =
        P • ∑ w, etaK E w (Φ i w) := by
      simp only [Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.sgn_mul, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← map_smul (etaK E w) P (Φ i w), ← hpart w, map_sum]
      simp only [map_smul]

    have hBF := congrArg (fun T : Module.End ℂ V => T v)
      (Formalism.FourierDecayAlt.P.border_first (Module.End ℂ V) n E hE (1 - p i))
    have h1 : (1 - p i - 1 : ℂ) = -p i := by ring
    have h2 : (1 - p i - 2 : ℂ) = -p i - 1 := by ring
    simp only [h1, h2, LinearMap.sub_apply, Module.End.mul_apply] at hBF
    have hcp : cpol p (-p i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
    rw [hS, hcap, (mem_CapSp.mp hv) (-p i), hcp, zero_smul, map_zero, zero_sub] at hBF
    have hP : P ≠ 0 := erase_ne_zero p hp i
    have hcl : cpol l (1 - p i) ≠ 0 := by
      unfold cpol
      rw [Finset.prod_ne_zero_iff]
      intro j _ h
      exact hl j (by linear_combination -h)
    have hci := cpol_down_self p hp i
    have hE2 : ∑ w, etaK E w (Φ i w) = -(P⁻¹ * cpol l (1 - p i)) • v := by
      calc ∑ w, etaK E w (Φ i w) = P⁻¹ • (P • ∑ w, etaK E w (Φ i w)) := by
            rw [smul_smul, inv_mul_cancel₀ hP, one_smul]
        _ = P⁻¹ • -(cpol l (1 - p i) • v) := by rw [hBF, neg_neg]
        _ = -(P⁻¹ * cpol l (1 - p i)) • v := by rw [smul_neg, smul_smul, neg_smul]
    refine ⟨-(cpol (Function.update p i (p i - 1)) (-p i) * (P⁻¹ * cpol l (1 - p i))), ?_, ?_⟩
    · exact neg_ne_zero.mpr (mul_ne_zero hci (mul_ne_zero (inv_ne_zero hP) hcl))
    · simp only [hqy, map_smul]
      rw [← Finset.smul_sum, hE2, smul_smul, mul_neg, neg_smul]

theorem fam_of_hw {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} {Z : Fin n → Module.End ℂ V} (hZ : IsVec F Z)
    (ν : Fin n → ℂ) (v : V) (hv : IsHW F ν v) :
    (∀ a c, F a a (Z c v) = (ν a - if a = c then 1 else 0) • Z c v) ∧
      ∀ a b c, a < b → F a b (Z c v) = if a = c then -(Z b v) else 0 := by
  obtain ⟨hdiag, hup⟩ := hv
  constructor
  · intro a c
    have h := congrArg (fun T : Module.End ℂ V => T v) (hZ a a c)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hdiag a, map_smul] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true, LinearMap.neg_apply] at h
      rw [if_pos rfl, sub_eq_iff_eq_add.mp h, sub_smul, one_smul]
      abel
    · simp only [if_neg hac, LinearMap.zero_apply] at h
      rw [if_neg hac, sub_zero]
      exact sub_eq_zero.mp h
  · intro a b c hab
    have h := congrArg (fun T : Module.End ℂ V => T v) (hZ a b c)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hup a b hab, map_zero, sub_zero] at h
    rw [h]
    split_ifs <;> simp

theorem fam_zero [FiniteDimensional ℂ V] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ V) (hF : GlRel F) (m : Fin n → ℂ)
    (hm : SDec m) (i : Fin n) (Φ : Fin n → V) (hmem : ∀ c, Φ c ∈ CapSp F m)
    (hd : ∀ a c, F a a (Φ c) = (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) • Φ c)
    (hr : ∀ a b c, a < b → F a b (Φ c) = if a = c then -(Φ b) else 0) (h0 : Φ i = 0) : ∀ c, Φ c = 0 := by
  classical
  by_contra hne
  rw [not_forall] at hne

  obtain ⟨c0, hc0⟩ := hne
  let S := Finset.univ.filter (fun c => Φ c ≠ 0)
  have hS : S.Nonempty := ⟨c0, by simp [S, hc0]⟩
  have hcS : Φ (S.max' hS) ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hbig : ∀ b, S.max' hS < b → Φ b = 0 := by
    intro b hb
    by_contra hb0
    exact absurd (S.le_max' b (by simp [S, hb0])) (not_le.mpr hb)
  have hHW : IsHW F (fun a => m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) -
      if a = S.max' hS then 1 else 0) (Φ (S.max' hS)) := by
    refine ⟨fun a => hd a _, fun a b hab => ?_⟩
    rw [hr a b _ hab]
    split_ifs with hac
    · subst hac
      rw [hbig b hab, neg_zero]
    · rfl
  have hne' : CapSp F m ≠ ⊥ := by
    intro h
    have hm0 := hmem (S.max' hS)
    rw [h] at hm0
    exact hcS ((Submodule.mem_bot ℂ).mp hm0)

  have hw := (Formalism.FourierDecayAlt.P.capelli_singular V n F m hF hne').2 hm _ _ (hmem _) hcS hHW
  by_cases hic : i = S.max' hS
  · exact hcS (hic ▸ h0)
  · have := hw i
    simp [hic] at this

end lemmas

section inj

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V']

theorem cap_map {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ V'} (J : V' →ₗ[ℂ] V)
    (hJ : ∀ a b v, J (F' a b v) = F a b (J v)) (m : Fin n → ℂ) (v : V') (hv : v ∈ CapSp F' m) : J v ∈ CapSp F m := by
  rw [mem_CapSp] at hv ⊢
  intro w
  rw [← Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int J hJ w v, hv w, map_smul]

private theorem strictAnti_of_box_of_strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (hL : StrictAnti L) (h : Box L M) :
    StrictAnti M := by
  intro j k hjk
  have h1 := (h k).2
  have h2 := (h j).1
  have h3 : L k.castSucc ≤ L j.succ := hL.antitone (by
    rw [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
    exact hjk)
  omega

theorem j_inj (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V')
    (β' : ℂ) (L' : Fin (n + 1) → ℤ) (M' : Fin n → ℤ) (hE' : Hyp E' β' L') (hM' : Box L' M')
    (J : V' →ₗ[ℂ] V) (hJ0 : J ≠ 0) (hJ : ∀ a b v, J (subA E' a b v) = subA E a b (J v))
    (hJr : ∀ v, J v ∈ CapSp (subA E) (shf β' M')) (x : V') (hx : x ∈ CapSp (subA E') (shf β' M')) (hx0 : x ≠ 0) :
    J x ≠ 0 := by
  intro hJx
  obtain ⟨hsGl', -⟩ := Formalism.FourierDecayAlt.P.submodule_relations (Module.End ℂ V') n E' hE'.gl
  have hstabC := (Formalism.FourierDecayAlt.P.capelli_stabilizer V' n (subA E') (shf β' M') hsGl').1

  have hstabK : Stab (subA E') (LinearMap.ker J ⊓ CapSp (subA E') (shf β' M')) := by
    intro a b w hw
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hw ⊢
    exact ⟨by rw [hJ, hw.1, map_zero], hstabC a b w hw.2⟩
  rcases Formalism.FourierDecayAlt.P.irreducible_capelli_modules V' n E' β' L' hE' M' hM' _ inf_le_right hstabK with h | h
  · have hxK : x ∈ LinearMap.ker J ⊓ CapSp (subA E') (shf β' M') := ⟨hJx, hx⟩
    rw [h] at hxK
    exact hx0 ((Submodule.mem_bot ℂ).mp hxK)
  ·
    apply hJ0
    have hanti : ∀ M'' : Fin n → ℤ, Box L' M'' → StrictAnti M'' := fun M'' hB => strictAnti_of_box_of_strictAnti hE'.anti hB
    have hpiece : ∀ M'' : Fin n → ℤ, Box L' M'' → CapSp (subA E') (shf β' M'') ≤ LinearMap.ker J := by
      intro M'' hB w hw
      rw [LinearMap.mem_ker]
      by_cases hMM : M'' = M'
      · subst hMM
        have hwK : w ∈ LinearMap.ker J ⊓ CapSp (subA E') (shf β' M'') := by rw [h]; exact hw
        exact hwK.1
      · have h1 : J w ∈ CapSp (subA E) (shf β' M'') := cap_map J hJ _ w hw
        have hdisj : Disjoint (CapSp (subA E) (shf β' M'')) (CapSp (subA E) (shf β' M')) :=
          (Formalism.FourierDecayAlt.P.capelli_independence V n (subA E) β').pairwiseDisjoint
            (i := ⟨M'', hanti M'' hB⟩) (j := ⟨M', hanti M' hM'⟩) (fun he => hMM (congrArg Subtype.val he))
        exact Submodule.disjoint_def.mp hdisj _ h1 (hJr w)
    have htop := (Formalism.FourierDecayAlt.P.branching_decomposition V' n E' β' L' hE').2
    have hle : (⨆ (M'' : Fin n → ℤ) (_ : Box L' M''), CapSp (subA E') (shf β' M'')) ≤ LinearMap.ker J :=
      iSup₂_le hpiece
    rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle

end inj

section core

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V']

private theorem capSp_family_eq_zero_above_index {n : ℕ} (F : Fin n → Fin n → Module.End ℂ V) (hF : GlRel F) (m : Fin n → ℂ)
    (hm : SDec m) (i : Fin n) (Φ : Fin n → V) (hmem : ∀ c, Φ c ∈ CapSp F m)
    (hd : ∀ a c, F a a (Φ c) = (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) • Φ c)
    (hr : ∀ a b c, a < b → F a b (Φ c) = if a = c then -(Φ b) else 0) : ∀ c, i < c → Φ c = 0 := by
  classical
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨c0, hic0, hc0⟩ := hne
  let S := Finset.univ.filter (fun c => i < c ∧ Φ c ≠ 0)
  have hS : S.Nonempty := ⟨c0, by simp [S, hic0, hc0]⟩
  have hmS := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hbig : ∀ b, S.max' hS < b → Φ b = 0 := by
    intro b hb
    by_contra hb0
    exact absurd (S.le_max' b (by simp [S, hb0, hmS.1.trans hb])) (not_le.mpr hb)
  have hHW : IsHW F (fun a => m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) -
      if a = S.max' hS then 1 else 0) (Φ (S.max' hS)) := by
    refine ⟨fun a => hd a _, fun a b hab => ?_⟩
    rw [hr a b _ hab]
    split_ifs with hac
    · subst hac
      rw [hbig b hab, neg_zero]
    · rfl
  have hne' : CapSp F m ≠ ⊥ := by
    intro h
    have hm0 := hmem (S.max' hS)
    rw [h] at hm0
    exact hmS.2 ((Submodule.mem_bot ℂ).mp hm0)
  have hw := (Formalism.FourierDecayAlt.P.capelli_singular V n F m hF hne').2 hm _ _ (hmem _) hmS.2 hHW (S.max' hS)
  have hci : S.max' hS ≠ i := ne_of_gt hmS.1
  simp [hci] at hw

private theorem exists_highest_weight_in_capSp_of_ne_bot {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ W) (hF : GlRel F) (p : Fin n → ℂ) (hp : SDec p) (hne : CapSp F p ≠ ⊥) :
    ∃ v, v ∈ CapSp F p ∧ v ≠ 0 ∧ IsHW F (fun a => p a + ((a : ℕ) : ℂ)) v := by
  obtain ⟨ν, v, hvS, hv0, hHW, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector W n F hF (CapSp F p)
    (Formalism.FourierDecayAlt.P.capelli_stabilizer W n F p hF).1 hne
  have hν := (Formalism.FourierDecayAlt.P.capelli_singular W n F p hF hne).2 hp ν v hvS hv0 hHW
  have hνe : ν = fun a => p a + ((a : ℕ) : ℂ) := funext hν
  exact ⟨v, hvS, hv0, hνe ▸ hHW⟩

private theorem fam_props_lemma_2 (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : Fin (n + 1) → ℂ)
    (hE : GlRel E) (hcap : ∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) (m p : Fin n → ℂ) (i : Fin n)
    (hm : SDec m) (hp : SDec p) (hpm : m = Function.update p i (p i - 1)) (hl : ∀ j, p i - 1 ≠ l j) (v : V)
    (hv : v ∈ CapSp (subA E) p) (hv0 : v ≠ 0) (hHW : IsHW (subA E) (fun a => p a + ((a : ℕ) : ℂ)) v) :
    (∀ c, qdet (subA E) (-p i) (yK E c v) ∈ CapSp (subA E) m) ∧
      (∀ a c, subA E a a (qdet (subA E) (-p i) (yK E c v)) =
        (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) •
          qdet (subA E) (-p i) (yK E c v)) ∧
      (∀ a b c, a < b → subA E a b (qdet (subA E) (-p i) (yK E c v)) =
        if a = c then -(qdet (subA E) (-p i) (yK E b v)) else 0) ∧
      (∃ t : ℂ, t ≠ 0 ∧ ∑ x, etaK E x (qdet (subA E) (-p i) (yK E x v)) = t • v) ∧
      qdet (subA E) (-p i) (yK E i v) ≠ 0 := by
  obtain ⟨hsGl, -, hsVec, -, -, -⟩ := Formalism.FourierDecayAlt.P.submodule_relations (Module.End ℂ V) n E hE
  have hpinj : Function.Injective p := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_inj hp
  have hmp : ∀ a, m a + (if a = i then 1 else 0) = p a := by
    intro a
    subst hpm
    by_cases h : a = i
    · subst h
      simp
    · simp [h]
  obtain ⟨hmemw, t, ht, hsumw⟩ := z_main n E l hE hcap p hpinj i hl v hv
  obtain ⟨hdw, hrw⟩ := fam_of_hw (zvec hsGl hsVec (-p i)) _ v hHW
  have hmem' : ∀ c, qdet (subA E) (-p i) (yK E c v) ∈ CapSp (subA E) m := by
    intro c
    rw [hpm]
    exact hmemw c
  have hd' : ∀ a c, subA E a a (qdet (subA E) (-p i) (yK E c v)) =
      (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) •
        qdet (subA E) (-p i) (yK E c v) := by
    intro a c
    have h := hdw a c
    simp only [Module.End.mul_apply] at h
    rw [h]
    congr 1
    linear_combination (hmp a).symm
  have hr' : ∀ a b c, a < b → subA E a b (qdet (subA E) (-p i) (yK E c v)) =
      if a = c then -(qdet (subA E) (-p i) (yK E b v)) else 0 := by
    intro a b c hab
    have h := hrw a b c hab
    simp only [Module.End.mul_apply] at h
    exact h
  refine ⟨hmem', hd', hr', ⟨t, ht, hsumw⟩, fun h0 => hv0 ?_⟩
  have hall := fam_zero (subA E) hsGl m hm i (fun c => qdet (subA E) (-p i) (yK E c v)) hmem' hd' hr' h0
  have hall' : ∀ c, qdet (subA E) (-p i) (yK E c v) = 0 := fun c => hall c
  have htv : t • v = 0 := by
    rw [← hsumw]
    simp [hall']
  exact (smul_eq_zero.mp htv).resolve_left ht

theorem core (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V')
    (l l' : Fin (n + 1) → ℂ) (hE : GlRel E) (hIrr : Irr E) (hcap : ∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v)
    (hE' : GlRel E') (hcap' : ∀ (w : ℂ) (v : V'), qdet E' w v = cpol l' w • v) (m p : Fin n → ℂ) (i : Fin n)
    (hm : SDec m) (hp : SDec p) (hpm : m = Function.update p i (p i - 1)) (hl : ∀ j, p i - 1 ≠ l j)
    (hl' : ∀ j, p i - 1 ≠ l' j) (hne : CapSp (subA E) p ≠ ⊥) (hne' : CapSp (subA E') p ≠ ⊥) (J : V' →ₗ[ℂ] V)
    (hJ : ∀ a b v, J (subA E' a b v) = subA E a b (J v)) (hJr : ∀ v, J v ∈ CapSp (subA E) m)
    (hinj : ∀ x ∈ CapSp (subA E') m, x ≠ 0 → J x ≠ 0) :
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧ (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) p := by
  obtain ⟨hsGl, -⟩ := Formalism.FourierDecayAlt.P.submodule_relations (Module.End ℂ V) n E hE
  obtain ⟨hsGl', -⟩ := Formalism.FourierDecayAlt.P.submodule_relations (Module.End ℂ V') n E' hE'
  have hpinj := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_inj hp
  obtain ⟨v', hv'S, hv'0, hv'HW⟩ := exists_highest_weight_in_capSp_of_ne_bot (subA E') hsGl' p hp hne'
  obtain ⟨v, hvS, hv0, hvHW⟩ := exists_highest_weight_in_capSp_of_ne_bot (subA E) hsGl p hp hne
  obtain ⟨hmem', hd', hr', -, hwi'⟩ := fam_props_lemma_2 n E' l' hE' hcap' m p i hm hp hpm hl' v' hv'S hv'0 hv'HW
  obtain ⟨hmem, hd, hr, ⟨t, ht, hsum⟩, hwi⟩ := fam_props_lemma_2 n E l hE hcap m p i hm hp hpm hl v hvS hv0 hvHW

  have hΨmem : ∀ c, J (qdet (subA E') (-p i) (yK E' c v')) ∈ CapSp (subA E) m := fun c => hJr _
  have hΨd : ∀ a c, subA E a a (J (qdet (subA E') (-p i) (yK E' c v'))) =
      (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) •
        J (qdet (subA E') (-p i) (yK E' c v')) := by
    intro a c
    rw [← hJ, hd' a c, map_smul]
  have hΨr : ∀ a b c, a < b → subA E a b (J (qdet (subA E') (-p i) (yK E' c v'))) =
      if a = c then -(J (qdet (subA E') (-p i) (yK E' b v'))) else 0 := by
    intro a b c hab
    rw [← hJ, hr' a b c hab]
    split_ifs <;> simp
  have hΨi : J (qdet (subA E') (-p i) (yK E' i v')) ≠ 0 := hinj _ (hmem' i) hwi'

  have hHWof : ∀ Φ : Fin n → V, (∀ c, Φ c ∈ CapSp (subA E) m) →
      (∀ a c, subA E a a (Φ c) =
        (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) • Φ c) →
      (∀ a b c, a < b → subA E a b (Φ c) = if a = c then -(Φ b) else 0) →
      IsHW (subA E) (fun a => m a + ((a : ℕ) : ℂ)) (Φ i) := by
    intro Φ h1 h2 h3
    have habove := capSp_family_eq_zero_above_index (subA E) hsGl m hm i Φ h1 h2 h3
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [h2 a i]
      congr 1
      split_ifs <;> ring
    · rw [h3 a b i hab]
      split_ifs with hai
      · subst hai
        rw [habove b hab, neg_zero]
      · rfl
  obtain ⟨κ, hκ⟩ := Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hE hIrr
    (hHWof (fun c => qdet (subA E) (-p i) (yK E c v)) hmem hd hr)
    (hHWof (fun c => J (qdet (subA E') (-p i) (yK E' c v'))) hΨmem hΨd hΨr) hwi

  have hdiff : ∀ c, J (qdet (subA E') (-p i) (yK E' c v')) = κ • qdet (subA E) (-p i) (yK E c v) := by
    have hz := fam_zero (subA E) hsGl m hm i
      (fun c => J (qdet (subA E') (-p i) (yK E' c v')) - κ • qdet (subA E) (-p i) (yK E c v))
      (fun c => Submodule.sub_mem _ (hΨmem c) (Submodule.smul_mem _ _ (hmem c)))
      (fun a c => by
        rw [map_sub, map_smul, hΨd a c, hd a c, smul_sub, smul_comm κ])
      (fun a b c hab => by
        rw [map_sub, map_smul, hΨr a b c hab, hr a b c hab]
        split_ifs <;> module)
      (by rw [hκ, sub_self])
    intro c
    exact sub_eq_zero.mp (hz c)
  have hcm : cpol m (-p i) ≠ 0 := by
    rw [hpm]
    exact cpol_down_self p hpinj i
  have hΨJ : ∀ c, J (qdet (subA E') (-p i) (yK E' c v')) = cpol m (-p i) • J (yK E' c v') := by
    intro c
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int J hJ (-p i) (yK E' c v'), (mem_CapSp.mp (hJr _)) (-p i)]
  have hs : ∑ c, etaK E c (J (yK E' c v')) = ((cpol m (-p i))⁻¹ * κ * t) • v := by
    calc ∑ c, etaK E c (J (yK E' c v'))
        = (cpol m (-p i))⁻¹ • ∑ c, etaK E c (J (qdet (subA E') (-p i) (yK E' c v'))) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hΨJ c, map_smul, smul_smul, inv_mul_cancel₀ hcm, one_smul]
      _ = ((cpol m (-p i))⁻¹ * κ * t) • v := by
          simp only [hdiff, map_smul]
          rw [← Finset.smul_sum, hsum, smul_smul, smul_smul]
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    apply hΨi
    rw [hκ, zero_smul]
  refine ⟨v', ?_, ?_⟩
  · rw [hs]
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcm) hκ0) ht) hv0
  · rw [hs]
    exact Submodule.smul_mem _ _ hvS

end core

private theorem ne_of_box_of_box_update_succ {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (hL : StrictAnti L) (i : Fin n)
    (h1 : Box L M) (h2 : Box L (Function.update M i (M i + 1))) (j : Fin (n + 1)) : M i ≠ L j := by
  have ha := (h1 i).1
  have hb := (h2 i).2
  rw [Function.update_self] at hb
  intro hj
  rcases le_or_gt j i.castSucc with hji | hji
  · have := hL.antitone hji
    omega
  · have := hL.antitone (Fin.castSucc_lt_iff_succ_le.mp hji)
    omega

theorem word_nonvanishing_algebraic : TWNeAlg := by
  intro V V' _ _ _ _ _ _ n E E' β β' L L' M M' i hE hE' hB hB' hBu hBu' hshf J hJ0 hJ hJr
  set p := shf β (Function.update M i (M i + 1)) with hpdef
  have hpm : shf β M = Function.update p i (p i - 1) := by
    funext j
    by_cases h : j = i
    · subst h
      simp only [hpdef, shf, Function.update_self]
      push_cast
      ring
    · simp only [hpdef, shf, Function.update_of_ne h]
  have hp' : p = shf β' (Function.update M' i (M' i + 1)) := by
    funext j
    have hj := congrFun hshf j
    simp only [shf] at hj
    by_cases h : j = i
    · subst h
      simp only [hpdef, shf, Function.update_self]
      push_cast
      linear_combination hj
    · simp only [hpdef, shf, Function.update_of_ne h]
      exact hj
  have hm : SDec (shf β M) := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shf β (strictAnti_of_box_of_strictAnti hE.anti hB)
  have hp : SDec p := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shf β (strictAnti_of_box_of_strictAnti hE.anti hBu)

  have hpi : p i - 1 = β + (M i : ℂ) := by
    simp only [hpdef, shf, Function.update_self]
    push_cast
    ring
  have hpi' : p i - 1 = β' + (M' i : ℂ) := by
    rw [hpi]
    simpa [shf] using congrFun hshf i
  have hl : ∀ j, p i - 1 ≠ shf β L j := by
    intro j h
    rw [hpi] at h
    simp only [shf, add_right_inj, Int.cast_inj] at h
    exact ne_of_box_of_box_update_succ hE.anti i hB hBu j h
  have hl' : ∀ j, p i - 1 ≠ shf β' L' j := by
    intro j h
    rw [hpi'] at h
    simp only [shf, add_right_inj, Int.cast_inj] at h
    exact ne_of_box_of_box_update_succ hE'.anti i hB' hBu' j h
  have hne : CapSp (subA E) p ≠ ⊥ := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hE).1 _ hBu
  have hne' : CapSp (subA E') p ≠ ⊥ := by
    rw [hp']
    exact (Formalism.FourierDecayAlt.P.branching_decomposition V' n E' β' L' hE').1 _ hBu'
  have hinj : ∀ x ∈ CapSp (subA E') (shf β M), x ≠ 0 → J x ≠ 0 := by
    intro x hx hx0
    refine j_inj n E E' β' L' M' hE' hB' J hJ0 hJ (fun w => ?_) x ?_ hx0
    · rw [← hshf]
      exact hJr w
    · rw [← hshf]
      exact hx
  exact core n E E' (shf β L) (shf β' L') hE.gl hE.irr hE.cap hE'.gl hE'.cap (shf β M) p i hm hp hpm hl hl'
    hne hne' J hJ hJr hinj

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
