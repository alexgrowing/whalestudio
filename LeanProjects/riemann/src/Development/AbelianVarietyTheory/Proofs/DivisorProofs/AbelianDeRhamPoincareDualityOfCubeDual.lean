import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimensionStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeDual

theorem lam_mul_left (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a a' t : T ⟶ A) :
    lam (cls L hL) (a * a') t = lam (cls L hL) a t + lam (cls L hL) a' t := by
  have h := hC S A hA L hL T a a' t
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![a * a' * t, a * a', a * t, a' * t, a, a', t, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  unfold lam
  rw [← sub_eq_zero, ← e]
  abel

theorem evc_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem isAdditive_lam (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) : IsAdditive (abelian₂ A L) ∧ IsAdditive (swap (abelian₂ A L)) := by
  haveI := hA.comm
  have hs : (swap (abelian₂ A L)).IsLB := pull_isLB hP _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_iff hs).2 fun Y a a' t ↦ ?_⟩
  · rw [evc_lam hL, evc_lam hL, evc_lam hL]
    exact lam_mul_left hC hA hL a a' t
  · rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_lam hL, evc_lam hL, evc_lam hL, lam_comm, lam_comm _ t a,
      lam_comm _ t a']
    exact lam_mul_left hC hA hL a a' t

theorem mono_of_isPerfect' {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) [IsMonHom x] : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem abelianDeRham_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  intro hC hD hPD hF R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨haddL, haddS⟩ := isAdditive_lam hC hA hL hP
  obtain ⟨B, _, P, hB, hdim, h1, h2⟩ := hD (Sp R) A hA
  have hgB := hdim g hg
  obtain ⟨x, hx, -⟩ := h1.univ A (abelian₂ A L) hP haddL
  haveI hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying (Sp R) A A B (abelian₂ A L) P h1 h2.additive hP haddS x hx
  have perf := h1.isPerfect h2
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hgB))
    perf.isLB perf.zero_left perf.zero_right
  have e : LBIso (P.pull (lift (fst A A) (snd A A ≫ x)).left) (abelian₂ A L) :=
    (cls_eq_iff (pull_isLB h1.isLB _) hP).1 ((cls_eq_iff hP (pull_isLB h1.isLB _)).2 hx).symm
  obtain ⟨φ', hφ', k⟩ := hφ.pull h1.isLB (homMor (dp0 R) (𝟙 _) (𝟙 A)) (homMor (dp0 R) (𝟙 _) x)
    (h := (lift (fst A A) (snd A A ≫ x)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd])
    hP e
  have hψ' := isCorrForm_lam hψ
  obtain rfl := hφ'.unique (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP hψ'
  have hform : ∀ a b, φ' a b = φ a (push (dp0 R) (𝟙 _) x b) := fun a b ↦ by
    have := k (push (dp0 R) (𝟙 _) (𝟙 A) a) a (push (dp0 R) (𝟙 _) x b) b (fun _ ↦ rfl) fun _ ↦ rfl
    rw [this, push_id]
    rfl
  obtain ⟨-, orth⟩ := hPD R A B g hA hB hg hgB P h1 φ hφ
  refine ⟨fun a ha b hb ↦ ?_, fun hK ↦ ?_⟩
  · rw [hform]
    exact orth a ha _ (push_mem_Fil x hb)
  · have mx : Mono x := mono_of_isPerfect' h1 (isPerfect_lam hL hK) x hx
    have ix : IsIso x := GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension (Sp R) A B hA hB g hg hgB x hmx mx
    have hd : IsDual A A (abelian₂ A L) := GlobalTheory.AbDual.transport (Sp R) A A B (abelian₂ A L) P h1 hP x ix hmx hx
    exact (hPD R A A g hA hA hg hg (abelian₂ A L) hd φ' hψ').1

end GlobalTheory.CubeDual
