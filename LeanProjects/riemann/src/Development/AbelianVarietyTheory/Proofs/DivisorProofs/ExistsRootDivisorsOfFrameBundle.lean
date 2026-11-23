import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagOverField
open GlobalTheory.Cartier
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG)

theorem app_π_eq_smul {X : Scheme.{0}} {G : X.Modules} {m : ℕ} {fl : Vert.Flag G m} {W : X.Opens}
    {v : Fin m → Γ(G, W)} (H : Spans fl W v) (i : Fin m) {T : Matrix (Fin m) (Fin m) Γ(X, W)}
    (hT : T.BlockTriangular id) {t t₀ : Γ(fl.F i.succ, W)} (ht : (fl.ι i.succ).app W t = v i)
    (ht₀ : (fl.ι i.succ).app W t₀ = ∑ k, T k i • v k) :
    (fl.π i).app W t₀ = T i i • (fl.π i).app W t := by
  obtain ⟨s, -, es⟩ := H i.castSucc
  have := (fl.isSubbundle i.succ).mono
  let w : Fin m → Γ(fl.F i.succ, W) := fun k => if h : (k : ℕ) < i then (fl.step i).app W (s ⟨k, h⟩) else t
  have hw (k : Fin m) : T k i • (fl.ι i.succ).app W (w k) = T k i • v k := by
    rcases lt_trichotomy k i with h | rfl | h
    · have h' : (k : ℕ) < i := h
      congr 1
      simp only [w, dif_pos h']
      refine Eq.trans ?_ (es ⟨k, h'⟩)
      rw [← fl.step_ι i]
      rfl
    · simp only [w, lt_irrefl, dif_neg, not_false_eq_true, ht]
    · rw [hT h, zero_smul, zero_smul]
  have e : t₀ = ∑ k, T k i • w k := by
    refine QCoh.injective_app_of_mono (fl.ι i.succ) W ?_
    rw [ht₀, map_sum]
    exact Finset.sum_congr rfl fun k _ => ((Scheme.Modules.Hom.app_smul _ _ _).trans (hw k)).symm
  rw [e, map_sum, Finset.sum_eq_single i]
  · rw [Scheme.Modules.Hom.app_smul]
    simp only [w, lt_irrefl, dif_neg, not_false_eq_true]
  · intro k _ hk
    rw [Scheme.Modules.Hom.app_smul]
    rcases lt_or_gt_of_ne hk with h | h
    · have h' : (k : ℕ) < i := h
      have z : (fl.π i).app W (w k) = 0 := by
        simp only [w, dif_pos h']
        have c : fl.step i ≫ fl.π i = 0 := Limits.cokernel.condition _
        change (fl.step i ≫ fl.π i).app W _ = 0
        rw [c]
        rfl
      rw [z, smul_zero]
    · rw [hT h, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem exists_chart_gr {X : Scheme.{0}} {G : X.Modules} {m : ℕ} {fl : Vert.Flag G m} {U : X.Opens}
    {v : Fin m → Γ(G, U)} (H : Spans fl U v) (i : Fin m) :
    ∃ t : Γ(fl.F i.succ, U), (fl.ι i.succ).app U t = v i ∧ IsFrame fun _ : Fin 1 => (fl.π i).app U t := by
  obtain ⟨s, t, -, h₂, h₃⟩ := H.exists_adaptedChart i
  refine ⟨t 0, (h₃ (Sum.inr 0)).trans (congrArg v (Fin.ext rfl)), ?_⟩
  convert h₂ using 3 with j
  exact congrArg t (Subsingleton.elim _ _)

theorem val_detUnit_of_eq_smul {X : Scheme.{0}} {G : X.Modules} {U U' V : X.Opens} {s : Γ(G, U)} {s' : Γ(G, U')}
    (hs : IsFrame fun _ : Fin 1 => s) (hs' : IsFrame fun _ : Fin 1 => s') (h : V ≤ U) (h' : V ≤ U') {a : Γ(X, V)}
    (e : resM G h' s' = a • resM G h s) : (hs.detUnit hs' h h' : Γ(X, V)) = a := by
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply, e,
    ← hs.basis_apply h default, map_smul, Module.Basis.repr_self]
  simp

theorem exists_graded : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ E' : Fr (ratOf Y) r r, (∀ y A', A' ∈ E'.S y ↔ AdFrame e fl y A') → ∃ gr : GlobalTheory.GoodMetric.Root r → Y.Dv, (∀ x, GlobalTheory.Cartier.toPic (gr x) = GlobalTheory.CechPic.cls ((fl x.1).root x.2) ((fl x.1).isLB_root x.2)) ∧ GlobalTheory.GoodMetric.IsGraded E' gr := by
  intro F _ Y ι _ r E e fl hE he E' hE'
  obtain ⟨B, hB⟩ := E'.nonempty (genericPoint Y.X)
  choose U₀ h₀ M₀ hM₀ hB₀ using (hE' _ _).1 hB
  choose t₀ ht₀ hf₀ using fun x : GlobalTheory.GoodMetric.Root r => exists_chart_gr (hM₀ x.1) x.2
  let c₀ (x : GlobalTheory.GoodMetric.Root r) : ((fl x.1).root x.2).ι := (⟨U₀ x.1, _, hf₀ x⟩ : Chart ((fl x.1).gr x.2) 1)
  have P (x : GlobalTheory.GoodMetric.Root r) := presents_ofLB ((fl x.1).isLB_root x.2) (c₀ x) (h₀ x.1)
  refine ⟨_, fun x => (P x).toPic_eq, B, hB, fun y x => ?_⟩
  obtain ⟨a, i⟩ := x
  obtain ⟨A, hA⟩ := E'.nonempty y
  obtain ⟨U, hy, M, hM, hAM⟩ := (hE' _ _).1 hA a
  obtain ⟨t, ht, hf⟩ := exists_chart_gr hM i
  let c : ((fl a).root i).ι := (⟨U, _, hf⟩ : Chart ((fl a).gr i) 1)
  refine ⟨A, hA, _, ?_, (P ⟨a, i⟩).isEqn c y hy⟩
  have := (hE a).isQuasicoherent
  have h₁ : U ⊓ U₀ a ≤ U := inf_le_left
  have h₂ : U ⊓ U₀ a ≤ U₀ a := inf_le_right
  have hN := spans_pullCol_res Y.str (e a) le_top h₁ hM
  have hN₀ := spans_pullCol_res Y.str (e a) le_top h₂ (hM₀ a)
  obtain ⟨T, hT, -, hMT⟩ := exists_upper_of_spans Y.str (he a) _ hN hN₀
  have hg : genericPoint Y.X ∈ U ⊓ U₀ a := memInf (gen_mem hy) (h₀ a)
  have hd : (hf.detUnit (hf₀ ⟨a, i⟩) h₁ h₂ : Γ(Y.X, U ⊓ U₀ a)) = T i i := by
    refine val_detUnit_of_eq_smul _ _ _ _ ?_
    rw [← app_resM, ← app_resM]
    refine app_π_eq_smul hN i hT ?_ ?_
    · rw [app_resM, ht]
      exact res_pullCol Y.str (e a) le_top h₁ M i
    · rw [app_resM, ht₀ ⟨a, i⟩]
      refine (res_pullCol Y.str (e a) le_top h₂ (M₀ a) i).trans (Eq.trans ?_ (sum_smul_pullCol Y.str (e a) le_top _ T i).symm)
      rw [hMT]
  have hv : (frameRat ((fl a).root i) (c₀ ⟨a, i⟩) (h₀ a) c : Y.X.functionField) = fnOf _ hg (T i i) :=
    (val_frameRat (L := (fl a).root i) (c₀ ⟨a, i⟩) (h₀ a) c (gen_mem hy)).trans (congrArg (fnOf _ hg) hd)
  refine Eq.trans ?_ hv.symm
  have hA' : A a = ((M.map (resG Y.X h₁)).map (fnOf _ hg)).transpose := by
    rw [hAM]
    ext j l
    exact (fnOf_resG h₁ hg _).symm
  have hB' : B a = (T.map (fnOf _ hg)).transpose * A a := by
    rw [hA', ← Matrix.transpose_mul, ← Matrix.map_mul, ← hMT, hB₀]
    ext j l
    exact (fnOf_resG h₂ hg _).symm
  have hu : IsUnit (A a).det := by
    rw [hA', Matrix.det_transpose]
    have hu := (isUnit_det_of_spans Y.str (he a) _ hN).map (fnOf _ hg)
    rwa [RingHom.map_det] at hu
  change (B a * (A a)⁻¹) i i = _
  rw [hB', Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end GlobalTheory.FlagOverField
