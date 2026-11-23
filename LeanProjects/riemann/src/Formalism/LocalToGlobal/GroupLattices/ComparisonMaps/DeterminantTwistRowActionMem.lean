import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem dw_eq {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) = deltaLTw O Kf m lam g := by
  unfold Dl0
  rw [if_pos hlam]
  exact le_antisymm (iInf₂_le g ⟨hg, rfl⟩) (le_iInf₂ fun h hh => dl_indep hinj m lam g h hg hh.2)

theorem dw_tw {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ deltaLTw O Kf m lam h) :
    (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf g⁻¹ F ∈ deltaLTw O Kf m lam (g * h) := by
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨f, hf, hfe⟩ := hF0
  have hfe' : map (algebraMap O Kf) f = rowAct Kf h F0 := hfe
  refine ⟨rowAct Kf g⁻¹ F0, ?_, ?_⟩
  · refine ⟨f, hf, ?_⟩
    change map (algebraMap O Kf) f = rowAct Kf (g * h) (rowAct Kf g⁻¹ F0)
    have e1 : rowAct Kf (g * h) (rowAct Kf g⁻¹ F0) = rowAct Kf h F0 := by
      have h1 := rowActMul Kf (m + 1) (m + 1) (g * h) g⁻¹
      have h2 : g⁻¹ * (g * h) = h := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]
      rw [h2] at h1
      exact congrArg (fun f => f F0) h1
    rw [e1]
    exact hfe'
  · show (g * h).det ^ (-(lam (Fin.last m))) • rowAct Kf g⁻¹ F0 =
      g.det ^ (-(lam (Fin.last m))) • rowAct Kf g⁻¹ (h.det ^ (-(lam (Fin.last m))) • F0)
    rw [map_smul, smul_smul, Matrix.det_mul, mul_zpow]

theorem determinant_twist_row_action_mem {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (hg : IsUnit g.det) (hh : IsUnit h.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ Dl0 O m lam (colSpan O h)) :
    (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf g⁻¹ F ∈ Dl0 O m lam (colSpan O (g * h)) := by
  rw [dw_eq hinj m lam hlam h hh] at hF
  rw [dw_eq hinj m lam hlam (g * h) (by rw [Matrix.det_mul]; exact hg.mul hh)]
  exact dw_tw (O := O) m lam g h hg F hF

theorem dw_HtenW {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : ∀ s, Antitone (lamAt lam0 s))
    (g h : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : ∀ s, IsUnit (g s).det)
    (hh : ∀ s, IsUnit (h s).det) (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hz : z ∈ HtenW O lam0 (fun s => colSpan O (h s))) :
    je_rho Kf lam0 g z ∈ HtenW O lam0 (fun s => colSpan O (g s * h s)) := by
  unfold HtenW tensorLat at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => ((g s).det ^ (-(lamAt lam0 s (Fin.last m)))) • rowAct Kf (g s)⁻¹ (F s),
      fun s => determinant_twist_row_action_mem hinj m _ (hdom s) (g s) (h s) (hg s) (hh s) (F s) (hF s), ?_⟩
    unfold je_rho
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    simp only [(blockActTensor Kf Kf (Fin n') (m + 1) (m + 1) (fun s => (g s)⁻¹)).1, map_smul]
    exact je_prod_smul _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

theorem dw_HtenW' {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : ∀ s, Antitone (lamAt lam0 s))
    (g : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : ∀ s, IsUnit (g s).det)
    (Λ Λ' : Fin n' → Submodule O (Fin (m + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s))
    (hΛ' : ∀ s, Λ' s = (Λ s).map ((Matrix.mulVecLin (g s)).restrictScalars O))
    (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hz : z ∈ HtenW O lam0 Λ) :
    je_rho Kf lam0 g z ∈ HtenW O lam0 Λ' := by
  choose h hh hΛh using hΛ
  have e1 : Λ = fun s => colSpan O (h s) := funext hΛh
  have e2 : Λ' = fun s => colSpan O (g s * h s) := by
    funext s
    rw [hΛ' s, hΛh s, je_colSpan_mul]
  rw [e2]
  rw [e1] at hz
  exact dw_HtenW hinj lam0 hdom g h hg hh z hz

variable {p : ℕ}

theorem dw_ext (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (Lv : Lat G v)
    (hLv : IsLattice (G.P.W v) Lv) (z : Pol G v)
    (hz : z ∈ HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv) :
    je_loc G v A z ∈ HtenW G.O (G.P.lam0 v) fun s =>
      extO G.O (G.P.ι v) (G.P.σ v) s.val (Lv.map (nt_phi (G.P.W v) A)) :=
  dw_HtenW' (lb_inj G v) (G.P.lam0 v) (je_dom G v) (je_g G v A) (je_g_det G v A) _ _
    (fun s => je_extO_lat G v s.val Lv hLv) (fun s => je_extO G v A s Lv) z hz

theorem equivSys_HtupW (G : GAtP p) : EquivSys G G.P.HtupW := by
  intro i γ L hL ξ hξ
  unfold Places.HtupW Places.tenV at hξ ⊢
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨fun v => je_loc G v ((G.lev i).act v γ) (F v),
      fun v => dw_ext G v _ (L v) (hL v) (F v) (hF v), je_natAct_prod G _ F⟩
  | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower, smul_comm]; exact Submodule.smul_mem _ a hx

end Formalism.L2.G.Cmp
