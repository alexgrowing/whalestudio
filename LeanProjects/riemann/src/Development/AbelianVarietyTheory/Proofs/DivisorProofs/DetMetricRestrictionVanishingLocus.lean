import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

variable {X Z : Scheme.{0}}

theorem resM_det_g {F : X.Modules} (c c' : Chart F 1) :
    resM F (inf_le_right : c.U ⊓ c'.U ≤ c'.U) (c'.e 0) =
      Units.val (α := Γ(X, c.U ⊓ c'.U)) ((det F 1).g c c') • resM F (inf_le_left : c.U ⊓ c'.U ≤ c.U) (c.e 0) := by
  have e : Units.val (α := Γ(X, c.U ⊓ c'.U)) ((det F 1).g c c') = (c.isFrame.basis inf_le_left).det fun i => resM F inf_le_right (c'.e i) :=
    c.isFrame.val_detUnit c'.isFrame inf_le_left inf_le_right
  rw [e, Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]
  have := (c.isFrame.basis (inf_le_left : c.U ⊓ c'.U ≤ c.U)).sum_repr (resM F inf_le_right (c'.e 0))
  rw [Fintype.sum_unique, IsFrame.basis_apply] at this
  exact this.symm

theorem exists_unimodular {L' V : X.Modules} {l' : L' ⟶ V} (hL' : IsVB L' 1) (hl' : IsSubbundle l')
    {U : X.Opens} {t' : Γ(L', U)} (ht : IsFrame fun _ : Fin 1 => t') {f₁ f₂ : Γ(V, U)} {α β : Γ(X, U)}
    (e : l'.app U t' = α • f₁ + β • f₂) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ a b : Γ(X, W), resG X h α * a + resG X h β * b = 1 := by
  obtain ⟨_, s, hs⟩ := hl'
  have hS : (ShortComplex.mk l' _ (Limits.cokernel.condition l')).ShortExact :=
    { exact := ShortComplex.exact_cokernel l' }
  obtain ⟨c, hc⟩ := VBExt.exists_adaptedChart hS hL' hs x
  have hWc : U ⊓ c.U ≤ c.U := inf_le_right
  have hWU : U ⊓ c.U ≤ U := inf_le_left
  let B := (VBExt.isFrame_sumElim hS c.he c.ht).basis hWc
  let ψ := B.coord (.inl 0)
  have h1 : ψ (resM V hWc (l'.app c.U (c.e 0))) = 1 := by
    have : B (.inl 0) = resM V hWc (l'.app c.U (c.e 0)) := by
      simp only [B, IsFrame.basis_apply, Sum.elim_inl]
    rw [← this]
    simp [ψ]
  let v := (ht.basis hWU).repr (resM L' hWc (c.e 0)) 0
  have h2 : resM L' hWc (c.e 0) = v • resM L' hWU t' := by
    have := (ht.basis hWU).sum_repr (resM L' hWc (c.e 0))
    rw [Fintype.sum_unique, IsFrame.basis_apply] at this
    exact this.symm
  have h3 : resM V hWc (l'.app c.U (c.e 0)) =
      v • (resG X hWU α • resM V hWU f₁ + resG X hWU β • resM V hWU f₂) := by
    rw [← app_resM, h2, Scheme.Modules.Hom.app_smul, app_resM, e, map_add, resM_smul, resM_smul]
  refine ⟨_, hWU, ⟨hx, hc⟩, v * ψ (resM V hWU f₁), v * ψ (resM V hWU f₂), ?_⟩
  rw [h3, map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
  rw [← h1]
  ring

theorem app_eq_zero_of_vanishesAt [IsIntegral Z] {F Q : X.Modules} {s : F ⟶ Q} (i : Z ⟶ X)
    (hv : VanishesAt s (i (genericPoint Z))) {U : X.Opens} {t : Γ(F, U)} {e : Γ(Q, U)} {b : Γ(X, U)}
    (he : IsFrame fun _ : Fin 1 => e) (hs : s.app U t = b • e) : i.app U b = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hg : genericPoint Z ∈ Z.basicOpen (i.app U b) := by
    refine ((genericPoint_spec Z).mem_open_set_iff (Z.basicOpen _).isOpen).2 ?_
    obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).1 hne
    exact ⟨z, trivial, hz⟩
  rw [← Scheme.preimage_basicOpen] at hg
  exact hv U t e b (X.basicOpen_le _ hg) he hs hg

theorem app_resG (i : Z ⟶ X) {U T : X.Opens} (h : T ≤ U) (a : Γ(X, U)) :
    i.app T (resG X h a) = resG Z (fun _ hz => h hz : i ⁻¹ᵁ T ≤ i ⁻¹ᵁ U) (i.app U a) := by
  exact congr($(i.naturality (homOfLE h).op) a)

theorem isUnit_app (i : Z ⟶ X) {U : X.Opens} {α β : Γ(X, U)} (hβ : i.app U β = 0)
    (H : ∀ x ∈ U, ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ a b : Γ(X, W),
      resG X h α * a + resG X h β * b = 1) : IsUnit (i.app U α) := by
  refine RingedSpace.isUnit_of_isUnit_germ Z.toRingedSpace _ _ fun z hz => ?_
  refine (Z.mem_basicOpen _ z hz).1 ?_
  rw [← Scheme.preimage_basicOpen]
  obtain ⟨W, h, hW, a, b, e⟩ := H (i z) hz
  have hb : i z ∉ X.basicOpen β := fun hm => by
    have : z ∈ i ⁻¹ᵁ X.basicOpen β := hm
    rw [Scheme.preimage_basicOpen, hβ, Scheme.basicOpen_zero] at this
    exact this
  have hu : IsUnit (X.presheaf.germ W (i z) hW (resG X h α * a + resG X h β * b)) := by
    rw [e, map_one]; exact isUnit_one
  rw [map_add, map_mul, map_mul] at hu
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h₁ | h₁
  · have h₂ := isUnit_of_mul_isUnit_left h₁
    refine (X.mem_basicOpen _ _ hz).2 ?_
    simpa only [resG, TopCat.Presheaf.germ_res_apply] using h₂
  · have h₂ := isUnit_of_mul_isUnit_left h₁
    exact absurd ((X.mem_basicOpen _ _ hz).2 (by simpa only [resG, TopCat.Presheaf.germ_res_apply] using h₂)) hb

section Main

variable {V L Q L' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V}

theorem isFrame_res_one {F : X.Modules} {U T : X.Opens} {e : Fin 1 → Γ(F, U)} (he : IsFrame e) (h : T ≤ U) :
    IsFrame fun _ : Fin 1 => resM F h (e 0) := by
  have : (fun i => resM F h (e i)) = fun _ : Fin 1 => resM F h (e 0) :=
    funext fun i => by rw [Subsingleton.elim i 0]
  exact this ▸ he.res h

theorem exists_unit [IsIntegral Z] (hS : (ShortComplex.mk l m w).ShortExact) (hL' : IsVB L' 1)
    (hl' : IsSubbundle l') (i : Z ⟶ X) (hv : VanishesAt (l' ≫ m) (i (genericPoint Z)))
    (a : VBExt.AdaptedChart (ShortComplex.mk l m w) 1 1) (c : Chart L' 1) :
    ∃ (u : (Γ(Z, i ⁻¹ᵁ (a.U ⊓ c.U)))ˣ) (α β : Γ(X, a.U ⊓ c.U)),
      u.val = i.app _ α ∧ i.app _ β = 0 ∧
      l'.app _ (resM L' inf_le_right (c.e 0)) =
        α • resM V inf_le_left (l.app a.U (a.e 0)) + β • resM V inf_le_left (a.t 0) := by
  have hU : a.U ⊓ c.U ≤ a.U := inf_le_left
  have hc : a.U ⊓ c.U ≤ c.U := inf_le_right
  let B := (VBExt.isFrame_sumElim hS a.he a.ht).basis hU
  have e : l'.app _ (resM L' hc (c.e 0)) =
      B.repr (l'.app _ (resM L' hc (c.e 0))) (.inl 0) • resM V hU (l.app a.U (a.e 0)) +
      B.repr (l'.app _ (resM L' hc (c.e 0))) (.inr 0) • resM V hU (a.t 0) := by
    have := B.sum_repr (l'.app _ (resM L' hc (c.e 0)))
    rw [Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique] at this
    simp only [B, IsFrame.basis_apply, Sum.elim_inl, Sum.elim_inr] at this
    exact this.symm
  generalize B.repr (l'.app _ (resM L' hc (c.e 0))) (.inl 0) = α at e
  generalize B.repr (l'.app _ (resM L' hc (c.e 0))) (.inr 0) = β at e
  have hlm (x : Γ(L, a.U)) : m.app a.U (l.app a.U x) = 0 := congr(($w).app a.U x)
  have hβ : i.app _ β = 0 := by
    refine app_eq_zero_of_vanishesAt i hv (t := resM L' hc (c.e 0))
      (e := m.app _ (resM V hU (a.t 0))) ?_ ?_
    · have := isFrame_res_one (e := fun k => m.app a.U (a.t k)) a.ht hU
      simpa only [app_resM] using this
    · change m.app _ (l'.app _ _) = _
      rw [e, map_add, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_resM, hlm, map_zero,
        smul_zero, zero_add]
  obtain ⟨u, hu⟩ := isUnit_app i hβ fun x hx =>
    exists_unimodular hL' hl' (isFrame_res_one c.isFrame hc) e hx
  exact ⟨u, α, β, hu, hβ, e⟩

theorem unit_cocycle (hS : (ShortComplex.mk l m w).ShortExact) (i : Z ⟶ X)
    {a a₂ : VBExt.AdaptedChart (ShortComplex.mk l m w) 1 1} {c c₂ : Chart L' 1}
    {u : (Γ(Z, i ⁻¹ᵁ (a.U ⊓ c.U)))ˣ} {u₂ : (Γ(Z, i ⁻¹ᵁ (a₂.U ⊓ c₂.U)))ˣ}
    {α β : Γ(X, a.U ⊓ c.U)} {α₂ β₂ : Γ(X, a₂.U ⊓ c₂.U)}
    (hu : u.val = i.app _ α) (hu₂ : u₂.val = i.app _ α₂) (hβ₂ : i.app _ β₂ = 0)
    (e : l'.app _ (resM L' inf_le_right (c.e 0)) =
      α • resM V inf_le_left (l.app a.U (a.e 0)) + β • resM V inf_le_left (a.t 0))
    (e₂ : l'.app _ (resM L' inf_le_right (c₂.e 0)) =
      α₂ • resM V inf_le_left (l.app a₂.U (a₂.e 0)) + β₂ • resM V inf_le_left (a₂.t 0))
    (z : Z) (hz : i z ∈ a.U ⊓ c.U) (hz₂ : i z ∈ a₂.U ⊓ c₂.U) :
    gm (𝟙 Z) z _ u = gm (𝟙 Z ≫ i) z _ ((det L 1).g a.sub a₂.sub) *
      (gm (𝟙 Z ≫ i) z _ ((det L' 1).g c c₂))⁻¹ * gm (𝟙 Z) z _ u₂ := by
  have h₁ : (a.U ⊓ c.U) ⊓ (a₂.U ⊓ c₂.U) ≤ a.U ⊓ c.U := inf_le_left
  have h₂ : (a.U ⊓ c.U) ⊓ (a₂.U ⊓ c₂.U) ≤ a₂.U ⊓ c₂.U := inf_le_right
  generalize hT : (a.U ⊓ c.U) ⊓ (a₂.U ⊓ c₂.U) = T at h₁ h₂
  have hzT : i z ∈ T := hT ▸ ⟨hz, hz₂⟩
  have hf : T ≤ a.U ⊓ a₂.U := le_inf (h₁.trans inf_le_left) (h₂.trans inf_le_left)
  have hg : T ≤ c.U ⊓ c₂.U := le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)
  have hTa : T ≤ a.U := h₁.trans inf_le_left
  have hTa₂ : T ≤ a₂.U := h₂.trans inf_le_left
  have hTc : T ≤ c.U := h₁.trans inf_le_right
  have hTc₂ : T ≤ c₂.U := h₂.trans inf_le_right
  let f : (Γ(X, T))ˣ := res hf ((det L 1).g a.sub a₂.sub)
  let g : (Γ(X, T))ˣ := res hg ((det L' 1).g c c₂)
  let B := (VBExt.isFrame_sumElim hS a.he a.ht).basis hTa
  let ψ := B.coord (.inl 0)
  have hA : ψ (resM V hTa (l.app a.U (a.e 0))) = 1 := by
    have : B (.inl 0) = resM V hTa (l.app a.U (a.e 0)) := by
      simp only [B, IsFrame.basis_apply, Sum.elim_inl]
    rw [← this]
    simp [ψ]
  have hB : ψ (resM V hTa (a.t 0)) = 0 := by
    have : B (.inr 0) = resM V hTa (a.t 0) := by
      simp only [B, IsFrame.basis_apply, Sum.elim_inr]
    rw [← this]
    simp [ψ]
  have hv : l'.app T (resM L' hTc (c.e 0)) = resG X h₁ α • resM V hTa (l.app a.U (a.e 0)) +
      resG X h₁ β • resM V hTa (a.t 0) := by
    have := congrArg (resM V h₁) e
    simpa only [app_resM, resM_resM, map_add, resM_smul] using this
  have hv₂ : l'.app T (resM L' hTc₂ (c₂.e 0)) = resG X h₂ α₂ • resM V hTa₂ (l.app a₂.U (a₂.e 0)) +
      resG X h₂ β₂ • resM V hTa₂ (a₂.t 0) := by
    have := congrArg (resM V h₂) e₂
    simpa only [app_resM, resM_resM, map_add, resM_smul] using this
  have hgv : resM L' hTc₂ (c₂.e 0) = g.val • resM L' hTc (c.e 0) := by
    have := congrArg (resM L' hg) (resM_det_g c c₂)
    rw [resM_resM, resM_smul, resM_resM] at this
    exact this
  have hfv : resM L hTa₂ (a₂.e 0) = f.val • resM L hTa (a.e 0) := by
    have e₆ : resM L (inf_le_right : a.U ⊓ a₂.U ≤ a₂.U) (a₂.e 0) =
        Units.val (α := Γ(X, a.U ⊓ a₂.U)) ((det L 1).g a.sub a₂.sub) •
          resM L (inf_le_left : a.U ⊓ a₂.U ≤ a.U) (a.e 0) := resM_det_g (F := L) a.sub a₂.sub
    have := congrArg (resM L hf) e₆
    rw [resM_resM, resM_smul, resM_resM] at this
    exact this
  have key₀ : g.val * resG X h₁ α = resG X h₂ α₂ * f.val + resG X h₂ β₂ * ψ (resM V hTa₂ (a₂.t 0)) := by
    have e₃ : g.val • l'.app T (resM L' hTc (c.e 0)) = l'.app T (resM L' hTc₂ (c₂.e 0)) := by
      rw [hgv, Scheme.Modules.Hom.app_smul]
    have e₄ : resM V hTa₂ (l.app a₂.U (a₂.e 0)) = f.val • resM V hTa (l.app a.U (a.e 0)) := by
      rw [← app_resM, hfv, Scheme.Modules.Hom.app_smul, app_resM]
    rw [hv₂, e₄, hv] at e₃
    have := congrArg ψ e₃
    simp only [map_add, map_smul, hA, hB, smul_eq_mul, mul_zero, add_zero, mul_one] at this
    exact this
  have hZ₁ : i ⁻¹ᵁ T ≤ i ⁻¹ᵁ (a.U ⊓ c.U) := fun _ hz => h₁ hz
  have hZ₂ : i ⁻¹ᵁ T ≤ i ⁻¹ᵁ (a₂.U ⊓ c₂.U) := fun _ hz => h₂ hz
  have E₀ : pullU i T g * res hZ₁ u = res hZ₂ u₂ * pullU i T f := by
    refine Units.ext ?_
    have := congrArg (i.app T) key₀
    simp only [map_add, map_mul, app_resG, hβ₂, map_zero, zero_mul, add_zero, ← hu, ← hu₂] at this
    exact this
  have E : res hZ₁ u = pullU i T f * (pullU i T g)⁻¹ * res hZ₂ u₂ := by
    have e₅ : res hZ₁ u = (pullU i T g)⁻¹ * (res hZ₂ u₂ * pullU i T f) := by rw [← E₀, inv_mul_cancel_left]
    rw [e₅]
    ac_rfl
  have A := gm_res (𝟙 Z) z hZ₁ hzT u
  have A₂ := gm_res (𝟙 Z) z hZ₂ hzT u₂
  have F := (gm_res (𝟙 Z ≫ i) z hf hzT ((det L 1).g a.sub a₂.sub)).symm.trans (gm_pull (𝟙 Z) i z T hzT f).symm
  have G := (gm_res (𝟙 Z ≫ i) z hg hzT ((det L' 1).g c c₂)).symm.trans (gm_pull (𝟙 Z) i z T hzT g).symm
  rw [← A, ← A₂, E, map_mul, map_mul, map_inv, ← F, ← G]
  rfl

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem detWeight_restrict {r : ℕ} (h : Met p σ V r) (hl : IsSubbundle l) (hL : IsVB L 1) (c : Chart L 1)
    (x : CxPts p σ) : (h.restrict hl hL).detWeight.φ c x =
      -Real.log (h.form (l.app c.U (c.e 0)) (l.app c.U (c.e 0)) x).re := by
  change -Real.log (h.gram (fun a => l.app c.U (c.e a)) x).det.re = _
  rw [Matrix.det_unique]
  rfl

theorem form_re_pos {r : ℕ} (h : Met p σ V r) (hl : IsSubbundle l) (hL : IsVB L 1) (c : Chart L 1)
    {x : CxPts p σ} (hx : x ∈ ptsIn p σ c.U) : 0 < (h.form (l.app c.U (c.e 0)) (l.app c.U (c.e 0)) x).re := by
  have := det_re_pos ((h.restrict hl hL).posDef c x hx)
  change 0 < (h.gram (fun a => l.app c.U (c.e a)) x).det.re at this
  rw [Matrix.det_unique] at this
  exact this

theorem form_of_coef {r : ℕ} (h : Met p σ V r) {U : X.Opens} {x : CxPts p σ} {α β : Γ(X, U)} {A B v : Γ(V, U)}
    (e : v = α • A + β • B) (hβ : ev p σ U β x = 0) :
    h.form v v x = ((‖ev p σ U α x‖ ^ 2 : ℝ) : ℂ) * h.form A A x := by
  have e₁ : h.form v A x = ev p σ U α x * h.form A A x := by
    rw [e, h.form_add_left, h.form_smul_left, h.form_smul_left, hβ, zero_mul, add_zero]
  have e₂ : h.form A v x = starRingEnd ℂ (ev p σ U α x) * h.form A A x := by
    rw [← h.conj_form, e₁, map_mul, h.conj_form]
  calc h.form v v x = h.form (α • A + β • B) v x := by rw [← e]
    _ = ev p σ U α x * h.form A v x + ev p σ U β x * h.form B v x := by
      rw [h.form_add_left, h.form_smul_left, h.form_smul_left]
    _ = _ := by
      rw [hβ, zero_mul, add_zero, e₂, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Main

theorem isometric_restr_of_vanishesAt :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (V L Q L' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q)
      (w : l ≫ m = 0) (l' : L' ⟶ V), (ShortComplex.mk l m w).ShortExact → IsVB Q 1 →
      ∀ (hL : IsVB L 1) (hL' : IsVB L' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')
        (h : VMetric p V (1 + 1)) (H : h.IsCInf) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X),
        VanishesAt (l' ≫ m) (i (genericPoint Z)) →
          ((VMetric.det (H.restrict hl hL)).restr i).Isometric
            ((VMetric.det (H.restrict hl' hL')).restr i) := by
  intro k _ X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z _ i hv
  refine HermLB.Isometric.symm ?_
  choose u α β hu hβ e using
    fun j : VBExt.AdaptedChart (ShortComplex.mk l m w) 1 1 × Chart L' 1 => exists_unit hS hL' hl' i hv j.1 j.2
  refine HermLB.isometric_of_local
    (J := VBExt.AdaptedChart (ShortComplex.mk l m w) 1 1 × Chart L' 1) (fun j => i ⁻¹ᵁ (j.1.U ⊓ j.2.U)) (fun z => ?_) (fun j _ => j.1.sub)
    (fun j _ => j.2) (fun j _ hz => mem_pull.2 hz.1) (fun j _ hz => mem_pull.2 hz.2) u
    (fun z j j' hz hz' => ?_) fun σ j y hy => ?_
  · obtain ⟨a, ha⟩ := VBExt.exists_adaptedChart hS hL hQ (i z)
    obtain ⟨U, t, hz, ht⟩ := hL' (i z)
    exact ⟨(a, ⟨U, t, ht⟩), ha, hz⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g (det L 1) i (𝟙 Z) z (fun _ => j.1.sub) (fun _ => j'.1.sub)
        (mem_pull.2 hz.1) (mem_pull.2 hz'.1))
      (gm_pull_g (det L' 1) i (𝟙 Z) z (fun _ => j.2) (fun _ => j'.2)
        (mem_pull.2 hz.2) (mem_pull.2 hz'.2)))).symm
    exact unit_cocycle hS i (hu j) (hu j') (hβ j') (e j) (e j') z hz hz'
  · have hx : Points.PtsOver.map i rfl _ y ∈ ptsIn p σ (j.1.U ⊓ j.2.U) := hy
    have hx₁ := (mem_ptsIn_inf.1 hx).1
    have hx₂ := (mem_ptsIn_inf.1 hx).2
    have hb : ev p σ _ (β j) (Points.PtsOver.map i rfl _ y) = 0 := by
      rw [← ev_app i rfl, hβ, ev_eq hy, map_zero]
    have ha : ev (i ≫ p) σ _ (u j).val y = ev p σ _ (α j) (Points.PtsOver.map i rfl _ y) := by
      rw [hu, ev_app i rfl]
    have hα := ev_ne_zero hy (u j).isUnit
    have hf := form_of_coef (h.met σ) (e j) hb
    rw [app_resM, (h.met σ).form_resM _ _ _ hx, (h.met σ).form_resM _ _ _ hx, ← ha] at hf
    have hp := form_re_pos (h.met σ) hl hL j.1.sub hx₁
    have E₁ := (Weight.pull_φ ((h.met σ).restrict hl hL).detWeight i rfl (fun _ => j.1.sub) y).trans
      (detWeight_restrict (h.met σ) hl hL j.1.sub _)
    have E₂ := (Weight.pull_φ ((h.met σ).restrict hl' hL').detWeight i rfl (fun _ => j.2) y).trans
      (detWeight_restrict (h.met σ) hl' hL' j.2 _)
    refine E₁.trans (Eq.trans ?_ (congrArg (· + _) E₂).symm)
    rw [hf, Complex.re_ofReal_mul, Real.log_mul (by positivity) (by exact hp.ne'), logSq]
    exact (show ∀ a b : ℝ, -b = -(a + b) + a from fun a b => by ring) _ _

end GlobalTheory.CurveDens
