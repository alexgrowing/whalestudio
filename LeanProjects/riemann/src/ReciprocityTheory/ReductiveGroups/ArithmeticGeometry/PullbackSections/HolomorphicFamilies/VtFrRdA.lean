import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdHol
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {Z Z' : Scheme.{0}}

private lemma ringHom_units_zpow_lemma {R S : Type*} [CommRing R] [Field S] (f : R →+* S) (u : Rˣ) (k : ℤ) :
    f ↑(u ^ k) = (f ↑u) ^ k := by
  have hk : ((Units.map (f : R →* S) (u ^ k) : Sˣ) : S) = ((Units.map (f : R →* S) u ^ k : Sˣ) : S) := by
    rw [map_zpow]
  rw [Units.val_zpow_eq_zpow_val] at hk
  exact hk

theorem vtf_valU (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) (k : ℤ) :
    valAt' p V ((u ^ k : Γ(Z, V)ˣ) : Γ(Z, V)) = valAt' p V (u : Γ(Z, V)) ^ k := by
  rw [valAt', valAt', dif_pos h, dif_pos h]
  delta valAt
  exact ringHom_units_zpow_lemma ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (p.appLE V ⊤ h).hom) u k

theorem vtf_val_res (p : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, U)ˣ) :
    valAt' p V (res hVU u : Γ(Z, V)) = valAt' p U (u : Γ(Z, U)) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ U := h.trans (fun x hx => hVU hx)
  rw [valAt', valAt', dif_pos h, dif_pos h']
  delta valAt res
  congr 1
  first
  | (rw [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  | simp [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem vtf_val_pullU (p : Sp ℂ ⟶ Z) (f : Z ⟶ Z') (U : Z'.Opens) (u : Γ(Z', U)ˣ) :
    valAt' p (f ⁻¹ᵁ U) (pullU f U u : Γ(Z, f ⁻¹ᵁ U)) = valAt' (p ≫ f) U (u : Γ(Z', U)) := by
  by_cases hc : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have hc' : ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun x hx => hc hx
    rw [valAt', valAt', dif_pos hc, dif_pos hc']
    delta valAt pullU
    congr 1
  · have hc' : ¬ ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun h' => hc (fun x hx => h' hx)
    rw [valAt', valAt', dif_neg hc, dif_neg hc']

end Units

section Rd

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}

abbrev vtfQ (a : Over.mk x0 ⟶ A) : Over.mk x0 ⟶ Over.mk x0 ⊗ A := lift (𝟙 _) a

theorem vtfQ_snd (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (snd (Over.mk x0) A).left = a.left := by
  show (lift (𝟙 _) a ≫ snd (Over.mk x0) A).left = a.left
  rw [lift_snd]

theorem vtfQ_fst (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (fst (Over.mk x0) A).left = 𝟙 _ := by
  show (lift (𝟙 _) a ≫ fst (Over.mk x0) A).left = 𝟙 _
  rw [lift_fst]
  rfl

theorem vtf_pt_uniq (a : Over.mk x0 ⟶ A) (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)
    (h1 : pt ≫ (snd (Over.mk x0) A).left = a.left) (h2 : pt ≫ (fst (Over.mk x0) A).left = 𝟙 _) :
    pt = (vtfQ A a).left := by
  have hw : pt ≫ (Over.mk x0 ⊗ A).hom = x0 := by
    rw [← Over.w (fst (Over.mk x0) A), ← Category.assoc, h2, Category.id_comp]
    rfl
  let q : Over.mk x0 ⟶ Over.mk x0 ⊗ A := Over.homMk pt hw
  have hq : q = vtfQ A a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [vtfQ, lift_fst]
      ext
      exact h2
    · simp only [vtfQ, lift_snd]
      ext
      exact h1
  exact congrArg CommaMorphism.left hq

theorem vtf_chart (k : ℤ) (a : Over.mk x0 ⟶ A) (i : Fin 1 → L.ι) (h : ⊤ ≤ a.left ⁻¹ᵁ L.U (i 0)) :
    ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ (LPow A L k (Over.mk x0)).U i := by
  intro x _
  have hx : a.left.base x ∈ L.U (i 0) := h (by trivial)
  have hx' : (snd (Over.mk x0) A).left.base ((vtfQ A a).left.base x) ∈ L.U (i 0) := by
    have e : ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x = a.left.base x := by
      rw [vtfQ_snd]
    change ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x ∈ L.U (i 0)
    rw [e]
    exact hx
  refine Set.mem_iInter.mpr fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact hx'

theorem vtf_val_g {k : ℤ} (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (i i' : Fin 1 → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U i ⊓ (LPow A L k (Over.mk x0)).U i')) :
    valAt' p _ ((LPow A L k (Over.mk x0)).g i i').val =
      valAt' (p ≫ (snd (Over.mk x0) A).left) (L.U (i 0) ⊓ L.U (i' 0)) (L.g (i 0) (i' 0)).val ^ k := by
  delta LPow LB.LinComb at h ⊢
  dsimp only at h ⊢
  rw [Fin.prod_univ_one, vtf_valU p h]
  congr 1
  exact (vtf_val_res p _ h _).trans (vtf_val_pullU p (snd (Over.mk x0) A).left _ (L.g (i 0) (i' 0)))

theorem vtf_read {k : ℤ} (F : LB.Sec (LPow A L k (Over.mk x0))) (a : Over.mk x0 ⟶ A) (fr : L.ι → ℂ)
    (hfr : ∀ j j', ⊤ ≤ a.left ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j = valAt' a.left _ (L.g j j' : Γ(A.left, L.U j ⊓ L.U j')) * fr j')
    (j j' : L.ι) (hj : ⊤ ≤ a.left ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ a.left ⁻¹ᵁ L.U j') (θ : ℂ)
    (h : valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ * fr j ^ k) :
    valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j')) (F.f (fun _ => j')) = θ * fr j' ^ k := by
  have hjj : ⊤ ≤ a.left ⁻¹ᵁ (L.U j' ⊓ L.U j) := fun q hq => ⟨hj' hq, hj hq⟩
  have hp : ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U (fun _ => j') ⊓
      (LPow A L k (Over.mk x0)).U (fun _ => j)) :=
    fun q hq => ⟨vtf_chart A L k a _ hj' hq, vtf_chart A L k a _ hj hq⟩
  have e := congrArg (valAt' (vtfQ A a).left _) (F.compat (fun _ => j') (fun _ => j))
  rw [valAt'_mul] at e
  have e1 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_left :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j'))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j')) := by
    exact valAt'_res _ _ hp _
  have e2 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_right :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j)) := by
    exact valAt'_res _ _ hp _
  rw [e1, e2, vtf_val_g A L _ _ _ hp, vtfQ_snd, h] at e
  rw [e, hfr j' j hjj, mul_zpow]
  ring

theorem vtf_twist {a b : ℤ} {ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A} {m : Over.mk x0 ⊗ A ⟶ A}
    {hm : ψ ≫ snd (Over.mk x0) A = m}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b (Over.mk x0))} {s' : LB.Sec (LPow A L a (Over.mk x0))}
    (h : IsTwistPull A L ψ m hm a b α s s') (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (j : Fin 2 → L.ι)
    (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) :
    valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0)) =
      valAt' p _ (α.s j).val *
        valAt' (p ≫ ψ.left) ((LPow A L b (Over.mk x0)).U (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  calc valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0))
      = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom
            (s'.f (fun _ => j 0))) := by
        exact (valAt'_res p (chart_le_zero A L m j) hp _).symm
    _ = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          ((show Γ((Over.mk x0 ⊗ A).left, LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) from (α.s j).val) *
            ((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
              ((ψ.left.app _).hom (s.f (fun _ => j 1)))) := by rw [h j]
    _ = _ := by
        rw [valAt'_mul]
        refine congrArg₂ (· * ·) rfl ?_
        calc _ = valAt' p (ψ.left ⁻¹ᵁ (LPow A L b (Over.mk x0)).U (fun _ => j 1))
              ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
              exact valAt'_res p (chart_le_pull A L ψ m hm j) hp _
          _ = _ := by exact valAt'_comp p ψ.left _ _

end Rd

end ReciprocityTheory.ChartRestriction.G.PullbackSections
