import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem exists_pullSec (a : ℤ) {T T' : Over S0} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s', IsPullSec A L a h hh s s' := by
  have hl : ∀ j, (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := fun j => chart_le_res A L h hh a j
  have hc : h.left ≫ (snd T A).left = (snd T' A).left := by
    rw [← Over.comp_left, hh]
  refine ⟨⟨fun j => ((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j)), ?_⟩,
    fun j => rfl⟩
  intro j j'
  apply fn_ext
  intro y hy
  have v : ∀ j, y ∈ (LPow A L a T').U j →
      gs (𝟙 _) y _ (((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ h.left) y ((LPow A L a T).U j) (s.f j) :=
    fun j hj => (gs_res _ y _ hj _).trans (gs_pull _ h.left y _ (hl j hj) _)
  refine ((gs_res (𝟙 _) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y j j' hy.1 hy.2))) ((gs_res (𝟙 _) y _ hy _).trans (v j' hy.2)))).symm)
  refine (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ h.left) y
    (hl j hy.1) (hl j' hy.2)).trans ?_
  simp only [trF, Category.assoc, hc]
  try rfl

theorem exists_value (hL : L.IsLB) (a : ℤ) {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))) (hτ : τ.IsGen) :
    ∃ v, IsValueAt A L a s z τ v := by
  have hpz : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left]
    simp [ptSecT]
  obtain ⟨w, hw⟩ : ∃ w : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j),
      ∀ j, w j = (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) *
        (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from ((τ.s j)⁻¹).val) := ⟨_, fun _ => rfl⟩
  have loc : ∀ j x, x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      gs (𝟙 _) x _ (w j) = gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) * ((gm (𝟙 _) x _ (τ.s j))⁻¹).val := by
    intro j x hx
    rw [hw j]
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) x (val_le A L z j) hx _).trans
      (gs_pull (𝟙 _) (ptSecT A z).left x _ (val_le A L z j hx) _)) ?_)
    exact (gs_unit (𝟙 _) x _ hx ((τ.s j)⁻¹)).trans (congrArg Units.val (map_inv _ _))
  have hcompat : TopCat.Presheaf.IsCompatible T.left.sheaf.val (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) w := by
    intro j j'
    apply fn_ext
    intro x hx
    change gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_left).op).hom (w j)) =
      gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_right).op).hom (w j'))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, loc j x hx.1, loc j' x hx.2]
    rw [show gs (𝟙 _ ≫ (ptSecT A z).left) x ((LPow A L a T).U j) (s.f j) = _ from
      sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ x
        (val_le A L z j hx.1) (val_le A L z j' hx.2)]
    rw [show gm (𝟙 _) x ((LB.LinComb L (fun _ : Fin 1 => z.left) fun _ => a).U j) (τ.s j) = _ from
      gen_trans hτ (𝟙 _) x hx.1 hx.2]
    have ht : trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _ ≫ (ptSecT A z).left) x j j' =
        trF (L := L) (fun _ : Fin 1 => z.left) (fun _ => a) (𝟙 _) x j j' := by
      simp only [trF, Category.assoc, hpz]
    rw [ht, mul_inv_rev, Units.val_mul]
    have key : ∀ (t G : (T.left.presheaf.stalk x)ˣ) (P : T.left.presheaf.stalk x),
        (t : T.left.presheaf.stalk x) * P * (((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) *
          ((t⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) =
          P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) := by
      intro t G P
      linear_combination (P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) * Units.mul_inv t
    exact key _ _ _
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => z.left) j := by
    intro x _
    have hx : z.left x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨v, hv, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.left.sheaf
    (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) ⊤ (fun j => homOfLE le_top) hcov w hcompat
  refine ⟨v, fun j => ?_⟩
  have e : (T.left.presheaf.map (homOfLE le_top).op).hom v = w j := hv j
  have key : ∀ (R : Type) [CommRing R] (p : R) (t : Rˣ), p = p * ((t⁻¹ : Rˣ) : R) * (t : R) := by
    intro R _ p t
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [e, hw j]
  exact key _ _ (τ.s j)

theorem value_stalk (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by
  have h1 := congrArg (gs r y (LB.wchart L (fun _ : Fin 1 => z.left) j)) (hv j)
  refine ((gs_pull r (ptSecT A z).left y _ (val_le A L z j hy) _).symm.trans
    ((gs_res r y (val_le A L z j) hy _).symm.trans h1)).trans ?_
  exact (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y le_top hy v) (gs_unit r y _ hy _))

theorem pullSec_stalk (a : ℤ) {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a h hh s s') {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (y : Z) (j : Fin 1 → L.ι) (hy : r y ∈ (LPow A L a T').U j) :
    gs r y _ (s'.f j) = gs (r ≫ h.left) y _ (s.f j) := by
  rw [hs j]
  exact (gs_res r y (chart_le_res A L h hh a j) hy _).trans (gs_pull r h.left y _ (chart_le_res A L h hh a j hy) _)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
