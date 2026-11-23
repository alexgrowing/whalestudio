import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem exists_j_of_mem_flagOpen (X : FlagCover Y) {y : X.YY} (hy : y ∈ flagOpen X) :
    ∃ x : Xo.XF c, X.π y = Y.j x := by
  obtain ⟨w, rfl⟩ := (opensRange_inc X).ge hy
  refine ⟨(pullback.snd X.π Y.j) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem j_mem_closure_iff {s : Set (Xo.XF c)} (hs : IsClosed s) (x : Xo.XF c) :
    Y.j x ∈ closure (Y.j '' s) ↔ x ∈ s :=
  Set.ext_iff.1 (Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _ hs) x

section Ext

variable (X : FlagCover Y) (Z : Comp Xo c)

def openOn : X.YY.Opens := flagOpen X ⊓ X.π ⁻¹ᵁ barComp Y Z

def openOff : X.YY.Opens :=
  flagOpen X ⊓ X.π ⁻¹ᵁ ⟨(closure (Y.j '' (Z : Set (Xo.XF c))))ᶜ, isClosed_closure.isOpen_compl⟩

theorem flagOpen_le_sup : flagOpen X ≤ openOn X Z ⊔ openOff X Z := fun y hy => by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X hy
  by_cases hZ : x ∈ (Z : Set (Xo.XF c))
  · refine Or.inl ⟨hy, ?_⟩
    show X.π y ∈ barComp Y Z
    rw [hx]; exact (j_mem_barComp Z x).2 hZ
  · refine Or.inr ⟨hy, ?_⟩
    show X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
    rw [hx, j_mem_closure_iff (TrivOrderTieCompare.isClopen_comp Z).isClosed]
    exact hZ

theorem not_mem_openOn_openOff {y : X.YY} (h₁ : y ∈ openOn X Z) (h₂ : y ∈ openOff X Z) : False := by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X h₁.1
  have a : X.π y ∈ barComp Y Z := h₁.2
  have b : X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c))) := h₂.2
  rw [hx] at a b
  exact b (subset_closure ⟨x, (j_mem_barComp Z x).1 a, rfl⟩)

end Ext

section Glue

variable {X : FlagCover Y} {Z : Comp Xo c} {e : Ix Dw → ℤ}

theorem exists_extZero (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)) :
    ∃ m' : H0 (flagStr X) (X.LL e) (flagOpen X),
      H0.pull (inc₀ X Z) le_rfl m' = m ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X.YY) (k : X.F.J)
        (hO : ⊤ ≤ x ⁻¹ᵁ flagOpen X) (hk : ⊤ ≤ x ⁻¹ᵁ X.F.U k), ⊤ ≤ x ⁻¹ᵁ openOff X Z →
        H0.val (B := X.LL e) x k hO hk m' = 0 := by
  have hiso : IsoOver (inc₀ X Z) (openOn X Z) := isoOver_of_isOpenImmersion _ (by
    rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)
  have e₁ : U₀ X Z ≤ inc₀ X Z ⁻¹ᵁ openOn X Z := fun z hz => ⟨hz, z.2⟩
  have e₂ : inc₀ X Z ⁻¹ᵁ openOn X Z ≤ U₀ X Z := fun z hz => hz.1
  obtain ⟨m₁, hm₁⟩ := (hiso.bijective_pull (p := flagStr X) (X.F.isLB_LL e) e₁ e₂).2 m
  let W : Bool → X.YY.Opens := fun b => Bool.rec (openOff X Z) (openOn X Z) b
  have hW : ∀ b, W b ≤ flagOpen X := fun b => by cases b <;> exact inf_le_left
  have hc : flagOpen X ≤ iSup W := fun y hy => by
    rcases flagOpen_le_sup X Z hy with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, h⟩
  let s : ∀ b, H0 (flagStr X) (X.LL e) (W b) := fun b => Bool.rec (motive := fun b => H0 (flagStr X) (X.LL e) (W b)) 0 m₁ b
  obtain ⟨m', hm'⟩ := GlobalTheory.LB.exists_mod_of_cover (F := GlobalTheory.LB.toMod (X.LL e)) W hW hc s (by
    rintro (_ | _) (_ | _)
    · rfl
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.2 hy.1).elim
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.1 hy.2).elim
    · rfl)
  have r₁ : H0.restr (p := flagStr X) (hW true) m' = m₁ := hm' true
  have r₂ : H0.restr (p := flagStr X) (hW false) m' = 0 := hm' false
  refine ⟨m', ?_, fun S _ x k hO hk hx => ?_⟩
  · have h₃ : H0.pull (p := flagStr X) (inc₀ X Z) e₁ (H0.restr (p := flagStr X) (hW true) m') =
        H0.pull (p := flagStr X) (inc₀ X Z) le_rfl m' := H0.pull_restr _ _ _ _
    rw [r₁] at h₃
    exact h₃.symm.trans hm₁
  · have a := GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ (hW false)) (GlobalTheory.FlagMod.le_preimage_inf hO hk)
      (GlobalTheory.FlagMod.le_preimage_inf hx hk) (H0.loc (p := flagStr X) m' k)
    refine a.symm.trans ?_
    change H0.val (B := X.LL e) x k hx hk (H0.restr (p := flagStr X) (hW false) m') = 0
    rw [r₂, map_zero]

end Glue

theorem exists_suppOn_sec₀_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  intro E _ _ _ H Dw l Xo c Y X Z e m
  obtain ⟨m', h₁, h₂⟩ := exists_extZero m
  refine ⟨(secOf X e).symm m', ?_, ?_⟩
  · intro S _ _ y hy
    have hv : FlagCover.val (toSecO m') y = 0 := by
      refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
      have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
      rw [map_zero, coef_toSecO _ _ _ _ hO, h₂ _ _ _ _ _ ?_, mul_zero]
      intro s _
      refine ⟨hO (Set.mem_univ s), ?_⟩
      show X.π ((X.pt P' ≫ X.inc) s) ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
      rw [FlagCover.pt_inc, ← Scheme.Hom.comp_apply, (X.lies_ptY P').1, Scheme.Hom.comp_apply,
        j_mem_closure_iff (TrivOrderTieCompare.isClopen_comp Z).isClosed, ← FlagMod.frX_frMap hP,
        Scheme.Hom.comp_apply]
      exact hy _
    change evR Xo c (FlagCover.toRule (toSecO m')) y = 0
    by_cases hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    · rw [FlagCover.evR_toRule _ y hT, hv]
    · unfold evR evalAt
      rw [dif_neg hT]
  · show H0.pull (inc₀ X Z) le_rfl ((secOf X e) ((secOf X e).symm m')) = m
    rw [LinearEquiv.apply_symm_apply]
    exact h₁

end GlobalTheory.CompHS
