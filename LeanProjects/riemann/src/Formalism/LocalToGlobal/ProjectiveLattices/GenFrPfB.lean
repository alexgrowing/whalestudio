import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfV

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem gfp_chart_iso {R : Type} [CommRing R] {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ G₁} (hx : IsUnivChart G₁ n xc) :
    IsUnivChart G₂ n (fun m => xc m ≫ e.hom) := by
  have h1 : ∀ X : Over (Spec (CommRingCat.of R)), (1 : X ⟶ G₁) ≫ e.hom = 1 := by
    intro X
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, hx.1 m]
  · rw [← Category.assoc, hx.2.1 m, h1]
  · intro A _ _ aug m hker y hy
    have hy' : ReciprocityTheory.ChartRestriction.G.Chart.spMap aug ≫ (y ≫ e.inv) = 1 := by
      rw [← Category.assoc, hy, ← h1, Category.assoc, e.hom_inv_id, Category.comp_id]
    obtain ⟨ψ, hψ, huniq⟩ := hx.2.2 A aug m hker (y ≫ e.inv) hy'
    refine ⟨ψ, ⟨hψ.1, ?_⟩, fun ψ' hψ' => huniq ψ' ⟨hψ'.1, ?_⟩⟩
    · rw [← Category.assoc, ← Iso.comp_inv_eq, hψ.2]
    · rw [Iso.comp_inv_eq, hψ'.2, Category.assoc]

def gfpEig {L : Type} [Field L] [Algebra c.F L] {x : Sp L ⟶ Xo.X} {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
    (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) : Submodule L (Fin n → L) :=
  eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a))

section BC

variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gfpVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gfpVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gfpVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  have ht : tvec (x := xc) (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc).symm
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx
        (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a)) _).symm
  have e1 : ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    simp
    first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  simp only [gfpVec, ht, Over.comp_left, Category.assoc, e1]

theorem gfp_bc {L' : Type} [Field L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L') (JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gfp_inj hx' ?_⟩
  rw [gfpVec_tmap hx', hv, hv, gfpVec_tmap hx, Category.assoc]

variable [Algebra c.F L]

theorem gfp_finrank (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Module.finrank L (gfpEig (c := c) hx τ) = Dw.mult τ := by
  classical
  obtain ⟨xc', hx', -, htm⟩ := gfp_bc (L' := AlgebraicClosure L) hx
  have hrank := ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := L) (k := AlgebraicClosure L)
    (fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)))
    (fun a => tmap hx' ((Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a)))
    htm (fun a => algebraMap c.F L (embK c τ a))
  let β : KA l →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp
    ((algebraMap c.F L).comp (IntermediateField.inclusion c.le).toRingHom)
  have hβ : (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) ≫ Xo.s = spMap β := by
    rw [Category.assoc, hx0]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hd := (Xo.univ.geom (AlgebraicClosure L) _ β hβ).1
  let τ' : 𝓞 E →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp ((algebraMap c.F L).comp (embK c τ))
  have key : ∀ N, LieMult Xo.univ.t.act (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) τ' N →
      Module.finrank (AlgebraicClosure L) (eigLat hx'
        (fun a => (Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a))
        (fun a => τ' a)) = N :=
    fun N h => ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult gfp_hcId (Category.comp_id _) hx' Xo.univ.t.act
      Xo.univ.t.act.act (fun a => by rw [Category.comp_id, Category.id_comp]) _ (fun a => rfl) τ' h
  have hinj : Function.Injective ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) := RingHom.injective _
  have e0 : τ' H.rt = β (baseKA l).ρ ↔ τ (H.rt : E) = H.rt0 := by
    constructor
    · intro h
      have h' := @hinj (embK c τ H.rt) (IntermediateField.inclusion c.le (baseKA l).ρ) h
      exact congrArg (fun z : c.F => (z : ℂ)) h'
    · intro h
      have h' : embK c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext h
      exact congrArg ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) h'
  refine hrank.trans ?_
  unfold Datum.mult
  split_ifs with h
  · exact key _ ((hd τ').1 (e0.2 h))
  · exact key _ ((hd τ').2 (fun h' => h (e0.1 h')))

theorem gfp_basis (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ)
    (d : Fin (Dw.mult τ) → Fin n → L) (hd : LinearIndependent L d) (hdW : ∀ i, d i ∈ gfpEig (c := c) hx τ)
    (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (he : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → L, IsCombAt x (fun i => gfpVec x xc (d i)) a w := by
  obtain ⟨cc, rfl⟩ := gfp_exists hx w hw
  have hcc : cc ∈ gfpEig (c := c) hx τ := (gfp_eig_iff hx τ cc).1 he
  have hle : Submodule.span L (Set.range d) ≤ gfpEig (c := c) hx τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdW i
  have hfr : Module.finrank L (Submodule.span L (Set.range d)) =
      Module.finrank L (gfpEig (c := c) hx τ) := by
    rw [finrank_span_eq_card hd, Fintype.card_fin, gfp_finrank hx0 hx τ]
  have heq : Submodule.span L (Set.range d) = gfpEig (c := c) hx τ :=
    Submodule.eq_of_le_of_finrank_eq hle hfr
  have hspan : cc ∈ Submodule.span L (Set.range d) := heq ▸ hcc
  obtain ⟨a, ha⟩ : ∃ a : Fin (Dw.mult τ) → L, ∑ i, a i • d i = cc := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun L).1 hspan
    | exact Submodule.mem_span_range_iff_exists_fun.1 hspan
  refine ⟨a, (gfp_comb_iff hx d a cc).2 ha.symm, ?_⟩
  intro a' ha'
  have h2 : cc = ∑ j, a' j • d j := (gfp_comb_iff hx d a' cc).1 ha'
  have h3 : ∑ j, a' j • d j = ∑ j, a j • d j := h2.symm.trans ha.symm
  funext i
  have h4 := Fintype.linearIndependent_iff.1 hd (a' - a) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h3, sub_self]) i
  simpa [sub_eq_zero] using h4

end BC

end Formalism.L2.Pj
