import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pos_ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pos_frMap (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {K₁ K₂ : Type}
    [Field K₁] [Field K₂] [Algebra c.F K₁] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂) (y : FrPt Xo c K₁) :
    ∃ z : FrPt Xo c K₂, FrMap φ y z := by
  classical
  let _ : Algebra K₁ K₂ := φ.toRingHom.toAlgebra
  have htow : ∀ r : c.F, algebraMap c.F K₂ r = algebraMap K₁ K₂ (algebraMap c.F K₁ r) := fun r => (φ.commutes r).symm
  have : FaithfulSMul K₁ K₂ := (faithfulSMul_iff_algebraMap_injective K₁ K₂).2 (algebraMap K₁ K₂).injective
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback y.x).obj Xo.univ.t.G)
  have hco : ∀ τ i, ∃ cc, y.u τ i = gfpVec y.x xc cc := fun τ i => gfp_exists hx _ (y.tan τ i)
  choose d hdu using hco
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i =>
    (gfp_eig_iff hx τ _).1 (by rw [← hdu τ i]; exact y.eig τ i)
  have hd : ∀ τ, LinearIndependent K₁ (d τ) := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hu : y.u τ = fun i => gfpVec y.x xc (d τ i) := funext (hdu τ)
    have h0 : (0 : Fin n → K₁) ∈ gfpEig (c := c) hx τ := Submodule.zero_mem _
    obtain ⟨a, -, ha⟩ := y.basis τ (gfpVec y.x xc 0) (gfp_tan hx 0) ((gfp_eig_iff hx τ 0).2 h0)
    have e1 : IsCombAt y.x (y.u τ) g (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) g 0).2 hg.symm
    have e2 : IsCombAt y.x (y.u τ) 0 (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) 0 0).2 (by simp)
    have e3 := (ha g e1).trans (ha 0 e2).symm
    exact fun i => congrFun e3 i
  obtain ⟨xc', hx', hv, htm⟩ := gfp_bc (L' := K₂) hx
  have hx0' := gfp_over_bc htow y.x_over
  have hW' : ∀ τ j, (algebraMap K₁ K₂ ∘ d τ j) ∈ gfpEig (c := c) hx' τ := by
    intro τ j
    have h0 := hdW τ j
    unfold gfpEig at h0 ⊢
    rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h0 ⊢
    intro a
    rw [htm a (d τ j), h0 a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, htow]
  have hli : ∀ τ, LinearIndependent K₂ (fun i => algebraMap K₁ K₂ ∘ d τ i) := fun τ =>
    linearIndependent_algebraMap_comp_iff.mpr (hd τ)
  refine ⟨⟨spMap (algebraMap K₁ K₂) ≫ y.x, hx0', fun τ i => gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i),
    fun τ i => gfp_tan hx' _, fun τ i => (gfp_eig_iff hx' τ _).2 (hW' τ i),
    fun τ w hw he => gfp_basis hx0' hx' τ _ (hli τ) (hW' τ) w hw he,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.secCP (ReciprocityTheory.ChartRestriction.G.PullbackSections.cpS (algebraMap K₁ K₂) y.x) y.s,
    fun s' => ReciprocityTheory.ChartRestriction.G.PullbackSections.genBC_frame y.x hS hT (algebraMap K₁ K₂) y.s y.gen s'⟩, rfl, fun τ i => ?_,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm (algebraMap K₁ K₂) y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _,
    fun i h => rfl⟩
  show gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i) = spMap (dualMap φ.toRingHom) ≫ y.u τ i
  rw [hdu τ i]
  exact hv (d τ i)

end Formalism.L2.Pj
