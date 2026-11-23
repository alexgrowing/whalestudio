import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateHermitianSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogGramSquareSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinatesStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam.FlagCpt

theorem smoothOn_met_of_eigMet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (G : EigMet Z (embOf e σ)) (T : Set (CxPts (genStr Z) (embOf e σ))), IsOpen T → G.SmoothOn (manifold Z (embOf e σ)) T → ∀ n : Pad.Letter Dw → ℤ, IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) ∧ (Y.met G n).SmoothOn (Y.down ⁻¹' T) := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ F _ _ e Y σ G T hT hG n
  have hc : Continuous (Y.down (σ := σ)) := CxPts.continuous_of_comp (f := Y.π) (fun _ => rfl)
  have hS : IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) := hT.preimage hc
  refine ⟨hS, ?_⟩
  have key : ∀ y : Y.Y.X, ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ), y ∈ U ∧
      (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧
      (Y.Y.an σ).SmoothOn (Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U) (fun q => Real.log ((Y.met G n).h (prodPow t n) q)) := by
    intro y
    obtain ⟨U, t, V, φ, Fr, A, hy, hφ, hUV, ht, hfr⟩ := GlobalTheory.T.exists_local_flag_coordinates E H Dw l Xo c O β Z F e Y σ y
    refine ⟨U, t, hy, ht, ?_⟩
    choose gf hre him hgf using fun (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)) => hG V φ Fr τ a b hφ
    set S' : Set (Y.Y.pts σ) := Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U with hS'def
    have hS' : IsOpen S' := hS.inter (isOpen_ptsIn _)
    have hsub : S' ⊆ Y.down ⁻¹' (T ∩ ptsIn _ _ V.1) := fun q hq => ⟨hq.1, hUV q hq.2⟩
    let Mf : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => gf τ a b (Y.down q)
    let Af : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => ev Y.Y.str σ U (A τ a b) q
    have hM : ∀ τ a b, (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).re) ∧ (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).im) :=
      fun τ a b => ⟨((hre τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub,
        ((him τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub⟩
    have hA : ∀ τ a b, (Y.Y.an σ).HoloOn S' (fun q => Af τ q a b) :=
      fun τ a b => AnRead.holoOn_ev_of_subset _ (fun _ hq => hq.2)
    have hgram : ∀ q ∈ S', ∃ g : Y.FrameAt q, Y.Adapted q t g 1 ∧
        ∀ τ, G.gram (Y.down q) g τ = (Af τ q)ᴴ * Mf τ q * Af τ q := by
      intro q hq
      obtain ⟨hv, g, f, had, hmap, hco⟩ := hfr q hq.2
      refine ⟨g, had, fun τ => ?_⟩
      have e1 : f.co g τ = Af τ q := by
        rw [hco τ]; ext a b; simp [Af, ev_eq hq.2]
      have e2 : G.gram (Y.down q) f τ = Mf τ q := by
        ext a b; exact hgf τ a b (Y.down q) hq.1 hv f hmap
      rw [G.change _ f g τ, e1, e2]
    have hpos : ∀ τ, ∀ q ∈ S', ((Af τ q)ᴴ * Mf τ q * Af τ q).PosDef := fun τ q hq => by
      obtain ⟨g, -, hg⟩ := hgram q hq
      rw [← hg τ]; exact G.pos _ _ _
    have hsm : ∀ z : Letter Dw, (Y.Y.an σ).SmoothOn S' (fun q => Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2)) :=
      fun z => GlobalTheory.T.log_gram_square_smooth _ S' _ (GlobalTheory.T.conjugate_hermitian_smooth _ S' hS' _ _ (hA z.1) (hM z.1)) (hpos z.1) z.2
    refine AnRead.SmoothOn.congr (f := fun q => ∑ z : Letter Dw, (n z : ℝ) * Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2))
      (fun i => ContDiffOn.sum fun z _ => contDiffOn_const.mul (hsm z i)) fun q hq => ?_
    obtain ⟨g, had, hg⟩ := hgram q hq
    rw [FlagCpt.met_h G n had]
    simp only [prodPow, FlagCpt.genSq, hg, Pi.one_apply, _root_.one_zpow, Finset.prod_const_one, Units.val_one, norm_one, one_pow, div_one]
    rw [Real.log_prod (fun z _ => (zpow_pos (grSq_pos (hpos z.1 q hq) z.2) (n z)).ne')]
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  choose U t hy ht hs using key
  refine Var.Met.smoothOn_of_cover hS (fun q _ => by rw [FlagCpt.posSet_met]; exact Set.mem_univ q)
    (T := fun y => ptsIn Y.Y.str σ (U y)) (fun _ => isOpen_ptsIn _) (fun q => ⟨Var.base q, mem_ptsIn.2 (hy _)⟩)
    (e := fun y => prodPow (t y) n) (fun y q hq => FlagCpt.prodPow_mem n (fun τ i => ht y _ (mem_ptsIn.1 hq) τ i))
    fun y => ?_
  refine AnRead.SmoothOn.congr (f := fun q => -Real.log ((Y.met G n).h (prodPow (t y) n) q)) (fun i => (hs y i).neg) ?_
  exact fun q _ => rfl

end GlobalTheory.ShFam.FlagCpt
