import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseBlock
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockTriangularOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement

noncomputable section

namespace GlobalTheory.FrameUnif

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem cover_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hT : CoverTri e F M) (y : FrPt Xo c (CAt σ)) :
    ∃ k, ∃ x : (M.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) y := by
  obtain ⟨k, x, Pm, hPm, hxy, hv⟩ := hT y
  obtain ⟨Pm', hPm', -, hx', hd', -⟩ := hun k x
  have hP : Pm' = Pm := by
    ext a j
    rw [hPm', hPm]
  subst hP
  refine ⟨k, x, ?_⟩
  have hxx : y.x = (un k x).x := hxy.symm.trans hx'.symm
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (un k x) y y).2.1 hxx fun τ i => ?_
  obtain ⟨cf, h1, h2, h3⟩ := hv (un k x).u hd' τ i
  exact ⟨cf, h1, h2, by rw [← hxx]; exact h3⟩

theorem fibre_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un)
    (hM : ModelBase M) (hB : FibTri e F M) (k k' : Fin F.n) (x : (M.X k).dom) (x' : (M.X k').dom) :
    (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k' x')) ↔
      ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩ := by
  constructor
  · rintro ⟨t, hx, hu, -⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun.1 k x
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun.1 k' x'
    refine hB k k' x x' Pm Pm' (un k x).u (un k' x').u hPm hPm' (hxP.symm.trans (hx.symm.trans hxP')) hd hd'
      fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, heq⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
    have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
    have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
    obtain ⟨t1, ht1, -⟩ := hun.2.2.1 k' γ hγ x hxg
    have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
      have hx2 := x'.2
      rw [h3] at hx2
      exact hx2
    obtain ⟨t2, ht2, -⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
    have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
    rw [hx'] at ht2
    exact ⟨t2 * t1, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ _).2.2.1 t1 t2 ht1 ht2⟩

theorem rdU_of_mem (U : Formalism.L2.PjFree.Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (h : x ∈ (U.X k).dom) : rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]

theorem readSec_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un) (hM : ModelBase M)
    (hW : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ)
      (y y' : FrPt Xo c (CAt σ)), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y) :
    ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k,
      ((unfOf e F M un).X k).IsSec (laU (unfOf e F M un) a n k) (rdU (unfOf e F M un) f k) := by
  intro a n hd f hf k
  refine ⟨hun.2.2.2 a n hd f hf k, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb : rmul x b ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).1 b hb
    obtain ⟨t, ht, hw⟩ := hun.2.1 k ⟨x, hx⟩ b hb hxb
    refine (rdU_of_mem _ f k hxb).trans ?_
    rw [rdU_of_mem _ f k hx, ← hw a n hd]
    exact congrArg toC (hW a n f hf t _ _ ht)
  · have hxg : lact γ x ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).2 γ hγ
    obtain ⟨t, ht, hw⟩ := hun.2.2.1 k γ hγ ⟨x, hx⟩ hxg
    refine (rdU_of_mem _ f k hxg).trans ?_
    rw [rdU_of_mem _ f k hx, show ((unfOf e F M un).X k).χ (laU (unfOf e F M un) a n k) γ = 1 from hM.chi k _ γ,
      ← hw a n hd]
    exact congrArg toC (hW a n f hf t _ _ ht)

end

theorem isUnf_built : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → IsUnf (unfOf e F M un) := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  exact ⟨hM.rank, hM.type,
    cover_unfOf e F M un hun.1 (GlobalTheory.CoverFrame.coverTri E H Dw l Xo c σ g e F r M hσ hM hN),
    fibre_unfOf e F M un hun hM (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN),
    readSec_unfOf e F M un hun hM ((GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred),
    g, e, F, id, M.φ, hM.ef, hun.1⟩

end GlobalTheory.FrameUnif
