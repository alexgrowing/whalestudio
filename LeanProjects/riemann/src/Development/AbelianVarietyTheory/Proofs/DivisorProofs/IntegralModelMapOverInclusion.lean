import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatibleStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_discr_smul_eigen_mem_span_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
      ∃ x : Fin g → LieG P.Gt, (∀ b, ITie P π (x b) (e b)) ∧
        ∀ (σ : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ)) e U →
        ∀ x' : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x' →
        ∃ M : Fin g → 𝓞_ℂ_[p], ((discr E : ℤ) : ℂ_[p]) • P.bLie x' =
          ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
  intro E _ _ _ H Dw p _ _ l l' Xo Xo' c c' W Y r ν hle hOI _ yb yy P π ψ y hHT β hβ g e hB
  have hPt : PtOn Y yb yy P π ψ := hHT.1
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.p_adic_point_pairing_compatible E H Dw p l' Xo' c' W Y yb yy P π ψ hPt
  choose x hx using fun b => (h1 (e b) (hB.1 b)).exists
  refine ⟨x, hx, ?_⟩
  intro σ U hEig x' hx'
  obtain ⟨u', hu'T, hu'X⟩ := h2 x'
  have hemb := GlobalTheory.FlatModel.htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y hHT β hβ σ
  have hEG : IsEigG Y.t (β.comp (embV c' W σ)) u' := by
    rw [hemb]
    exact (h4 _ x' u' hu'T hu'X).2 hx'
  have hid : spMap (RingHom.id 𝓞_ℂ_[p]) ≫ yb = yb := by
    rw [show spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  have hdual : (fun i => spMap (dualMap (RingHom.id 𝓞_ℂ_[p])) ≫ e i) = e := by
    have : dualMap (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
      ext s <;> simp [dualMap]
    funext i
    rw [this, show spMap (RingHom.id (DualNumber 𝓞_ℂ_[p])) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨w, hw, -⟩ := hB.2 𝓞_ℂ_[p] (RingHom.id _) u' (by rw [hid]; exact hu'T)
  rw [hid, hdual] at hw
  have hL := h3 g e x w u' x' hB.1 hx hw hu'X
  have hmem := hEig.2 w u' hw hEG
  obtain ⟨M, hM⟩ := (Submodule.mem_span_range_iff_exists_fun 𝓞_ℂ_[p]).1 hmem
  refine ⟨M, ?_⟩
  have hcoord : ∀ b, ((discr E : ℤ) : 𝓞_ℂ_[p]) * w b = ∑ k, M k * U k b := by
    intro b
    have := congrFun hM b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  rw [hL, Finset.smul_sum]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) (hcoord b)
  exact_mod_cast this

end GlobalTheory.FlatModel
