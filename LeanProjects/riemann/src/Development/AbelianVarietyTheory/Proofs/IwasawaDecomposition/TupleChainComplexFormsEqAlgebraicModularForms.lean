import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
