import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem crd_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY Kc)), I.StdKer l Z t → (∀ i hi, I.IdY l Z u a i hi (eY i hi)) → AdPins A dt → ∀ i hi, A.crd i hi = 1 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt A hK hY hA i hi
  obtain ⟨τ⟩ : Nonempty (I.rec7 l Z).what₂.Tau := ⟨(I.rec7 l Z).eTau.symm 1⟩
  let f : Formalism.L2.Forms.Fr (I.rec7 l Z) i hi := ⟨fun _ => 1, fun _ => by simp⟩
  set y := (eY i hi).symm f with hy
  have hYy : (eY i hi y).1 = y.1 := hY i hi y
  have hf : (eY i hi y) = f := by rw [hy, Equiv.apply_symm_apply]
  have h1 := hA.frm i hi y τ
  have h2 := hK.O.frm u a i y
  have hc : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (A.crd i hi).1 τ = 1 := by
    have e1 : ((charts I l Z u a bad Ch chOf eY Kc i hi).eY y).1 τ = 1 := by
      show ((eY i hi y).1) τ = 1
      rw [hf]
    rw [e1, mul_one, h2, ← hYy, hf] at h1
    exact h1.symm
  apply Units.ext
  refine Matrix.ext fun p q => ?_
  have := congrFun (congrFun hc p) q
  simp only [Formalism.L2.Forms.atInf, Matrix.map_apply] at this
  rw [Units.val_one]
  apply (Formalism.L2.Forms.embT (I.rec7 l Z) τ).injective
  rw [this]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.TwU.AtTrue
