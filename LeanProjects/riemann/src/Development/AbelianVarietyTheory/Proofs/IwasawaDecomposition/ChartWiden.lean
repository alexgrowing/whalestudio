import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open scoped TensorProduct

def chartWiden {D : D7} {T : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))} (hb : bad ⊆ bad') {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) : LevelChart D T bad' i hi stab lat where
  lev :=
    { K.lev with
      Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (hb h)) hT
      chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (hb hv)) }
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

def chartAll {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (β : Unit) :
    LevelChart D T bad i hi (fun c : {c : cl // (fun _ : cl => ()) c = β} => stab c.1) (fun c => lat c.1) where
  lev := K.lev
  y c := K.y c.1
  y_bij := by
    have e : Function.Bijective (fun c : {c : cl // (fun _ : cl => ()) c = β} => c.1) :=
      ⟨Subtype.val_injective, fun c => ⟨⟨c, rfl⟩, rfl⟩⟩
    exact K.y_bij.comp e
  y_lat c := K.y_lat c.1
  stabI c := K.stabI c.1
  stabI_inj c := K.stabI_inj c.1
  stabI_range c := K.stabI_range c.1

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

set_option maxHeartbeats 4000000 in

structure TwLevJ {Ch0 : B.Word → ℕ → Type} {chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i}
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)))
    (u : B.Word) (a : I.ι) {Ch : Type} (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _)
      (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1)
      (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) where

  levJ : Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f Q

  Yb : Type
  [YbFin : Finite Yb]
  [YbAct : MulAction levJ.U Yb]

  yb : Ch → Yb
  yb_orbit : ∀ y : Yb, ∃! β, ∃ κ : levJ.U, κ • yb β = y

  lb : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) levJ.Lb
  le : ∀ β, (K β).lev.U ≤ levJ.U.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  stab : ∀ β (κ : levJ.U), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 ∈ (K β).lev.U ↔ κ • yb β = yb β

  chiJ : levJ.U →* ℂˣ
  chiJ_eq : ∀ β (κ : levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (K β).lev.chi κ' = chiJ κ

  J_g : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v levJ.Lb,
      x ∈ levJ.Uloc v ↔ ∃ M ∈ HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v,
        (M : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) (kv (I.rec7 l Z).host.F v)) = redJS F u j v hv x

  J_off : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Q → v ∉ badG (I.rec7 l Z) →
    (levJ.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom = (F u).levJ.Uloc v

  yG : Yb → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
    ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v
  yG_smul : ∀ (κ : levJ.U) y j v hv,
    yG (κ • y) j v hv = redJS F u j v hv (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) *ᵥ yG y j v hv

  YQ : Type
  yQ : Yb → YQ
  y_inj : ∀ y y', yG y = yG y' → yQ y = yQ y' → y = y'
  yQ_off : ∀ (κ : levJ.U) y, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → yQ (κ • y) = yQ y

attribute [instance] TwLevJ.YbFin TwLevJ.YbAct

end GlobalTheory.Mem.Col2.TC

end
