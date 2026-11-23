import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem op_add_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S}
    (τ τ' σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = (τ.deg n).app (Sq.self p) a + (τ'.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = τ.op n x + τ'.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) τ' n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h2).2.2.1
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_smul_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S} (d : ℤ)
    (τ σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = d • (τ.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • τ.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h1).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_id_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {S : Scheme.{0}} (d : ℤ)
    (σ : Fam (𝟙 S) (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self (𝟙 S)) a = d • a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj S)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).1) x
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ ha ha).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

theorem UpperTheory.Gal.TranscendenceTraces.trLin_of :
    TrChar → FamLin → WtLin → RpBasic → RpOp → TrLin := by
  intro hChar hFam hWt hRp hOp q _ n i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' hw hw' hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).1 p w w' (trFam p w q i) (trFam p w' q i)
      (hChar q i p w hw hq).2.1 (hChar q i p w' hw' hq).2.1
    rw [(hChar q i p (w.add w') (hWt.1 p w w' hw hw') hq).2.2 σ hσ n]
    exact op_add_of hRp hOp _ _ σ (fun a => hσd n _ a) x
  · intro Z S p _ d w hw hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.1 p d w (trFam p w q i) (hChar q i p w hw hq).2.1
    rw [(hChar q i p (w.smul d) (hWt.2.1 p d w hw) hq).2.2 σ hσ n]
    exact op_smul_of hRp hOp d _ σ (fun a => hσd n _ a) x
  · intro S d hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.2 S d
    rw [(hChar q i (𝟙 S) (Wt.const S d) (hWt.2.2 (𝟙 S) d) hq).2.2 σ hσ n]
    exact op_id_of hRp hOp d σ (fun a => hσd n a) x
