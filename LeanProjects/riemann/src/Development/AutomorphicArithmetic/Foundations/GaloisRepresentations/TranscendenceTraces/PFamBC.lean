import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famBC_of :
    FamBC := by
  intro q i Z' S' Z S v p' p g w h τ hτ
  let push : Sq p' → Sq p := fun A =>
    { U := A.U, V := A.V, u := A.u ≫ g, v := A.v ≫ v, r := A.r,
      pb := A.pb.paste_horiz h }
  let pushTo : ∀ {A B : Sq p'}, A.To B → (push A).To (push B) := fun {A B} t =>
    { g := t.g, k := t.k,
      hu := by simp only [push, ← Category.assoc, t.hu],
      hv := by simp only [push, ← Category.assoc, t.hv],
      hr := t.hr }
  let τ' : Fam p' (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)) :=
    { deg := fun s =>
        { app := fun A => (τ.deg s).app (push A),
          nat := fun {A B} t a => (τ.deg s).nat (pushTo t) a },
      comm := fun A s t a => τ.comm (push A) s t a }
  refine ⟨τ', ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb1, hb2⟩ := hτ (push A) a
    refine ⟨b, hb1, ?_⟩
    intro Ω _ _ x
    have := hb2 Ω x
    simpa only [IsSum, Wt.comap, push, Category.assoc] using this
  · intro n a
    let t : (push (Sq.self p')).To (Sq.self p) :=
      { g := g, k := v,
        hu := by simp [push, Sq.self],
        hv := by simp [push, Sq.self],
        hr := by simpa [push, Sq.self] using h.w }
    exact ((τ.deg n).nat t a).symm
