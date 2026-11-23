import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLawG

theorem locTopG_source : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _hsel hL b P hP g z hmid
  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hgC
  refine ⟨⟨g, hgI⟩, rfl, ?_⟩
  intro k hk y y' y'' hy' hky
  obtain ⟨r, hr, hrg, hz⟩ := hmid
  have hred : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (g x) = (redGL _ P.1 k).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [hk]
    exact redV_redGL (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1) hx
  have hmem : redGL _ P.1 k ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H :=
    (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ (redGL _ P.1 k)).2 ⟨g, hgC, hred⟩
  set c : X.Kˣ := (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨redGL _ P.1 k, hmem⟩ with hcdef
  have hcz : (c : X.K) = z := by
    rw [hz]
    exact hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨redGL _ P.1 k, hmem⟩ g r hr hrg hred
  have hlev : GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k c :=
    ⟨fun _ => ⟨hmem, rfl⟩, fun _ h => absurd hP h⟩
  have hrho : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    refine unitV_congr _ ?_
    rw [(det_glint k).2, ← redGL_val, hk, redGL_val]
    exact (det_glint (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1)).2
  rw [hrho, ← hcz]
  have hm := hL.hm
  have key := GlobalTheory.TopLaw.locTop_source hX hPr hL hlev
  clear_value c
  clear hcdef hcz hrho hred hz hrg hr hmem
  revert key y
  cases R with
  | mk e k0 m t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    change m = m2 + 2 at hm
    subst hm
    intro y key
    have := key y (fun _ => hy') (fun h => absurd hP h) (fun _ => hky) (fun h => absurd hP h)
    unfold locTop at this
    rw [PhiTopG_eq]
    exact this

end GlobalTheory.TopLawG
