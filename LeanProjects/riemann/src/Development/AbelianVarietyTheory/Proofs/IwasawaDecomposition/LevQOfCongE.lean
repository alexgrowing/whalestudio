import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem levQ_of_congE {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : j < R.m) (b : L.β j) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (g : Formalism.L2.Col.GLint X.E (R.N j) P.1)
    (h1 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (g.1 x - x) ∈ stdAt X.E (R.N j) P.1) :
    ∃ h : g ∈ (L.levQ j b ⟨P.1, hP⟩).H, (L.levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  have m := GlobalTheory.TwU.MidIndep.extE_cong_mem hL j hj b P g.1 h1
    (GlobalTheory.TwU.MidIndep.cong_inv P.1 _ _ (hL.cst_ok.D_pos P) g.1 h1)
  have hx := GlobalTheory.CongLevel.extE_inX (cOf R j) g.1
  have hmem : g ∈ (L.levQ j b ⟨P.1, hP⟩).H := by
    rw [hL.grpQ j b ⟨P.1, hP⟩, Subgroup.mem_subgroupOf]
    exact ⟨_, m.1, hx⟩
  refine ⟨hmem, Units.ext ?_⟩
  rw [hL.chrQ j b ⟨P.1, hP⟩ ⟨g, hmem⟩ _ m.1 hx]
  exact m.2

theorem levQ_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (j : ℕ), j < B.R.m → ∀ (b : (I.idx a).β j) (P : SBof I a) (hP : P.1 ∈ I.Q a) (g : Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1), CongE P.1 ((I.cst a).D P) g.1 1 → ∃ h : g ∈ ((I.idx a).levQ j b ⟨P.1, hP⟩).H, ((I.idx a).levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  intro B X I hOk a j hj b P hP g hg
  refine levQ_of_congE (hOk.idx_ok a) j hj b P hP g fun x hx => ?_
  rw [Nat.cast_pow]
  exact hg x hx

end GlobalTheory.Mem.Col2.AdT

end
