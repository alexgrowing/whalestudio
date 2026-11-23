import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
open GlobalTheory.TopStep Formalism.HermitianLatticesTheory
noncomputable section

namespace GlobalTheory.Mem.Df

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (C : ChainIn X.E X.K X.Tau R) (b0 : (C.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (C.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (C.S R.m).G b0) (tz : X.E)

@[reducible] def perStepX : PerIn C where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H _ := ⊤

variable (σ : X.K →+* ℂ)

theorem mem_perStepX_Mt (F : ∀ b, (stepX Ch sel mu P).D b → Pol ℂ X.Tau (R.N R.m - 1)) :
    F ∈ (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ ↔
      FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F () (trivPt X _ _ _ _ p) := by
  constructor
  · intro h p
    refine ⟨(h () _).1, fun g hg => ?_⟩
    show F () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (h () (trivPt X _ _ _ _ p)).2 g hg
  · rintro h ⟨⟩ d
    obtain ⟨p, rfl⟩ := (trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).surjective d
    refine ⟨(h p).1, fun g hg => ?_⟩
    exact (congrArg (F ()) (stepX_smul_trivPt Ch sel mu P g p)).trans ((h p).2 g hg)

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

def mtEquivStepX : MtP W Ch sel mu P σ ≃ₗ[ℂ] (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ :=
  LinearEquiv.ofBijective
    { toFun := fun F => ⟨fun _ p => F.1 (toRow sel mu p.1.1),
        (mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ _).2
          ((frLaw_comp_iff σ W.sgTrue (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd F.1).2 F.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨fun F G h => Subtype.ext (funext fun d => by
      obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
      exact congrFun (congrFun (congrArg Subtype.val h) ()) (trivPt X _ _ _ _ p)),
    fun F => by
      obtain ⟨G, hG, e⟩ := ((mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ F.1).1 F.2).exists_form σ W.sgTrue
        (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd
      refine ⟨⟨G, hG⟩, Subtype.ext (funext fun _ => funext fun p => (e p.1.1).trans ?_)⟩
      exact congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p)⟩

end General

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_vGs_Q (hI : I.Ok) (l : I.Laws) (a : I.ι) : Disjoint (B.primes X).vGs (I.Q a) :=
  GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup a) l.pr hI.sel_ok (fun i => hI.g_mem i)

theorem mtCx_equiv_per : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  intro B X I hI _ l _ u a
  let g := mtEquivStepX B.wts I.Ch I.sel (I.tup a) I.Ps (I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext
    (I.perIn u a).tz B.embLL (disjoint_vGs_Q I hI l a)
  exact ⟨g, fun F p => rfl⟩

end GlobalTheory.Mem.Df

end
