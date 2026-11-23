import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIdG_unique (X : Stages) {px : PreX X.B.toPre} {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    {eG eG' : Gc X.B px ≃* G0 Pg X.toD7.R.r} (h : IsPlacewiseIdentity X (px := px) eG) (h' : IsPlacewiseIdentity X (px := px) eG') : eG = eG' := by
  subst hPg
  exact MulEquiv.ext fun g => funext fun P => (h g P.1 P.2 P.2).trans (h' g P.1 P.2 P.2).symm

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) (h' : IsStdChar D ψ' s) :
    ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem isInfFam_unique {D : D7} {θ θ' : Formalism.IndefR.Datum.InfFam D} (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  Formalism.IndefR.Eqv.infFamUnique_holds D θ θ' h h'

theorem exists_emb_of_range_le {K L : Type} [Field K] [Field L] (f : K →+* ℂ) (g : L →+* ℂ) (h : Set.range f ⊆ Set.range g) :
    ∃ ι : K →+* L, ∀ x, g (ι x) = f x := by
  let incl : K →+* g.fieldRange := f.codRestrict g.fieldRange fun x => by
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    exact ⟨y, hy⟩
  refine ⟨(RingHom.rangeRestrictFieldEquiv g).symm.toRingHom.comp incl, fun x => ?_⟩
  have := congrArg Subtype.val ((RingHom.rangeRestrictFieldEquiv g).apply_symm_apply (incl x))
  simpa [incl] using this

open Formalism.IndefR.Mult in

theorem parAt_enl (X X' : Stages) (hB : X'.B.toPre = X.B.toPre) (ι : X.toD7.what₂.LL →+* X'.toD7.what₂.LL)
    (hι : ∀ x, X'.toD7.what₂.embLL (ι x) = X.toD7.what₂.embLL x) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (σ' : X'.toD7.what₂.LL →+* ℂ) : HEq (parAt (Wc X'.toD7 i') σ') (parAt (Wc X.toD7 i) (σ'.comp ι)) := by
  obtain ⟨⟨P, LL, eL, _, eE, eφ⟩, C, W, V, S, N, G⟩ := X
  obtain ⟨⟨P', LL', eL', _, eE', eφ'⟩, C', W', V', S', N', G'⟩ := X'
  dsimp only at hB
  subst hB
  obtain ⟨i, hi0⟩ := i
  obtain ⟨i', hi1⟩ := i'
  dsimp only at hi
  subst hi
  have hE : ∀ x, ι (eE x) = eE' x := fun x => by
    apply eL'.injective
    have h1 := congrArg (fun f => f x) eφ
    have h2 := congrArg (fun f => f x) eφ'
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    exact (hι (eE x)).trans (h1.trans h2.symm)
  apply heq_of_eq
  funext ρ
  have hc : ∀ τ, labE σ' τ = labE (σ'.comp ι) τ := fun τ => by
    ext x
    simp only [labE, labLL, RingHom.coe_comp, Function.comp_apply]
    exact congrArg σ' (hE _).symm
  have hl : labE σ' = labE (σ'.comp ι) := funext hc
  unfold parAt kapAt lab
  erw [hl]
  rfl

end GlobalTheory.Mem.R3.Rw

end
