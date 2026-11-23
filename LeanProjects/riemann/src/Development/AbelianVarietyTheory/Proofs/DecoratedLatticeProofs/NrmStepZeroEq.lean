import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
