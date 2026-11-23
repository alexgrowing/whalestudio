import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

open GlobalTheory.Mem.Col2.StepZero

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

theorem cl_rep_reRep (k : ((stepY ST y β Λ Θ pref).reRep pf).Cl) :
    (stepY ST y β Λ Θ pref).cl k.1 (((stepY ST y β Λ Θ pref).reRep pf).rep k) = k := by
  obtain ⟨b, q⟩ := k
  exact congrArg (Sigma.mk b) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

def secRe [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    have e1 := clMap_cl (y := y) (Θ := Θ) (Λ₀ := Λ₀) pref lam hΛ ((clEquiv pref lam hy hΛ hΘ).symm c).1
      (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))
    have e2 := cl_rep_reRep pref pf ((clEquiv pref lam hy hΛ hΘ).symm c)
    exact e1.symm.trans ((congrArg (clMap (Λ₀ := Λ₀) pref lam) e2).trans ((clEquiv pref lam hy hΛ hΘ).apply_symm_apply c))

theorem mem_lat_reRep [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) (x : (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).V) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    x ∈ (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).L ↔ φ ∈ (base ST lam Λ₀).intDel := by
  rw [(base ST lam Λ₀).mem_intDel_iff h₀ (secRe pref lam pf hy hΛ hΘ)]
  refine (clEquiv pref lam hy hΛ hΘ).symm.surjective.forall.trans (forall_congr' fun c => ?_)
  show x.1 _ ∈ _ ↔ _
  rw [hx]
  rfl

end Gen

theorem colStep0_mem_lat : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → (x ∈ ((I.fm l u a).lat 0).L ↔ φ ∈ MfL (Pr := B.primes X) B.wts I.Ch u) := by
  intro B X I h hX l u a x φ hc
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have h₀ := colOk B.wts I.Ch hX u 0
  have key := mem_lat_reRep ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a))
    (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL) ((l.fmL u a).fam 0) h₀
  exact key x φ hc

end GlobalTheory.Core.Ht2

end
