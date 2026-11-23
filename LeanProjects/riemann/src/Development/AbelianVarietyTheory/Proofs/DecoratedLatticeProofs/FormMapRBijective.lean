import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

noncomputable section

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (pr : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)
  (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}

def clMapR (c : ((stepY ST y β Λ Θ pref).reRep pr).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco

theorem clMapR_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMapR (Λ₀ := Λ₀) pref pr lam (((stepY ST y β Λ Θ pref).reRep pr).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  have e := congrArg (fun q : (stepY ST y β Λ Θ pref).D b => q.1.1.deco) (((stepY ST y β Λ Θ pref).reRep pr).mv_smul b p)
  rw [← e]
  exact ((base ST lam Λ₀).cls_smul (down (y := y) pref hΛ b (((stepY ST y β Λ Θ pref).reRep pr).mv b p)) _).symm

theorem clMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMapR (Λ₀ := Λ₀) pref pr lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim (α := β) _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q, ← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨((stepY ST y β Λ Θ pref).reRep pr).cl default p, clMapR_cl pref pr lam hΛ default p⟩

def clEquivR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    ((stepY ST y β Λ Θ pref).reRep pr).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMapR_bijective pref pr lam hy hΛ hΘ)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pr).rep ((clEquivR pref pr lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := (clEquivR pref pr lam hy hΛ hΘ).apply_symm_apply c

def formMapR (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok) :
    (base ST lam Λ₀).EqFun →ₗ[X.K] ((stepY ST y β Λ Θ pref).reRep pr).FormsK X.emb lam h where
  toFun φ := ⟨fun c => φ.1 (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco, fun c g =>
    (form_smul pref lam hΛ hΘ φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) :
    Function.Bijective (formMapR pref pr lam hΛ hΘ h) := by
  refine ⟨fun φ ψ e => ?_, fun f => ?_⟩
  · apply ((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).injective
    apply Subtype.ext
    funext c
    exact congrFun (congrArg Subtype.val e) ((clEquivR pref pr lam hy hΛ hΘ).symm c)
  · let f₀ : ((base ST lam Λ₀).toCSDOf h₀ (secR pref pr lam hy hΛ hΘ)).Forms :=
      ⟨fun c => f.1 ((clEquivR pref pr lam hy hΛ hΘ).symm c), fun c g₀ => by
        obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ _ _ _ g₀.1 g₀.2
        have h3 := f.2 ((clEquivR pref pr lam hy hΛ hΘ).symm c) ⟨g, h2⟩
        have h4 := rho_eq pref lam hΛ hΘ _ g
        rw [h1] at h4
        exact (LinearMap.congr_fun h4 _).symm.trans h3⟩
    refine ⟨((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).symm f₀, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c₀, rfl⟩ := (clEquivR pref pr lam hy hΛ hΘ).symm.surjective c
    exact congrFun (congrArg Subtype.val
      (((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).apply_symm_apply f₀)) c₀

end Forget

theorem exists_colZeroR {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
    {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
    (pr : ∀ b, (stepAt sel mu cst L Tp u 0).D b → Prop) (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2)
    (h : (((stepAt sel mu cst L Tp u 0).reRep pr).fam X.emb (lamT (W.hc u) 0)).Ok) :
    ∃ κ : MfV W Ch u ≃ₗ[X.K] ((stepAt sel mu cst L Tp u 0).reRep pr).FormsK X.emb (lamT (W.hc u) 0) h,
      ∀ φ c, (κ φ).1 c = φ.1 (((stepAt sel mu cst L Tp u 0).reRep pr).rep c).1.1.deco :=
  letI := idxUnique hL
  ⟨LinearEquiv.ofBijective _ (formMapR_bijective (Tp.pref u 0) pr (lamT (W.hc u) 0) (ysAt_zero sel mu cst)
    (levGAt_zero Tp hL) (levQAt_zero Tp hL) h (colOk W Ch hX u 0)), fun _ _ => rfl⟩

end GlobalTheory.Core.ColZero

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_colEquiv {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) :
    ∃ κ : ColsK I u ≃ₗ[B.fields.K] ((I.fm l u a).lat 0).V, ∀ φ, IsCol I u a l (κ φ) φ :=
  exists_colZeroR (Pr := B.primes X) B.wts (I.Tp a) u (I.pref u a 0) hX (h.idx_ok a) ((l.fmL u a).fam 0)

end GlobalTheory.Core.ColZero

end
