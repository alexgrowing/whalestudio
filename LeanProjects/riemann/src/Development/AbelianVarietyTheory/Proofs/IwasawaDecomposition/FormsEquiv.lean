import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDecoStatement

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.StepZero

section Gen
open _root_.Formalism.L2.Forms
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c γ
  have hγ : (γ : S.G c.1) = 1 := hS c.1 γ (S.rp c.1 c.2) γ.2
  show (S.rho emb lam c.1) (γ : S.G c.1) (x c) = x c
  rw [hγ, map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let f : S.FormsK emb lam hF →ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : S'.FormsK emb lam hF' →ₗ[K] S.FormsK emb lam hF :=
    { toFun := fun y => ⟨fun c => y.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, ?_, ?_⟩
  · ext y c
    simp [f, g]
  · ext x c
    simp [f, g]
  · intro x
    constructor
    · intro hx c
      have h1 := hx (e0.symm c)
      have h2 := hL (e0.symm c)
      rw [Equiv.apply_symm_apply] at h2
      show x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh c.1 (S'.rep c))
      rw [h2]
      exact h1
    · intro hx c
      have h1 : x.1 (e0.symm (e0 c)) ∈ delAtr emb lam (S'.Lsh (e0 c).1 (S'.rep (e0 c))) := hx (e0 c)
      rw [hL c, Equiv.symm_apply_apply] at h1
      exact h1
  · intro x
    rfl
end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1600000 in

theorem law0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ l : I.Laws, I.Law0 l := by
  intro B X I hI l u a
  obtain ⟨e, he1, he2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u I.mu0).free0 (l.lev u a).free0 ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    (fun c => by
      have h := (GlobalTheory.T.cl0_bijective_and_deco_eq I hI u a (l.idx0 a).some).2 c
      show ((I.stp u a 0).rep (I.cl0 u a (l.idx0 a).some c)).1.1.deco.1.Lsh = ((I.stp u I.mu0 0).rep c).1.1.deco.1.Lsh
      rw [h])
  exact ⟨e, he1, fun x => he2 x⟩

end GlobalTheory.Mem.Col2.StepZero

end
