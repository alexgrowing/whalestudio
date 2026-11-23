import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GlueSection
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem wI_cP (B : Blow q i π D d) (α : B.ι) : wI B α ≫ cP B = (oW B α).ι := by
  unfold wI cP
  exact Sigma.ι_desc _ _

private theorem mem_V (B : Blow q i π D d) {U : Scheme.{0}} {p : U ⟶ W} {α : B.ι}
    (c : U ⟶ (oW B α : Scheme.{0})) (h : p = c ≫ (oW B α).ι) (y : U) : (p ≫ i) y ∈ B.V α := by
  subst h
  have h₁ : (c y).1 ∈ oW B α := (c y).2
  have h₂ : i (c y).1 ∈ B.V α := h₁
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact h₂

private theorem exists_loc (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B)
    (h : a ≫ cP B = b ≫ cP B) (x : V) :
    ∃ (U : V.Opens) (α β : B.ι) (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
      (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)), x ∈ U ∧
      U.ι ≫ a = a₁ ≫ wI B α ∧ U.ι ≫ b = b₁ ≫ wI B β ∧ LocMat B α β (U.ι ≫ a ≫ cP B) M := by
  obtain ⟨U₁, α, a₀, hx₁, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  obtain ⟨U₂, β, b₀, hx₂, hb⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) b x
  have ha' : (U₁ ⊓ U₂).ι ≫ a = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ wI B α := by
    have ha₀ : U₁.ι ≫ a = a₀ ≫ wI B α := ha
    rw [Category.assoc, ← ha₀, ← Category.assoc, Scheme.homOfLE_ι]
  have hb' : (U₁ ⊓ U₂).ι ≫ b = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ wI B β := by
    have hb₀ : U₂.ι ≫ b = b₀ ≫ wI B β := hb
    rw [Category.assoc, ← hb₀, ← Category.assoc, Scheme.homOfLE_ι]
  have e₁ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ (oW B α).ι := by
    rw [← Category.assoc, ha', Category.assoc, wI_cP]
  have e₂ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ (oW B β).ι := by
    rw [h, ← Category.assoc, hb', Category.assoc, wI_cP]
  obtain ⟨M, hM⟩ := locMatExists B α β ((U₁ ⊓ U₂).ι ≫ a ≫ cP B)
    (fun y => ⟨mem_V B _ e₁ y, mem_V B _ e₂ y⟩)
  exact ⟨U₁ ⊓ U₂, α, β, _, _, M, ⟨hx₁, hx₂⟩, ha', hb', hM⟩

private theorem compat (B : Blow q i π D d) {V S : Scheme.{0}} (a b : V ⟶ WP B) {U U' : V.Opens}
    (f : S ⟶ (U : Scheme.{0})) (f' : S ⟶ (U' : Scheme.{0})) (e : f ≫ U.ι = f' ≫ U'.ι)
    {α β α' β' : B.ι} (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
    (a₁' : (U' : Scheme.{0}) ⟶ oW B α') (b₁' : (U' : Scheme.{0}) ⟶ oW B β')
    (ha : U.ι ≫ a = a₁ ≫ wI B α) (hb : U.ι ≫ b = b₁ ≫ wI B β)
    (ha' : U'.ι ≫ a = a₁' ≫ wI B α') (hb' : U'.ι ≫ b = b₁' ≫ wI B β')
    (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)) (M' : Matrix (Fin d) (Fin d) Γ((U' : Scheme.{0}), ⊤))
    (hM : LocMat B α β (U.ι ≫ a ≫ cP B) M) (hM' : LocMat B α' β' (U'.ι ≫ a ≫ cP B) M') :
    M.map f.appTop.hom = M'.map f'.appTop.hom := by
  by_cases hS : Nonempty S
  · obtain ⟨s⟩ := hS
    have ea : (f ≫ a₁) ≫ wI B α = (f' ≫ a₁') ≫ wI B α' := by
      rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, e]
    have eb : (f ≫ b₁) ≫ wI B β = (f' ≫ b₁') ≫ wI B β' := by
      rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, e]
    obtain rfl : α = α' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s ea
    obtain rfl : β = β' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s eb
    have n₁ := locMatNat B α β f _ M hM
    have n₂ := locMatNat B α β f' _ M' hM'
    have ep : f ≫ U.ι ≫ a ≫ cP B = f' ≫ U'.ι ≫ a ≫ cP B := by
      rw [← Category.assoc, e, Category.assoc]
    rw [ep] at n₁
    exact locMatUnique B α β _ _ _ n₁ n₂
  · have : IsEmpty S := not_nonempty_iff.mp hS
    ext r c
    exact sectionExt _ _ (fun x => isEmptyElim x)

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), GMat B a b M := by
  intro K _ W Z Y q i π D d B V a b h
  choose U α β a₁ b₁ M hx ha hb hM using exists_loc B a b h
  have hg : ∀ r c, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = M x r c := fun r c =>
    glueSection U hx (fun x => M x r c) (fun x y S f f' e => by
      have h₁ := compat B a b f f' e (a₁ x) (b₁ x) (a₁ y) (b₁ y) (ha x) (hb x) (ha y) (hb y)
        (M x) (M y) (hM x) (hM y)
      exact congrFun (congrFun h₁ r) c)
  choose G hG using hg
  refine ⟨Matrix.of G, fun x => ⟨U x, α x, β x, a₁ x, b₁ x, hx x, ha x, hb x, ?_⟩⟩
  have e : (Matrix.of G).map (U x).ι.appTop.hom = M x := by
    ext r c
    exact hG r c x
  rw [e]
  exact hM x
