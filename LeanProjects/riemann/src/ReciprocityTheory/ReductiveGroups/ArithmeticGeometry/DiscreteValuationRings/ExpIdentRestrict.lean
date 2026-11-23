import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

def ExpIdent (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) : Prop :=
  ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      j₁ 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res (inf_le_left.trans inf_le_left :
          U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
          U.expW e p j₁ S jf jt ≤
            (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
          (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

lemma sum_attach_mono {X β : Type} [AddCommMonoid β] {S S' : Finset X} (hSS : S ⊆ S')
    (T : S' → β) (h0 : ∀ α : S', α.1 ∉ S → T α = 0) :
    ∑ α ∈ S'.attach, T α = ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ := by
  classical
  set g : X → β := fun α => if h : α ∈ S' then T ⟨α, h⟩ else 0 with hg
  have h1 : ∑ α ∈ S'.attach, T α = ∑ α ∈ S', g α := by
    rw [← Finset.sum_attach S' g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos α.2]
  have h2 : ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ = ∑ α ∈ S, g α := by
    rw [← Finset.sum_attach S g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos (hSS α.2)]
  rw [h1, h2]
  exact (Finset.sum_subset hSS fun α hα' hα => by
    simp only [hg, dif_pos hα']
    exact h0 ⟨α, hα'⟩ hα).symm

theorem expIdent_mono (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) {S S' : Finset D.toPre.X} (hSS : S ⊆ S')
    (hvan : ∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0)
    (h : ExpIdent U e k σ f S) : ExpIdent U e k σ f S' := by
  classical
  intro p j₁ jf jt hj hcoh'
  set m : PUnit.{1} ⊕ ((S × Fin 4) ⊕ (S × Fin 4)) → PUnit.{1} ⊕ ((S' × Fin 4) ⊕ (S' × Fin 4)) :=
    Sum.map id (Sum.map (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)) (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)))
    with hm
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    intro a b hab
    have h1 := hcoh' (m a) (m b) (by
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact hab)
    rcases a with a | a | a <;> rcases b with b | b | b <;> exact h1
  have hS := h p j₁ jf jt hj hcoh
  have hle : U.expW e p j₁ S' jf jt ≤ U.expW e p j₁ S jf jt :=
    inf_le_inf_left _ (Finset.inf_mono hSS)
  have key := congrArg (rs hle) hS
  simp only [rs, res, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_sum] at key
  rw [sum_attach_mono hSS _ (fun α hα => by
    have h0 := hvan α.1 hα (jf α.1)
    erw [h0, map_zero, zero_mul])]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at key
  convert key using 4
  all_goals first | rfl | exact Subsingleton.elim _ _ | skip
  all_goals (erw [Units.coe_map, Units.coe_map]; exact (rs_rs _ hle _).symm)

lemma map_map_hom {Z : Scheme.{0}} {U W V : Z.Opens} (h : W ≤ U) (h' : V ≤ W) (x : Γ(Z, U)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE h).op).hom x) =
      (Z.presheaf.map (homOfLE (h'.trans h)).op).hom x := rs_rs h h' x

lemma sum_attach_dite {X β : Type} [DecidableEq X] [AddCommMonoid β] (S : Finset X) (g : S → β) :
    ∑ x ∈ S.attach, g x = ∑ x ∈ S, (if h : x ∈ S then g ⟨x, h⟩ else 0) := by
  rw [← Finset.sum_attach S (fun x => if h : x ∈ S then g ⟨x, h⟩ else 0)]
  exact Finset.sum_congr rfl fun x _ => by simp only [dif_pos x.2]

theorem expIdent_restrict [DecidableEq D.toPre.X] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (h : ExpIdent U e k σ f S)
    (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
    (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) (hj : j₁ 0 = p.2 PUnit.unit)
    (hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))))
    {O : (thickObj R I e G).left.Opens} (hO : O ≤ U.expW e p j₁ S jf jt) :
    (res (hO.trans (inf_le_left.trans inf_le_left)) ((U.w e).s p)).val ^ k *
        rs (hO.trans (inf_le_left.trans inf_le_right)) (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S, (if hα : α ∈ S then rs (hO.trans (U.expW_le_f e p j₁ jf jt hα))
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))) *
        (res (hO.trans (U.expWeight_le_chart_weight e p j₁ jf jt hα)) (((U.gt e).t α).s (jt α))).val else 0) := by
  have key := congrArg (rs hO) (h p j₁ jf jt hj hcoh)
  simp only [rs, res, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_sum, map_map_hom] at key
  rw [sum_attach_dite] at key
  refine key.trans (Finset.sum_congr rfl fun α hα => ?_)
  simp only [dif_pos hα]
  congr 1
  erw [Units.coe_map, map_map_hom]
  rfl

theorem expIdent_pull [DecidableEq D.toPre.X] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (h : ExpIdent U e k σ f S)
    (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
    (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) (hj : j₁ 0 = p.2 PUnit.unit)
    (hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))))
    {Z : Scheme.{0}} (hh : Z ⟶ (thickObj R I e G).left) {O : Z.Opens}
    (hO : O ≤ hh ⁻¹ᵁ U.expW e p j₁ S jf jt) :
    rs hO ((hh.app _).hom (res (inf_le_left.trans inf_le_left :
        U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
          (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val) ^ k *
      rs hO ((hh.app _).hom (rs (inf_le_left.trans inf_le_right : U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)
        (((fstG I e G).left.app _).hom (σ.f j₁)))) =
      ∑ α ∈ S, (if hα : α ∈ S then
        rs hO ((hh.app _).hom (rs (U.expW_le_f e p j₁ jf jt hα)
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))))) *
        rs hO ((hh.app _).hom (res (U.expWeight_le_chart_weight e p j₁ jf jt hα) (((U.gt e).t α).s (jt α))).val)
        else 0) := by
  have key := expIdent_restrict U e k σ f S h p j₁ jf jt hj hcoh (le_refl _)
  have key2 := congrArg (fun x => rs hO ((hh.app _).hom x)) key
  simp only [map_mul, map_pow, map_sum] at key2
  refine key2.trans (Finset.sum_congr rfl fun α hα => ?_)
  simp only [dif_pos hα, map_mul]

end ReciprocityTheory.ChartRestriction.G.DVR
