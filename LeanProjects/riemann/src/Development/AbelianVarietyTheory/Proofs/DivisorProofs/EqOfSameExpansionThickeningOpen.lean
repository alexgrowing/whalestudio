import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

theorem map_map_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem map_res_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h2).op).hom (res h1 u).val = (res (h2.trans h1) u).val :=
  map_map_homOfLE h1 h2 u.val

theorem sum_attach_eq_sum_of_subset {β M : Type*} [AddCommMonoid M] {S S' : Finset β} (hS : S ⊆ S') (F : β → M)
    (T : S → M) (hT : ∀ x, T x = F x) (hz : ∀ α ∈ S', α ∉ S → F α = 0) :
    ∑ x ∈ S.attach, T x = ∑ α ∈ S', F α := by
  rw [← Finset.sum_subset hS hz, ← Finset.sum_attach S F]
  exact Finset.sum_congr rfl fun x _ => hT x

theorem eq_of_expandsAt_of_chartExpOn : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  intro R _ _ I D A G _ _ U e k σ f i' W hW g hE hC
  classical
  obtain ⟨S₁, h1v, E1⟩ := hE
  obtain ⟨S₂, h2v, E2⟩ := hC
  have hex : ∀ x : D.toPre.P.A.left, ∃ i, x ∈ D.toPre.P.L.U i := fun x => by
    have hx : x ∈ (⨆ i, D.toPre.P.L.U i) := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  choose idx0 hidx0 using hex
  have key : ∀ y ∈ W, ∃ (V : (thickObj R I e G).left.Opens) (hV : V ≤ W), y ∈ V ∧
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom
        (((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom
          (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i'))) =
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom g := by
    intro y hy
    let idx : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun φ => idx0 (φ.base y)
    have hidx : ∀ φ, φ.base y ∈ D.toPre.P.L.U (idx φ) := fun φ => hidx0 _
    let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => idx (U.gt e).pG.left, fun _ => i' 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx ((U.gt e).pG.left ≫ D.toPre.famφB α κ)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx (D.toPre.Oφ (U.gt e).pG α κ)
    have hcoh : ∀ S : Finset D.toPre.X, CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      intro S a b hab
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact congrArg idx hab
    have hmem : ∀ S, y ∈ U.expW e p i' S jf jt := by
      intro S
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hidx _, Set.mem_iInter.2 fun _ => ?_⟩, hW hy⟩, ?_⟩
      · exact Set.mem_iInter.1 (hW hy) 0
      · refine Finset.inf_induction (p := fun O : (thickObj R I e G).left.Opens => y ∈ O) trivial
          (fun a ha b hb => ⟨ha, hb⟩) ?_
        intro α _
        exact ⟨Set.mem_iInter.2 fun κ => hidx ((U.gt e).pG.left ≫ D.toPre.famφB α κ),
          Set.mem_iInter.2 fun κ => hidx _⟩

    have hV1 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₁ jf jt :=
      inf_le_left.trans (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_left))
    have hV2 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₂ jf jt ⊓ W :=
      inf_le_inf_right _ (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_right))
    have E1V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV1).op).hom
      (E1 p i' jf jt rfl (hcoh S₁))
    have E2V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV2).op).hom
      (E2 p jf jt rfl (hcoh S₂))
    simp only [map_mul, map_pow, map_sum, map_res_homOfLE, map_map_homOfLE] at E1V E2V
    let tV : ∀ α, α ∈ S₁ ∪ S₂ → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α h => ((thickObj R I e G).left.presheaf.map
          (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt h))).op).hom
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))) *
        (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt h)) (((U.gt e).t α).s (jt α))).val
    let F : D.toPre.X → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α => if h : α ∈ S₁ ∪ S₂ then tV α h else 0
    have hz1 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₁ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h1v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    have hz2 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₂ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h2v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_left F _ (fun x => ?_) hz1] at E1V
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_right F _ (fun x => ?_) hz2] at E2V
    rotate_left
    · simp only [F, dif_pos (Finset.mem_union_right S₁ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    · simp only [F, dif_pos (Finset.mem_union_left S₂ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    refine ⟨U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W, inf_le_right, ⟨hmem _, hy⟩, ?_⟩
    rw [map_map_homOfLE]
    exact ((Units.isUnit _).pow k).mul_left_cancel (E1V.trans E2V.symm)
  choose V hVW hyV hEq using key
  refine TopCat.Sheaf.eq_of_locally_eq' (thickObj R I e G).left.sheaf (fun y : W => V y.1 y.2) W
    (fun y => homOfLE (hVW y.1 y.2)) ?_ _ _ fun y => hEq y.1 y.2
  intro y hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyV y hy⟩

end GlobalTheory.MumMult
