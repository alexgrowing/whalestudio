import Development.EtaleCohomology.EtaleSheaves.LineOneCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartSurjCut

def Root : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  AICSch Z → IsUnit (q : A) → Nonempty (Prim q Γ(Z, ⊤))

def LCIso : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Ht q (sch.obj X) 0 i,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      pull _ (sch.map f) (tw q i) 0 (e X s g) = e Y t (g.comap f.base.hom)

def LCSurj : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem goal_of (hR : Root) (hL : LCIso) (hT : LCSurj) : ChartSurj := by
  unfold Root at hR
  unfold LCIso at hL
  unfold LCSurj at hT
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.ChartSurjCut
