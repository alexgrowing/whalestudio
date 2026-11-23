import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.CubeIso

section

variable {X X₁ X₂ Y : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem mem_ext {x : X} {j₁ : L₁.ι} {j₂ : L₂.ι} (h₁ : f₁ x ∈ L₁.U j₁) (h₂ : f₂ x ∈ L₂.U j₂) :
    x ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) :=
  ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
        (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂'))
      ((extLB L₁ L₂ f₁ f₂).g (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂')) =
      gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') * gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') := by
  have hm : r z ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
      (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂') := ⟨mem_ext h₁ h₂, mem_ext h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hm _).trans ?_) ((gm_res r z _ hm _).trans ?_))
  · exact gm_pull_g L₁ f₁ r z (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g L₂ f₂ r z (fun _ => j₂) (fun _ => j₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

def ev (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) (k : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓ L.U k)
    (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k))

theorem ev_trans {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι) (k k' : L.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂')
    (h : r z ∈ L.U k) (h' : r z ∈ L.U k') :
    ev w r z j₁ j₂ k = gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') *
      gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') * (gm r z (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        ev w r z j₁' j₂' k' := by
  rw [← gm_ext_g r z j₁ j₁' j₂ j₂' h₁ h₁' h₂ h₂']
  exact AdjComp.gm_iso hw r z (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂', k')
    ⟨mem_ext h₁ h₂, h⟩ ⟨mem_ext h₁' h₂', h'⟩

theorem exists_linComb (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (w₀ : LB.Iso L (extLB L₁ L₂ f₁ f₂))
    (hw₀ : w₀.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ₁ : K → (Y ⟶ X₁)) (ε : K → ℤ) (σ : K → K)
    (h₁ : ∀ k, φ k ≫ f₁ = φ₁ k) (h₂ : ∀ k, φ k ≫ f₂ = φ (σ k) ≫ f₂)
    (hε : ∀ (G : Type) [CommGroup G] (a : K → G), (∀ k, a k = a (σ k)) → ∏ k, a k ^ ε k = 1) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L₁ φ₁ ε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (jC : K → L₁.ι) (jA : K → L.ι) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ φ₁ jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) →
        gm f z (LB.wchart L₁ φ₁ jC ⊓ LB.wchart L φ jA) (w.s (jC, jA)) =
          ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
  obtain rfl : (fun k => φ k ≫ f₁) = φ₁ := funext h₁
  have cover : ∀ y : Y, ∃ β : K → L₂.ι, (∀ k, f₂ (φ k y) ∈ L₂.U (β k)) ∧ ∀ k, β k = β (σ k) := fun y => by
    choose c hc using exists_chart hL₂
    exact ⟨fun k => c ((φ k ≫ f₂) y), fun k => hc _, fun k => congrArg (fun q : Y ⟶ X₂ => c (q y)) (h₂ k)⟩
  have glue : ∀ (jC : K → L₁.ι) (jA : K → L.ι),
      ∃ s : Γ(Y, LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ (fun k => φ k ≫ f₁) jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) → gm f z _ s = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
    intro jC jA
    let W : {β : K → L₂.ι // ∀ k, β k = β (σ k)} → Y.Opens := fun β =>
      LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA ⊓ LB.wchart L₂ (fun k => φ k ≫ f₂) β.1
    have l₀ : ∀ β, W β ≤ LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA := fun β => inf_le_left
    have l₁ : ∀ β k, W β ≤ φ k ⁻¹ᵁ
        ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k)) ⊓ L.U (jA k)) := fun β k y hy =>
      ⟨mem_ext (Set.mem_iInter.1 hy.1.1 k) (Set.mem_iInter.1 hy.2 k), Set.mem_iInter.1 hy.1.2 k⟩
    let u : ∀ β, Γ(Y, W β)ˣ := fun β => ∏ k, res (l₁ β k)
      (pullU (φ k) _ (w₀.s (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k), jA k))) ^ ε k
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) β (hz : f z ∈ W β),
        gm f z (W β) (u β) = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β.1 k) (jA k) ^ ε k := fun Z f z β hz =>
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res f z (l₁ β k) hz _).trans (gm_pull f (φ k) z _ (l₁ β k hz) _))))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨β, hβ, hβ'⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨β, hβ'⟩, hy, Set.mem_iInter.2 hβ⟩) u (fun β β' y hy => by
        rw [hu _ (𝟙 Y) y β hy.1, hu _ (𝟙 Y) y β' hy.2]
        have a : ∀ k, ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β.1 k) (jA k) =
            gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k)) *
              ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β'.1 k) (jA k) := fun k => by
          have m₁ : f₁ (φ k y) ∈ L₁.U (jC k) := Set.mem_iInter.1 hy.1.1.1 k
          have m : φ k y ∈ L.U (jA k) := Set.mem_iInter.1 hy.1.1.2 k
          rw [Category.id_comp, ev_trans hw₀ (φ k) y (jC k) (jC k) (β.1 k) (β'.1 k) (jA k) (jA k) m₁ m₁
            (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k) m m, gm_self hL₁ (φ k ≫ f₁) y m₁,
            gm_self hL (φ k) y m, _root_.one_mul, inv_one, _root_.mul_one]
        simp only [a, mul_zpow, Finset.prod_mul_distrib]
        rw [hε _ (fun k => gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k))) (fun k => by
          have key : ∀ (q q' : Y ⟶ X₂) (i i' j j' : L₂.ι), q = q' → i = i' → j = j' →
              gm q y (L₂.U i ⊓ L₂.U j) (L₂.g i j) = gm q' y (L₂.U i' ⊓ L₂.U j') (L₂.g i' j') := by
            rintro _ _ _ _ _ _ rfl rfl rfl; rfl
          exact key _ _ _ _ _ _ (h₂ k) (β.2 k) (β'.2 k)), _root_.one_mul])
    refine ⟨s, fun Z f z β hC hA hβ hβ' => ?_⟩
    have hy : f z ∈ W ⟨β, hβ'⟩ := ⟨⟨hC, hA⟩, Set.mem_iInter.2 hβ⟩
    exact (gm_res f z (l₀ ⟨β, hβ'⟩) hy s).symm.trans
      ((congrArg (gm f z (W ⟨β, hβ'⟩)) (hs ⟨β, hβ'⟩)).trans (hu Z f z ⟨β, hβ'⟩ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z f z jC jA β hC hA hβ hβ' => hs jC jA Z f z β hC hA hβ hβ'⟩
  obtain ⟨β, hβ, hβ'⟩ := cover y
  have e₁ := hs i.1 i.2 _ (𝟙 Y) y β hy.1.1 hy.1.2 hβ hβ'
  have e₂ := hs j.1 j.2 _ (𝟙 Y) y β hy.2.1 hy.2.2 hβ hβ'
  have gC := gm_linComb L₁ (fun k => φ k ≫ f₁) ε (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
  have gA := gm_linComb L φ ε (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
  refine (gm_res (𝟙 Y) y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) ((gm_div (LB.LinComb L φ ε) (LB.LinComb L₁ (fun k => φ k ≫ f₁) ε) (𝟙 Y) y i j hy).trans
    (congrArg₂ (fun a b => a * b⁻¹) gC gA)) ((gm_res (𝟙 Y) y _ hy _).trans e₂)).trans ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Category.id_comp]
  rw [ev_trans hw₀ (φ k) y (i.1 k) (j.1 k) (β k) (β k) (i.2 k) (j.2 k) (Set.mem_iInter.1 hy.1.1 k)
    (Set.mem_iInter.1 hy.2.1 k) (hβ k) (hβ k) (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k),
    gm_self hL₂ (φ k ≫ f₂) y (hβ k), _root_.mul_one, mul_zpow, mul_zpow, inv_zpow]

end

theorem cancel_two (G : Type) [CommGroup G] (a : ULift.{0} (Finset (Fin 2)) → G)
    (h : ∀ I, a I = a ⟨insert 0 I.down⟩) : ∏ I, a I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  rw [← Equiv.prod_comp (Equiv.ulift.{0}.symm : Finset (Fin 2) ≃ ULift.{0} (Finset (Fin 2)))]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e₀ : a ⟨∅⟩ = a ⟨{0}⟩ := h ⟨∅⟩
  have e₁ : a ⟨{1}⟩ = a ⟨{0, 1}⟩ := h ⟨{1}⟩
  show a ⟨∅⟩ ^ (1 : ℤ) * (a ⟨{0}⟩ ^ (-1 : ℤ) * (a ⟨{1}⟩ ^ (-1 : ℤ) * a ⟨{0, 1}⟩ ^ (1 : ℤ))) = 1
  rw [e₀, e₁]
  simp

end GlobalTheory.MumProd.CubeIso

namespace GlobalTheory.MumProd

theorem exists_cubeIso : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  intro S B B₁ B₂ T _ _ _ _ _ _ M M₁ M₂ hM hM₁ hM₂ p₁ p₂ wM hwM x x₁ h₁ h₂
  obtain ⟨w, hw, H⟩ := CubeIso.exists_linComb hM hM₁ hM₂ wM hwM (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B x I.down).left) (fun I => (psum B₁ x₁ I.down).left) (fun I => (-1) ^ (2 - I.down.card))
    (fun I => ⟨insert 0 I.down⟩) (fun I => by rw [← Over.comp_left, h₁])
    (fun I => by rw [← Over.comp_left, ← Over.comp_left, h₂]) CubeIso.cancel_two
  exact ⟨w, hw, fun Z f z jC jA β hC hA hβ hβ' => H Z f z jC jA β hC hA hβ hβ'⟩

end GlobalTheory.MumProd
