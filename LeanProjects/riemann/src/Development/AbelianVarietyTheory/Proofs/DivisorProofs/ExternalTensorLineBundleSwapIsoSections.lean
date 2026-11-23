import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjointStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdSwap

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem pullU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    pullU f V (res h a) = res (fun _ hx => h hx : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U a) := by
  apply Units.ext
  have e := congrArg (fun q => q.hom a.val) (f.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem swap_le (p : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι) :
    (LB.div (extLB L₂ L₁ f₂ f₁) L).U p ≤ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((p.1.2, p.1.1), p.2) :=
  fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩

def swapIso (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) : LB.Iso L (extLB L₂ L₁ f₂ f₁) where
  s := fun p => res (swap_le p) (w.s ((p.1.2, p.1.1), p.2))

theorem gm_div {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (M N : LB X) (p q : M.ι × N.ι)
    (h : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q) :
    gm f y _ ((LB.div M N).g p q) = gm f y _ (M.g p.1 q.1) * (gm f y _ (N.g p.2 q.2))⁻¹ := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ h _)
    ((map_inv _ _).trans (congrArg _ (gm_res f y _ h _))))

theorem gm_tens {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (M N : LB X) (p q : M.ι × N.ι)
    (h : f y ∈ (tensLB M N).U p ⊓ (tensLB M N).U q) :
    gm f y _ ((tensLB M N).g p q) = gm f y _ (M.g p.1 q.1) * gm f y _ (N.g p.2 q.2) := by
  show gm f y _ (res _ (M.g p.1 q.1) * res _ (N.g p.2 q.2)) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ h _) (gm_res f y _ h _))

theorem g_swap (i j : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι)
    (hle : (LB.div (extLB L₂ L₁ f₂ f₁) L).U i ⊓ (LB.div (extLB L₂ L₁ f₂ f₁) L).U j ≤
      (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((i.1.2, i.1.1), i.2) ⊓ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((j.1.2, j.1.1), j.2)) :
    (LB.div (extLB L₂ L₁ f₂ f₁) L).g i j =
      res hle ((LB.div (extLB L₁ L₂ f₁ f₂) L).g ((i.1.2, i.1.1), i.2) ((j.1.2, j.1.1), j.2)) := by
  apply unit_ext
  intro x hx
  have hx' := hle hx
  have e1 := (gm_div (𝟙 X) x (extLB L₂ L₁ f₂ f₁) L i j hx).trans
    (congrArg (· * _) (gm_tens (𝟙 X) x (L₂.pull f₂) (L₁.pull f₁) i.1 j.1 ⟨hx.1.1, hx.2.1⟩))
  have e2 := (gm_res (𝟙 X) x hle hx _).trans ((gm_div (𝟙 X) x (extLB L₁ L₂ f₁ f₂) L _ _ hx').trans
    (congrArg (· * _) (gm_tens (𝟙 X) x (L₁.pull f₁) (L₂.pull f₂) (i.1.2, i.1.1) (j.1.2, j.1.1) ⟨hx'.1.1, hx'.2.1⟩)))
  exact e1.trans ((congrArg₂ (· * ·) (mul_comm _ _) rfl).trans e2.symm)

theorem externalTensorLineBundleSwapIso_sections (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : (LB.div (extLB L₂ L₁ f₂ f₁) L).ι) :
    (swapIso w).s p = res (swap_le p) (w.s ((p.1.2, p.1.1), p.2)) := rfl

theorem swapIso_isGen {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) : (swapIso w).IsGen := by
  intro i j
  have hle : (LB.div (extLB L₂ L₁ f₂ f₁) L).U i ⊓ (LB.div (extLB L₂ L₁ f₂ f₁) L).U j ≤
      (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((i.1.2, i.1.1), i.2) ⊓ (LB.div (extLB L₁ L₂ f₁ f₂) L).U ((j.1.2, j.1.1), j.2) :=
    fun _ hx => ⟨⟨⟨hx.1.1.2, hx.1.1.1⟩, hx.1.2⟩, ⟨⟨hx.2.1.2, hx.2.1.1⟩, hx.2.2⟩⟩
  have e := congrArg (res hle) (hw ((i.1.2, i.1.1), i.2) ((j.1.2, j.1.1), j.2))
  rw [map_mul] at e
  erw [res_res, res_res] at e
  rw [externalTensorLineBundleSwapIso_sections, externalTensorLineBundleSwapIso_sections]
  erw [res_res, res_res]
  rw [g_swap i j hle]
  exact e

theorem mapsAt₂_swap {Y : Scheme.{0}} {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))}
    (h : MapsAt₂ w p n a b₁ b₂) : MapsAt₂ (swapIso w) p n a b₂ b₁ := by
  intro j₂ j₁ jL
  have hle : p ⁻¹ᵁ (LB.div (extLB L₂ L₁ f₂ f₁) L).U (extIdx (f₁ := f₂) (f₂ := f₁) j₂ j₁, jL) ≤
      p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) :=
    fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  have e := congrArg (res hle) (h j₁ j₂ jL)
  rw [map_mul, map_mul, map_zpow] at e
  erw [res_res, res_res, res_res] at e
  have key : pullU p _ ((swapIso w).s (extIdx j₂ j₁, jL)) = res hle (pullU p _ (w.s (extIdx j₁ j₂, jL))) :=
    pullU_res p (swap_le _) _
  rw [key, mul_comm]
  exact e

section Deg

variable {R : Type} [CommRing R] [IsDomain R]

theorem lift_swap_isIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} (f : T ⟶ A) (g : T ⟶ B)
    (h : IsIso (lift f g)) : IsIso (lift g f) := by
  have e : lift g f = lift f g ≫ lift (snd A B) (fst A B) := by ext <;> simp
  have hs : IsIso (lift (snd A B) (fst A B)) :=
    ⟨⟨lift (snd B A) (fst B A), by ext <;> simp, by ext <;> simp⟩⟩
  rw [e]
  infer_instance

theorem isSumDeg_swap {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X}
    {q₂ : D.X →+ D₂.X} (h : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) : IsSumDeg D D₂ D₁ p₂ p₁ q₂ q₁ := by
  obtain ⟨w, hw, ⟨b₁, b₂, hm, hc₁, hc₂⟩, hψ⟩ := h.w
  refine ⟨h.hom₂, h.hom₁, lift_swap_isIso _ _ h.lim, ?_, h.c_pr₂, h.c_pr₁,
    ⟨swapIso w, swapIso_isGen hw, ⟨b₂, b₁, mapsAt₂_swap hm, hc₂, hc₁⟩, fun x => ?_⟩⟩
  · exact Prod.swap_bijective.comp h.xsum
  · obtain ⟨c₁, c₂, hm', h₁, h₂⟩ := hψ x
    exact ⟨c₂, c₁, mapsAt₂_swap hm', h₂, h₁⟩

end Deg

theorem adj_snd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I)
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ →
    ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] →
      i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ h i₂ j₂ h₁ h₂ h₃ h₄
  exact GlobalTheory.T.product_degeneration_first_factor_adjoint R I D D₂ D₁ p₂ p₁ q₂ q₁ (isSumDeg_swap h) i₂ j₂ h₂ h₁ h₄ h₃

end GlobalTheory.MumProdSwap
