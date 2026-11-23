import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem gm_appLE {X Y : Scheme.{0}} (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ a ⁻¹ᵁ U) (u : Γ(X, U)ˣ)
    {x : Y} (hx : x ∈ V) :
    gm (𝟙 Y) x V (Units.map (a.appLE U V h).hom.toMonoidHom u) = gm a x U u := by
  have e : Units.map (a.appLE U V h).hom.toMonoidHom u = res h (pullU a U u) := by
    apply Units.ext
    simp [res, pullU, Scheme.Hom.appLE]
  rw [e, gm_res _ x h hx, gm_pull (𝟙 Y) a x U (h hx) u, Category.id_comp]

theorem cob_group {G : Type} [CommGroup G] (p q r u v B T : G) (h₁ : p * q = v) (h₂ : r * u = v) :
    p * (q * B⁻¹ * T) = r * B⁻¹ * (u * T) := by
  calc p * (q * B⁻¹ * T) = p * q * (B⁻¹ * T) := by simp only [_root_.mul_assoc]
    _ = r * u * (B⁻¹ * T) := by rw [h₁, h₂]
    _ = r * B⁻¹ * (u * T) := mul_mul_mul_comm r u B⁻¹ T

theorem exists_gen_of_units (X Y : Scheme.{0}) (L : LB X) (hL : L.IsLB) (a b : Y ⟶ X) (hab : ∀ y, a y = b y)
    (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ)
    (ht : ∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')),
      res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) =
        Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ *
          res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  have hA : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, a y ∈ L.U (i 0) := fun i y hy =>
    Set.mem_iInter.1 hy 0
  have hB : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, b y ∈ L.U (i 1) := fun i y hy =>
    Set.mem_iInter.1 hy 1
  have hle : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ a ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i 1)) := fun i y hy =>
    ⟨hA i y hy, by
      show a y ∈ L.U (i 1)
      rw [hab y]; exact hB i y hy⟩
  have hle' : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ b ⁻¹ᵁ L.U (i 1) := fun i y hy => hB i y hy
  let s : ∀ i : Fin 2 → L.ι, Γ(Y, LB.wchart L ![a, b] i)ˣ := fun i =>
    res (hle i) (pullU a _ (L.g (i 0) (i 1))) * res (hle' i) (t (i 1))
  have hs : ∀ (i : Fin 2 → L.ι) (x : Y), x ∈ LB.wchart L ![a, b] i →
      gm (𝟙 Y) x _ (s i) = gm a x _ (L.g (i 0) (i 1)) * gm (𝟙 Y) x _ (t (i 1)) := by
    intro i x hx
    have h₁ : gm (𝟙 Y) x _ (res (hle i) (pullU a _ (L.g (i 0) (i 1)))) = gm a x _ (L.g (i 0) (i 1)) := by
      rw [gm_res _ x _ hx, gm_pull (𝟙 Y) a x _ (hle i hx), Category.id_comp]
    rw [map_mul, h₁, gm_res _ x _ hx]
  refine ⟨⟨s⟩, fun i i' => unit_ext fun x hx => ?_⟩
  have hmem : b x ∈ L.U (i 1) ⊓ L.U (i' 1) := ⟨hB i x hx.1, hB i' x hx.2⟩
  have hh : b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) ≤ a ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := fun y hy => by
    show a y ∈ L.U (i 1) ⊓ L.U (i' 1)
    rw [hab y]; exact hy
  have e := congrArg (gm (𝟙 Y) x (b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)))) (ht (i 1) (i' 1) hh)
  have hmem' : x ∈ b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := hmem
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 Y) x _ hmem', gm_res (𝟙 Y) x _ hmem', gm_appLE a hh _ hmem',
    gm_pull (𝟙 Y) b x _ hmem, Category.id_comp] at e
  have c₁ := gm_cocycle hL a x (hA i x hx.1) (show a x ∈ L.U (i 1) from (hle i hx.1).2)
    (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have c₂ := gm_cocycle hL a x (hA i x hx.1) (hA i' x hx.2) (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have hg := gm_linComb L ![a, b] ![1, -1] (𝟙 Y) x i i' hx.1 hx.2
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx]
  show gm (𝟙 Y) x (LB.wchart L ![a, b] i) (s i) =
    gm (𝟙 Y) x (LB.wchart L ![a, b] i ⊓ LB.wchart L ![a, b] i') ((LB.LinComb L ![a, b] ![1, -1]).g i i') *
      gm (𝟙 Y) x (LB.wchart L ![a, b] i') (s i')
  rw [hg, hs i x hx.1, hs i' x hx.2, e, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, zpow_one, zpow_neg]
  exact cob_group _ _ _ _ _ _ _ c₁ c₂

end GlobalTheory.CompanionTheory.Ar.Coc
