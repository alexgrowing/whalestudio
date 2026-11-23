import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.zero_eq_one {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y : Fam G κ} (hy : IsFPt y) : y 0 = 1 := by
  have hc : (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ 0) = AlgHom.id R _ := by
    apply jet_ext
    intro j
    rw [AlgHom.comp_apply, jetAug_zR, map_zero]
    apply jetAug_zero_injective κ
    rw [map_zero, AlgHom.id_apply, jetAug_zR]
  have hid : spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [spMap_left]
    exact Spec.map_id _
  calc y 0 = spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) ≫ y 0 := by rw [hid, Category.id_comp]
    _ = spMap (Algebra.ofId R (JetR R κ 0)) ≫ spMap (jetAug R κ 0) ≫ y 0 := by
      rw [← Category.assoc, spMap_comp, hc]
    _ = 1 := by rw [hy.2 0]; exact MonObj.comp_one _

theorem exUnique_ser (hJ : JetAlgSt) (hR : RepSt) (hS : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {k : ℕ} {Y : Over (Spec (CommRingCat.of R))}
    (L : ∀ T : Over (Spec (CommRingCat.of R)), (Fin k → (T ⟶ G)) → (T ⟶ Y))
    (hL : ∀ (T T' : Over (Spec (CommRingCat.of R))) (h : T' ⟶ T) (y : Fin k → (T ⟶ G)),
      h ≫ L T y = L T' (fun j => h ≫ y j))
    (U : Y.left.Opens) (hU : ⊤ ≤ (L _ (fun _ => η[G])).left ⁻¹ᵁ U) (f : Γ(Y.left, U)) :
    ∃! g : PS R k d, ∀ (n : ℕ) (a : Fin k → Pt R n d) (y : Fin k → Fam G (Fin n × Fin d)),
      (∀ j, Rep x (a j) (y j)) → HasSer (fun m => (L _ (fun j => y j m)).left) U f (ev a g) := by
  obtain ⟨h1, -, h3, -, h5⟩ := hR R G d x hx (Fin k × Fin d)
  have hpt : ∀ (j : Fin k) (i : Fin d), constantCoeff (pt R (n := k) d j i) = 0 :=
    fun j => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt j
  choose y₀ hy₀ using fun j : Fin k => (h1 (pt R (n := k) d j) (hpt j)).exists
  have hF : ∀ j, IsFPt (y₀ j) := fun j => h3 _ _ (hy₀ j)
  have hcomp : ∀ m, (spMap (jetTruncR R (Fin k × Fin d) m)).left ≫ (L _ (fun j => y₀ j (m + 1))).left =
      (L _ (fun j => y₀ j m)).left := by
    intro m
    rw [← Over.comp_left, hL]
    congr 2
    funext j
    exact (hF j).1 m
  have h0 : ⊤ ≤ (L _ (fun j => y₀ j 0)).left ⁻¹ᵁ U := by
    have e : L _ (fun j => y₀ j 0) = toUnit _ ≫ L _ (fun _ => η[G]) := by
      rw [hL]
      congr 1
      funext j
      exact (hF j).zero_eq_one
    rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
    intro p _
    exact hU (Set.mem_univ _)
  obtain ⟨⟨τ, hτ⟩, -, -, hsub⟩ :=
    hS R (Fin k × Fin d) Y.left (fun m => (L _ (fun j => y₀ j m)).left) hcomp U h0
  refine ⟨τ f, fun n a y hy => ?_, fun g hg => ?_⟩
  · let b : Fin k × Fin d → MvPowerSeries (Fin n × Fin d) R := fun p => a p.1 p.2
    have hb : ∀ p, constantCoeff (b p) = 0 := fun p => (hy p.1).1 p.2
    choose ψ hψ using fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin k × Fin d) b hb m).1
    have hyy : ∀ j, y j = fun m => spMap (ψ m) ≫ y₀ j m := by
      intro j
      have r := h5 (Fin n × Fin d) b ψ hb hψ _ _ (hy₀ j)
      have e : (fun i => MvPowerSeries.subst b (pt R (n := k) d j i)) = a j := by
        funext i
        exact MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hb) (j, i)
      rw [e] at r
      exact ((hR R G d x hx (Fin n × Fin d)).1 (a j) (hy j).1).unique (hy j) r
    have r := hsub (Fin n × Fin d) b ψ hb hψ f (τ f) ((hτ f _).2 rfl)
    have e : (fun m => (L _ (fun j => y j m)).left) =
        fun m => (spMap (ψ m)).left ≫ (L _ (fun j => y₀ j m)).left := by
      funext m
      rw [← Over.comp_left, hL]
      simp only [hyy]
    rw [e]
    exact r
  · have r := hg k (fun j => pt R (n := k) d j) y₀ hy₀
    have e : ev (fun j => pt R (n := k) d j) g = g := by
      unfold ev
      exact congrFun MvPowerSeries.subst_self g
    rw [e] at r
    exact (hτ f g).1 r

theorem serEx : JetAlgSt → RepSt → SerSt → SerExSt := by
  intro hJ hR hS R _ G _ d x hx
  refine ⟨fun U hU f => ?_, fun U hU f => ?_, fun U hU f => ?_⟩
  · have H := exUnique_ser hJ hR hS hx (k := 1) (Y := G) (fun _ y => y 0) (fun _ _ _ _ => rfl) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a y ha => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a] ![y] (fun j => by fin_cases j; exact ha)
    · have e : a = ![a 0] := by funext j; fin_cases j; rfl
      rw [e]
      exact h n (a 0) (y 0) (ha 0)
  · have H := exUnique_ser hJ hR hS hx (k := 2) (Y := G ⊗ G) (fun _ y => lift (y 0) (y 1))
      (fun _ _ _ _ => comp_lift _ _ _) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b y z ha hb => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b] ![y, z] (fun j => by fin_cases j; exacts [ha, hb])
    · have e : a = ![a 0, a 1] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (y 0) (y 1) (ha 0) (ha 1)
  · have H := exUnique_ser hJ hR hS hx (k := 3) (Y := G ⊗ G ⊗ G)
      (fun _ y => lift (y 0) (lift (y 1) (y 2)))
      (fun _ _ _ _ => by rw [comp_lift, comp_lift]) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b c y z w ha hb hc => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b, c] ![y, z, w] (fun j => by fin_cases j; exacts [ha, hb, hc])
    · have e : a = ![a 0, a 1, a 2] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (a 2) (y 0) (y 1) (y 2) (ha 0) (ha 1) (ha 2)

end GlobalTheory.JetSer
