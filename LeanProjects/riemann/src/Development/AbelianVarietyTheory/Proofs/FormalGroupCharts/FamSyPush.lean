import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.PushSym

theorem val_carries {X X' Y Z : Scheme.{0}} {L' : LB X'} (L : LB X) (F : X' ⟶ X) (w : LB.Iso L' (L.pull F))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) (h : Carries L F w φ ε g g') (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι} (hJ' : Good L' z J') :
    val g' r z J = (∏ k, gm (r ≫ φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
      (w.s (fun _ => J ((r ≫ φ k) ≫ F), J' (r ≫ φ k))) ^ ε k) * val g r z J' := by
  have m1 : ∀ k, (r ≫ φ k) z ∈ (L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) := fun k =>
    Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨Set.mem_iInter.2 m1, hJ'.mem φ r⟩
  have e := congrArg (gm r z (LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓
    LB.wchart L' φ (fun k => J' (r ≫ φ k)))) (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  refine ((gm_res r z _ hm _).trans (gm_res r z _ hm.1 _)).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
    ⟨m1 k, hJ' (r ≫ φ k)⟩ _)

theorem val_scaleGenG {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

theorem prod_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T : Over X0} (a b : T ⟶ t.G) (s : T ⟶ T) (ha : s ≫ a = b) (hb : s ≫ b = a) {U : Type} [CommGroup U]
    (h : (T.left ⟶ t.G.left) → U) :
    ∏ k, h (s.left ≫ cφG t ![a, b] k) ^ cε 2 k = ∏ k, h (cφG t ![a, b] k) ^ cε 2 k := by
  have e : ∀ k, s.left ≫ cφG t ![a, b] k = cφG t ![b, a] k := fun k => by
    have := psum_hom (preHom (G := t.G) s) ![a, b] k.down
    have e2 : (fun i => preHom (G := t.G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e2] at this
    exact congrArg (fun q => q.left) this
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ cε 2 k) (e k)).trans ?_
  refine (prod_cube₂ b a h).trans (Eq.trans ?_ (prod_cube₂ a b h).symm)
  rw [_root_.mul_comm b a, mul_right_comm (h (a * b).left)]

theorem famSy_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ sy : PS V 2 d, FamSy t (𝟙 (Sp V)) d x sy e → FamSy t' (𝟙 (Sp V)) d x' sy e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' _ _ _ hP sy hs m
  obtain ⟨u, hu, hc⟩ := hs m
  obtain ⟨-, c, -, hce, hcar⟩ := hP m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  choose J' hJ' using fun χ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ'' : Good t.PP.L y J' := hJ'
  have hsub : (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) = Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.rel d ![1, 0] := by
    funext ⟨i, j⟩; fin_cases i <;> rfl
  have k := (val_corr hJ'' hc (𝟙 _)).trans ((val_scaleGenG t _ _ _ _ _ y hJ'').trans
    (congrArg₂ (· * ·) rfl (val_pull hJ'' _ _ _)))
  refine Eq.trans ?_ ((val_scaleGenG t' _ _ _ _ _ y hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm
  have v := fun r : (jOG (𝟙 (Sp V)) d m 2).left ⟶ (jOG (𝟙 (Sp V)) d m 2).left =>
    (val_corr hJ hce r).symm.trans (val_carries _ _ w _ _ _ _ hcar r y hJ hJ'')
  refine (v _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (v _)).symm)
  refine (congrArg₂ (· * ·) ?_ k).trans (mul_left_comm _ _ _)
  have p := (prod_swap t _ _ _ (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 0)
    (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 1)
    (fun ψ => gm ψ y ((t'.PP.L.pull n.φ).U (fun _ => J (ψ ≫ n.φ)) ⊓ t.PP.L.U (J' ψ)) (w.s (fun _ => J (ψ ≫ n.φ), J' ψ)))).symm
  rw [← hsub] at p
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (p.trans (Finset.prod_congr rfl fun k _ => ?_))
  · rw [Category.id_comp]; rfl
  · rw [Category.id_comp]; rfl

end GlobalTheory.PushSym
