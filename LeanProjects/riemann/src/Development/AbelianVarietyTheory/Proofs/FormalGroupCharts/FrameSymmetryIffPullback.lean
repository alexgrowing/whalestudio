import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameSym

section Val

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K₁ : Type} [Fintype K] [Fintype K₁]

theorem val_tie (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι}
    (hJ' : Good L' z J') :
    val c r z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have P := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 hm
  · have := P Z r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F))
      (fun k => hJ' (r ≫ φ' k))
    rw [Category.comp_id] at this
    rw [val_of c r z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact this
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

def scale (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scale φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem good_exists (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose d hd using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨d, hd⟩

theorem corr_sym_iff (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    (φ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (e : LB.Gen (LB.LinComb L φ ε₁)) (hc : LB.Gen.Corr L _ _ _ _ c e)
    (s : Y ⟶ Y) (hs : FormEq φ' ε (fun k => s ≫ φ' k) ε) (u : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr L _ _ _ _ e (scale _ _ u (LB.pullGen L φ ε₁ e s)) ↔
      LB.Gen.Corr L' _ _ _ _ a (scale _ _ u (LB.pullGen L' φ' ε a s)) := by
  have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      (val e (𝟙 Y) y J = val (scale _ _ u (LB.pullGen L φ ε₁ e s)) (𝟙 Y) y J ↔
        val a (𝟙 Y) y J' = val (scale _ _ u (LB.pullGen L' φ' ε a s)) (𝟙 Y) y J') := by
    intro y J J' hJ hJ'
    rw [val_scale _ _ _ _ hJ, val_scale _ _ _ _ hJ', val_pull hJ, val_pull hJ', ← val_corr hJ hc, ← val_corr hJ hc,
      val_tie w φ' ε a c hm _ y hJ hJ', val_tie w φ' ε a c hm _ y hJ hJ']
    have h := hs _ (fun ψ => gw w ψ y (J (ψ ≫ F)) (J' ψ))
    simp only [Category.id_comp]
    rw [← h, mul_left_comm, mul_right_inj]
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := good_exists hL y
    exact (key y J J' hJ hJ').1 (val_corr hJ h _)
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := good_exists hL' y
    exact (key y J J' hJ hJ').2 (val_corr hJ' h _)

end Val

theorem formEq_swap {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] {T : Over B} (a b : T ⟶ G) (s : T ⟶ T)
    (ha : s ≫ a = b) (hb : s ≫ b = a) :
    FormEq (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![a, b] I.down).left) (cε 2)
      (fun I => s.left ≫ (psum G ![a, b] I.down).left) (cε 2) := by
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![a, b] I).left = (psum G ![b, a] I).left := fun I => by
    have := psum_hom (preHom (G := G) s) ![a, b] I
    have e : (fun i => preHom (G := G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e] at this
    exact congrArg (fun z => z.left) this
  simp only [hp]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one]
  rw [_root_.mul_comm b a]
  exact congrArg _ (mul_left_comm _ _ _)

theorem jetMap_mk {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ')
    (p : MvPolynomial κ R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl

theorem swap_jpt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (m : ℕ)
    (φ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (i k : Fin 2) (h : φ i = fun j => X (k, j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have e : (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) = jetCopy d m k := by
    refine Ideal.Quotient.algHom_ext S (MvPolynomial.algHom_ext fun p => ?_)
    show jetSubstP m _ (jetCopy d m i (Ideal.Quotient.mk _ (X p))) = jetCopy d m k (Ideal.Quotient.mk _ (X p))
    simp [jetSubstP, jetCopy, jetMap_mk, h]
  rw [jptG, jptG, ← Category.assoc, ← e]
  congr 1
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem frame_sym_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (sy : PS S 2 d), (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) ↔ (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (e' m) (scaleGenG t' _ _ (unitΓ u⁻¹) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' _ e e' _ _ ht sy
  refine forall_congr' fun m => exists_congr fun u => and_congr Iff.rfl ?_
  obtain ⟨c₁, hc, hm⟩ := ht m
  exact corr_sym_iff t.PP.isLB t'.PP.isLB w _ (cε 2) (e' m) c₁ hm
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) hc _
    (formEq_swap t'.G _ _ _ (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 0 1 rfl)
      (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 1 0 rfl)) (unitΓ u⁻¹)

end GlobalTheory.FrameSym
