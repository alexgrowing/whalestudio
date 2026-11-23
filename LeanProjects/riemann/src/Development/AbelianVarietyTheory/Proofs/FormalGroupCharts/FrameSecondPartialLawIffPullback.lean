import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePartialLawTwo

section Val

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hφ : ∀ k, φ' k ≫ F = h ≫ φ k) (r : Z ⟶ Y') {z : Z} {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hφ])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem pmaps_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε t)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) (flatGen L F φ' ε t)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 H
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (t.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

end Val

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem prod_sq {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ t.G.left) → U) :
    ∏ I, h (ρ.left ≫ cφG t ![a, b] I) ^ cε 2 I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ t.G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), ρ.left ≫ cφG t ![a, b] I = (psum t.G ![ρ ≫ a, ρ ≫ b] I.down).left :=
    fun I => congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => by fin_cases i <;> rfl)))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum t.G ![ρ ≫ a, ρ ≫ b] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ cε 2 I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum t.G ![ρ ≫ a, ρ ≫ b] ∅ = 1 := rfl
  have p₁ : psum t.G ![ρ ≫ a, ρ ≫ b] {0} = ρ ≫ a := _root_.mul_one _
  have p₂ : psum t.G ![ρ ≫ a, ρ ≫ b] {1} = ρ ≫ b := _root_.mul_one _
  have p₄ : psum t.G ![ρ ≫ a, ρ ≫ b] {0, 1} = (ρ ≫ a) * (ρ ≫ b) := congrArg ((ρ ≫ a) * ·) (_root_.mul_one _)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_one, zpow_neg_one]
  ac_rfl

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem subst_jpt (m : ℕ) {n n' : ℕ} (φ : Fin n → Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) :
    homAt x0 (jetSubstP m fun p : Fin n × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => φ i p.2) ≫ x m := by
  simp only [jptG, ← Category.assoc, GermD.homAt_comp]
  congr 2
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp [jetCopy, jetSubstP, GermD.jetMap_mk]

theorem subst_X (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) ≫ x m =
      jptG t x0 d x m i := by
  simp only [jptG]
  congr 2
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp [jetCopy, jetSubstP, GermD.jetMap_mk]

theorem subst_law (m : ℕ) (F : Fin d → PS S 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (law : homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
      jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) {n : ℕ} (σ : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psIn d m σ (F p.2)) ≫ x m =
      jptG t x0 d x m (σ 0) * jptG t x0 d x m (σ 1) := by
  rw [← FBIdPh.relabel_jpt t x0 d x m σ 0, ← FBIdPh.relabel_jpt t x0 d x m σ 1, ← MonObj.comp_mul, ← law,
    ← Category.assoc, GermD.homAt_comp, FBIdPh.jetSubstP_comp m _ _
      (fun p => (FBIdPh.cc_psTrunc m _).trans (hF _)) (fun p => by simp [FBIdPh.rel])]
  congr 3
  funext p
  rw [psIn, MvPolynomial.rename_eq_aeval]
  rfl

end Pts

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {t' : SAB H (Sp S)} {mp : SABMap t' t x0}
  {w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)}

theorem val_cubic (hθ : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t
      (mp.cm.thetaPull t.PP.L t.cub.t)) {Y : Scheme.{0}} {s : Y ⟶ X0} {s' : Y ⟶ Sp S}
    (a b c : Over.mk s ⟶ t.G) (a' b' c' : Over.mk s' ⟶ t'.G) (ha : a'.left ≫ mp.φ = a.left)
    (hb : b'.left ≫ mp.φ = b.left) (hc : c'.left ≫ mp.φ = c.left) {y : Y} {J J'}
    (hJ : Good t.PP.L y J) (hJ' : Good t'.PP.L y J') :
    val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift a (lift b c)).left) (𝟙 Y) y J =
      (om w y J J' (a' * b' * c').left * (om w y J J' (a' * b').left)⁻¹ * (om w y J J' (a' * c').left)⁻¹ *
        (om w y J J' (b' * c').left)⁻¹ * om w y J J' a'.left * om w y J J' b'.left * om w y J J' c'.left *
        (om w y J J' (1 : Over.mk s' ⟶ t'.G).left)⁻¹) *
      val (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift a' (lift b' c')).left) (𝟙 Y) y J' := by
  have pm := (maps_iff w (thφ t'.G (x3 t'.G)) (thφ t.G (x3 t.G)) thε t'.cub.t t.cub.t mp.cm.F3 _
    (mp.cm.theta_le t.PP.L) (fun _ => rfl)).1 hθ
  have q : (lift a' (lift b' c')).left ≫ mp.cm.F3 = (lift a (lift b c)).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i
    · simpa [x3] using ha
    · simpa [x3] using hb
    · simpa [x3] using hc
  have e := val_of_pmaps pm (fun I => mp.cm.psum_comm I.down) (lift a' (lift b' c')).left hJ hJ'
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  refine Eq.trans (congrArg (fun r => val (L := t.PP.L) (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J)
    (Category.id_comp _)) (e.trans (congrArg₂ (· * ·) (prod_cub a' b' c' (om w y J J')) ?_))
  exact congrArg (fun r => val (L := t'.PP.L) (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J')
    (Category.id_comp _).symm

variable {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G}

theorem val_frame {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m} {m : ℕ}
    {c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2))}
    (h₁ : LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m))
    (h₂ : LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁))
    {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (a b : jOG (𝟙 (Sp S)) d m n ⟶ t'.G)
    (ha : homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => φ 0 p.2) ≫ x' m = a)
    (hb : homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => φ 1 p.2) ≫ x' m = b)
    {y : Sp (Jet S (Fin n × Fin d) m)} {J J'} (hJ : Good t.PP.L y J) (hJ' : Good t'.PP.L y J') :
    val (peG t x0 d x e m φ) (𝟙 (Sp (Jet S (Fin n × Fin d) m))) y J =
      (om w y J J' (a * b).left * (om w y J J' a.left)⁻¹ * (om w y J J' b.left)⁻¹ *
        om w y J J' (1 : jOG (𝟙 (Sp S)) d m n ⟶ t'.G).left) *
      val (peG t' (𝟙 (Sp S)) d x' e' m φ) (𝟙 (Sp (Jet S (Fin n × Fin d) m))) y J' := by
  have pm := pmaps_flat w _ _ _ _ h₂
  have e₀ := val_of_pmaps pm (fun _ => (Category.id_comp _).symm)
    (homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left hJ hJ'
  have p := prod_sq t' (homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) (om w y J J')
  rw [subst_jpt, subst_jpt, ha, hb] at p
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  refine (val_corr hJ h₁ _).symm.trans (Eq.trans (congrArg (fun r => val c₁ r y J)
    ((Category.id_comp _).trans (Category.comp_id _).symm)) (e₀.trans (congrArg₂ (· * ·) p ?_)))
  exact congrArg (fun r => val (L := t'.PP.L) (φ := cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (ε := cε 2) (e' m) r y J') (Category.id_comp _).symm

theorem jpt_push (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left) (m : ℕ) {n : ℕ} (i : Fin n) :
    (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = (jptG t x0 d x m i).left :=
  (Category.assoc _ _ _).trans (congrArg ((homAt x0 (jetCopy d m i)).left ≫ ·) (hx m))

end Comparison₂

theorem corr_iff_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    {K₁ K₂ K₃ K₄ : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃] [Fintype K₄]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {φ₃ : K₃ → (Y ⟶ X')} {ε₃ : K₃ → ℤ} {φ₄ : K₄ → (Y ⟶ X')} {ε₄ : K₄ → ℤ}
    {a : LB.Gen (LB.LinComb L φ₁ ε₁)} {b : LB.Gen (LB.LinComb L φ₂ ε₂)}
    {a' : LB.Gen (LB.LinComb L' φ₃ ε₃)} {b' : LB.Gen (LB.LinComb L' φ₄ ε₄)}
    (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      ∃ c, val a (𝟙 Y) y J = c * val a' (𝟙 Y) y J' ∧ val b (𝟙 Y) y J = c * val b' (𝟙 Y) y J') :
    LB.Gen.Corr L _ _ _ _ a b ↔ LB.Gen.Corr L' _ _ _ _ a' b' := by
  constructor
  · intro H
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
    obtain ⟨c, e₁, e₂⟩ := h y J J' hJ hJ'
    exact mul_left_cancel (e₁.symm.trans ((val_corr hJ H _).trans e₂))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Y ⟶ X' => exists_chart hL' (χ y)
    obtain ⟨c, e₁, e₂⟩ := h y J J' hJ hJ'
    exact e₁.trans ((congrArg (c * ·) (val_corr hJ' H _)).trans e₂.symm)

theorem units_cancel {U : Type} [CommGroup U] (g p q r p₀₁₂ p₁₂ p₀₁ p₀₂ p₀ p₁ p₂ o : U) :
    g * ((p₀₁₂ * p₀⁻¹ * p₁₂⁻¹ * o * p) * ((p₀₁ * p₀⁻¹ * p₁⁻¹ * o * q)⁻¹ * (p₀₂ * p₀⁻¹ * p₂⁻¹ * o * r)⁻¹)) =
      (p₀₁₂ * p₁₂⁻¹ * p₀₁⁻¹ * p₀₂⁻¹ * p₁ * p₂ * p₀ * o⁻¹) * (g * (p * (q⁻¹ * r⁻¹))) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.FramePartialLawTwo

open GlobalTheory.FramePartialLawTwo in

theorem GlobalTheory.frame_second_partial_law_iff_pullback :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph2 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx hθ e e' _ _ he F ph2 hF law
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  obtain ⟨c₁, h₁, h₂⟩ := he m
  refine corr_iff_of_val t.PP.isLB t'.PP.isLB fun y J J' hJ hJ' => ?_
  have eθ := val_cubic hθ (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (jpt_push hx m 1) (jpt_push hx m 2) (jpt_push hx m 0) hJ hJ'
  have eA := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] _ _
    (subst_X t' _ d x' m 0) (subst_law t' _ d x' m F hF (law m) ![1, 2]) hJ hJ'
  have eB := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 1) hJ hJ'
  have eC := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 2) hJ hJ'
  rw [mul_comm (_ * _) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)),
    mul_comm (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)),
    mul_comm (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3))] at eθ
  refine ⟨_, eθ, ?_⟩
  refine ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) eA ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) eB))
      ((val_inv _ _).trans (congrArg (·⁻¹) eC)))))))).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl ((GermB.val_scale t' _ _ _ _ _ _ _ hJ').trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  exact units_cancel _ _ _ _ _ _ _ _ _ _ _ _
