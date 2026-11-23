import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslMove

section Values

variable {X X' Y Y' : Scheme.{0}} {L₀ : LB X} {L₁ : LB X'} {F : X' ⟶ X}

def wv (w : LB.Iso L₁ (L₀.pull F)) {Z : Scheme.{0}} (z : Z) (J₀ : (Z ⟶ X) → L₀.ι) (J : (Z ⟶ X') → L₁.ι)
    (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ := gw w ψ z (J₀ (ψ ≫ F)) (J ψ)

theorem exists_good_pt {Z : Scheme.{0}} (hL : L₀.IsLB) (z : Z) : ∃ J, Good L₀ z J := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨J, hJ⟩

theorem gs_appLE {Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ U)
    (hz : r z ∈ W) (a : Γ(X, U)) : gs r z W ((g.appLE U W h).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z h hz _).trans (gs_pull r g z U (h hz) a)

theorem gs_pow {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hz : r z ∈ W) (a : Γ(Y, W)) (n : ℕ) :
    gs r z W (a ^ n) = gs r z W a ^ n := by
  simp only [gs_eq r z W hz, map_pow]

theorem val_move {w : LB.Iso L₁ (L₀.pull F)} {K : Type} [Fintype K] {φ₁ : K → (Y' ⟶ X')} {φ₀ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L₁ φ₁ ε)} {t : LB.Gen (LB.LinComb L₀ φ₀ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ₁ k ≫ F = h ≫ φ₀ k) (H : PMaps w φ₁ φ₀ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') {z : Z} {J₀ J}
    (hJ₀ : Good L₀ z J₀) (hJ : Good L₁ z J) :
    val t (r ≫ h) z J₀ = (∏ k, wv w z J₀ J (r ≫ φ₁ k) ^ ε k) * val a r z J := by
  rw [val_of t (r ≫ h) z J₀ (fun k => J₀ ((r ≫ φ₁ k) ≫ F)) (fun k => by rw [Category.assoc, ← hc, Category.assoc])]
  exact H Z r z _ _ (fun k => hJ₀ ((r ≫ φ₁ k) ≫ F)) (fun k => hJ (r ≫ φ₁ k))

def GenRel (w : LB.Iso L₁ (L₀.pull F)) (h : Y' ⟶ Y) {a₀ b₀ : Y ⟶ X} {a b : Y' ⟶ X'} {m n : ℤ}
    (t : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![a₀, b₀] ![m, n]))
    (u : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![a, b] ![m, n])) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J₀ J, Good L₀ z J₀ → Good L₁ z J →
    val t (r ≫ h) z J₀ = wv w z J₀ J (r ≫ a) ^ m * wv w z J₀ J (r ≫ b) ^ n * val u r z J

theorem exists_genRel (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {w : LB.Iso L₁ (L₀.pull F)} (hw : w.IsGen) (h : Y' ⟶ Y)
    {a₀ b₀ : Y ⟶ X} {a b : Y' ⟶ X'} (ha : h ≫ a₀ = a ≫ F) (hb : h ≫ b₀ = b ≫ F) {m n : ℤ}
    (t : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![a₀, b₀] ![m, n])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![a, b] ![m, n]), u.IsGen ∧ GenRel w h t u := by
  have hc : ∀ k, (![a, b] : Fin 2 → _) k ≫ F = h ≫ (![a₀, b₀] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact ha.symm
    · exact hb.symm
  obtain ⟨u, hu, hm⟩ := H1.exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw) ![a₀, b₀] ![a, b] ![m, n] h hc t ht
  refine ⟨u, hu, fun Z r z J₀ J hJ₀ hJ => (val_move hc hm r hJ₀ hJ).trans ?_⟩
  rw [Fin.prod_univ_two]
  rfl

end Values

section Points

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left}

include hp

theorem base_comm {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) : τ ≫ T₀.hom = T.hom ≫ f := by
  rw [← Over.w x₀, ← Category.assoc, hx, Category.assoc, hp.1.w, ← Category.assoc, Over.w x]

theorem pt_iff (hτ : τ ≫ T₀.hom = T.hom ≫ f) (x : T ⟶ A) (x₀ : T₀ ⟶ G) : τ ≫ x₀.left = x.left ≫ φ ↔
    preHom (Over.homMk τ hτ : Over.mk (T.hom ≫ f) ⟶ T₀) x₀ = pushHom hp T x :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun q => q.left) h⟩

theorem pt_mul {x y : T ⟶ A} {x₀ y₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hy : τ ≫ y₀.left = y.left ≫ φ) :
    τ ≫ (x₀ * y₀).left = (x * y).left ≫ φ := by
  have hτ := base_comm hp hx
  rw [pt_iff hp hτ] at hx hy ⊢
  rw [map_mul, map_mul, hx, hy]

theorem pt_pow {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (n : ℕ) :
    τ ≫ (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  have hτ := base_comm hp hx
  rw [pt_iff hp hτ] at hx ⊢
  rw [map_pow, map_pow, hx]

theorem pt_inv {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) :
    τ ≫ (x₀⁻¹).left = (x⁻¹).left ≫ φ := by
  have hτ := base_comm hp hx
  rw [pt_iff hp hτ] at hx ⊢
  rw [map_inv, map_inv, hx]

variable {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
  (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)

include h₁ h₂

theorem pt_transl {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) :
    Ψ ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := by
  refine pt_mul hp (x := fst T A ≫ x) (x₀ := fst T₀ G ≫ x₀) ?_ h₂
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, h₁, Category.assoc, hx, Category.assoc]

omit hp h₂ [GrpObj G] [GrpObj A] in
theorem lift_comm {m : T ⊗ A ⟶ A} {m₀ : T₀ ⊗ G ⟶ G} (hm : Ψ ≫ m₀.left = m.left ≫ φ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ) :
    (lift (fst T A) m).left ≫ Ψ = Ψ ≫ (lift (fst T₀ G) m₀).left := by
  have e₁ : ((lift (fst T A) m).left ≫ Ψ) ≫ (fst T₀ G).left = (Ψ ≫ (lift (fst T₀ G) m₀).left) ≫ (fst T₀ G).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, h₁, ← Category.assoc, ← Over.comp_left, lift_fst]
  have e₂ : ((lift (fst T A) m).left ≫ Ψ) ≫ (snd T₀ G).left = (Ψ ≫ (lift (fst T₀ G) m₀).left) ≫ (snd T₀ G).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hm]
  exact pullback.hom_ext e₁ e₂

end Points

section Sections

open GlobalTheory.VVRank

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left}
  {T : Over S'} {T₀ : Over S} {L₀ : LB G.left} {L₁ : LB A.left}

def SecRel (w : LB.Iso L₁ (L₀.pull φ)) (Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left) {a : ℤ} (s₀ : LB.Sec (LPow G L₀ a T₀))
    (s : LB.Sec (LPow A L₁ a T)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J₀ J, Good L₀ z J₀ → Good L₁ z J →
    sv G s₀ (r ≫ Ψ) z J₀ = (wv w z J₀ J (r ≫ (snd T A).left) ^ a).val * sv A s r z J

variable {w : LB.Iso L₁ (L₀.pull φ)} {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left}

theorem secRel_twist {ψ₀ : T₀ ⊗ G ⟶ T₀ ⊗ G} {m₀ : T₀ ⊗ G ⟶ G} {hm₀ : ψ₀ ≫ snd T₀ G = m₀}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} (e : ψ.left ≫ Ψ = Ψ ≫ ψ₀.left) {a b : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, -b])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : GenRel w Ψ α₀ α)
    {s₀ t₀ s t} (H₀ : IsTwistPull G L₀ ψ₀ m₀ hm₀ a b α₀ s₀ t₀) (H : IsTwistPull A L₁ ψ m hm a b α s t)
    (hs : SecRel w Ψ s₀ s) : SecRel w Ψ t₀ t := by
  intro Z r z J₀ J hJ₀ hJ
  rw [sv_of_isTwistPull G H₀ _ z hJ₀, sv_of_isTwistPull A H _ z hJ, hα Z r z J₀ J hJ₀ hJ, Category.assoc, ← e,
    ← Category.assoc, hs Z _ z J₀ J hJ₀ hJ, Category.assoc, ← Over.comp_left, hm, ← _root_.mul_assoc,
    ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _ (wv w z J₀ J (r ≫ m.left) ^ b),
    inv_mul_cancel_right]

theorem secRel_iff (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ) {a : ℤ} (n : ℕ)
    (hn : a = n) (s₀ : LB.Sec (LPow G L₀ a T₀)) (s : LB.Sec (LPow A L₁ a T)) :
    SecRel w Ψ s₀ s ↔ ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens)
      (h₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (h₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ a T₀).U (fun _ => i)) (h₂ : W ≤ (LPow A L₁ a T).U (fun _ => j)),
      (Ψ.appLE ((LPow G L₀ a T₀).U (fun _ => i)) W h₁).hom (s₀.f (fun _ => i)) =
        ((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) ^ n *
        ((T ⊗ A).left.presheaf.map (homOfLE h₂).op).hom (s.f (fun _ => j)) := by
  have key : ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens)
      (k₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (k₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ a T₀).U (fun _ => i)) (k₂ : W ≤ (LPow A L₁ a T).U (fun _ => j))
      (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z), r z ∈ W →
      gs r z W ((Ψ.appLE ((LPow G L₀ a T₀).U (fun _ => i)) W k₁).hom (s₀.f (fun _ => i))) =
        gs (r ≫ Ψ) z ((LPow G L₀ a T₀).U (fun _ => i)) (s₀.f (fun _ => i)) ∧
      gs r z W (((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W k₀).hom
          (Units.val (w.s ((fun _ => i), j))) ^ n *
        ((T ⊗ A).left.presheaf.map (homOfLE k₂).op).hom (s.f (fun _ => j))) =
        (gw w (r ≫ (snd T A).left) z i j ^ a).val * gs r z ((LPow A L₁ a T).U (fun _ => j)) (s.f (fun _ => j)) := by
    intro i j W k₀ k₁ k₂ Z r z hz
    refine ⟨gs_appLE r Ψ z _ W k₁ hz _, (gs_mul r z W hz _ _).trans
      (congrArg₂ (· * ·) ?_ (gs_res r z k₂ hz _))⟩
    rw [hn, zpow_natCast, Units.val_pow_eq_pow_val, gs_pow r z W hz, gs_appLE r _ z _ W k₀ hz]
    exact congrArg (· ^ n) (gs_unit (r ≫ (snd T A).left) z
      ((L₀.pull φ).U (fun _ => i) ⊓ L₁.U j) (k₀ hz) (w.s (fun _ => i, j)))
  have e : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left), (r ≫ Ψ) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ :=
    fun r => by rw [Category.assoc, h₂, Category.assoc]
  constructor
  · intro H i j W k₀ k₁ k₂
    refine fn_ext fun y hy => ?_
    obtain ⟨a₁, a₂⟩ := key i j W k₀ k₁ k₂ _ (𝟙 _) y hy
    obtain ⟨J₀, hJ₀, e₀⟩ := exists_good L₀ hL₀ y (fun _ : Unit => (𝟙 _ ≫ (snd T A).left) ≫ φ) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => mem_pull.1 (k₀ hy).1)
    obtain ⟨J, hJ, e₁⟩ := exists_good L₁ hL₁ y (fun _ : Unit => 𝟙 _ ≫ (snd T A).left) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => (k₀ hy).2)
    have := H _ (𝟙 _) y J₀ J hJ₀ hJ
    rw [sv, sv, sval_of s₀ _ y J₀ (fun _ => i) (fun _ => by rw [e]; exact e₀ ()),
      sval_of s _ y J (fun _ => j) (fun _ => e₁ ()), wv, e₀ (), e₁ ()] at this
    exact a₁.trans (this.trans a₂.symm)
  · intro H Z r z J₀ J hJ₀ hJ
    let i := J₀ ((r ≫ (snd T A).left) ≫ φ)
    let j := J (r ≫ (snd T A).left)
    let W : (T ⊗ A).left.Opens := (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ⊓
      (Ψ ⁻¹ᵁ (LPow G L₀ a T₀).U (fun _ => i) ⊓ (LPow A L₁ a T).U (fun _ => j))
    have hz : r z ∈ W := ⟨⟨mem_pull.2 (hJ₀ ((r ≫ (snd T A).left) ≫ φ)), hJ (r ≫ (snd T A).left)⟩,
      Set.mem_iInter.2 fun _ => by
        have := hJ₀ ((r ≫ Ψ) ≫ (snd T₀ G).left)
        rw [show J₀ ((r ≫ Ψ) ≫ (snd T₀ G).left) = i from congrArg J₀ (e r)] at this
        exact this, Set.mem_iInter.2 fun _ => hJ (r ≫ (snd T A).left)⟩
    obtain ⟨a₁, a₂⟩ := key i j W inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right) Z r z hz
    rw [sv, sval_of s₀ _ z J₀ (fun _ => i) (fun _ => congrArg J₀ (e r))]
    exact a₁.symm.trans ((congrArg (gs r z W) (H i j W _ _ _)).trans a₂)

end Sections

section Theta

open GlobalTheory.VVRank

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {L₀ : LB G.left} {L₁ : LB A.left}
  (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen)
  {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
  (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)

theorem transl_snd (x : T ⟶ A) : (translT A x).left ≫ (snd T A).left = (translPt A x).left := by
  rw [← Over.comp_left, translT, lift_snd]

theorem transl_transl (x y : T ⟶ A) : (translT A y).left ≫ (translPt A x).left = (translPt A (x * y)).left := by
  rw [← Over.comp_left, translT, translPt_eq x, MonObj.comp_mul, lift_fst_assoc, lift_snd, translPt_eq, translPt_eq,
    MonObj.comp_mul, _root_.mul_assoc]

theorem translPt_one : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem neg_snd : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

theorem neg_transl [IsCommMonObj A] (x : T ⟶ A) : (negT A T).left ≫ (translPt A x).left =
    (translT A x⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left, negT, translT, translPt_eq x, MonObj.comp_mul, lift_fst_assoc, lift_snd,
    lift_snd_assoc, translPt_eq]
  show ((fst T A ≫ x) * (snd T A)⁻¹).left = (((fst T A ≫ x⁻¹) * snd T A)⁻¹).left
  rw [GrpObj.comp_inv, mul_inv, inv_inv]

theorem val_rigPow (ρ : LB.Gen (L₁.pull (eSec A))) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (J) :
    val (rigPow A L₁ ρ k) r z J = val (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ r z J ^ k :=
  map_zpow (gm r z (LB.wchart L₁ (fun _ : PUnit => eSec A) fun _ => J (r ≫ eSec A))) _ k

theorem telescope {U : Type} [CommGroup U] (n : ℕ) (g : ℕ → U) (v : Fin n → U) (hg : g n = g 0)
    (h : ∏ j : Fin n, g j * (g (j + 1))⁻¹ * v j = 1) : ∏ j, v j = 1 := by
  rw [Finset.prod_mul_distrib, Fin.prod_univ_eq_prod_range (fun j => g j * (g (j + 1))⁻¹) n] at h
  simp only [← div_eq_mul_inv] at h
  rwa [Finset.prod_range_div', hg, div_self', _root_.one_mul] at h

theorem sym_cancel {U : Type} [CommGroup U] {p q r s a b c d : U}
    (h : p * q⁻¹ * a * (q * r⁻¹ * b) * (r * s⁻¹ * c * (p * s⁻¹ * d)⁻¹) = 1) : a * b * (c * d⁻¹) = 1 := by
  rw [← h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

include hp hL₀ hL₁ hw h₁ h₂

theorem exists_symLift [IsCommMonObj A] {k : ℤ} {n : ℕ} (hk : ∀ θ : ThetaGrp A L₁ k T, θ.pt ^ n = 1) {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) {θ₀ : ThetaGrp G L₀ k T₀} (H : SymLift G L₀ k n x₀ θ₀) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧ ∀ s₀ t₀ s, IsActOf G L₀ k θ₀ s₀ t₀ → SecRel w Ψ s₀ s →
      ∃ t, IsActOf A L₁ k θ s t ∧ SecRel w Ψ t₀ t := by
  obtain rfl := H.pt_eq
  have tr : ∀ {y : T ⟶ A} {y₀ : T₀ ⟶ G}, τ ≫ y₀.left = y.left ≫ φ →
      (translT A y).left ≫ Ψ = Ψ ≫ (translT G y₀).left := fun hy => lift_comm h₁ (pt_transl hp h₁ h₂ hy) h₂
  have hi : Ψ ≫ (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left ≫ φ := pt_inv hp h₂
  have ng : (negT A T).left ≫ Ψ = Ψ ≫ (negT G T₀).left := lift_comm h₁ hi h₂
  obtain ⟨u, hu, hv⟩ := exists_genRel hL₀ hL₁ hw Ψ h₂ (pt_transl hp h₁ h₂ hx) θ₀.φ θ₀.isGen
  have hxn : x ^ n = 1 := hk ⟨x, u, hu⟩
  refine ⟨⟨x, u, hu⟩, ⟨rfl, ?_, ?_⟩, fun s₀ t₀ s ha hs => ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    obtain ⟨J₀, hJ₀⟩ := exists_good_pt hL₀ y
    have e := (ThetaPullback.val_powGen θ₀ n Ψ hJ₀).symm.trans ((val_corr hJ₀ H.pow_eq _).trans (val_one _))
    refine (ThetaPullback.val_powGen ⟨x, u, hu⟩ n _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine telescope n (fun j => wv w y J₀ J (translPt A (x ^ j)).left ^ k) _ (by rw [hxn, pow_zero]) (Eq.trans ?_ e)
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← tr (pt_pow hp hx j), hv _ _ y J₀ J hJ₀ hJ, transl_snd, transl_transl, ← pow_succ', zpow_neg, Category.id_comp]
  · obtain ⟨ν₀, hν₀, hs⟩ := H.sym
    obtain ⟨ν, hν, hn⟩ := exists_genRel hL₀ hL₁ hw Ψ h₂ hi ν₀ hν₀
    refine ⟨ν, hν, corr_of_val hL₁ fun y J hJ => ?_⟩
    obtain ⟨J₀, hJ₀⟩ := exists_good_pt hL₀ y
    have e := (ThetaPullback.val_symGen θ₀ ν₀ Ψ hJ₀).symm.trans ((val_corr hJ₀ hs _).trans (val_one _))
    refine (ThetaPullback.val_symGen ⟨x, u, hu⟩ ν _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    have a₂ := hn _ (𝟙 _) y J₀ J hJ₀ hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at a₂
    rw [← tr (pt_inv hp hx), ← ng, hv _ _ y J₀ J hJ₀ hJ, hv _ _ y J₀ J hJ₀ hJ, hn _ _ y J₀ J hJ₀ hJ, a₂, transl_snd,
      transl_transl, mul_inv_cancel, translPt_one, neg_snd, neg_transl] at e
    simp only [zpow_neg] at e
    rw [Category.id_comp, Category.id_comp]
    exact sym_cancel e
  · obtain ⟨t, ht⟩ := exists_isTwistPull A (ψ := translT A x) (hm := lift_snd _ _) hL₁ hu s
    exact ⟨t, ht, secRel_twist (tr hx) hv ha ht hs⟩

omit h₁ h₂ in

theorem exists_normMul {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ : LB.Gen (L₁.pull (eSec A))}
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} (he : eSec A ≫ φ = e ≫ eSec G)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) ρ ρ₀ e) (N : ℕ)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])} (g₀ : α₀.IsGen)
    (n₀ : IsNormMul G L₀ ρ₀ N α₀) :
    ∃ α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧
      IsNormMul A L₁ ρ N α ∧ GenRel w φ α₀ α := by
  obtain ⟨α, hα, hv⟩ := exists_genRel hL₀ hL₁ hw φ (a := 𝟙 A.left) (b := (mulA A N).left)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (pt_pow hp (T := A) (T₀ := G) (x := 𝟙 A) (x₀ := 𝟙 G) ((Category.comp_id _).trans (Category.id_comp _).symm) N) α₀ g₀
  refine ⟨α, hα, corr_of_val hL₁ fun y J hJ => ?_, hv⟩
  obtain ⟨J₀, hJ₀⟩ := exists_good_pt hL₀ y
  have a₁ := hv _ (eSec A) y J₀ J hJ₀ hJ
  have a₂ := val_move (fun _ => he) hρ (𝟙 _) hJ₀ hJ
  have a₃ := (val_pull hJ₀ α₀ (eSec G) e).symm.trans ((val_corr hJ₀ n₀ e).trans ((val_mul hJ₀ _ _ _).trans
    (congrArg₂ (· * ·) (val_rigPow _ _ _ _ _) (val_inv _ _))))
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp, zpow_one] at a₂
  rw [← he, a₁, a₂, Category.comp_id, NormMulUniv.eSec_mulA] at a₃
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_rigPow _ _ _ _ _) (val_inv _ _))).symm)
  rw [Category.id_comp]
  rw [mul_zpow, mul_inv, _root_.mul_mul_mul_comm, zpow_neg_one] at a₃
  exact mul_left_cancel a₃

end Theta

theorem exists_isUUOver {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {L₀ : RigLB G} {L₁ : RigLB A}
    {w : LB.Iso L₁.L (L₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} (he : eSec A ≫ φ = e ≫ eSec G)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) L₁.rig L₀.rig e) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁.L ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G L₀.L 1 T₀)} {s : LB.Sec (LPow A L₁.L 1 T)} (hs : SecRel w Ψ s₀ s)
    {x₁ x₂ : T ⟶ A} {y₁ y₂ : T₀ ⟶ G} (hx₁ : τ ≫ y₁.left = x₁.left ≫ φ) (hx₂ : τ ≫ y₂.left = x₂.left ≫ φ)
    {F₀ : LB.Sec (LPow G L₀.L ((N : ℤ) ^ 2) T₀)} (H : IsUUOver G L₀ N s₀ y₁ y₂ F₀) :
    ∃ F, IsUUOver A L₁ N s x₁ x₂ F ∧ SecRel w Ψ F₀ F := by
  obtain ⟨β₀, β, r₁, r₂, V₁, V₂, g₀, n₀, cβ, tw, sl₁, ac₁, sl₂, ac₂⟩ := H
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp L₀.isLB L₁.isLB hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull L₁.isLB α₀ gα₀ T
  have v : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) L₁.isLB gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) v tw tw' hs
  obtain ⟨U₁, l₁, a₁⟩ := exists_symLift hp L₀.isLB L₁.isLB hw h₁ h₂ hk hx₁ sl₁
  obtain ⟨U₂, l₂, a₂⟩ := exists_symLift hp L₀.isLB L₁.isLB hw h₁ h₂ hk hx₂ sl₂
  obtain ⟨s₂, b₁, R₂⟩ := a₁ _ _ _ ac₁ R₁
  obtain ⟨F, b₂, R₃⟩ := a₂ _ _ _ ac₂ R₂
  exact ⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, gα₀, nα₀, cα, tw', l₁, b₁, l₂, b₂⟩, R₃⟩

theorem pt_pow_eq_one (hK : KerPowSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) {k : ℤ}
    (hk : k = n) {T : Over S} (θ : ThetaGrp P.A P.L k T) : θ.pt ^ n = 1 := by
  subst hk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact pow_zero _
  · exact (hK S P n hn T θ.pt).1 fun _ => ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩

theorem isUUOver_move : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c S) (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)), y'.x = y.x ≫ ρ → pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left → pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ → CubIso ν w → (∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens) (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))) (h₁ : W ≤ pm ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo y'.x)).U (fun _ => i)) (h₂ : W ≤ (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo y.x)).U (fun _ => j)), (pm.appLE ((LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo y'.x)).U (fun _ => i)) W h₁).hom ((y'.s).f (fun _ => i)) = ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) ^ 1 * ((Gx y.x).presheaf.map (homOfLE h₂).op).hom ((y.s).f (fun _ => j))) → ∀ (N : ℕ) (x₁ x₂ : ptO Xo y.x ⟶ Xo.univ.t.G) (x₁' x₂' : ptO Xo y'.x ⟶ Xo.univ.t.G), x₁'.left = x₁.left ≫ ν.φ → x₂'.left = x₂.left ≫ ν.φ → ∀ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s x₁' x₂' F' → ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s x₁ x₂ F ∧ (∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens) (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))) (h₁ : W ≤ pm ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) (h₂ : W ≤ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)).U (fun _ => j)), (pm.appLE ((LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) W h₁).hom ((F').f (fun _ => i)) = ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) ^ (N ^ 2) * ((Gx y.x).presheaf.map (homOfLE h₂).op).hom ((F).f (fun _ => j))) := by
  intro hLaw E _ _ _ H Dw l Xo c S _ _ ρ ν y y' pm w _ h₁ h₂ hw hs N x₁ x₂ x₁' x₂' e₁ e₂ F' hF
  have := UnivPol.isLocallyNoetherian Xo
  have hL := Xo.univ.t.PP.isLB
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig Xo.univ.t.PP.rig ν.cm.e _
    (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2.1
  obtain ⟨F, hU, hR⟩ := exists_isUUOver ν.cart (T := ptO Xo y.x) (T₀ := ptO Xo y'.x) (τ := 𝟙 (Sp S)) hw.1
    (h₁.trans (Category.comp_id _).symm) h₂ ν.cm.e_comm hρ N
    (fun θ => pt_pow_eq_one hLaw.kerPow (UnivPol.pol Xo) (N ^ 2) (Nat.cast_pow N 2).symm θ)
    ((secRel_iff hL hL h₂ 1 Nat.cast_one.symm y'.s y.s).2 hs)
    ((Category.id_comp _).trans e₁) ((Category.id_comp _).trans e₂) hF
  exact ⟨F, hU, (secRel_iff hL hL h₂ (N ^ 2) (Nat.cast_pow N 2).symm F' F).1 hR⟩

end GlobalTheory.TranslMove
