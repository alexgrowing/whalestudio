import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelEigen

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem sval_act {n : ℤ} {θ : ThetaGrp A L n T} {s s' : LB.Sec (LPow A L n T)} (H : IsActOf A L n θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) (hJ : Good L z J) :
    sval s' r z J = (tval θ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hz : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [sval_of s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)]
  exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
    ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
      ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))

theorem translT_snd_comp (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ snd T A ≫ a = snd T A ≫ a := by
  rw [← Category.assoc, translT, lift_snd]
  show ((fst T A ≫ c) * snd T A) ≫ a = _
  rw [MonObj.mul_comp, Category.assoc, hc, MonObj.comp_one, _root_.one_mul]

theorem translT_whisker (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ T ◁ a = T ◁ a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, whiskerLeft_snd, translT_snd_comp a hc]

theorem translT_comm [IsCommMonObj A] (x y : T ⟶ A) : translT A x ≫ translT A y = translT A y ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.assoc, H1.transl_snd]
    exact H1.transl_comm x y

theorem exists_kernel_lift (hL : L.IsLB) (a : A ⟶ A) [IsMonHom a] {m k : ℤ}
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ a).left] ![m, -k])) (hmu : mu.IsGen)
    {c : T ⟶ A} (hc : c ≫ a = 1) :
    ∃ θ : ThetaGrp A L m T, θ.pt = c ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θ r z J = val mu r z J * (val mu (r ≫ (translT A c).left) z J)⁻¹ := by
  have e₀ : (translT A c).left ≫ (snd T A).left = (translPt A c).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT A c).left ≫ (snd T A ≫ a).left = (snd T A ≫ a).left := by
    rw [← Over.comp_left, translT_snd_comp a hc]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A c).left]) (ε' := ![m, -m])
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁,
        zpow_neg, inv_inv, Pi.neg_apply]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ mu (LB.invGen L _ _ (LB.pullGen L _ _ mu (translT A c).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hmu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hmu _)))
  refine ⟨⟨c, u, hu⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem commIsOf_of_weilIs (hL : L.IsLB) [Unique T.left] {n : ℤ} (θx θy : ThetaGrp A L n T)
    {e : Γ(T.left, ⊤)ˣ} (H : WeilIs A L n θx.pt θy.pt e) : CommIsOf A L n θx θy e := by
  obtain ⟨V, hV, -, H⟩ := H default
  obtain rfl : V = ⊤ := top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hV
  let h := overResι (T := T) ⊤
  have : IsIso h.left := inferInstanceAs (IsIso (Scheme.topIso T.left).hom)
  have : IsIso ((Over.forget S).map h) := this
  have : IsIso h := isIso_of_reflects_iso h (Over.forget S)
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1 (H θx' θy' hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  obtain ⟨r', rfl⟩ : ∃ r' : Z ⟶ (overRes (T := T) ⊤ ⊗ A).left, r = r' ≫ (h ▷ A).left :=
    ⟨r ≫ (inv (h ▷ A)).left, by rw [Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.comp_id]⟩
  have t : ∀ x : T ⟶ A, (r' ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r' ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r' ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom e) =
      gm ((r' ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ e := by
    refine (gm_pull (r' ≫ (fst (overRes (T := T) ⊤) A).left) h.left z ⊤ trivial e).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  have := H' Z r' z J hJ
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t] at this
  exact this.trans (congrArg _ g)

end GlobalTheory.KernelEigen

namespace GlobalTheory

open KernelEigen CommPairing in

theorem translate_pullback_eigensection : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (a : A ⟶ A), IsMonHom a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])), mu.IsGen → ∀ (s : LB.Sec (LPow A L (k : ℤ) (Over.mk p))) (t' t : LB.Sec (LPow A L ((k * N : ℕ) : ℤ) (Over.mk p))), (∀ (z : (Over.mk p ⊗ A).left) (J), Good L z J → sval t' (𝟙 _) z J = (val mu (𝟙 _) z J).val * sval s (Over.mk p ◁ a).left z J) → ∀ θ : ThetaGrp A L ((k * N : ℕ) : ℤ) (Over.mk p), IsActOf A L ((k * N : ℕ) : ℤ) θ t' t → ∀ (c : Over.mk p ⟶ A) (e : Γ((Over.mk p).left, ⊤)ˣ), c ≫ a = 1 → WeilIs A L ((k * N : ℕ) : ℤ) c θ.pt e → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ A).left) (z : Z) (J), Good L z J → sval t (r ≫ (translT A c).left) z J * (val mu r z J).val = gs (r ≫ (fst (Over.mk p) A).left) z ⊤ e.val * (sval t r z J * (val mu (r ≫ (translT A c).left) z J).val) := by
  intro S A _ _ L hL K _ p a ha N k mu hmu s t' t ht' θ hθ c e hc hW Z r z J hJ
  haveI : Unique (Over.mk p).left := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨θc, rfl, hv⟩ := exists_kernel_lift hL a mu hmu hc
  have hC := (commIsOf_iff hL _ _ _).1 (commIsOf_of_weilIs hL θc θ hW) Z r z J hJ
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff hL _ _ t' _ _ s (Over.mk p ◁ a).left _ _ mu
  have ht := hs.1 (hs.2 fun y J hJ => by rw [ht' y J hJ, Category.id_comp, _root_.mul_comm])
  have e₁ : (r ≫ (translT A θc.pt).left) ≫ (translT A θ.pt).left =
      (r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, translT_comm]
  have e₂ : ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) ≫ (Over.mk p ◁ a).left =
      (r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left := by
    rw [Category.assoc, ← Over.comp_left, translT_whisker a hc]
  rw [sval_act hθ _ z J hJ, sval_act hθ _ z J hJ, e₁, ht _ _ z J hJ, ht _ _ z J hJ, e₂,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ z ⊤ trivial]
  rw [hv _ _ z J hJ, hv _ _ z J hJ] at hC
  generalize tval θ (r ≫ (translT A θc.pt).left) z J = x₁ at hC ⊢
  generalize tval θ r z J = x₂ at hC ⊢
  generalize val mu ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) z J = x₃ at hC ⊢
  generalize val mu (r ≫ (translT A θ.pt).left) z J = x₄ at hC ⊢
  generalize val mu (r ≫ (translT A θc.pt).left) z J = x₅ at hC ⊢
  generalize val mu r z J = x₆ at hC ⊢
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm (r ≫ (fst (Over.mk p) A).left) z ⊤ e = x₇ at hC ⊢
  have key : x₁ * x₃ * x₆ = x₇ * x₂ * x₄ * x₅ := by
    apply Additive.ofMul.injective
    have a₀ := congrArg Additive.ofMul hC
    simp only [ofMul_mul, ofMul_inv] at a₀ ⊢
    linear_combination (norm := abel) a₀
  have key' := congrArg Units.val key
  simp only [Units.val_mul] at key'
  linear_combination (sval s ((r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left) z J) * key'

end GlobalTheory
