import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.PureWt

theorem cf_diag {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
    {f : A →+* R} {m : Multiplicative X →* R}
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (σ : R →+ R) (κ : X → A)
    (hσ : ∀ b ψ, σ (f b * m (Multiplicative.ofAdd ψ)) = f (κ ψ) * (f b * m (Multiplicative.ofAdd ψ)))
    (χ : X) (s : R) : WtPart.cf hb χ (σ s) = κ χ * WtPart.cf hb χ s := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, WtPart.cf_zero, mul_zero]
  | add x y hx hy => simp only [map_add, WtPart.cf_add, mul_add, hx, hy]
  | single ψ b =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, hσ, ← _root_.mul_assoc, ← map_mul, WtPart.cf_mono,
      WtPart.cf_mono]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

theorem exists_char_ne {k X K : Type} [Field k] [Infinite k] [AddCommGroup X] (b : Module.Basis K ℤ X)
    {χ α : X} (h : χ ≠ α) :
    ∃ t : Multiplicative X →* kˣ, t (Multiplicative.ofAdd χ) ≠ t (Multiplicative.ofAdd α) := by
  obtain ⟨i, hi⟩ : ∃ i, b.repr χ i ≠ b.repr α i := by
    by_contra hn
    push Not at hn
    exact h (b.repr.injective (Finsupp.ext hn))
  have hn : (b.repr χ i - b.repr α i).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 hi)
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x ^ (b.repr χ i - b.repr α i).natAbs ≠ 1 := by
    by_contra hc
    push Not at hc
    generalize (b.repr χ i - b.repr α i).natAbs = n at hn hc
    have : NeZero n := ⟨hn⟩
    have : Finite kˣ := Finite.of_surjective (fun x : rootsOfUnity n k => (x : kˣ))
      fun x => ⟨⟨x, (mem_rootsOfUnity n x).2 (hc x)⟩, rfl⟩
    have : Finite k := Finite.of_surjective (fun x : Option kˣ => x.elim (0 : k) Units.val) fun x => by
      by_cases hx : x = 0
      · exact ⟨none, hx.symm⟩
      · exact ⟨some (Units.mk0 x hx), rfl⟩
    exact not_finite k
  refine ⟨(zpowersHom kˣ x).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom), fun e => hx ?_⟩
  have e' : x ^ (b.repr χ i) = x ^ (b.repr α i) := e
  rw [pow_natAbs_eq_one, zpow_sub, e', mul_inv_cancel]

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

theorem translate_mem {Z : Over S} (τ : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (V : E.B.left.Opens) (z : Z.left)
    (hz : g.left z ∈ D.q.left ⁻¹ᵁ V) : ((τ ≫ D.i) * g).left z ∈ D.q.left ⁻¹ᵁ V :=
  haveI := D.q_hom
  GtBaseChange.translate_mem D.q D.i D.isKernel τ g V z hz

theorem gm_points {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd χ)) =
      gm τ.left z ⊤ (charUnit S X χ) := by
  apply Units.ext
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial, splitTorusPointsEquiv_val]
  rfl

theorem hasWt_mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) (c : Γ(E.B.left, V)) (χ : E.X) :
    UFib.HasWt D.i (D.q.left ⁻¹ᵁ V)
      ((D.q.left.app V).hom c * WtPart.mono D j V h (Multiplicative.ofAdd χ)) χ := by
  intro Z τ g z hz
  have hz' := translate_mem D τ g V z hz
  set v := AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom with hv
  let A : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ := (gm ((τ ≫ D.i) * g).left z _).comp v
  let C : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ :=
    (gm (𝟙 Z.left) z ⊤).comp (splitTorusPointsEquiv S E.X Z τ) * (gm g.left z _).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k) := by
      simp [hv]
    refine congrArg Additive.ofMul ?_
    change gm _ z _ (v (Multiplicative.ofAdd (E.basis k))) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))) *
        gm _ z _ (v (Multiplicative.ofAdd (E.basis k)))
    rw [hvk, gm_points, gm_res _ z _ hz, gm_res _ z _ hz']
    exact (GtBaseChange.hasWeight_iff D.i _ _ _ (D.act_le _) _).2 (D.equiv j k) Z τ g z (h hz)
  have e : gm ((τ ≫ D.i) * g).left z _ (v (Multiplicative.ofAdd χ)) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd χ)) *
        gm g.left z _ (v (Multiplicative.ofAdd χ)) :=
    congrArg (fun φ => Additive.toMul (φ χ)) hAC
  have em : WtPart.mono D j V h (Multiplicative.ofAdd χ) = (v (Multiplicative.ofAdd χ)).val := rfl
  rw [em, gs_mul _ z _ hz, gs_mul _ z _ hz', gs_unit _ z _ hz, gs_unit _ z _ hz', e, gm_points,
    gs_pull _ _ z V hz, gs_pull _ _ z V hz', TorusTranslate.translate_comp_q, Units.val_mul]
  ring

theorem translate_appLE (V : E.B.left.Opens) (τ : G ⟶ splitTorus S E.X)
    (hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (χ : E.X) (hs : UFib.HasWt D.i _ s χ) (a : Γ(S, ⊤))
    (ha : τ.left.appTop.hom (charUnit S E.X χ).val = G.hom.appTop.hom a) :
    (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s =
      (D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a) * s := by
  refine fn_ext fun z hz => ?_
  have e := hs G τ (𝟙 G) z hz
  have e₁ : gs (𝟙 G.left) z _ ((((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s) =
      gs ((τ ≫ D.i) * 𝟙 G).left z _ s :=
    (gs_res (𝟙 G.left) z hle hz _).trans ((gs_pull (𝟙 G.left) ((τ ≫ D.i) * 𝟙 G).left z (D.q.left ⁻¹ᵁ V) (hle hz) s).trans (by rw [Category.id_comp]))
  have e₂ : gs (𝟙 G.left) z _ ((D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a)) =
      gs G.hom z ⊤ a := by
    refine (gs_pull (𝟙 G.left) _ z V hz _).trans ((gs_res (𝟙 G.left ≫ D.q.left) z (U := E.B.hom ⁻¹ᵁ ⊤) le_top hz _).trans
      ((gs_pull _ E.B.hom z ⊤ trivial a).trans ?_))
    rw [Category.id_comp, Over.w]
  rw [e₁, e, gs_mul (𝟙 G.left) z (D.q.left ⁻¹ᵁ V) hz, e₂, gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  exact congrArg₂ (· * ·) (congrArg (G.left.presheaf.germ ⊤ z trivial).hom ha) rfl

theorem hasWt_iff_weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  intro k _ _ E G _ D j V hV h f α
  have hb := D.coord j V hV h
  constructor
  · intro hf χ hχ
    obtain ⟨t, ht⟩ := exists_char_ne (k := k) E.basis hχ
    let c : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    let e := splitTorusPointsEquiv (Sp k) E.X G
    let τ := e.symm ((Units.map (G.hom.appTop.hom.comp c).toMonoidHom).comp t)
    have hτ : ∀ ψ, τ.left.appTop.hom (charUnit (Sp k) E.X ψ).val =
        G.hom.appTop.hom (c (t (Multiplicative.ofAdd ψ))) := fun ψ => by
      rw [← splitTorusPointsEquiv_val]
      change (e (e.symm _) _).val = _
      rw [e.apply_symm_apply]
      rfl
    have hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) :=
      fun z hz => translate_mem D τ (𝟙 G) V z hz
    let κ : k →+* Γ(E.B.left, V) := (E.B.hom.appLE ⊤ V le_top).hom.comp c
    have e₁ := cf_diag hb (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom.toAddMonoidHom
      (fun ψ => κ (t (Multiplicative.ofAdd ψ)))
      (fun b ψ => translate_appLE D V τ hle _ ψ (hasWt_mono D j V h b ψ) _ (hτ ψ)) χ f
    have e₂ := cf_diag hb (AddMonoidHom.mulLeft ((D.q.left.app V).hom (κ (t (Multiplicative.ofAdd α)))))
      (fun _ => κ (t (Multiplicative.ofAdd α))) (fun _ _ => rfl) χ f
    have e₃ := e₁.symm.trans ((congrArg (WtPart.cf hb χ) (translate_appLE D V τ hle f α hf _ (hτ α))).trans e₂)
    rw [← sub_eq_zero, ← sub_mul, ← map_sub] at e₃
    exact ((IsUnit.mk0 _ (sub_ne_zero.2 fun e => ht (Units.ext e))).map κ).mul_right_eq_zero.1 e₃
  · intro hf
    have e : f = (D.q.left.app V).hom (WtPart.cf hb α f) * WtPart.mono D j V h (Multiplicative.ofAdd α) := by
      refine WtPart.cf_ext hb fun χ => ?_
      rw [WtPart.cf_mono]
      split_ifs with hχ
      · rw [hχ]
      · exact hf χ fun e => hχ e.symm
    rw [e]
    exact hasWt_mono D j V h _ α

end GlobalTheory.ZH.PureWt
end
