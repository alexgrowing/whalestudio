import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem fam_mul_Oinv {H : Type} [CommGroup H] (Ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → H)
    (α : D.toPre.X) :
    (∏ a, Ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, Ω (Oφl U e α a) ^ Oinvε a =
      Ω (pGl U e) ^ k := by
  have a₀ : (pGl U e) ≫ D.toPre.famφB α 0 = (pGl U e) := Category.comp_id _
  have a₁ : (pGl U e) ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : (pGl U e) ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : (pGl U e) ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = (pGl U e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

theorem sval_eq_sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) :
    sval σ q z N = sv U k σ q z (N q) :=
  sval_of σ q z N (fun _ => N q) (fun _ => congrArg N (Category.comp_id _))

end

theorem exp_alg {A X X₁ X₂ : Type} [CommRing A] (k : ℕ) (E : X ≃ X₁ × X₂) (S₁ : Finset X₁) (S₂ : Finset X₂)
    {oM oL W W₁ W₂ : Aˣ} {s s₁ s₂ : A} {f : X → A} {f₁ : X₁ → A} {f₂ : X₂ → A} {t a b : X → Aˣ} {t₁ : X₁ → Aˣ}
    {t₂ : X₂ → Aˣ} (hW : oM * W = W₁ * W₂ * oL) (hs : (oL ^ k).val * s = s₁ * s₂)
    (hf : ∀ x, (a x).val * f x = f₁ (E x).1 * f₂ (E x).2) (ht : ∀ x, b x * t x = t₁ (E x).1 * t₂ (E x).2)
    (ho : ∀ x, a x * b x = oM ^ k) (H₁ : (W₁ ^ k).val * s₁ = ∑ x ∈ S₁, f₁ x * (t₁ x).val)
    (H₂ : (W₂ ^ k).val * s₂ = ∑ x ∈ S₂, f₂ x * (t₂ x).val) :
    (W ^ k).val * s = ∑ x ∈ (S₁ ×ˢ S₂).map E.symm.toEmbedding, f x * (t x).val := by
  refine (oM ^ k).mul_right_inj.1 ?_
  rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul, _root_.mul_assoc, hs, mul_pow,
    Units.val_mul, _root_.mul_mul_mul_comm, H₁, H₂, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_map,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨y, rfl⟩ := E.surjective x
  have e₀ : E.symm.toEmbedding (E y) = y := E.symm_apply_apply y
  rw [e₀, _root_.mul_mul_mul_comm, ← hf, ← Units.val_mul, ← ht, ← ho y, Units.val_mul, Units.val_mul,
    _root_.mul_mul_mul_comm]

set_option maxHeartbeats 1600000 in

theorem expandsAt_boxProd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ A U hq wM wL e k hp₁ hp₂ hT hW σ σ₁ σ₂ f f₁ f₂ hσ hf
    hE₁ hE₂
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U₁ e k σ₁ f₁ hE₁
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U₂ e k σ₂ f₂ hE₂
  have hg₁ := thick_fstG I e (fst G₁ G₂)
  have hg₂ := thick_fstG I e (snd G₁ G₂)
  revert hp₁ hp₂ hT hW hg₁ hg₂
  generalize ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left = ρ₁
  generalize ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left = ρ₂
  intro hp₁ hp₂ hT hW hg₁ hg₂
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₁).left at ρ₁
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₂).left at ρ₂
  change pGl U e ≫ p₁.left = ρ₁ ≫ pGl U₁ e at hp₁
  change pGl U e ≫ p₂.left = ρ₂ ≫ pGl U₂ e at hp₂
  change fGl I (G₁ ⊗ G₂) e ≫ (fst G₁ G₂).left = ρ₁ ≫ fGl I G₁ e at hg₁
  change fGl I (G₁ ⊗ G₂) e ≫ (snd G₁ G₂).left = ρ₂ ≫ fGl I G₂ e at hg₂
  let E : D.toPre.X ≃ D₁.toPre.X × D₂.toPre.X := Equiv.ofBijective _ hq
  refine expandsAt_of_val U e k σ f ((S₁ ×ˢ S₂).map E.symm.toEmbedding) fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.toPre.P.isLB y
  have hF : ∀ α, (∏ a, om wM y J₁ J₂ J (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a).val *
      sval (f α) (pGl U e) y J =
      sval (f₁ (E α).1) (ρ₁ ≫ pGl U₁ e) y J₁ * sval (f₂ (E α).2) (ρ₂ ≫ pGl U₂ e) y J₂ := fun α => by
    rw [← hp₁, ← hp₂]
    exact hf α _ (pGl U e) y J₁ J₂ J hJ₁ hJ₂ hJ
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · refine (Units.mul_right_eq_zero _).1 ((hF α).trans ?_)
    by_cases h₁ : (E α).1 ∈ S₁
    · have h₂ : (E α).2 ∉ S₂ := fun h₂ =>
        hα (Finset.mem_map.2 ⟨E α, Finset.mem_product.2 ⟨h₁, h₂⟩, E.symm_apply_apply α⟩)
      rw [(hS₂ _ ρ₂ y J₂ hJ₂).1 _ h₂, mul_zero]
    · rw [(hS₁ _ ρ₁ y J₁ hJ₁).1 _ h₁, zero_mul]
  · obtain ⟨N, hN, eN⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit) (fun _ => fGl I (G₁ ⊗ G₂) e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : N (fGl I (G₁ ⊗ G₂) e) = jL := eN ⟨⟩
    obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at U₁.LG.isLB y
    obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at U₂.LG.isLB y
    have hT' : ∀ α, (∏ a, om wM y J₁ J₂ J (Oφl U e α a) ^ Oinvε a) * val (tG U e α) (𝟙 _) y J =
        val (tG U₁ e (E α).1) ρ₁ y J₁ * val (tG U₂ e (E α).2) ρ₂ y J₂ := fun α => by
      have := hT α _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
      simp only [Category.id_comp] at this
      exact this
    have hW' : om wM y J₁ J₂ J (pGl U e) * wv U e (𝟙 _) y (J (pGl U e)) (N (fGl I (G₁ ⊗ G₂) e)) =
        wv U₁ e ρ₁ y (J₁ (ρ₁ ≫ pGl U₁ e)) (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          wv U₂ e ρ₂ y (J₂ (ρ₂ ≫ pGl U₂ e)) (N₂ (ρ₂ ≫ fGl I G₂ e)) * om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) := by
      have := hW _ (𝟙 _) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at this
      rw [← hp₁, ← hp₂, ← hg₁, ← hg₂]
      exact this
    have hσ' : (om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) ^ k).val *
        sv U k σ (fGl I (G₁ ⊗ G₂) e) y (N (fGl I (G₁ ⊗ G₂) e)) =
        sv U₁ k σ₁ (ρ₁ ≫ fGl I G₁ e) y (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          sv U₂ k σ₂ (ρ₂ ≫ fGl I G₂ e) y (N₂ (ρ₂ ≫ fGl I G₂ e)) := by
      have := hσ _ (fGl I (G₁ ⊗ G₂) e) y N₁ N₂ N hN₁ hN₂ hN
      rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast] at this
      rw [← sval_eq_sv, ← sval_eq_sv, ← sval_eq_sv, ← hg₁, ← hg₂]
      exact this
    exact exp_alg k E S₁ S₂ hW' hσ' hF hT' (fun α => fam_mul_Oinv U e k (om wM y J₁ J₂ J) α)
      ((hS₁ _ ρ₁ y J₁ hJ₁).2 _ (hN₁ (ρ₁ ≫ fGl I G₁ e))) ((hS₂ _ ρ₂ y J₂ hJ₂).2 _ (hN₂ (ρ₂ ≫ fGl I G₂ e)))

end GlobalTheory.ProdUnif
