import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpansionLinear

section General

variable {X Y Y' : Scheme.{0}}

def secComb {L : LB X} {I : Type} [Fintype I] (c : I → Γ(X, ⊤)) (s : I → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (s i).f j
  compat := fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (s i)).compat j j'

theorem resTop_mul (W : X.Opens) (a b : Γ(X, ⊤)) : resTop W (a * b) = resTop W a * resTop W b := by
  simp only [resTop, map_mul]

theorem app_resTop (h : Y ⟶ X) (W : X.Opens) (a : Γ(X, ⊤)) :
    (h.app W).hom (resTop W a) = resTop _ (h.appTop.hom a) := by
  simp only [resTop, Scheme.Hom.appTop]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private theorem presheaf_map_resTop_eq_resTop {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := by
  simp only [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_comb {W W' : X.Opens} (hW : W' ≤ W) {I : Type} [Fintype I] (a : I → Γ(X, ⊤)) (y : I → Γ(X, W))
    (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (X.presheaf.map (homOfLE hW).op).hom x = ∑ l, resTop W' (a l) * (X.presheaf.map (homOfLE hW).op).hom (y l) := by
  subst hx
  simp only [map_sum, map_mul, presheaf_map_resTop_eq_resTop]

theorem pull_comb (h : Y ⟶ X) {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ h ⁻¹ᵁ W) {I : Type} [Fintype I]
    (a : I → Γ(X, ⊤)) (y : I → Γ(X, W)) (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom x) =
      ∑ l, resTop W' (h.appTop.hom (a l)) * (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom (y l)) := by
  subst hx
  simp only [map_sum, map_mul, app_resTop, presheaf_map_resTop_eq_resTop]

private theorem sum_mul_sum_eq_sum_reindex_sigma {M : Type} [CommRing M] {I : Type} [Fintype I] {m : I → ℕ} {N : ℕ}
    (e : Fin N ≃ Σ l, Fin (m l)) (A : I → M) (C P : ∀ l, Fin (m l) → M) (C' : Fin N → M)
    (hC : ∀ i, C' i = A (e i).1 * C (e i).1 (e i).2) :
    ∑ l, A l * ∑ i, C l i * P l i = ∑ i, C' i * P (e i).1 (e i).2 := by
  rw [Fintype.sum_equiv e (fun i => C' i * P (e i).1 (e i).2) (fun x => A x.1 * C x.1 x.2 * P x.1 x.2)
    (fun i => by rw [hC]), Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

theorem secLin_comb (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y)
    {I : Type} [Fintype I] (a : I → Γ(Y', ⊤)) (s : I → LB.Sec (LB.LinComb L φ₁ ε₁))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (h₀ : ∀ j, s₀.f j = ∑ l, resTop _ (a l) * (s l).f j)
    {m : I → ℕ} (σ : ∀ l, Fin (m l) → LB.Sec (LB.LinComb L φ₂ ε₂)) (c : ∀ l, Fin (m l) → Γ(Y', ⊤))
    (H : ∀ l, GeneratorPullback.SecLin L φ₁ ε₁ (s l) φ₂ ε₂ (σ l) h (c l)) {N : ℕ} (e : Fin N ≃ Σ l, Fin (m l))
    (c' : Fin N → Γ(Y', ⊤)) (hc' : ∀ i, c' i = a (e i).1 * c (e i).1 (e i).2) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₀ φ₂ ε₂ (fun i => σ (e i).1 (e i).2) h c' := by
  intro j₁ j₂ hc
  rw [res_comb (W := L.wchart φ₁ j₁) _ a (fun l => (s l).f j₁) (s₀.f j₁) (h₀ j₁)]
  have H' := fun l => H l j₁ j₂ hc
  simp only [H']
  exact sum_mul_sum_eq_sum_reindex_sigma e _ _ _ _ (fun i => by rw [hc', resTop_mul])

theorem isoRelM_comb {X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁) (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {I : Type} [Fintype I]
    (a : I → LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : I → LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (α : I → Γ(Z₁, ⊤)) (β : I → Γ(Z₂, ⊤)) (hαβ : ∀ l, h₁.appTop.hom (α l) = h₂.appTop.hom (β l))
    (a₀ : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (ha : ∀ j, a₀.f j = ∑ l, resTop _ (α l) * (a l).f j)
    (hb : ∀ j, b₀.f j = ∑ l, resTop _ (β l) * (b l).f j)
    (H : ∀ l, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (a l) g₂ h₂ (b l)) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a₀ g₂ h₂ b₀ := by
  refine ⟨e₁, e₂, fun p j₁ j₂ hj₁ hj₂ => ?_⟩
  rw [pull_comb h₂ (W := L₂.wchart (fun _ => g₂) j₂) _ β (fun l => (b l).f j₂) (b₀.f j₂) (hb j₂),
    pull_comb h₁ (W := L₁.wchart (fun _ => g₁) j₁) _ α (fun l => (a l).f j₁) (a₀.f j₁) (ha j₁), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(H l).2.2 p j₁ j₂ hj₁ hj₂, ← hαβ l, mul_left_comm]

theorem scal_mul {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (a b : R) :
    scal p (a * b) = scal p a * scal p b := by
  simp only [scal, map_mul]

end General

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {I : Type} (S : Finset I) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ l ∈ S, s l).s α).f j = ∑ l ∈ S, ((s l).s α).f j := by
  classical
  refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
  · rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem genF_left_comp_fst_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_fst]

private theorem genF_left_comp_snd_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem expandsF_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (s : Fin n → Fam D.toPre F k) (t₀ : LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ l, U.ExpandsF F k w (t l) (s l)) → (∀ jj, t₀.f jj = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t l).f jj) → U.ExpandsF F k w t₀ (∑ l, c l • s l) := by
  intro R _ _ I D A G _ _ U F _ _ k w hw n c t s t₀ ht h0
  choose σ hσ using ht
  choose m cc σ₁ f hE hS hF using fun l => (hσ l).2
  have e₂ : 𝟙 _ ≫ UnifPre.gFK (G := G) F =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) := by
    unfold UnifPre.gFK
    exact Category.id_comp _
  refine ⟨secComb (fun l => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c l)) σ, ?_, ?_⟩
  · exact isoRelM_comb A.L U.LG.L _ _ w _ k _ _ _ _ (genF_left_comp_snd_TFK U F) e₂ t σ
      (fun l => scal (fst (TFK (R := R) F) A.A).left (c l)) _
      (fun l => by rw [← genF_left_comp_fst_TFK U F]; rfl) t₀ _ h0 (fun _ => rfl) (fun l => (hσ l).1)
  · refine ⟨∑ l, m l, fun i => c (finSigmaFinEquiv.symm i).1 * cc _ (finSigmaFinEquiv.symm i).2,
      fun i => σ₁ _ (finSigmaFinEquiv.symm i).2, fun i => f _ (finSigmaFinEquiv.symm i).2,
      fun i e => hE _ _ e, ?_, fun α => ?_⟩
    · exact secLin_comb U.LG.L _ _ _ _ _ _ σ _ (fun _ => rfl) σ₁ _ hS finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)
    · refine secLin_comb D.toPre.P.L _ _ _ _ _
        (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l)) (fun l => (s l).s α) _
        (fun j => by rw [fam_sum_f]; rfl) (fun l i => f l i α) _ (fun l => hF l α) finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)

end GlobalTheory.ExpansionLinear
