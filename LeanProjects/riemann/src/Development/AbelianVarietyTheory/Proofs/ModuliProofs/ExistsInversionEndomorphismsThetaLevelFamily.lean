import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.EndBuild

theorem pow_val_natCast {A : Type} [Monoid A] {k : ℕ} (y : A) (hy : y ^ k = 1) (m : ℕ) :
    y ^ ((m : ZMod k)).val = y ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m hy]

def labMap {g : ℕ} {J : Type} (k : ℕ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (i : Option J) (h : Ix g k) : Ix g k :=
  i.elim (-h) (fun j i' => ((∑ c, (Mat j i' c : ZMod k).val * (h c).val : ℕ) : ZMod k))

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]

theorem lab_comp {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (ht : t.Shape Mat κ)
    (i : Option J) (h : Ix g k) :
    t.lab h ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A) = t.lab (labMap k Mat i h) := by
  haveI := t.ab.comm
  cases i with
  | none =>
    simp only [Option.elim, labMap]
    rw [GrpObj.comp_inv, Category.comp_id]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [TObj.lab, TObj.lab, linComb_eq_prod, linComb_eq_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← pow_add, ← pow_val_natCast _ (t.torsion c)]
    simp
  | some j =>
    simp only [Option.elim, labMap]
    haveI := t.hom j
    have e : t.lab h ≫ t.act j = ∏ c, (t.pt c ≫ t.act j) ^ (h c).val := by
      rw [TObj.lab, linComb_eq_prod]
      have := map_prod (IsMonHom.monoidHom (t.act j) (Out.baseOver S)) (fun c => t.pt c ^ (h c).val) Finset.univ
      simp only [map_pow] at this
      exact this
    rw [e, TObj.lab, linComb_eq_prod]
    simp only [(ht j).1, TObj.lab, linComb_eq_prod, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_val_natCast _ (t.torsion c), Finset.prod_pow_eq_pow_sum]

theorem graphIdeal_le {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w → SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w → SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' ≤ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  unfold graphIdeal
  refine le_iInf fun T => le_iInf fun _ => le_iInf fun β => le_iInf fun y => le_iInf fun v₁ => le_iInf fun v₂ =>
    le_iInf fun hy => ?_
  refine iInf_le_of_le T <| iInf_le_of_le inferInstance <| iInf_le_of_le β <| iInf_le_of_le (y ≫ e) <|
    iInf_le_of_le v₁ <| iInf_le_of_le v₂ <| iInf_le_of_le ⟨?_, ?_, ?_⟩ le_rfl
  · rw [Category.assoc, he, hy.1]
  · rw [Category.assoc]; exact h₁ _ _ _ hy.2.1
  · rw [Category.assoc]; exact h₂ _ _ _ hy.2.2

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') [IsIso e] (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w ↔ SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w ↔ SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  refine le_antisymm (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he (fun T _ y w => (h₁ T y w).1)
    (fun T _ y w => (h₂ T y w).1)) (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv e) (by rw [← he, IsIso.inv_hom_id_assoc])
    (fun T _ y w hw => ?_) (fun T _ y w hw => ?_))
  · rw [← Category.assoc, h₁]; simpa using hw
  · rw [← Category.assoc, h₂]; simpa using hw

theorem cut_fibre {o R K : Type} [CommRing o] [CommRing R] [Field K] {g N m : ℕ} [NeZero (N ^ 2)] {J : Type}
    {b : TBase o (N ^ 2)} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (i : Option J) (Q : Polynomial ℚ) (d : ℕ)
    {s : Sp K ⟶ Sp o} (t : TObj g (N ^ 2) J b s) (ht : t.Shape Mat κ)
    (σ : Ix g (N ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
    (hcut : ∀ (p q : Ix g (N ^ 2) → Ix g (N ^ 2) → K) (f : t.A ⟶ t.A), f = i.elim (𝟙 t.A)⁻¹ t.act →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (p h) ∧
        SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ N)).left (q h)) →
      CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2))
    (Z : Over (Sp R)) (M : LB Z.left) (hM : M.IsLB) (th : Ix g (N ^ 2) → M.Sec)
    (sc : Ix g (N ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g (N ^ 2) → Ix g (N ^ 2) → R)
    (hp : ∀ h, SecCoord M th (sc h).left (p h)) (x : R →+* K) (φ : t.A.left ⟶ Z.left)
    (hφ : IsPullback φ t.A.hom Z.hom (spMap x))
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left) (w : Ix g (N ^ 2) → T),
      SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w)
    (hl : ∀ h, (t.lab h ^ N).left ≫ φ = spMap x ≫ (sc h).left) :
    CutBy (graphIdeal (pullback.snd Z.hom (spMap x)) M th (pullback.fst _ _) M th
      (hφ.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ)) Q d
      (fun h c => x (p h c.1 * p (labMap (N ^ 2) Mat i h) c.2)) := by
  have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (fun a => x (p h a)) := by
    intro h
    refine (hσ K _ _).2 ?_
    have e : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ =
        spMap x ≫ (sc h).left := by
      rw [← hl h, ← Category.assoc, ← Over.comp_left, lift_snd]
    have := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R (sc h).left (p h) hM (hp h)).1 K x
    exact e ▸ this
  have H := hcut (fun h a => x (p h a)) (fun h a => x (p (labMap (N ^ 2) Mat i h) a)) _ rfl
    (fun h => ⟨hpt h, by rw [lab_comp t ht]; exact hpt _⟩)
  haveI : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom))
  have hs : (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    (pullback.condition (f := 𝟙 (Sp K)) (g := t.A.hom)).symm.trans (Category.comp_id _)
  rw [graphIdeal_eq (fst (Over.mk (𝟙 (Sp K))) t.A).left (pullback.snd Z.hom (spMap x)) _ σ (𝟙 _) _ σ
    (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A))).left M th _ M th _
    ((snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ hφ.isoPullback.hom)]
  · simpa only [map_mul] using H
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact hs
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc _ _ φ,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]

theorem exists_endomorphisms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hvd hPF hfib => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨hrep, hsm, -, hp⟩ := hPF
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  have hsm' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have key : ∀ i : Option J, ∃ F : Z ⟶ Z, ∀ (K : Type) [Field K] (x : R →+* K) (f : pullback Z.hom (spMap x) ⟶ Z.left),
      (∃ (_ : IsAlgClosed K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left)
        (hφ : IsPullback φ t'.A.hom Z.hom (spMap x)), t'.Shape Mat κ ∧
        (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
        (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
        f = hφ.isoPullback.inv ≫ (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) →
      f = pullback.fst _ _ ≫ F.left := by
    intro i
    obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
    refine GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d _
      hrep hrep hprop hprop hsm' ?_ ?_
    · rintro K _ x f ⟨_, t', φ, hφ, ht, ⟨σ, hE, hσ⟩, hl, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t' ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t'.A ⟶ t'.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · have e : spMap x ≫ spMap β = spMap (x.comp β) := by rw [← Spec.map_comp]; rfl
        clear hσ hl hφ φ
        generalize spMap x ≫ spMap β = s at e t' ht σ hE
        subst e
        exact fun p' q' f hf h => hQ K (x.comp β) t' σ p' q' f ht hf hE h
    · intro q r hq hr
      obtain ⟨P, ⟨K, _, _, x, t', hx, ht, hth⟩, hP⟩ := hvd q r hq hr
      obtain ⟨φ, hφ, hσ, -, hl⟩ := hfib K x t' ht hth
      exact ⟨P, ⟨K, _, x, _, hx, inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩, hP⟩
  choose F hF using key
  refine ⟨F, fun K _ _ x t' φ ht hfb i => ?_⟩
  obtain ⟨hφ, hσ, -, hl⟩ := hfb
  have := hF i K x _ ⟨inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc] at this
  exact this.symm

end GlobalTheory.ZM.EndBuild
end
