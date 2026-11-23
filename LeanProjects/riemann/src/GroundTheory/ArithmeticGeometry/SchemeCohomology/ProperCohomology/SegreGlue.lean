import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] (n m : ℕ)

abbrev prodP : Scheme.{u} := pullback (toSpecBase A n) (toSpecBase A m)

def segreIndex : Fin (n + 1) × Fin (m + 1) ≃ Fin (n * m + n + m + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

variable {n m}

abbrev segreOpen (i : Fin (n + 1)) (j : Fin (m + 1)) : (prodP A n m).Opens :=
  pullback.fst (toSpecBase A n) (toSpecBase A m) ⁻¹ᵁ Proj.basicOpen (grading A n) (X i) ⊓
    pullback.snd (toSpecBase A n) (toSpecBase A m) ⁻¹ᵁ Proj.basicOpen (grading A m) (X j)

omit [CommRing A] in

lemma top_le_preimage_ι_comp {Y Z : Scheme.{u}} (V : Y.Opens) (q : Y ⟶ Z) {U : Z.Opens}
    (h : V ≤ q ⁻¹ᵁ U) : ⊤ ≤ (V.ι ≫ q) ⁻¹ᵁ U := by
  intro x _
  exact h x.2

omit [CommRing A] in

lemma homOfLE_appTop_appLE {Y Z : Scheme.{u}} (q : Y ⟶ Z) {U : Z.Opens} {V W : Y.Opens}
    (hW : W ≤ V) (hV : V ≤ q ⁻¹ᵁ U) (s : Γ(Z, U)) :
    (Y.homOfLE hW).appTop ((V.ι ≫ q).appLE U ⊤ (top_le_preimage_ι_comp V q hV) s) =
      (W.ι ≫ q).appLE U ⊤ (top_le_preimage_ι_comp W q (hW.trans hV)) s := by
  have key : ∀ (g : W.toScheme ⟶ Z) (_ : g = W.ι ≫ q) (e : (⊤ : W.toScheme.Opens) ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e s = (W.ι ≫ q).appLE U ⊤ (top_le_preimage_ι_comp W q (hW.trans hV)) s := by
    rintro _ rfl _
    rfl
  have h1 : (Y.homOfLE hW).appTop = (Y.homOfLE hW).appLE ⊤ ⊤ (fun _ _ => trivial) :=
    (Scheme.Hom.appLE_eq_app _).symm
  rw [h1]
  exact (congr($(Scheme.Hom.appLE_comp_appLE (Y.homOfLE hW) (V.ι ≫ q) U ⊤ ⊤ _ _) s)).trans
    (key _ (Scheme.homOfLE_ι_assoc _ _ _) _)

variable {A}

lemma appLE_chartHom_identity {Y : Scheme.{u}} (q : Y ⟶ projectiveSpace A n) (j k : Fin (n + 1))
    (W : Y.Opens) (hj : W ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X j))
    (hk : W ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k)) {t : ℕ}
    {a : MvPolynomial (Fin (n + 1)) A} (ha : a ∈ grading A n t) :
    q.appLE _ W hj (chartHom j a) * q.appLE _ W hk (chartHom k (X j)) ^ t =
      q.appLE _ W hk (chartHom k a) := by
  have hW : W ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k * X j) := by
    rw [Proj.basicOpen_mul, Scheme.Hom.preimage_inf]
    exact le_inf hk hj
  have hres : ∀ {U : (projectiveSpace A n).Opens}
      (hU : Proj.basicOpen (grading A n) (X k * X j) ≤ U) (hWU : W ≤ q ⁻¹ᵁ U) (z : Γ(projectiveSpace A n, U)),
      q.appLE U W hWU z = q.appLE _ W hW ((projectiveSpace A n).presheaf.map (homOfLE hU).op z) :=
    fun hU hWU z => by rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  have ha' : a ∈ grading A n (t • 1) := by rwa [smul_eq_mul, mul_one]
  rw [hres (basicOpen_mul_le_right j k), hres (basicOpen_mul_le_left j k),
    hres (basicOpen_mul_le_left j k), chartHom_of_mem j ha]
  exact map_mul_pow_eq _ t (chart_identity j k ha')

lemma map_eq_pow_mul_of_isHomogeneous {σ R S : Type*} [CommRing R] [CommRing S]
    (φ ψ : MvPolynomial σ R →+* S) (c : S) (hC : ∀ r, ψ (C r) = φ (C r))
    (hX : ∀ i, ψ (X i) = c * φ (X i)) {m : ℕ} {p : MvPolynomial σ R} (hp : p.IsHomogeneous m) :
    ψ p = c ^ m * φ p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = m := by
    have := hp (mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  rw [monomial_eq, map_mul, map_mul, hC, map_finsuppProd, map_finsuppProd]
  simp only [map_pow, hX, mul_pow]
  have hc : (d.prod fun _ k => c ^ k) = c ^ m := by
    rw [← hdeg, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [Finsupp.prod_mul, hc]
  ring

variable (A)

def segreU (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Fin (n + 1)) : Γ(segreOpen A i j, ⊤) :=
  ((segreOpen A i j).ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)).appLE
    (Proj.basicOpen (grading A n) (X i)) ⊤ (top_le_preimage_ι_comp _ _ inf_le_left) (chartHom i (X a))

def segreV (i : Fin (n + 1)) (j : Fin (m + 1)) (b : Fin (m + 1)) : Γ(segreOpen A i j, ⊤) :=
  ((segreOpen A i j).ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)).appLE
    (Proj.basicOpen (grading A m) (X j)) ⊤ (top_le_preimage_ι_comp _ _ inf_le_right) (chartHom j (X b))

def segreRing (i : Fin (n + 1)) (j : Fin (m + 1)) :
    MvPolynomial (Fin (n * m + n + m + 1)) A →+* Γ(segreOpen A i j, ⊤) :=
  eval₂Hom ((((segreOpen A i j).ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)).appLE
      (Proj.basicOpen (grading A n) (X i)) ⊤ (top_le_preimage_ι_comp _ _ inf_le_left)).hom.comp
      ((chartHom i).comp C))
    (fun c => segreU A i j ((segreIndex n m).symm c).1 * segreV A i j ((segreIndex n m).symm c).2)

lemma segreRing_X (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Fin (n + 1)) (b : Fin (m + 1)) :
    segreRing A i j (X (segreIndex n m (a, b))) = segreU A i j a * segreV A i j b := by
  rw [segreRing, eval₂Hom_X', Equiv.symm_apply_apply]

lemma segreU_self (i : Fin (n + 1)) (j : Fin (m + 1)) : segreU A i j i = 1 := by
  rw [segreU, chartHom_X_self, map_one]

lemma segreV_self (i : Fin (n + 1)) (j : Fin (m + 1)) : segreV A i j j = 1 := by
  rw [segreV, chartHom_X_self, map_one]

lemma segreRing_irrelevant (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (HomogeneousIdeal.irrelevant (grading A (n * m + n + m))).toIdeal.map (segreRing A i j) = ⊤ :=
  map_irrelevant_eq_top _ (segreIndex n m (i, j)) (by
    rw [segreRing_X, segreU_self, segreV_self, mul_one]
    exact isUnit_one)

def segreLocal (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (segreOpen A i j).toScheme ⟶ projectiveSpace A (n * m + n + m) :=
  Proj.fromOfGlobalSections (grading A _) (segreRing A i j) (segreRing_irrelevant A i j)

lemma segreRing_res_X (i : Fin (n + 1)) (j : Fin (m + 1)) {W : (prodP A n m).Opens}
    (hW : W ≤ segreOpen A i j) (a : Fin (n + 1)) (b : Fin (m + 1)) :
    ((prodP A n m).homOfLE hW).appTop (segreRing A i j (X (segreIndex n m (a, b)))) =
      (W.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)).appLE _ ⊤
          (top_le_preimage_ι_comp _ _ (hW.trans inf_le_left)) (chartHom i (X a)) *
        (W.ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)).appLE _ ⊤
          (top_le_preimage_ι_comp _ _ (hW.trans inf_le_right)) (chartHom j (X b)) := by
  rw [segreRing_X, map_mul, segreU, segreV, homOfLE_appTop_appLE _ hW inf_le_left,
    homOfLE_appTop_appLE _ hW inf_le_right]

lemma segreRing_res_C (i : Fin (n + 1)) (j : Fin (m + 1)) {W : (prodP A n m).Opens}
    (hW : W ≤ segreOpen A i j) (r : A) :
    ((prodP A n m).homOfLE hW).appTop (segreRing A i j (C r)) =
      (W.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)).appLE _ ⊤
          (top_le_preimage_ι_comp _ _ (hW.trans inf_le_left)) (chartHom i (C r)) := by
  rw [segreRing, eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply]
  exact homOfLE_appTop_appLE _ hW inf_le_left _

lemma segreLocal_agree (i k : Fin (n + 1)) (j l : Fin (m + 1)) :
    (prodP A n m).homOfLE (inf_le_left : segreOpen A i j ⊓ segreOpen A k l ≤ _) ≫
        segreLocal A i j =
      (prodP A n m).homOfLE (inf_le_right : segreOpen A i j ⊓ segreOpen A k l ≤ _) ≫
        segreLocal A k l := by
  rw [segreLocal, segreLocal,
    ProjHom.comp_fromOfGlobalSections _ _ (fun c => X c) (fun _ => 1) (fun _ => one_pos)
      (fun c => X_mem c) iSup_basicOpen_X,
    ProjHom.comp_fromOfGlobalSections _ _ (fun c => X c) (fun _ => 1) (fun _ => one_pos)
      (fun c => X_mem c) iSup_basicOpen_X]
  set W := segreOpen A i j ⊓ segreOpen A k l
  set q₁ := W.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)
  set q₂ := W.ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)
  have hi : ⊤ ≤ q₁ ⁻¹ᵁ Proj.basicOpen (grading A n) (X i) :=
    top_le_preimage_ι_comp _ _ (inf_le_left.trans inf_le_left)
  have hj : ⊤ ≤ q₂ ⁻¹ᵁ Proj.basicOpen (grading A m) (X j) :=
    top_le_preimage_ι_comp _ _ (inf_le_left.trans inf_le_right)
  have hk : ⊤ ≤ q₁ ⁻¹ᵁ Proj.basicOpen (grading A n) (X k) :=
    top_le_preimage_ι_comp _ _ (inf_le_right.trans inf_le_left)
  have hl : ⊤ ≤ q₂ ⁻¹ᵁ Proj.basicOpen (grading A m) (X l) :=
    top_le_preimage_ι_comp _ _ (inf_le_right.trans inf_le_right)
  set c : Γ(W, ⊤) := q₁.appLE _ ⊤ hk (chartHom k (X i)) * q₂.appLE _ ⊤ hl (chartHom l (X j))
  have hc : IsUnit c := by
    refine IsUnit.of_mul_eq_one (q₁.appLE _ ⊤ hi (chartHom i (X k)) *
      q₂.appLE _ ⊤ hj (chartHom j (X l))) ?_
    have e₁ := appLE_chartHom_identity q₁ i k ⊤ hi hk (X_mem k)
    have e₂ := appLE_chartHom_identity q₂ j l ⊤ hj hl (X_mem l)
    rw [pow_one, chartHom_X_self, map_one] at e₁ e₂
    rw [show ∀ x y z w : Γ(W, ⊤), x * y * (z * w) = (z * x) * (w * y) from
      fun _ _ _ _ => by ring, e₁, e₂, mul_one]
  refine (ProjHom.fromOfGlobalSections_eq_of_twist _ _ (fun c => X c) (fun _ => 1)
    (fun _ => one_pos) (fun c => X_mem c) iSup_basicOpen_X _ _ c hc fun m' a ha => ?_).symm
  refine map_eq_pow_mul_of_isHomogeneous _ _ c (fun r => ?_) (fun z => ?_)
    ((mem_homogeneousSubmodule m' a).1 ha)
  · simp only [RingHom.comp_apply]
    rw [segreRing_res_C, segreRing_res_C]
    have e := appLE_chartHom_identity q₁ i k ⊤ hi hk (t := 0) (isHomogeneous_C _ r)
    rw [pow_zero, mul_one] at e
    exact e.symm
  · obtain ⟨⟨a, b⟩, rfl⟩ := (segreIndex n m).surjective z
    simp only [RingHom.comp_apply]
    rw [segreRing_res_X, segreRing_res_X]
    have e₁ := appLE_chartHom_identity q₁ i k ⊤ hi hk (X_mem a)
    have e₂ := appLE_chartHom_identity q₂ j l ⊤ hj hl (X_mem b)
    rw [pow_one] at e₁ e₂
    rw [← e₁, ← e₂]
    ring

variable (n m) in

lemma iSup_segreOpen : ⨆ c : Fin (n + 1) × Fin (m + 1), segreOpen A c.1 c.2 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show pullback.fst (toSpecBase A n) (toSpecBase A m) x ∈
      ⨆ i : Fin (n + 1), Proj.basicOpen (grading A n) (X i) by rw [iSup_basicOpen_X]; trivial)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show pullback.snd (toSpecBase A n) (toSpecBase A m) x ∈
      ⨆ j : Fin (m + 1), Proj.basicOpen (grading A m) (X j) by rw [iSup_basicOpen_X]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩

variable (n m) in

def segreCover : (prodP A n m).OpenCover :=
  (prodP A n m).openCoverOfIsOpenCover (fun c : Fin (n + 1) × Fin (m + 1) => segreOpen A c.1 c.2)
    (iSup_segreOpen A n m)

variable (n m) in

def segre : prodP A n m ⟶ projectiveSpace A (n * m + n + m) :=
  (segreCover A n m).glueMorphisms (fun c => segreLocal A c.1 c.2) fun c d => by
    have H := isPullback_opens_inf (segreOpen A c.1 c.2) (segreOpen A d.1 d.2)
    change pullback.fst (segreOpen A c.1 c.2).ι (segreOpen A d.1 d.2).ι ≫ segreLocal A c.1 c.2 =
      pullback.snd (segreOpen A c.1 c.2).ι (segreOpen A d.1 d.2).ι ≫ segreLocal A d.1 d.2
    rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc, Category.assoc,
      segreLocal_agree]

lemma ι_segre (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (segreOpen A i j).ι ≫ segre A n m = segreLocal A i j :=
  (segreCover A n m).ι_glueMorphisms _ _ (i, j)

lemma fromOfGlobalSections_toSpecBase {N : ℕ} {O : Scheme.{u}}
    (φ : MvPolynomial (Fin (N + 1)) A →+* Γ(O, ⊤))
    (hφ : (HomogeneousIdeal.irrelevant (grading A N)).toIdeal.map φ = ⊤) :
    Proj.fromOfGlobalSections (grading A N) φ hφ ≫ toSpecBase A N =
      O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (φ.comp C)) := by
  rw [toSpecBase, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  rfl

variable (n m) in

theorem segre_toSpecBase :
    segre A n m ≫ toSpecBase A (n * m + n + m) =
      pullback.fst (toSpecBase A n) (toSpecBase A m) ≫ toSpecBase A n := by
  refine (segreCover A n m).hom_ext _ _ fun c => ?_
  change (segreOpen A c.1 c.2).ι ≫ _ = (segreOpen A c.1 c.2).ι ≫ _
  have htop : ((segreOpen A c.1 c.2).ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)) ⁻¹ᵁ
      Proj.basicOpen (grading A n) (X c.1) = ⊤ :=
    top_unique (top_le_preimage_ι_comp _ _ inf_le_left)
  rw [← Category.assoc, ι_segre, segreLocal, fromOfGlobalSections_toSpecBase, ← Category.assoc,
    eq_fromOfGlobalSections_of_preimage_eq_top _ c.1 htop, fromOfGlobalSections_toSpecBase]
  congr 3
  ext r
  simp [segreRing]

end ProjSpace
end
end GroundTheory.Arith.SchemeCoh
