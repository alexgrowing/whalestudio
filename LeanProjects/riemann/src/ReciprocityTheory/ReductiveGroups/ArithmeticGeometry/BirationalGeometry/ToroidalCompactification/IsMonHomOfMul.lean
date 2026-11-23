import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

section Transport

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι) :
    (Z.presheaf.stalk z)ˣ := ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k

private theorem mem_wchart_lemma {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] (M : LB A) (ψ : Idx → (B ⟶ A))
    (j : Idx → M.ι) (b : B) : b ∈ LB.wchart M ψ j ↔ ∀ k, ψ k b ∈ M.U (j k) := by
  show b ∈ ⋂ k, (ψ k).base ⁻¹' (M.U (j k) : Set A) ↔ _
  exact Set.mem_iInter

private theorem gm_res_pullU_lemma_2 {A B C : Scheme.{0}} (f : B ⟶ A) (U : A.Opens) (V : B.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (r : C ⟶ B) (c : C) (hc : r c ∈ V) (s : Γ(A, U)ˣ) :
    gm r c V (res h (pullU f U s)) = gm (r ≫ f) c U s := by
  have hc' : (r ≫ f) c ∈ U := by simpa using h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ f ⁻¹ᵁ U := hc'
  have key : f.app U ≫ B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      f.app U ≫ r.app (f ⁻¹ᵁ U) ≫ C.presheaf.germ (r ⁻¹ᵁ f ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(A, U))) key

theorem pw_trans {w : LB.Iso L' (L.pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pw w φ' ε r z p q = trF (fun k => φ' k ≫ F) ε r z p p' * (trF φ' ε r z q q')⁻¹ * pw w φ' ε r z p' q' := by
  rw [mem_wchart_lemma] at hp hp' hq hq'
  simp only [pw, trF]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hw Z (r ≫ φ' k) z (p k) (p' k) (q k) (q' k) (by simpa using hp k) (by simpa using hp' k)
    (by simpa using hq k) (by simpa using hq' k)]
  simp only [Category.assoc, mul_zpow, inv_zpow]

theorem exists_pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pw w φ' ε r z p q := by
  have hle : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := by
    intro k y hy
    have h1 := (mem_wchart_lemma _ _ _ _).mp hy.1
    have h2 := (mem_wchart_lemma _ _ _ _).mp hy.2
    show φ' k y ∈ ((L.pull F).U fun _ => p k) ⊓ L'.U (q k)
    exact ⟨(mem_wchart_lemma _ _ _ _).mpr fun _ => by simpa using h1 k, h2 k⟩
  refine ⟨∏ k, res (hle k) (pullU (φ' k) ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k))
    (w.s (fun _ => p k, q k))) ^ ε k, ?_⟩
  intro Z r z hz
  simp only [pw, gw, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact congrArg (· ^ ε k) (gm_res_pullU_lemma_2 (φ' k) _ _ (hle k) r z hz _)

theorem trF_self {M : LB X} (hM : M.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {j : K → M.ι}
    (hj : r z ∈ LB.wchart M φ j) : trF φ ε r z j j = 1 := by
  have hg : ∀ i, M.g i i = 1 := by
    intro i
    have h1 := hM.g_self i
    have h2 : ∀ g : Γ(X, M.U i ⊓ M.U i)ˣ, g = res (inf_le_left : M.U i ⊓ M.U i ≤ M.U i)
        (res (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i) g) := by
      intro g
      have e : X.presheaf.map (homOfLE (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i)).op ≫
          X.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U i ≤ M.U i)).op = 𝟙 _ := by
        rw [← Functor.map_comp]
        exact X.presheaf.map_id _
      ext
      exact (congrArg (fun φ => CommRingCat.Hom.hom φ (g : Γ(X, M.U i ⊓ M.U i))) e).symm
    rw [h2 (M.g i i), h1, map_one]
  simp only [trF, hg, map_one, one_zpow, Finset.prod_const_one]

private theorem units_ext_gm_lemma_3 {A : Scheme.{0}} {V : A.Opens} (a b : Γ(A, V)ˣ)
    (H : ∀ (y : A) (hy : y ∈ V), gm (𝟙 A) y V a = gm (𝟙 A) y V b) : a = b := by
  have key : ∀ (y : A) (hy : y ∈ V) (s : Γ(A, V)ˣ),
      ((gm (𝟙 A) y V s : A.presheaf.stalk y)) = A.presheaf.germ V y hy (s : Γ(A, V)) := by
    intro y hy s
    have hy1 : (𝟙 A) y ∈ V := by simpa using hy
    simp only [gm, dif_pos hy1]
    first
    | rfl
    | simp [pullU]
  ext
  refine TopCat.Presheaf.section_ext A.sheaf V _ _ fun y hy => ?_
  have h := congrArg Units.val (H y hy)
  rw [key y hy, key y hy] at h
  exact h

private theorem gm_res_lemma_4 {B C : Scheme.{0}} {U V : B.Opens} (h : V ≤ U) (r : C ⟶ B) (c : C)
    (hc : r c ∈ V) (s : Γ(B, U)ˣ) : gm r c V (res h s) = gm r c U s := by
  have hc' : r c ∈ U := h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ U := hc'
  have key : B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      r.app U ≫ C.presheaf.germ (r ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(B, U))) key

theorem isGen_of_gm {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (h : ∀ (y : Y) (j j' : K → M.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart M φ j' →
      gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart M φ j') (t.s j')) : t.IsGen := by
  intro i j
  apply units_ext_gm_lemma_3
  intro y hy
  have hi : y ∈ LB.wchart M φ i := hy.1
  have hj : y ∈ LB.wchart M φ j := hy.2
  have hk : ∀ k, LB.wchart M φ i ⊓ LB.wchart M φ j ≤ φ k ⁻¹ᵁ (M.U (i k) ⊓ M.U (j k)) :=
    fun k => le_inf (inf_le_left.trans (LB.wchart_le M φ i k)) (inf_le_right.trans (LB.wchart_le M φ j k))
  have eg : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j)
      (∏ k, res (hk k) (pullU (φ k) (M.U (i k) ⊓ M.U (j k)) (M.g (i k) (j k))) ^ ε k) =
        trF φ ε (𝟙 Y) y i j := by
    simp only [trF, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact congrArg (· ^ ε k) (gm_res_pullU_lemma_2 (φ k) _ _ (hk k) (𝟙 Y) y hy _)
  have e1 : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j) (res inf_le_left (t.s i)) =
      gm (𝟙 Y) y (LB.wchart M φ i) (t.s i) := gm_res_lemma_4 inf_le_left (𝟙 Y) y hy (t.s i)
  have e2 : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j) (res inf_le_right (t.s j)) =
      gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) := gm_res_lemma_4 inf_le_right (𝟙 Y) y hy (t.s j)
  rw [map_mul]
  exact e1.trans ((h y i j hi hj).trans (congrArg₂ (· * ·) eg.symm e2.symm))

private theorem gm_id_lemma_6 {A : Scheme.{0}} (V : A.Opens) (y : A) (hy : y ∈ V) (s : Γ(A, V)ˣ) :
    ((gm (𝟙 A) y V s : A.presheaf.stalk y)) = A.presheaf.germ V y hy (s : Γ(A, V)) := by
  have hy1 : (𝟙 A) y ∈ V := by simpa using hy
  simp only [gm, dif_pos hy1]
  first
  | rfl
  | simp [pullU]

private theorem glue_units_lemma_5 {A : Scheme.{0}} {I : Type} (V : A.Opens) (U : I → A.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : ∀ y ∈ V, ∃ i, y ∈ U i) (σ : ∀ i, Γ(A, U i)ˣ)
    (hσ : ∀ i j (y : A), y ∈ U i → y ∈ U j → gm (𝟙 A) y (U i) (σ i) = gm (𝟙 A) y (U j) (σ j)) :
    ∃ s : Γ(A, V)ˣ, ∀ i, res (hU i) s = σ i := by
  have hcover : V ≤ iSup U := fun y hy => Opens.mem_iSup.mpr (hcov y hy)
  have compat : ∀ τ : ∀ i, Γ(A, U i)ˣ,
      (∀ i j (y : A), y ∈ U i → y ∈ U j → gm (𝟙 A) y (U i) (τ i) = gm (𝟙 A) y (U j) (τ j)) →
      TopCat.Presheaf.IsCompatible A.sheaf.1 U (fun i => ((τ i : Γ(A, U i)))) := by
    intro τ hτ i j
    refine TopCat.Presheaf.section_ext A.sheaf _ _ _ fun y hy => ?_
    have h := congrArg Units.val (hτ i j y hy.1 hy.2)
    rw [gm_id_lemma_6 _ _ hy.1, gm_id_lemma_6 _ _ hy.2] at h
    have e1 : A.presheaf.germ (U i ⊓ U j) y hy (A.presheaf.map (Opens.infLELeft (U i) (U j)).op
        (τ i : Γ(A, U i))) = A.presheaf.germ (U i) y hy.1 (τ i : Γ(A, U i)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    have e2 : A.presheaf.germ (U i ⊓ U j) y hy (A.presheaf.map (Opens.infLERight (U i) (U j)).op
        (τ j : Γ(A, U j))) = A.presheaf.germ (U j) y hy.2 (τ j : Γ(A, U j)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    exact e1.trans (h.trans e2.symm)
  obtain ⟨s0, hs0, -⟩ := TopCat.Sheaf.existsUnique_gluing' A.sheaf U V (fun i => homOfLE (hU i)) hcover _
    (compat σ hσ)
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' A.sheaf U V (fun i => homOfLE (hU i)) hcover _
    (compat (fun i => (σ i)⁻¹) fun i j y hi hj => by
      show gm (𝟙 A) y (U i) (σ i)⁻¹ = gm (𝟙 A) y (U j) (σ j)⁻¹
      rw [map_inv, map_inv, hσ i j y hi hj])
  have germ_eq : ∀ (s : Γ(A, V)) (τ : ∀ i, Γ(A, U i)),
      (∀ i, A.presheaf.map (homOfLE (hU i)).op s = τ i) →
      ∀ (y : A) (hy : y ∈ V) (i : I) (hi : y ∈ U i),
        A.presheaf.germ V y hy s = A.presheaf.germ (U i) y hi (τ i) := by
    intro s τ hs y hy i hi
    rw [← hs i, TopCat.Presheaf.germ_res_apply]
  have h01 : (s0 : Γ(A, V)) * (s1 : Γ(A, V)) = 1 := by
    refine TopCat.Presheaf.section_ext A.sheaf V _ _ fun y hy => ?_
    obtain ⟨i, hi⟩ := hcov y hy
    have e0 := germ_eq s0 _ hs0 y hy i hi
    have e1 := germ_eq s1 _ hs1 y hy i hi
    have e : A.presheaf.germ V y hy ((s0 : Γ(A, V)) * (s1 : Γ(A, V))) = A.presheaf.germ V y hy 1 := by
      calc A.presheaf.germ V y hy ((s0 : Γ(A, V)) * (s1 : Γ(A, V)))
          = A.presheaf.germ V y hy s0 * A.presheaf.germ V y hy s1 := map_mul _ _ _
        _ = A.presheaf.germ (U i) y hi ((σ i : Γ(A, U i))) *
              A.presheaf.germ (U i) y hi (((σ i)⁻¹ : Γ(A, U i)ˣ) : Γ(A, U i)) := by rw [e0, e1]
        _ = A.presheaf.germ (U i) y hi ((σ i * (σ i)⁻¹ : Γ(A, U i)ˣ) : Γ(A, U i)) := by
              rw [Units.val_mul, map_mul]
        _ = A.presheaf.germ V y hy 1 := by
              rw [_root_.mul_inv_cancel, Units.val_one, map_one, map_one]
    exact e
  exact ⟨⟨s0, s1, h01, (_root_.mul_comm (s1 : Γ(A, V)) (s0 : Γ(A, V))).trans h01⟩, fun i => Units.ext (hs0 i)⟩

private theorem gm_of_isGen_lemma_7 {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] {M : LB A}
    {ψ : Idx → (B ⟶ A)} {ex : Idx → ℤ} (t : LB.Gen (LB.LinComb M ψ ex)) (ht : t.IsGen) (y : B)
    (i j : Idx → M.ι) (hi : y ∈ LB.wchart M ψ i) (hj : y ∈ LB.wchart M ψ j) :
    gm (𝟙 B) y (LB.wchart M ψ i) (t.s i) = trF ψ ex (𝟙 B) y i j * gm (𝟙 B) y (LB.wchart M ψ j) (t.s j) := by
  have hy : y ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := ⟨hi, hj⟩
  have hk : ∀ k, LB.wchart M ψ i ⊓ LB.wchart M ψ j ≤ ψ k ⁻¹ᵁ (M.U (i k) ⊓ M.U (j k)) :=
    fun k => le_inf (inf_le_left.trans (LB.wchart_le M ψ i k)) (inf_le_right.trans (LB.wchart_le M ψ j k))
  have eg : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j)
      (∏ k, res (hk k) (pullU (ψ k) (M.U (i k) ⊓ M.U (j k)) (M.g (i k) (j k))) ^ ex k) =
        trF ψ ex (𝟙 B) y i j := by
    simp only [trF, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact congrArg (· ^ ex k) (gm_res_pullU_lemma_2 (ψ k) _ _ (hk k) (𝟙 B) y hy _)
  have e1 : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j) (res inf_le_left (t.s i)) =
      gm (𝟙 B) y (LB.wchart M ψ i) (t.s i) := gm_res_lemma_4 inf_le_left (𝟙 B) y hy (t.s i)
  have e2 : gm (𝟙 B) y (LB.wchart M ψ i ⊓ LB.wchart M ψ j) (res inf_le_right (t.s j)) =
      gm (𝟙 B) y (LB.wchart M ψ j) (t.s j) := gm_res_lemma_4 inf_le_right (𝟙 B) y hy (t.s j)
  have h := congrArg (gm (𝟙 B) y _) (ht i j)
  rw [map_mul] at h
  exact e1.symm.trans (h.trans (congrArg₂ (· * ·) eg e2))

theorem exists_up {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  classical
  have hcovq : ∀ y : Y, ∃ q : K → L'.ι, y ∈ LB.wchart L' φ' q := by
    intro y
    have hk : ∀ k, ∃ i, φ' k y ∈ L'.U i := fun k =>
      Opens.mem_iSup.mp (by rw [hL'.cover]; first | trivial | exact Set.mem_univ _ | simp)
    choose q hq using hk
    exact ⟨q, (mem_wchart_lemma _ _ _ _).mpr hq⟩
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hle1 : ∀ p q, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L (fun k => φ' k ≫ F) p := fun _ _ => inf_le_left
  have hle2 : ∀ p q, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L' φ' q := fun _ _ => inf_le_right
  have key : ∀ {y : Y} (T P A : (Y.presheaf.stalk y)ˣ), 1 * T⁻¹ * P * (T * A) = P * A :=
    fun T P A => by rw [_root_.one_mul, _root_.mul_assoc, _root_.mul_left_comm P, inv_mul_cancel_left]
  have hcompat : ∀ p q q' (y : Y), y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q' →
      gm (𝟙 Y) y _ (u p q * res (hle2 p q) (a.s q)) =
        gm (𝟙 Y) y _ (u p q' * res (hle2 p q') (a.s q')) := by
    intro p q q' y h1 h2
    have h1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := by simpa using h1
    have h2' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q' := by simpa using h2
    rw [map_mul, map_mul, hu p q Y (𝟙 Y) y h1', hu p q' Y (𝟙 Y) y h2', gm_res_lemma_4 (hle2 p q) (𝟙 Y) y h1' (a.s q),
      gm_res_lemma_4 (hle2 p q') (𝟙 Y) y h2' (a.s q'), pw_trans hw φ' ε (𝟙 Y) y h1'.1 h1'.1 h1'.2 h2'.2,
      trF_self hL _ ε (𝟙 Y) y h1'.1, gm_of_isGen_lemma_7 a ha y q q' h1.2 h2.2]
    exact key _ _ _
  have hglue : ∀ p, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ q,
      res (hle1 p q) s = u p q * res (hle2 p q) (a.s q) := fun p =>
    glue_units_lemma_5 _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (hle1 p)
      (fun y hy => ⟨(hcovq y).choose, hy, (hcovq y).choose_spec⟩)
      (fun q => u p q * res (hle2 p q) (a.s q)) (hcompat p)
  choose ts hts using hglue
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (ts p) =
        pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro Z r z p q hp hq
    have hpq : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨hp, hq⟩
    rw [← gm_res_lemma_4 (hle1 p q) r z hpq (ts p), hts p q, map_mul, hu p q Z r z hpq,
      gm_res_lemma_4 (hle2 p q) r z hpq (a.s q)]
  refine ⟨⟨ts⟩, ?_, fun Z r z p q hp hq => hval Z r z p q hp hq⟩
  apply isGen_of_gm
  intro y p p' hp hp'
  obtain ⟨q, hq⟩ := hcovq y
  have hp1 : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by simpa using hp
  have hp1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p' := by simpa using hp'
  have hq1 : (𝟙 Y) y ∈ LB.wchart L' φ' q := by simpa using hq
  show gm (𝟙 Y) y _ (ts p) = _ * gm (𝟙 Y) y _ (ts p')
  rw [hval Y (𝟙 Y) y p q hp1 hq1, hval Y (𝟙 Y) y p' q hp1' hq1,
    pw_trans hw φ' ε (𝟙 Y) y hp1 hp1' hq1 hq1, trF_self hL' φ' ε (𝟙 Y) y hq1, inv_one, _root_.mul_one,
    _root_.mul_assoc]

theorem exists_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  classical
  have hcovp : ∀ y : Y, ∃ p : K → L.ι, y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by
    intro y
    have hk : ∀ k, ∃ i, (φ' k ≫ F) y ∈ L.U i := fun k =>
      Opens.mem_iSup.mp (by rw [hL.cover]; first | trivial | exact Set.mem_univ _ | simp)
    choose p hp using hk
    exact ⟨p, (mem_wchart_lemma _ _ _ _).mpr hp⟩
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hle1 : ∀ q p, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L (fun k => φ' k ≫ F) p := fun _ _ => inf_le_left
  have hle2 : ∀ q p, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L' φ' q := fun _ _ => inf_le_right
  have key : ∀ {y : Y} (T P A : (Y.presheaf.stalk y)ˣ), (T * P)⁻¹ * (T * A) = P⁻¹ * A :=
    fun T P A => by rw [mul_inv_rev, _root_.mul_assoc, inv_mul_cancel_left]
  have key2 : ∀ {y : Y} (T P G : (Y.presheaf.stalk y)ˣ), (1 * T⁻¹ * P)⁻¹ * G = T * (P⁻¹ * G) :=
    fun T P G => by rw [_root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_left_comm]
  have hcompat : ∀ q p p' (y : Y), y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p' ⊓ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ ((u p q)⁻¹ * res (hle1 q p) (t.s p)) =
        gm (𝟙 Y) y _ ((u p' q)⁻¹ * res (hle1 q p') (t.s p')) := by
    intro q p p' y h1 h2
    have h1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := by simpa using h1
    have h2' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p' ⊓ LB.wchart L' φ' q := by simpa using h2
    rw [map_mul, map_mul, map_inv, map_inv, hu p q Y (𝟙 Y) y h1', hu p' q Y (𝟙 Y) y h2',
      gm_res_lemma_4 (hle1 q p) (𝟙 Y) y h1' (t.s p), gm_res_lemma_4 (hle1 q p') (𝟙 Y) y h2' (t.s p'),
      pw_trans hw φ' ε (𝟙 Y) y h1'.1 h2'.1 h1'.2 h1'.2, trF_self hL' φ' ε (𝟙 Y) y h1'.2, inv_one,
      _root_.mul_one, gm_of_isGen_lemma_7 t ht y p p' h1.1 h2.1]
    exact key _ _ _
  have hglue : ∀ q, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ p,
      res (hle2 q p) s = (u p q)⁻¹ * res (hle1 q p) (t.s p) := fun q =>
    glue_units_lemma_5 _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (hle2 q)
      (fun y hy => ⟨(hcovp y).choose, (hcovp y).choose_spec, hy⟩)
      (fun p => (u p q)⁻¹ * res (hle1 q p) (t.s p)) (hcompat q)
  choose as has using hglue
  refine ⟨⟨as⟩, ?_⟩
  apply isGen_of_gm
  intro y q q' hq hq'
  obtain ⟨p, hp⟩ := hcovp y
  have hp1 : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by simpa using hp
  have hq1 : (𝟙 Y) y ∈ LB.wchart L' φ' q := by simpa using hq
  have hq1' : (𝟙 Y) y ∈ LB.wchart L' φ' q' := by simpa using hq'
  have hv : ∀ q₀ (hq₀ : (𝟙 Y) y ∈ LB.wchart L' φ' q₀), gm (𝟙 Y) y (LB.wchart L' φ' q₀) (as q₀) =
      (pw w φ' ε (𝟙 Y) y p q₀)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q₀ hq₀
    have hpq : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q₀ := ⟨hp1, hq₀⟩
    rw [← gm_res_lemma_4 (hle2 q₀ p) (𝟙 Y) y hpq (as q₀), has q₀ p, map_mul, map_inv, hu p q₀ Y (𝟙 Y) y hpq,
      gm_res_lemma_4 (hle1 q₀ p) (𝟙 Y) y hpq (t.s p)]
  show gm (𝟙 Y) y _ (as q) = _ * gm (𝟙 Y) y _ (as q')
  rw [hv q hq1, hv q' hq1', pw_trans hw φ' ε (𝟙 Y) y hp1 hp1 hq1 hq1', trF_self hL _ ε (𝟙 Y) y hp1]
  exact key2 _ _ _

theorem maps_of_good {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (hψ : ∀ k, φ' k ≫ F = 𝟙 _ ≫ φ k)
    (h : ∀ (y : Y) J J', Good L y J → Good L' y J' → val t (𝟙 Y) y J =
      (∏ k, gw w (φ' k) y (J (φ' k ≫ F)) (J' (φ' k)) ^ ε k) * val a (𝟙 Y) y J') :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a (GeneratorPullback.pullAlong L F (𝟙 Y) φ ε φ' hψ t) := by
  classical
  rintro ⟨P1, P2⟩
  dsimp only
  apply units_ext_gm_lemma_3
  intro y hy
  have hy1 : y ∈ LB.wchart (L.pull F) φ' P1 := hy.1
  have hy2 : y ∈ LB.wchart L' φ' P2 := hy.2
  have hy1k : ∀ k, F (φ' k y) ∈ L.U (P1 k ⟨⟩) := fun k => by
    have h1 := (mem_wchart_lemma _ _ _ _).mp hy1 k
    have h2 := (mem_wchart_lemma _ _ _ _).mp h1 ⟨⟩
    simpa using h2
  have hy2k : ∀ k, φ' k y ∈ L'.U (P2 k) := (mem_wchart_lemma _ _ _ _).mp hy2
  have hφ : ∀ k, φ k y = F (φ' k y) := fun k => by
    have e := congrArg (fun m : Y ⟶ X => m y) (hψ k)
    simpa using e.symm
  have cov : ∀ ψ : Y ⟶ X, ∃ i, ψ y ∈ L.U i := fun ψ =>
    Opens.mem_iSup.mp (by rw [hL.cover]; first | trivial | exact Set.mem_univ _ | simp)
  have cov' : ∀ ψ : Y ⟶ X', ∃ i, ψ y ∈ L'.U i := fun ψ =>
    Opens.mem_iSup.mp (by rw [hL'.cover]; first | trivial | exact Set.mem_univ _ | simp)
  choose J hJ using cov
  choose J' hJ' using cov'
  have hh := h y J J' hJ hJ'
  have mJp : y ∈ LB.wchart L φ (fun k => P1 k ⟨⟩) := (mem_wchart_lemma _ _ _ _).mpr fun k => by
    show φ k y ∈ L.U (P1 k ⟨⟩)
    rw [hφ k]
    exact hy1k k
  have mJφ : y ∈ LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k)) :=
    (mem_wchart_lemma _ _ _ _).mpr fun k => by simpa using hJ (𝟙 Y ≫ φ k)
  have mJ'φ' : y ∈ LB.wchart L' φ' (fun k => J' (𝟙 Y ≫ φ' k)) :=
    (mem_wchart_lemma _ _ _ _).mpr fun k => by simpa using hJ' (𝟙 Y ≫ φ' k)
  have eR1 : gm (𝟙 Y) y (LB.wchart (L.pull F) φ' P1 ⊓ LB.wchart L' φ' P2) ((LB.linCombIso w φ' ε).s (P1, P2)) =
      ∏ k, gw w (φ' k) y (P1 k ⟨⟩) (P2 k) ^ ε k := by
    have hk : ∀ k, LB.wchart (L.pull F) φ' P1 ⊓ LB.wchart L' φ' P2 ≤
        φ' k ⁻¹ᵁ ((L.pull F).U (P1 k) ⊓ L'.U (P2 k)) := fun k =>
      le_inf (inf_le_left.trans (LB.wchart_le (L.pull F) φ' P1 k))
        (inf_le_right.trans (LB.wchart_le L' φ' P2 k))
    show gm (𝟙 Y) y _ (∏ k, res (hk k) (pullU (φ' k) ((L.pull F).U (P1 k) ⊓ L'.U (P2 k))
      (w.s (P1 k, P2 k))) ^ ε k) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow]
    exact congrArg (· ^ ε k) ((gm_res_pullU_lemma_2 (φ' k) _ _ (hk k) (𝟙 Y) y hy _).trans
      (by rw [Category.id_comp] <;> rfl))
  have eR2 : gm (𝟙 Y) y (LB.wchart (L.pull F) φ' P1 ⊓ LB.wchart L' φ' P2) (res inf_le_right (a.s P2)) =
      gm (𝟙 Y) y (LB.wchart L' φ' P2) (a.s P2) := gm_res_lemma_4 inf_le_right (𝟙 Y) y hy (a.s P2)
  have eR3 := gm_of_isGen_lemma_7 a ha y _ _ hy2 mJ'φ'
  have eT : trF φ ε (𝟙 Y) y (fun k => P1 k ⟨⟩) (fun k => J (𝟙 Y ≫ φ k)) =
      ∏ k, gm (φ' k ≫ F) y (L.U (P1 k ⟨⟩) ⊓ L.U (J (φ' k ≫ F))) (L.g (P1 k ⟨⟩) (J (φ' k ≫ F))) ^ ε k := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (congrArg (fun m : Y ⟶ X => gm m y (L.U (P1 k ⟨⟩) ⊓ L.U (J m)) (L.g (P1 k ⟨⟩) (J m)) ^ ε k)
      (hψ k)).symm
  have eT' : trF φ' ε (𝟙 Y) y P2 (fun k => J' (𝟙 Y ≫ φ' k)) =
      ∏ k, gm (φ' k) y (L'.U (P2 k) ⊓ L'.U (J' (φ' k))) (L'.g (P2 k) (J' (φ' k))) ^ ε k := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    exact congrArg (fun m : Y ⟶ X' => gm m y (L'.U (P2 k) ⊓ L'.U (J' m)) (L'.g (P2 k) (J' m)) ^ ε k)
      (Category.id_comp (φ' k))
  have eV : ∀ k, gw w (φ' k) y (P1 k ⟨⟩) (P2 k) =
      gm (φ' k ≫ F) y (L.U (P1 k ⟨⟩) ⊓ L.U (J (φ' k ≫ F))) (L.g (P1 k ⟨⟩) (J (φ' k ≫ F))) *
        (gm (φ' k) y (L'.U (P2 k) ⊓ L'.U (J' (φ' k))) (L'.g (P2 k) (J' (φ' k))))⁻¹ *
          gw w (φ' k) y (J (φ' k ≫ F)) (J' (φ' k)) := fun k =>
    hw Y (φ' k) y _ _ _ _ (hy1k k) (by simpa using hJ (φ' k ≫ F)) (hy2k k) (hJ' (φ' k))
  have eP : ∏ k, gw w (φ' k) y (P1 k ⟨⟩) (P2 k) ^ ε k =
      (∏ k, gm (φ' k ≫ F) y (L.U (P1 k ⟨⟩) ⊓ L.U (J (φ' k ≫ F))) (L.g (P1 k ⟨⟩) (J (φ' k ≫ F))) ^ ε k) *
        (∏ k, gm (φ' k) y (L'.U (P2 k) ⊓ L'.U (J' (φ' k))) (L'.g (P2 k) (J' (φ' k))) ^ ε k)⁻¹ *
          ∏ k, gw w (φ' k) y (J (φ' k ≫ F)) (J' (φ' k)) ^ ε k := by
    simp only [eV, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have final : ∀ (g h v A : (Y.presheaf.stalk y)ˣ), g * (v * A) = g * h⁻¹ * v * (h * A) := by
    intro g h v A
    rw [_root_.mul_assoc (g * h⁻¹) v (h * A), _root_.mul_left_comm v h A, _root_.mul_assoc g h⁻¹,
      inv_mul_cancel_left]
  rw [map_mul]
  refine (gm_res_lemma_4 inf_le_left (𝟙 Y) y hy _).trans ?_
  refine (gm_res_pullU_lemma_2 (𝟙 Y) _ _ _ (𝟙 Y) y hy1 _).trans ?_
  rw [Category.comp_id]
  refine (gm_of_isGen_lemma_7 t ht y _ _ mJp mJφ).trans ?_
  refine (congrArg (_ * ·) hh).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) eR1 (eR2.trans eR3)).symm
  rw [eT, eT', eP]
  exact final _ _ _ _

end Transport

theorem isMonHom_of_mul {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    (mul : ∀ (T : Over S) (x y : T ⟶ G₁), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hμ : μ ≫ e = (e ⊗ₘ e) ≫ μ := by
    have h := mul _ (fst G₁ G₁) (snd G₁ G₁)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1
  have h1 : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ e = 1 := by
    have h := mul _ (1 : 𝟙_ (Over S) ⟶ G₁) 1
    rw [_root_.mul_one] at h
    exact mul_left_cancel (a := (1 : 𝟙_ (Over S) ⟶ G₁) ≫ e) (by rw [_root_.mul_one, ← h])
  have hu : toUnit (𝟙_ (Over S)) = 𝟙 _ := toUnit_unique _ _
  simp only [Hom.one_def, hu, Category.id_comp] at h1
  exact ⟨h1, hμ⟩

theorem polOActPull : PolOActPullSt := by
  intro S S' f P P' g hg hw O _ _ o
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ P'.A), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  obtain ⟨w, gw'⟩ := LBIso.symm hw
  refine ⟨⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩,
    fun a s => ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.map_one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act b), pa, o.map_mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.map_add]
    exact MonObj.comp_mul _ _ _
  · obtain ⟨U, hU, t, ht⟩ := o.rosati a (f s)
    let V : (P'.A ⊗ P'.A).left.Opens := (P'.A ⊗ P'.A).hom ⁻¹ᵁ (f ⁻¹ᵁ U)
    let T' : Over S' := Over.mk (V.ι ≫ (P'.A ⊗ P'.A).hom)
    let j : T' ⟶ P'.A ⊗ P'.A := Over.homMk V.ι rfl
    let m := lift (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _))
    obtain ⟨n, hn⟩ : ∃ n : V.toScheme ⟶ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).toScheme, n ≫ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).ι = m.left :=
      ⟨IsOpenImmersion.lift _ m.left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ U) (Over.w m)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', -⟩ := exists_gen P.isLB (φ' := fun i => (V.ι ≫ rosatiφ P'.A (act a) (act (star a)) i) ≫ g)
      (ε' := rosatiε) (fun W _ k => by
        have p₁ := prod_ros (o.act a) (o.act (star a)) (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _)) k
        have p₂ := prod_ros (act a) (act (star a)) (j ≫ fst _ _) (j ≫ snd _ _) (fun q => k (q ≫ g))
        rw [← comp_lift, lift_fst_snd, Category.comp_id] at p₂
        rw [← pa, ← pa, ← pm, ← pm] at p₁
        exact ((Finset.prod_congr rfl fun i _ => by
          show k (n ≫ _ ≫ _) ^ _ = k (m.left ≫ _) ^ _
          rw [← Category.assoc, hn]).trans p₁).trans p₂.symm) (LB.pullGen P.L _ _ t n) (pullGen_isGen _ _ _ _ ht n)
    exact ⟨f ⁻¹ᵁ U, hU, exists_down ((isGen_iff w).1 gw') P.isLB P'.isLB t' ht'⟩

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

theorem pull_grp (hD : IsPullDeg φ D D') :
    IsGrpPullback D'.P.A D.P.A (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  exact ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback D.P.A (specOf φ))).congr (Category.id_comp _) rfl

theorem cub_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf (pull_grp hD)).F3) z J =
      (∏ I : thK.{0}, gw hD.w ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ (cubeMapOf (pull_grp hD)).F))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A))
    (ε := thε) D'.cub.t D'.cub.isGen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ I : thK.{0}, gw hD.w (r ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ (cubeMapOf (pull_grp hD)).F)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) *
        val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]; rfl
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun I => (cubeMapOf (pull_grp hD)).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf (pull_grp hD)).psum_comm I.down))
    _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf (pull_grp hD)).F3) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have C' : IsCub (cubV D'.cub y I') := isCub_cubV D'.cub hI'
      have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1
        (fun q => gw hD.w q y (I (q ≫ (cubeMapOf (pull_grp hD)).F)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm
      have o : pushPt (pull_grp hD).1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1 := map_one (pushHom (pull_grp hD) _)
      have q : e.left ≫ (cubeMapOf (pull_grp hD)).F3 =
          (lift (pushPt (pull_grp hD).1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt (pull_grp hD).1.w 1)
            (pushPt (pull_grp hD).1.w 1))).left := hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]
      refine (val_pull hI _ _ _).trans ?_
      rw [q, o]
      refine ((isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).face 1 1).trans ?_
      simp) _ (lift x (lift x' y)).left z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

def vS {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {ψ : K → (Sp F ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M ψ ε)) (y : Sp F) (J : (Sp F ⟶ X) → M.ι) : ((Sp F).presheaf.stalk y)ˣ := val t (𝟙 _) y J

def thS (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι)
    (a b c : TF (R := R) F ⟶ D.P.A) : ((Sp F).presheaf.stalk y)ˣ := th D (T := TF (R := R) F) y J a b c

def vK {F : Type} [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}} {M : LB X} {K : Type} [Fintype K]
    {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M ψ ε)) (y : Sp F) (J : (Sp F ⟶ X) → M.ι) :
    ((Sp F).presheaf.stalk y)ˣ := val t (𝟙 _ ≫ jFK (R := R) F) y J

set_option maxHeartbeats 2000000 in
theorem qkPullExists (hG : GlobalFnsSt) : QkPullExistsSt := by
  intro R R' _ _ _ _ φ D D' hD F _ _ _ hF k p'
  have gp := pull_grp hD
  have hw := (isGen_iff hD.w).1 hD.w_gen
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R :=
    ((congrArg (jFK (R := R') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _))
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := (Category.assoc _ _ _).trans hj
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let β : (TF (R := R') F ⟶ D'.P.A) → (TF (R := R) F ⟶ D.P.A) := fun x =>
    Over.homMk (x.left ≫ Φ) ((Over.w (pushPt gp.1.w x)).trans hT)
  have βm : ∀ x y, β (x * y) = β x * β y := fun x y => Over.OverMorphism.ext
    ((gp.2 _ x y _ _ rfl rfl).symm.trans (mul_left_congr hT (pushPt gp.1.w x) (pushPt gp.1.w y) (β x) (β y) rfl rfl))
  have β1 : β 1 = 1 := mul_eq_left.1 ((βm 1 1).symm.trans (congrArg β (_root_.mul_one 1)))
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TF (R := R') F).hom ≫ (D'.c χ).left) ≫ Φ = (TF (R := R) F).hom ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, ← Category.assoc]
    exact congrArg (· ≫ _) hT)
  let Ω : ∀ (y : Sp F) (_ : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (_ : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι),
      (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk y)ˣ := fun y J J' x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  have cub : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → ∀ a b c : TF (R := R') F ⟶ D'.P.A,
      thS D y J (β a) (β b) (β c) =
        Ω y J J' (a * b * c) * (Ω y J J' (a * b))⁻¹ * (Ω y J J' (a * c))⁻¹ * (Ω y J J' (b * c))⁻¹ * Ω y J J' a *
          Ω y J J' b * Ω y J J' c * (Ω y J J' 1)⁻¹ * thS D' y J' a b c := by
    intro y J J' hJ hJ' a b c
    have e := cub_pull hG hD (T' := TF (R := R') F) hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have good' : ∀ y : Sp F, ∃ J', Good D'.P.L y J' := fun y => by
    choose I hI using fun χ : Sp F ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
    exact ⟨I, hI⟩
  have gφ : ∀ (b : TF (R := R') F ⟶ D'.P.A) χ i, DegPre.gtφ D' F b χ i ≫ Φ = DegPre.gtφ D F (β b) (hD.xe χ) i := by
    intro b χ i
    fin_cases i
    · exact congrArg (fun q => q.left) ((βm (cP D' _ χ) b).trans (congrArg (· * β b) (βc χ)))
    · exact congrArg (fun q => q.left) (βc χ)
    · rfl
    · exact congrArg (fun q => q.left) β1
  have ex : ∀ g' : GtPtF D' F, ∃ g : GtPtF D F, g.b = β g'.b ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vS (g.s (hD.xe χ)) y J = (Ω y J J' (cP D' _ χ * g'.b))⁻¹ * Ω y J J' (cP D' _ χ) * Ω y J J' g'.b *
        (Ω y J J' 1)⁻¹ * vS (g'.s χ) y J' := by
    intro g'
    choose t ht hv using fun χ => exists_up hw D.P.isLB D'.P.isLB (g'.s χ) (g'.isGen χ)
    have vt : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS (t χ) y J =
        (Ω y J J' (cP D' _ χ * g'.b))⁻¹ * Ω y J J' (cP D' _ χ) * Ω y J J' g'.b * (Ω y J J' 1)⁻¹ *
          vS (g'.s χ) y J' := fun χ y J J' hJ hJ' => by
      refine (hv χ _ (𝟙 _) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
      refine Eq.trans ?_ (prod_gt g'.b χ (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q)))
      simp only [pw, Category.id_comp]; rfl
    obtain ⟨g, hb, hg⟩ := exists_gt (β g'.b) (fun χ => t (hD.xe.symm χ)) (fun χ => ht _) (fun χ U _ h =>
        Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
          ((gφ g'.b _ i).trans (by rw [AddEquiv.apply_symm_apply]))) (fun y J hJ => by
        obtain ⟨J', hJ'⟩ := good' y
        have z : vS (g'.s 0) y J' = 1 := (val_corr hJ' g'.s_zero _).trans (val_one _)
        show vS (t (hD.xe.symm 0)) y J = 1
        rw [map_zero, vt 0 y J J' hJ hJ', cPoint_zero, _root_.one_mul, z]
        simp [mul_comm]) (fun χ χ' y J hJ => by
        obtain ⟨J', hJ'⟩ := good' y
        obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
        obtain ⟨χ', rfl⟩ := hD.xe.surjective χ'
        have e₀ := gt_mul (𝟙 (TF (R := R') F)) hJ' g' χ χ'
        rw [Category.id_comp] at e₀
        have e : vS (g'.s (χ + χ')) y J' * thS D' y J' (cP D' _ χ) (cP D' _ χ') g'.b = vS (g'.s χ) y J' * vS (g'.s χ') y J' := e₀
        show vS (t (hD.xe.symm (hD.xe χ + hD.xe χ'))) y J * thS D y J (cP D _ (hD.xe χ)) (cP D _ (hD.xe χ')) (β g'.b) =
          vS (t (hD.xe.symm (hD.xe χ))) y J * vS (t (hD.xe.symm (hD.xe χ'))) y J
        rw [← map_add, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, ← βc, ← βc,
          cub y J J' hJ hJ', vt _ y J J' hJ hJ', vt _ y J J' hJ hJ', vt _ y J J' hJ hJ', cPoint_add]
        apply Additive.ofMul.injective
        have e' := congrArg Additive.ofMul e
        simp only [ofMul_mul, ofMul_inv] at e' ⊢
        linear_combination (norm := abel) e')
    refine ⟨g, hb, fun χ y J J' hJ hJ' => (hg _ y J hJ).trans ?_⟩
    show vS (t (hD.xe.symm (hD.xe χ))) y J = _
    rw [AddEquiv.symm_apply_apply]; exact vt χ y J J' hJ hJ'
  choose up hb hv using ex
  have add : ∀ g g' g'' : GtPtF D' F, g.IsAdd g' g'' → (up g).IsAdd (up g') (up g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, βm], fun χ y J hJ => ?_⟩
    obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have e : vS (g''.s χ) y J' * thS D' y J' (cP D' _ χ) g.b g'.b = vS (g.s χ) y J' * vS (g'.s χ) y J' := v₁ χ y J' hJ'
    show vS ((up g'').s (hD.xe χ)) y J * thS D y J (cP D _ (hD.xe χ)) (up g).b (up g').b =
      vS ((up g).s (hD.xe χ)) y J * vS ((up g').s (hD.xe χ)) y J
    have c := cub y J J' hJ hJ' (cP D' _ χ) g.b g'.b
    rw [_root_.mul_assoc (cP D' _ χ), ← b₁] at c
    rw [hv _ _ y J J' hJ hJ', hv _ _ y J J' hJ hJ', hv _ _ y J J' hJ hJ', hb, hb, ← βc, c]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  have vψ : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vK (D.psi (hD.xe χ)) y J = (Ω y J J' (cP D' _ χ))⁻¹ * vK (D'.psi χ) y J' := fun χ y J J' hJ hJ' => by
    have a₁ : jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := (Category.assoc _ _ _).symm
    have a₂ : jFK (R := R) F ≫ D.xK (hD.xe χ) = (cP D' (TF (R := R') F) χ).left ≫ Φ :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) (βc χ).symm)
    have e := pmaps_psi hD F hj χ _ (𝟙 _) y (fun _ => J ((cP D' (TF (R := R') F) χ).left ≫ Φ))
      (fun _ => J' (cP D' (TF (R := R') F) χ).left) (fun _ => by rw [a₁]; exact hJ _) (fun _ => by rw [a₁]; exact hJ' _)
    rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
    refine (val_pull hJ _ _ _).symm.trans ((val_of _ _ y J _ (fun _ => by rw [Category.id_comp, a₂])).trans (e.trans
      (congrArg₂ (· * ·) (by rw [a₁]) ((val_of _ _ y J' _ (fun _ => by rw [Category.id_comp, a₁])).symm.trans
        (val_pull hJ' _ _ _)))))
  have vρ : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vK D.rigK y J = Ω y J J' 1 * vK D'.rigK y J' := fun y J J' hJ hJ' => by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₁ : (TF (R := R') F).hom ≫ eSec D'.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left := rfl
    have a₂ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) β1.symm
    have e := pm _ (TF (R := R') F).hom y (fun _ => J ((1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TF (R := R') F ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one, hT] at e
    have b₁ : (𝟙 _ ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = (TF (R := R) F).hom := by rw [Category.id_comp]; rfl
    have b₂ : (𝟙 _ ≫ jFK (R := R') F) ≫ (toUnit (TK R')).left = (TF (R := R') F).hom := by rw [Category.id_comp]; rfl
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have vτ : ∀ {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) F] (D : DegPre R) (a b : D.X) (y : Sp F) J,
      Good D.P.L y J → vK (D.tau a b) y J =
      vK (D.psi (a + b)) y J * (vK (D.psi a) y J)⁻¹ * (vK (D.psi b) y J)⁻¹ * (vK D.rigK y J)⁻¹ := fun D a b y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p'.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  refine ⟨⟨hD.xe p'.y, up p'.g, up h, ⟨fun i => up (gs i), ?_, fun i => add _ _ _ (gst i), congrArg up gl⟩,
    (isIota_iff _ _).2 ⟨by rw [hb, ιb, βc], fun χ y J hJ => ?_⟩⟩, (hD.xe.symm_apply_apply _).symm,
    (congrArg (fun q => q.left) (hb p'.g)).symm, fun χ => ?_⟩
  · obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
    refine (isZero_iff _).2 ⟨by rw [hb, z₁, β1], fun χ y J hJ => ?_⟩
    obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have z₃ : vS ((gs 0).s χ) y J' = 1 := z₂ _ y J' hJ'
    show vS ((up (gs 0)).s (hD.xe χ)) y J = 1
    rw [hv _ _ y J J' hJ hJ', z₃, z₁, _root_.mul_one]
    simp
  · obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have ι₁ : vS (h.s χ) y J' = vK (D'.tau p'.y χ) y J' := ιv _ y J' hJ'
    show vS ((up h).s (hD.xe χ)) y J = vK (D.tau (hD.xe p'.y) (hD.xe χ)) y J
    rw [hv _ _ y J J' hJ hJ', ι₁, ιb, vτ D _ _ y J hJ, vτ D' _ _ y J' hJ', ← map_add, vψ _ y J J' hJ hJ',
      vψ _ y J J' hJ hJ', vψ _ y J J' hJ hJ', vρ y J J' hJ hJ', cPoint_add, mul_comm (cP D' _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hψ : ∀ i, DegPre.gtφ D' F p'.g.b χ i ≫ Φ = 𝟙 _ ≫ DegPre.gtφ D F (up p'.g).b (hD.xe χ) i := fun i => by
      rw [Category.id_comp, hb]; exact gφ _ _ i
    exact ⟨hψ, maps_of_good hw D.P.isLB D'.P.isLB _ (p'.g.isGen χ) _ ((up p'.g).isGen _) hψ fun y J J' hJ hJ' =>
      (hv p'.g χ y J J' hJ hJ').trans (congrArg₂ (· * ·)
        (prod_gt p'.g.b χ (fun r => gw hD.w r y (J (r ≫ Φ)) (J' r))).symm rfl)⟩

end Pull

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
