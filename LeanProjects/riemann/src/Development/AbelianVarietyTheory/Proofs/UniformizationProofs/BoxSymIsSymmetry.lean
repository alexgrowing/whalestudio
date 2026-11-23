import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.SubAddEqZeroOfEqAdd

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSymmetry

section Generators

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hUV : U ≤ V)
    (hz : r z ∈ U) (x : Γ(X, V)ˣ) : gm r z U (res hUV x) = gm r z V x := by
  have key : X.presheaf.map (homOfLE hUV).op ≫ r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z hz =
      r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z (hUV hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res
  rw [dif_pos hz, dif_pos (hUV hz)]
  unfold pullU
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  have e := congrArg (fun f => CommRingCat.Hom.hom f (x : Γ(X, V))) key
  simpa using e

theorem gm_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι)
    (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) := by
  unfold GeneratorPullback.boxGen
  dsimp only
  refine (map_prod (gm r z _) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact gm_res_eq_gm r z _ h _

private theorem gm_lin_lemma_2 {X X' Z : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (y : Z ⟶ X') (z : Z) (j j' : J → L.ι) (e : ℤ)
    (hy : y z ∈ (L.LinComb F fun _ => 1).U j ⊓ (L.LinComb F fun _ => 1).U j') :
    gm y z ((L.LinComb F fun _ => 1).U j ⊓ (L.LinComb F fun _ => 1).U j')
        ((L.LinComb F fun _ => 1).g j j') ^ e =
      ∏ i, gm y z ((L.pull (F i)).U (fun _ => j i) ⊓ (L.pull (F i)).U (fun _ => j' i))
        ((L.pull (F i)).g (fun _ => j i) (fun _ => j' i)) ^ e := by
  rw [Finset.prod_zpow]
  congr 1
  unfold LB.pull LB.LinComb at *
  dsimp only at *
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Fintype.prod_unique, zpow_one]
  refine (gm_res_eq_gm y z _ hy _).trans (gm_res_eq_gm y z _ ?_ _).symm
  unfold LB.wchart at hy ⊢
  exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 i, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 i⟩

theorem trF_box (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (jj jj' : K → (LB.LinComb L F (fun _ => 1)).ι)
    (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj)
    (h' : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj') :
    trF (L := LB.LinComb L F (fun _ => 1)) φ ε r z jj jj' =
      ∏ i, trF (L := L.pull (F i)) φ ε r z (fun k _ => jj k i) (fun k _ => jj' k i) := by
  unfold trF
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : (r ≫ φ k) z ∈ (L.LinComb F fun _ => 1).U (jj k) ⊓ (L.LinComb F fun _ => 1).U (jj' k) := by
    unfold LB.wchart at h h'
    exact ⟨Set.mem_iInter.1 h k, Set.mem_iInter.1 h' k⟩
  exact gm_lin_lemma_2 L F (r ≫ φ k) z (jj k) (jj' k) (ε k) hk

private theorem gm_pullU_eq_gm_comp' {X Y Z : Scheme.{0}} (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (V : X.Opens)
    (hz : r z ∈ f ⁻¹ᵁ V) (a : Γ(X, V)ˣ) : gm r z (f ⁻¹ᵁ V) (pullU f V a) = gm (r ≫ f) z V a := by
  have hz' : (r ≫ f) z ∈ V := by simpa using hz
  unfold gm
  rw [dif_pos hz, dif_pos hz']
  unfold pullU
  ext
  simp
  rfl

private theorem units_ext_of_gm_id_eq_on_open {Y : Scheme.{0}} {W : Y.Opens} (s s' : Γ(Y, W)ˣ)
    (h : ∀ y : Y, y ∈ W → gm (𝟙 Y) y W s = gm (𝟙 Y) y W s') : s = s' := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf W
  intro y hy
  have e := congrArg Units.val (h y hy)
  unfold gm pullU at e
  rw [dif_pos (by simpa using hy)] at e
  exact e

private theorem gm_linComb_transition_eq {X' Y Z : Scheme.{0}} (M : LB X') {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (a b : K → M.ι)
    (hz : r z ∈ (M.LinComb φ ε).U a ⊓ (M.LinComb φ ε).U b) :
    gm r z ((M.LinComb φ ε).U a ⊓ (M.LinComb φ ε).U b) ((M.LinComb φ ε).g a b) = trF (L := M) φ ε r z a b := by
  unfold trF
  unfold LB.LinComb at *
  dsimp only at *
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow]
  congr 1
  refine (gm_res_eq_gm r z _ hz _).trans (gm_pullU_eq_gm_comp' (φ k) r z (M.U (a k) ⊓ M.U (b k)) ?_ (M.g (a k) (b k)))
  unfold LB.wchart at hz
  exact ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩

private theorem mem_pull_wchart_of_mem_linComb_wchart {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (y : Y) (jj : K → J → L.ι) (i : J)
    (h : y ∈ (L.LinComb F fun _ => 1).wchart φ jj) : y ∈ (L.pull (F i)).wchart φ (fun k _ => jj k i) := by
  unfold LB.pull
  unfold LB.wchart LB.LinComb at *
  dsimp only at *
  unfold LB.wchart at *
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 h k) i

private theorem gm_pullAlong_section_eq_gm_comp {X X' Y Y' Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : (L.LinComb φ ε).Gen) (r : Z ⟶ Y') (z : Z)
    (a : K → (L.pull F).ι) (hz : r z ∈ (L.pull F).wchart ψ a) :
    gm r z ((L.pull F).wchart ψ a) ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s a) =
      gm (r ≫ h) z (L.wchart φ fun k => a k PUnit.unit) (t.s fun k => a k PUnit.unit) := by
  unfold GeneratorPullback.pullAlong
  dsimp only
  refine (gm_res_eq_gm r z _ hz _).trans (gm_pullU_eq_gm_comp' h r z _ ?_ _)
  unfold LB.wchart at hz ⊢
  refine Set.mem_iInter.2 fun k => ?_
  have h1 := Set.mem_iInter.1 hz k
  unfold LB.pull LB.LinComb at h1
  dsimp only at h1
  unfold LB.wchart at h1
  have h2 := Set.mem_iInter.1 h1 PUnit.unit
  have e := congrArg (fun m : Y' ⟶ X => m.base (r z)) (hψ k)
  simp at e h2
  simp [← e, h2]

theorem isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro (a : K → (L.LinComb F fun _ => 1).ι) (b : K → (L.LinComb F fun _ => 1).ι)
  apply units_ext_of_gm_id_eq_on_open
  intro y hy
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ ((L.LinComb F fun _ => 1).LinComb φ ε).U a ⊓
      ((L.LinComb F fun _ => 1).LinComb φ ε).U b := hy
  have ha : (𝟙 Y : Y ⟶ Y) y ∈ (L.LinComb F fun _ => 1).wchart φ a := hy.1
  have hb : (𝟙 Y : Y ⟶ Y) y ∈ (L.LinComb F fun _ => 1).wchart φ b := hy.2
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y _ hy' _, gm_res_eq_gm (𝟙 Y) y _ hy' _, gm_linComb_transition_eq _ φ ε (𝟙 Y) y a b hy']
  erw [gm_boxGen L F φ ε t (𝟙 Y) y a ha, gm_boxGen L F φ ε t (𝟙 Y) y b hb, trF_box L F φ ε (𝟙 Y) y a b ha hb,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull (F i)).LinComb φ ε).U (fun k _ => a k i) ⊓
      ((L.pull (F i)).LinComb φ ε).U (fun k _ => b k i) :=
    ⟨mem_pull_wchart_of_mem_linComb_wchart L F φ y a i hy.1, mem_pull_wchart_of_mem_linComb_wchart L F φ y b i hy.2⟩
  have e := congrArg (gm (𝟙 Y) y _) (ht i (fun k _ => a k i) (fun k _ => b k i))
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y _ hi _, gm_res_eq_gm (𝟙 Y) y _ hi _, gm_linComb_transition_eq _ φ ε (𝟙 Y) y _ _ hi] at e
  exact e

end Generators

variable {S : Scheme.{0}}

theorem eSec_comp_sym (H : Over S) [GrpObj H] (k : Fin 2) :
    eSec H ≫ (![(ι[H]).left, 𝟙 H.left] : Fin 2 → (H.left ⟶ H.left)) k = eSec H := by
  unfold eSec
  fin_cases k <;> simp [← Over.comp_left]

theorem eSec_comp_hom {G' G : Over S} [GrpObj G'] [GrpObj G] (f : G' ⟶ G) [IsMonHom f] :
    eSec G' ≫ f.left = eSec G := by
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

end GlobalTheory.BoxSymmetry

open GlobalTheory.BoxSymmetry in

theorem GlobalTheory.boxSym_isSymmetry : ∀ S : Scheme.{0}, BoxSymSt (S := S) := by
  intro S
  unfold BoxSymSt
  intro G' G _ _ _ _ j p L sy hL hsy hc
  have c' : ∀ k, eSec G' ≫ ![(ι[G']).left, 𝟙 G'.left] k = eSec G' := fun k => eSec_comp_sym G' k
  have c : ∀ k, eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k = eSec G := fun k => eSec_comp_sym G k
  have key : ∀ (y : (𝟙_ (Over S)).left) (a : Fin 2 → L.ι), (∀ k, a k = a 0) → eSec G y ∈ L.U (a 0) →
      gm (eSec G) y (L.wchart ![(ι[G]).left, 𝟙 G.left] a) (sy.s a) = 1 := by
    intro y a ha hy
    obtain ⟨J, hJ, hJa⟩ := exists_good L hL y (fun k => (𝟙 _ ≫ eSec G) ≫ ![(ι[G]).left, 𝟙 G.left] k) a
      (fun k k' _ => (ha k).trans (ha k').symm) (fun k => by
        show ((𝟙 _ ≫ eSec G) ≫ ![(ι[G]).left, 𝟙 G.left] k) y ∈ L.U (a k)
        rw [Category.id_comp, c k, ha k]
        exact hy)
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, val_one, val_of sy _ y J a hJa, Category.id_comp] at e
    exact e
  have hm : ∀ i, IsMonHom (p.pr i) := by
    intro i
    exact p.hom i
  refine ⟨?_, ?_⟩
  · unfold boxSym boxLB
    exact isGen_boxGen L _ _ _ _ fun i => LBxP.isGen_pullAlong L _ _ _ _ _ _ _ hsy
  · refine corr_of_val (LB.isLB_linComb hL _ _) fun y JB hJB => ?_
    rw [val_pull hJB, val_one,
      val_of _ _ y JB (fun k => JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k)) (fun _ => rfl)]
    have hmem := hJB.mem ![(ι[G']).left, 𝟙 G'.left] (𝟙 _ ≫ eSec G')
    erw [gm_boxGen L _ _ _ _ (𝟙 _ ≫ eSec G') y _ hmem]
    refine Finset.prod_eq_one fun i _ => ?_
    erw [gm_pullAlong_section_eq_gm_comp L _ _ _ _ _ _ sy (𝟙 _ ≫ eSec G') y _ (mem_pull_wchart_of_mem_linComb_wchart L _ _ _ _ i hmem)]
    rw [show (𝟙 _ ≫ eSec G') ≫ (p.pr i).left = eSec G by rw [Category.id_comp, eSec_comp_hom]]
    apply key
    · intro k
      show JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) i =
        JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i
      rw [Category.id_comp, c' k, c' 0]
    · show eSec G y ∈ L.U (JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i)
      have g1 := hJB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0)
      have g2 : ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) y ∈
          (p.pr i).left ⁻¹ᵁ L.U (JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i) := by
        unfold LB.LinComb LB.wchart at g1
        exact Set.mem_iInter.1 g1 i
      have e : (((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) ≫ (p.pr i).left) y = eSec G y := by
        rw [Category.id_comp, c' 0, eSec_comp_hom]
      rw [← e]
      exact g2

end
