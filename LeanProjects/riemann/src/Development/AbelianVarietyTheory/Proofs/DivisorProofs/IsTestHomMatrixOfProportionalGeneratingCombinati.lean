import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixCond

theorem unit_of_proportional {X : Scheme.{0}} {V : X.Opens} {m : ℕ} (B C : Fin m → Γ(X, V))
    (hC : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (C j)))
    (hB : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (B j)))
    (hP : ∀ x ∈ V, ∀ j j', gs (𝟙 X) x V (B j) * gs (𝟙 X) x V (C j') =
      gs (𝟙 X) x V (B j') * gs (𝟙 X) x V (C j)) :
    ∃ u : Γ(X, V)ˣ, ∀ j, B j = u.val * C j := by
  let W : Fin m → X.Opens := fun j => X.basicOpen (C j)
  have lW : ∀ j, W j ≤ V := fun j => X.basicOpen_le _
  have uC : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (C j)) := fun j y hy =>
    (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V (lW j hy) (C j)).2 hy
  have uB : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (B j)) := fun j y hy => by
    obtain ⟨j', hj'⟩ := hB y (lW j hy)
    have e := hP y (lW j hy) j' j
    have h2 := hj'.mul (uC j y hy)
    rw [e] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hu : ∀ j, IsUnit (resG X (lW j) (C j)) := fun j =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := uC j y hy
      rw [← gs_res (𝟙 X) y (lW j) hy, gs_eq _ y _ hy] at this
      exact this
  let w : ∀ j, Γ(X, W j) := fun j => resG X (lW j) (B j) * ((hu j).unit⁻¹).val
  have hw : ∀ j, ∀ y ∈ W j, gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C j) = gs (𝟙 X) y V (B j) := fun j y hy => by
    rw [← gs_res (𝟙 X) y (lW j) hy (C j), ← gs_mul _ y _ hy, _root_.mul_assoc]
    show gs (𝟙 X) y (W j) (resG X (lW j) (B j) * (((hu j).unit⁻¹).val * (hu j).unit.val)) = _
    rw [Units.inv_mul, _root_.mul_one, gs_res _ y _ hy]
  have wu : ∀ j, IsUnit (w j) := fun j => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hw j y hy
    have h1 : IsUnit (gs (𝟙 X) y (W j) (w j)) := by
      have := uB j y hy
      rw [← e] at this
      exact isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at h1
    exact h1
  obtain ⟨s, hs⟩ := glue_unit V W lW (fun y hy => by
      obtain ⟨j, hj⟩ := hC y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C j)).1 hj⟩)
    (fun j => (wu j).unit) (fun i j y hy => by
      apply Units.ext
      rw [← gs_unit _ y _ hy.1, ← gs_unit _ y _ hy.2]
      refine (uC i y hy.1).mul_right_cancel ?_
      refine (uC j y hy.2).mul_right_cancel ?_
      show gs (𝟙 X) y (W i) (w i) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j) =
        gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j)
      rw [hw i y hy.1, mul_right_comm, hw j y hy.2, hP y (lW i hy.1) i j])
  refine ⟨s, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := hC y hy
  have yi : y ∈ W i := (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C i)).1 hi
  have es : gs (𝟙 X) y V s.val = gs (𝟙 X) y (W i) (w i) := by
    rw [← gs_res (𝟙 X) y (lW i) yi]
    exact congrArg (fun q : Γ(X, W i)ˣ => gs (𝟙 X) y (W i) q.val) (hs i)
  rw [gs_mul _ y _ hy, es]
  refine hi.mul_right_cancel ?_
  rw [mul_right_comm, hw i y yi, hP y hy i j]

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem isMat_of_conditions : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM heA heB hcov hvA hvB hT hgen
    hprop hnorm
  have key : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ∃ u : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)ˣ, ∀ j : Fin mB,
        ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        u.val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom
          (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro p
    set V := (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p with hV
    have mB' : ∀ z ∈ V, (Φ'.left ≫ φB' ≫ θ B) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hz.1
    have mA' : ∀ z ∈ V, (φA' ≫ θ A) z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hz.2
    have gB : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V
        (((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs (Φ'.left ≫ φB' ≫ θ B) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) :=
      fun z hz j => (gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp])
    have gC : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V (∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        comb bA (φA' ≫ θ A) A'.hom c z p.2 j := fun z hz j => by
      rw [gs_finsum _ z _ hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul _ z _ hz]
      refine congrArg₂ (· * ·) ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]))
        ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]; rfl))
    obtain ⟨u, hu⟩ := unit_of_proportional (V := V)
      (fun j => ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1))
      (fun j => ∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2))
      (fun z hz => by
        obtain ⟨j, hj⟩ := hgen z p.2 (mA' z hz)
        exact ⟨j, by rw [gC z hz j]; exact hj⟩)
      (fun z hz => by
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((Φ'.left ≫ φB' ≫ θ B) z)))
        exact ⟨j, by rw [gB z hz j]; exact (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) _ z (mB' z hz)).1 hj⟩)
      (fun z hz j j' => by
        rw [gB z hz j, gB z hz j', gC z hz j, gC z hz j']
        exact hprop z p.2 p.1 (mA' z hz) (mB' z hz) j j')
    exact ⟨u, hu⟩
  choose u hu using key
  refine ⟨φA' ≫ θ A, φB' ≫ θ B, ⟨u⟩, by rw [Category.assoc, θ_snd, Category.comp_id],
    by rw [Category.assoc, θ_snd, Category.comp_id], ?_, ?_, fun j p => hu p j⟩
  · exact GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation Rg A B L M k mA mB bA bB R A' B' Φ' (φA' ≫ θ A) (φB' ≫ θ B) c u hgen (fun j p => hu p j)
  · exact GlobalTheory.T.isoNormalisation_at_zeroSection Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c u hcov hvA hvB hT hnorm
      (fun j p => hu p j)

end GlobalTheory.HomFixCond
