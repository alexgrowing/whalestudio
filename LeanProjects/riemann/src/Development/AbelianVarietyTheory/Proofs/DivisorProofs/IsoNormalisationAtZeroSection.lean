import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixNorm

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem gs_npow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem one_comp_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hφ (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem stalkMap_gm_pow {Z Y : Scheme.{0}} (t : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : t z ∈ V) (a : Γ(Y, V)ˣ) (n : ℕ) :
    (t.stalkMap z).hom ((gm (𝟙 Y) (t z) V a) ^ n).val = gs t z V a.val ^ n := by
  rw [Units.val_pow_eq_pow_val, ← gs_unit (𝟙 Y) (t z) V h, map_pow, ← gs_stalkMap t z V h]

theorem norm_at_zero : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c u hcov hA hB hT hN hrel p
  obtain ⟨gA, gB, hΦ, -⟩ := hT
  haveI : IsMonHom Φ' := hΦ
  have e₀ : zeroPt A' ≫ A'.hom = 𝟙 _ := by simp [zeroPt]
  have eΦ : zeroPt A' ≫ Φ'.left = zeroPt B' := by rw [zeroPt, zeroPt, ← Over.comp_left, IsMonHom.one_hom]
  have eA' : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by
    rw [← Category.assoc, zeroPt, one_comp_of_isGrpPullback gA, Category.assoc]; rfl
  have eB' : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by
    rw [← Category.assoc, eΦ, ← Category.assoc, zeroPt, one_comp_of_isGrpPullback gB, Category.assoc]; rfl
  refine fn_ext fun z hz => ?_

  have hz0 := hz
  obtain ⟨⟨hzU', hzA'⟩, hzB'⟩ := hz
  have hzU : zeroPt A' z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := hzU'
  have hzA : t z ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) := hzA'
  have hzB : t z ∈ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := hzB'
  have pA : eSec A (t z) ∈ L.U (p.2 0) := Set.mem_iInter.1 hzA PUnit.unit
  have pB : eSec B (t z) ∈ M.U (p.1 0) := Set.mem_iInter.1 hzB PUnit.unit
  have mA : (eSec A ≫ θ A) (t z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) A).left ((eSec A ≫ θ A) (t z)) ∈ L.U (p.2 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pA
  have mB : (eSec B ≫ θ B) (t z) ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) B).left ((eSec B ≫ θ B) (t z)) ∈ M.U (p.1 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pB
  have sB : ∀ j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((Φ'.left ≫ (φB' ≫ θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs t z ⊤ (βB j) * gs t z (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)) (eB.s (fun _ => p.1 0)).val ^ k := by
    intro j
    have v := hB j (t z) p.1 mB
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eB']
    erw [gs_comp t _ z _ mB]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzB, ← gs_stalkMap t z ⊤ trivial]
  have sA : ∀ i, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    intro i
    have v := hA i (t z) p.2 mA
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eA']
    erw [gs_comp t _ z _ mA]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzA, ← gs_stalkMap t z ⊤ trivial]
  have sC : ∀ i j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      ((A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom (c i j)) =
        gs (𝟙 _) z ⊤ (c i j) := by
    intro i j
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [e₀]
  have gt : ∀ x : Γ(Sp Rg, ⊤), gs t z ⊤ x = gs (𝟙 _) z ⊤ (t.appTop x) := by
    intro x
    have e := gs_pull (𝟙 (Sp R)) t z ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have nN : ∀ j, ∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i) = gs t z ⊤ (βB j) := by
    intro j
    rw [gt, hN j, gs_finsum _ z ⊤ trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [gt, gs_mul _ z ⊤ trivial]
  have hcz : (eSec B ≫ θ B) (t z) ∈ (⨆ j, nonzeroLocus (bB j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hcz
  have hu := (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) (eSec B ≫ θ B) (t z) mB).1 hj
  erw [hB j (t z) p.1 mB] at hu
  have hβ : IsUnit (gs t z ⊤ (βB j)) := by
    rw [gs_stalkMap t z ⊤ trivial]
    exact (isUnit_of_mul_isUnit_left hu).map _
  have E := congrArg (gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)) (hrel j p)
  rw [sB j, gs_mul _ _ _ hzU, gs_finsum _ _ _ hzU] at E
  simp only [gs_mul _ _ _ hzU, sC, sA] at E
  have hs : ∑ i, gs (𝟙 _) z ⊤ (c i j) * (gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k) =
      (∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i)) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hs, nN j] at E
  rw [gs_mul _ z _ hz0, gs_npow _ z _ hz0, gs_npow _ z _ hz0]
  erw [gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0]
  simp only [Category.id_comp]
  exact hβ.mul_left_cancel (by rw [E]; ring)

end GlobalTheory.HomFixNorm
