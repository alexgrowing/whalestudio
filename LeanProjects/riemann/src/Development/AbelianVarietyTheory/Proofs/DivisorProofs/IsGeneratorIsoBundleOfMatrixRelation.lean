import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv.CondGen

theorem gs_appLE_self {X Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (z : Y)
    (hz : z ∈ W) (f : Γ(X, U)) : gs (𝟙 Y) z W ((q.appLE U W e).hom f) = gs q z U f := by
  have h1 := gs_res (𝟙 Y) z e hz ((q.app U).hom f)
  have h2 := gs_pull (𝟙 Y) q z U (e hz) f
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

end GlobalTheory.HomFixUniv.CondGen

open GlobalTheory.HomFixUniv.CondGen in

theorem GlobalTheory.HomFixUniv.isGen_of_matRel : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  intro Rg _ A B _ _ L M k mA mB bA bB R _ A' B' Φ' ψA ψB c u hG hR p p'
  apply unit_ext
  intro z hz
  have hzp : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := hz.1
  have hzp' : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p' := hz.2
  have hmB : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hzp.1
  have hmB' : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p'.1 hzp'.1
  have hmA : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hzp.2
  have hmA' : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p'.2 hzp'.2
  have key : ∀ (q : (Fin 1 → M.ι) × (Fin 1 → L.ι)), z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U q → ∀ j : Fin mB,
      gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) q.1) ((bB j).f q.1) =
        (gm (𝟙 _) z _ (u q)).val * GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z q.2 j := by
    intro q hq j
    have e := congrArg (gs (𝟙 A'.left) z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U q)) (hR j q)
    refine (gs_appLE_self _ _ _ _ z hq _).symm.trans (e.trans ?_)
    rw [gs_mul _ z _ hq, gs_unit _ z _ hq, gs_fsum _ z _ hq]
    unfold GlobalTheory.HomFixUniv.comb
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ z _ hq]
    exact congrArg₂ (· * ·) (gs_appLE_self _ _ _ _ z hq _) (gs_appLE_self _ _ _ _ z hq _)
  have tB : ∀ j : Fin mB, gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) =
      (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val *
        gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1) ((bB j).f p'.1) :=
    fun j => sec_trans (bB j) (Φ'.left ≫ ψB) z hmB hmB'
  have tA : ∀ i : Fin mA, gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) ((bA i).f p.2) =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2) ((bA i).f p'.2) :=
    fun i => sec_trans (bA i) ψA z hmA hmA'
  have tC : ∀ j : Fin mB, GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p.2 j =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j := by
    intro j
    unfold GlobalTheory.HomFixUniv.comb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrArg (_ * ·) (tA i)).trans (mul_left_comm _ _ _)
  have hg : gm (𝟙 A'.left) z _ ((isoLB (L := L) (M := M) k Φ' ψA ψB).g p p') =
      trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1 *
        (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹ := by
    show gm (𝟙 A'.left) z _ (res _ _ * (res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ?_)
      ((map_inv _ _).trans (congrArg _ ((gm_res _ z _ hz _).trans ?_))))
    · exact (gm_linComb M _ _ (𝟙 A'.left) z p.1 p'.1 hzp.1 hzp'.1).trans (by simp only [trF, Category.id_comp])
    · exact (gm_linComb L _ _ (𝟙 A'.left) z p.2 p'.2 hzp.2 hzp'.2).trans (by simp only [trF, Category.id_comp])
  obtain ⟨j, hj⟩ := hG z p.2 hmA
  refine (gm_res _ z _ hz _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  rw [hg, gm_res _ z _ hz]
  apply Units.ext
  apply hj.mul_right_cancel
  have e1 := key p hzp j
  have e2 := key p' hzp' j
  have e3 := tB j
  have e4 := tC j
  have hinv := Units.inv_mul (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)
  rw [e1, e2, e4] at e3
  simp only [Units.val_mul]
  rw [e4]
  set TM := (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val
  set TL := (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val
  set TLi := ((trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹).val
  set U' := (gm (𝟙 A'.left) z _ (u p')).val
  set C' := GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j
  linear_combination e3 - (TM * U' * C') * hinv
