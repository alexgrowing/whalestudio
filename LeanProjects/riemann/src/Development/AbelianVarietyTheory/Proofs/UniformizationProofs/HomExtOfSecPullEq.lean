import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem ι_comp_eq_of_gs_eq {X Z : Scheme.{0}} (f g : Z ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (W : Z.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) (h : ∀ (a : Γ(X, U)), ∀ z ∈ W, gs f z U a = gs g z U a) :
    W.ι ≫ f = W.ι ≫ g := by
  have key : ∀ (U' : X.Opens) (hU' : U' = U) (V : Z.Opens) (hV : V ≤ W) (e₁ : V ≤ f ⁻¹ᵁ U') (e₂ : V ≤ g ⁻¹ᵁ U'),
      f.appLE U' V e₁ = g.appLE U' V e₂ := by
    intro U' hU' V hV e₁ e₂
    subst hU'
    ext a
    refine TopCat.Presheaf.section_ext Z.sheaf V _ _ fun z hz => ?_
    have hfz : f z ∈ U' := e₁ hz
    have hgz : g z ∈ U' := e₂ hz
    have := h a z (hV hz)
    rw [gs_eq f z U' hfz, gs_eq g z U' hgz] at this
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    erw [Z.presheaf.germ_res_apply, Z.presheaf.germ_res_apply]
    exact this
  rw [← f.resLE_comp_ι hf, ← g.resLE_comp_ι hg]
  congr 1
  have : IsAffine U := hU
  apply ext_of_isAffine
  show (Scheme.Hom.resLE f U W hf).app ⊤ = (Scheme.Hom.resLE g U W hg).app ⊤
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, Scheme.Hom.resLE_appLE]
  exact key _ (Scheme.Opens.ι_image_top U) _ (Scheme.Opens.ι_image_le _ _) _ _

private theorem hom_mul_eq_mul_of_eq_mul {R R' S : CommRingCat} (φ : R ⟶ S) (ψ : R' ⟶ S) (x y : R) (x' y' : R')
    (G₁ G₂ : S) (hx : φ.hom x = G₁ * ψ.hom x') (hy : φ.hom y = G₂ * ψ.hom y') :
    φ.hom (x * y) = (G₁ * G₂) * ψ.hom (x' * y') := by
  rw [map_mul, map_mul, hx, hy]
  ring

theorem exists_sec_extend_pos {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB)
    {N : ℕ} (s : H0 L N) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (N * m)), 1 ≤ m ∧ ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL N s).1 a
  refine ⟨m + 1, ⟨fun j => s.f j * @id Γ(X, (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U j) (t.f j), fun i j => ?_⟩, by omega, fun x i hx hi => ?_⟩
  · have hc : ((N * (m + 1) : ℕ) : ℤ) = (N : ℤ) + ((N * m : ℕ) : ℤ) := by push_cast; ring
    have key := hom_mul_eq_mul_of_eq_mul _ _ (s.f i) (t.f i) (s.f j) (t.f j) _ _ (s.compat i j) (t.compat i j)
    refine key.trans (congrArg₂ (· * ·) ?_ rfl)
    dsimp only [LB.LinComb]
    rw [Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_one, hc, zpow_add]
    exact (Units.val_mul _ _).symm
  · have hw : (𝟙 X) x ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hi
    have e := gs_mul (𝟙 X) x _ hw (s.f fun _ => i) (t.f fun _ => i)
    have ht' : gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (t.f fun _ => i) =
        gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (s.f fun _ => i) ^ m *
          gs (𝟙 X) x _ a := ht x (fun _ => i) hx hi
    refine e.trans ?_
    rw [ht']
    ring

private theorem gs_eq_stalkMap_gs_id_uniformization {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (hz : r z ∈ U) (b : Γ(X, U)) :
    gs r z U b = (r.stalkMap z).hom (gs (𝟙 X) (r z) U b) := by
  rw [gs_eq r z U hz, gs_eq (𝟙 X) (r z) U hz]
  have e := congrArg (fun φ => φ.hom b) (r.germ_stalkMap U z hz)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.symm

theorem gs_pull_extend {X Z : Scheme.{0}} {L : LB X} {N n m : ℕ} (s : H0 L N) (t : H0 L n) (a : Γ(X, nonzeroLocus s))
    (h : ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a)
    (r : Z ⟶ X) (z : Z) (i : L.ι) (hz : r z ∈ nonzeroLocus s) (hi : r z ∈ L.U i) :
    gs r z _ (t.f fun _ => i) = gs r z _ (s.f fun _ => i) ^ m * gs r z _ a := by
  have hw : r z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := (mem_wchart_oneTerm (0 : Fin 1)).2 hi
  have hwn : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => i) := hw
  have hwN : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) := hw
  rw [gs_eq_stalkMap_gs_id_uniformization r z _ hwn, gs_eq_stalkMap_gs_id_uniformization r z _ hwN, gs_eq_stalkMap_gs_id_uniformization r z _ hz, h (r z) i hz hi, map_mul, map_pow]

private theorem isUnit_gs_of_mem_basicOpen' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hb : r z ∈ X.basicOpen b) : IsUnit (gs r z U b) := by
  have hU : r z ∈ U := X.basicOpen_le b hb
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU]
  exact ((X.mem_basicOpen b (r z) hU).1 hb).map (r.stalkMap z).hom

private theorem mem_basicOpen_of_isUnit_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hU : r z ∈ U) (hb : IsUnit (gs r z U b)) : r z ∈ X.basicOpen b := by
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU] at hb
  rw [X.mem_basicOpen b (r z) hU]
  exact (isUnit_map_iff (r.stalkMap z).hom _).1 hb

private theorem exists_mem_basicOpen_of_mem_nonzeroLocus {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) {x : X}
    (hx : x ∈ nonzeroLocus a) : ∃ j : L.ι, x ∈ X.basicOpen (a.f fun _ => j) := by
  unfold nonzeroLocus at hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨j, rfl⟩ : ∃ j, k = fun _ => j := ⟨k 0, funext fun q => congrArg k (Subsingleton.elim q 0)⟩
  exact ⟨j, hk⟩

private theorem mem_nonzeroLocus_of_mem_basicOpen {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) (j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (a.f fun _ => j)) : x ∈ nonzeroLocus a := by
  unfold nonzeroLocus
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, hx⟩

private theorem exists_mem_chart' {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ j, x ∈ L.U j := by
  have hx : x ∈ ⨆ i, L.U i := by
    rw [hL.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

theorem hom_ext_of_sec_pull_eq : ∀ (X Z : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → (∃ (N : ℕ) (_ : 1 ≤ N) (κ : Type) (s : κ → H0 L N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i))) → ∀ (f g : Z ⟶ X) (v : LB.Iso (L.pull f) (L.pull g)), v.IsGen → (∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z) (j j' : L.ι), g z ∈ L.U j → f z ∈ L.U j' → Geo.Tor.gs g z _ (a.f (fun _ => j)) = (Geo.Tor.gw v (𝟙 Z) z j (fun _ => j') ^ n).val * Geo.Tor.gs f z _ (a.f (fun _ => j'))) → f = g := by
  intro X Z _ _ L hL hcov f g v _ hrel
  obtain ⟨N, hN, κ, s, hD, haff⟩ := hcov
  have fg : ∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z), f z ∈ nonzeroLocus a → g z ∈ nonzeroLocus a := by
    intro n hn a z hz
    obtain ⟨j', hj'⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus a hz
    obtain ⟨j, hj⟩ := exists_mem_chart' hL (g z)
    have hf' : f z ∈ L.U j' := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hj')
    have hgw : g z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => j) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hj
    have u2 : IsUnit (gs g z _ (a.f fun _ => j)) := by
      rw [hrel n hn a z j j' hj hf']
      exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen' f z _ hj')
    exact mem_nonzeroLocus_of_mem_basicOpen a j (mem_basicOpen_of_isUnit_gs g z _ hgw u2)
  have hW : ⨆ i, f ⁻¹ᵁ nonzeroLocus (s i) = ⊤ := by
    refine eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    have hz : f z ∈ ⨆ i, nonzeroLocus (s i) := by
      rw [hD]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, hi⟩
  refine (Z.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ nonzeroLocus (s i)) hW).hom_ext f g fun i => ?_
  show (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ f = (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ g
  refine ι_comp_eq_of_gs_eq f g (haff i) _ le_rfl (fun z hz => fg N hN (s i) z hz) fun a z hz => ?_
  have hfD : f z ∈ nonzeroLocus (s i) := hz
  have hgD : g z ∈ nonzeroLocus (s i) := fg N hN (s i) z hz
  obtain ⟨j, hb⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus (s i) hgD
  have hgj : g z ∈ L.U j := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hb)
  obtain ⟨j', hfj'⟩ := exists_mem_chart' hL (f z)
  obtain ⟨m, t, hm, ht⟩ := exists_sec_extend_pos hL (s i) a
  have step_before_last_eq_s_succ := hrel N hN (s i) z j j' hgj hfj'
  have eq_t := hrel (N * m) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) t z j j' hgj hfj'
  have ext_g := gs_pull_extend (s i) t a ht g z j hgD hgj
  have ext_f := gs_pull_extend (s i) t a ht f z j' hfD hfj'
  have hu : IsUnit (gs g z _ ((s i).f fun _ => j)) := isUnit_gs_of_mem_basicOpen' g z _ hb
  have key : gs g z _ ((s i).f fun _ => j) ^ m * gs g z _ a =
      gs g z _ ((s i).f fun _ => j) ^ m * gs f z _ a := by
    rw [← ext_g, eq_t, ext_f, step_before_last_eq_s_succ, mul_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
    ring
  exact ((hu.pow m).mul_left_cancel key).symm

end GlobalTheory
