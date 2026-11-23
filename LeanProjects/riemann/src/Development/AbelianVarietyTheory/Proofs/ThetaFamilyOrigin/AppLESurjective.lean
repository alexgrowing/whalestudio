import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.VeryAmpleCharts

variable {X Y : Scheme.{0}} (L : LB X) (N : ℕ) {u : Y ⟶ X} {ψ : X ⟶ Y} (hψ : ψ ≫ u = 𝟙 X)

abbrev tens (u : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin N) (fun _ => u) (fun _ => 1)

include hψ in
theorem chart_le (J : PUnit → L.ι) :
    (lbPow L N).U J ≤ ψ ⁻¹ᵁ (tens L N u).U (fun _ => J PUnit.unit) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q : X ⟶ X => q y ∈ L.U (J PUnit.unit)) hψ).mpr
    (Set.mem_iInter.1 hy PUnit.unit)

def move (s : (tens L N u).Sec) : (lbPow L N).Sec where
  f J := (ψ.appLE _ _ (chart_le L N hψ J)).hom (s.f (fun _ => J PUnit.unit))
  compat J J' := fn_ext fun y hy => by
    have h₁ := chart_le L N hψ J hy.1
    have h₂ := chart_le L N hψ J' hy.2
    have e := sec_trans s ψ y h₁ h₂
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_appLE ψ _ _ _ (𝟙 X) y hy.1,
      gs_appLE ψ _ _ _ (𝟙 X) y hy.2, Category.id_comp, gs_unit _ y _ hy]
    refine e.trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
    refine Eq.trans ?_ (gm_linComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) (𝟙 X) y J J' hy.1 hy.2).symm
    simp only [trF, hψ, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.prod_unique,
      zpow_natCast, Category.comp_id]

theorem gs_move (s : (tens L N u).Sec) (J : PUnit → L.ι) (y : X) (hy : y ∈ (lbPow L N).U J) :
    gs (𝟙 X) y _ ((move L N hψ s).f J) = gs ψ y _ (s.f (fun _ => J PUnit.unit)) :=
  (gs_appLE ψ _ _ _ (𝟙 X) y hy _).trans (by rw [Category.id_comp])

theorem locus_move (hL : L.IsLB) (s : (tens L N u).Sec) :
    Out.nonzeroLocus (move L N hψ s) = ψ ⁻¹ᵁ Out.nonzeroLocus s := by
  ext y
  refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
    (mem_nonzeroLocus _ (ψ y)).symm)
  · have h₁ := chart_le L N hψ k hk
    rw [gs_move L N hψ s k y hk, gs_stalkMap ψ y _ h₁] at u
    exact ⟨_, h₁, (isUnit_map_iff (ψ.stalkMap y).hom _).1 u⟩
  · obtain ⟨i, hi⟩ := exists_chart hL y
    have hk : y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    have h₁ := chart_le L N hψ _ hk
    refine ⟨_, hk, ?_⟩
    rw [gs_move L N hψ s _ y hk]
    have e := sec_trans s ψ y hj h₁
    exact isUnit_of_mul_isUnit_right
      ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))

theorem appLE_surjective [IsIso ψ] (U : Y.Opens) (V : X.Opens) (h : V = ψ ⁻¹ᵁ U) :
    Function.Surjective (ψ.appLE U V h.le).hom := by
  subst h
  rw [← Scheme.Hom.app_eq_appLE]
  exact (ConcreteCategory.bijective_of_isIso (ψ.app U)).2

end GlobalTheory.VeryAmpleCharts

namespace GlobalTheory

open VeryAmpleCharts

theorem veryAmple_lbPow : Out.AmpleSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ), 4 ≤ N → ∃ (m : ℕ) (s : Fin (m + 1) → (lbPow P.L N).Sec), (⨆ i, Out.nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ∃ r : Fin (m + 1) → Γ(P.A.left, Out.nonzeroLocus (s i)), (∀ j k, resG _ (inf_le_right : Out.nonzeroLocus (s i) ⊓ (lbPow P.L N).U k ≤ _) ((s j).f k) = resG _ inf_le_left (r j) * resG _ inf_le_right ((s i).f k)) ∧ ∀ f : Γ(P.A.left, Out.nonzeroLocus (s i)), ∃ F : MvPolynomial (Fin (m + 1)) K, f = MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F) := by
  intro hA K _ _ P N hN
  obtain ⟨m, s, hcov, hs⟩ := (hA (Sp K) P N hN).2 ⊤ (isAffineOpen_top _)
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso (P.A.left.topIso).hom)
  let ψ := inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  have loc := fun i => locus_move P.L N hψ P.isLB (s i)
  refine ⟨m, fun i => move P.L N hψ (s i), ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show ψ y ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, fun f => ?_⟩
  · have hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ (Out.powOver P.A P.L ⊤ N).U (fun _ => k PUnit.unit) :=
      ⟨(loc i).le hy.1, chart_le P.L N hψ k hy.2⟩
    have e := congrArg (gs ψ y _) (hr j (fun _ => k PUnit.unit))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    refine (gs_res _ y _ hy _).trans ((gs_move P.L N hψ _ k y hy.2).trans (e.trans (Eq.symm
      ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (congrArg (fun q => gs q y _ _) (Category.id_comp ψ))))
      ((gs_res _ y _ hy _).trans (gs_move P.L N hψ _ k y hy.2)))))))
  · obtain ⟨d, rfl⟩ := appLE_surjective (ψ := ψ) _ _ (loc i) f
    obtain ⟨p, rfl⟩ := hsurj d
    let c : Γ((⊤ : (Sp K).Opens).toScheme, ⊤) ⟶ CommRingCat.of K :=
      (Sp K).topIso.inv.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
    have w : ψ ≫ P.A.hom ∣_ ⊤ = P.A.hom ≫ (Sp K).topIso.inv := by
      rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ,
        Category.id_comp, Category.assoc]
      exact (Category.comp_id _).symm.trans (congrArg _ (Sp K).topIso.inv_hom_id.symm)
    have w' : (P.A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top ≫ ψ.appLE _ _ (loc i).le =
        c ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ P.A.hom.appLE ⊤ _ le_top := by
      have aux : ∀ {a b : P.A.left ⟶ (⊤ : (Sp K).Opens).toScheme} (_ : a = b) (V : P.A.left.Opens) h h',
          a.appLE ⊤ V h = b.appLE ⊤ V h' := by
        intro a b e V h h'; subst e; rfl
      simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
        ((aux w _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    refine ⟨MvPolynomial.map c.hom p, ?_⟩
    rw [MvPolynomial.eval₂_map]
    exact (MvPolynomial.map_eval₂Hom _ _ _ p).trans
      (congrArg (fun q => MvPolynomial.eval₂ q (fun j => (ψ.appLE _ _ (loc i).le).hom (r j)) p)
        (congrArg CommRingCat.Hom.hom w'))

end GlobalTheory
