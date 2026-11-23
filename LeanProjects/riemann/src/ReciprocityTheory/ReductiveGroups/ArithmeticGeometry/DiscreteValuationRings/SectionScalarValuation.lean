import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section Gen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem gs_sum (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  rw [gs_eq f z U h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (gs_eq f z U h (a i)).symm

theorem secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = sval s₁ r z J := by
  have hj : ∀ k, (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) : K₁ ⊕ K₂ → L.ι) k =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) k) := by
    intro k; cases k <;> rfl
  have hcoh : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := fun k₁ k₂ hk => by
    rw [hj, hj, hk]
  have H' := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) hcoh
  have hm1 : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) :=
    show r.base z ∈ (⋂ k, ((φ₁ k).base ⁻¹' (L.U (J (r ≫ φ₁ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ φ₁ k)
  have hm2 : r z ∈ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    show r.base z ∈ (⋂ k, ((h ≫ φ₂ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ₂ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ₂ k)
  have hm : r z ∈ (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) := ⟨hm1, hm2⟩
  have hle2 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) := inf_le_right.trans (wchart_comp_le φ₂ h (fun k => J (r ≫ h ≫ φ₂ k)))
  have hle1 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) := inf_le_left
  have l1 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ((Y'.presheaf.map (homOfLE hle2).op).hom ((h.app _).hom (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))))) =
      gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))) :=
    (gs_res r z hle2 hm _).trans (gs_pull r h z _ (hle2 hm) _)
  have l2 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) (resTop (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) 1 * (Y'.presheaf.map (homOfLE hle1).op).hom (s₁.f (fun k => J (r ≫ φ₁ k)))) =
      gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k))) := by
    simp only [resTop, map_one]
    rw [_root_.one_mul]
    exact gs_res r z hle1 hm _
  have key := congrArg (gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)))) H'
  have e : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ h ≫ φ₂ k)) := by
    funext k; rw [Category.assoc]
  show gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)))
      (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k))) = gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k)))
  rw [e]
  exact l1.symm.trans (key.trans l2)

theorem secScal_of_sval (hL : L.IsLB) {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J → sval s₂ (𝟙 Y' ≫ h) y J = sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1 := by
  intro j₁ j₂ hc
  simp only [resTop, map_one, _root_.one_mul]
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
  have := H y J hJ
  rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
    sval_of s₂ _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
  have le : LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact ((gs_res _ y _ hy _).trans (gs_pull _ h y _ (le hy.2) _)).trans (this.trans (gs_res _ y _ hy _).symm)

theorem sval_lin {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ j : K → L.ι, s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (b i) * sval (t i) r z J := by
  have hmem : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((φ k).base ⁻¹' (L.U (J (r ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  show gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k))) = _
  rw [hs, gs_sum r z _ hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hmem]
  congr 1
  exact gs_res r z le_top hmem (b i)

theorem sval_pullSec {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  have hmem : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((h ≫ φ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  calc sval (pullSec L φ ε s h) r z J
      = gs r z (LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)))
          ((Y'.presheaf.map (homOfLE (wchart_comp_le φ h (fun k => J (r ≫ h ≫ φ k)))).op).hom
            ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k))))) := rfl
    _ = gs r z (h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
          ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k)))) :=
        gs_res r z (wchart_comp_le φ h _) hmem _
    _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (s.f (fun k => J (r ≫ h ≫ φ k))) :=
        gs_pull r h z _ (wchart_comp_le φ h _ hmem) _
    _ = sval s (r ≫ h) z J := by
        have e : (fun k => J ((r ≫ h) ≫ φ k)) = fun k => J (r ≫ h ≫ φ k) := by
          funext k; rw [Category.assoc]
        show _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)))
          (s.f (fun k => J ((r ≫ h) ≫ φ k)))
        rw [e]

end Gen

section Move

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem gs_gF_comp {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hf : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    (y : (DegPre.BF D.toPre F).left) (ζ : F) :
    gs h y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  calc gs h y ⊤ (gF D.toPre F ζ)
      = gs (h ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
        gs_pull h (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _
    _ = gs (𝟙 _ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by rw [hf, Category.id_comp]
    _ = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) :=
        (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _).symm

theorem vge_move {k : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k) δ)
      (D.toPre.famφB χ) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : D.toPre.SecB k χ, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval t ρ z J = sval (σ i) (ρ ≫ TB) z J * (val eB ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) TB eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heB ρ z hJ)⟩
  choose σ' hσ' using e1
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e2 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e2
  refine ⟨n, fun i => c * a i, σ', σ'F, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F i _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm ((r : ℚ) : WithTop ℚ)]
    exact add_le_add hq (hva i)
  · show s'.f j = ∑ i, resTop _ (gF D.toPre F (c * a i)) * (σ'F i).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have m := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' m
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have Ti : ∀ i, gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * (gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I) := fun i => by
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F i) (𝟙 _) y hy' m, hτ]
      exact mul_left_comm _ _ _
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ i, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Ti i
    have CORE : sval s' (𝟙 _) y I = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
      have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
      rw [H1, H2, hc y I hIy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
        rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
      have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I := by
        rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hh, Category.id_comp]
      have A3 : sval (σ'F i) (𝟙 _) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I *
          (val eB (DegPre.prB D.toPre F).left y I).val := by
        rw [hσ'F i _ (𝟙 _) y I hIy, Category.id_comp, hσ' i _ _ y I hIy]
      rw [A1, A2, A3, map_mul, gs_mul _ y ⊤ (by trivial)]
      ring
    exact T0.trans ((congrArg (fun x => τ * x) CORE).trans RHS.symm)

end Move

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
