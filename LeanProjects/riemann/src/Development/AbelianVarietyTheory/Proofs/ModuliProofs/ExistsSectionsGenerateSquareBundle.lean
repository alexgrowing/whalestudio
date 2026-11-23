import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLiftStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

noncomputable section

namespace GlobalTheory.SquareGenerated

section
variable {X Y : Scheme.{0}} {H : LB X}

theorem unitAt_of_mem (s : LB.Sec H) (φ : Y ⟶ X) (y : Y) (hy : φ y ∈ Out.nonzeroLocus s) :
    UnitAt H (K := Fin 1) (fun _ => φ) (fun _ => 1) y := by
  have v : ∀ (j : Fin 1 → H.ι) (z : Y), z ∈ LB.wchart H (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z (LB.wchart H (fun _ : Fin 1 => φ) j)
        ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))) = gs (𝟙 Y ≫ φ) z (H.U (j 0)) (s.f (j 0)) := fun j z hz =>
    (gs_res _ z _ hz _).trans (gs_pull _ φ z _ (LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz) _)
  let s' : LB.Sec (LB.LinComb H (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            (congrArg Units.val (gm_linComb H _ _ (𝟙 Y) z j j' hz.1 hz.2)))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        have hm : (𝟙 Y ≫ φ) z ∈ H.U (j 0) ⊓ H.U (j' 0) :=
          ⟨LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz.1, LB.wchart_le H (fun _ : Fin 1 => φ) j' 0 hz.2⟩
        refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res _ z _ hm _))))
        rw [gs_unit _ z _ hm, Fin.prod_univ_one, zpow_one] }
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => k) ?_⟩
  have hm : y ∈ LB.wchart H (fun _ : Fin 1 => φ) (fun _ => k) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ hk
  show y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op).hom
          ((φ.app _).hom (s.f k)))
  have e := Y.basicOpen_res ((φ.app _).hom (s.f k))
    (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op
  refine e ▸ ⟨hm, ?_⟩
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f k)) y).1 hk

theorem exists_sec_pw (hH : H.IsLB) (t : ℤ) (y : X)
    (h : UnitAt H (K := Fin 1) (fun _ => 𝟙 X) (fun _ => t) y) :
    ∃ u : LB.Sec (pw H t), y ∈ Out.nonzeroLocus u := by
  obtain ⟨s, hs⟩ := h
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i z hz => Set.mem_iInter.2 fun _ => hz
  let u : LB.Sec (pw H t) :=
    { f := fun i => (X.presheaf.map (homOfLE (le i)).op).hom (s.f fun _ => i)
      compat := fun i j => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le i) hz.1 _)).trans
          (Eq.trans ?_ ((gs_mul (𝟙 X) z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 X) z _ hz _)
              ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le j) hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (le i hz.1) (le j hz.2)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
        exact (Fin.prod_univ_one _).trans (map_zpow _ _ _).symm }
  choose I hI using fun χ : X ⟶ X => exists_chart hH (χ y)
  have hm : y ∈ H.U (I (𝟙 X ≫ 𝟙 X)) := hI (𝟙 X ≫ 𝟙 X)
  refine ⟨u, TopologicalSpace.Opens.mem_iSup.2 ⟨I (𝟙 X ≫ 𝟙 X), (X.mem_basicOpen _ _ hm).2 ?_⟩⟩
  exact (congrArg IsUnit ((gs_eq (𝟙 X) y _ hm _).symm.trans (gs_res (𝟙 X) y (le _) hm _))).mpr (hs I hI)

end

theorem exists_sec_sq {O : Type} [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    {H : LB A.left} (hH : H.IsLB) (hT : Triv (Theta A H)) (s : LB.Sec H) (a : 𝟙_ (Over (Sp O)) ⟶ A)
    (y : A.left) (h₁ : ((toUnit A ≫ a) * 𝟙 A).left y ∈ Out.nonzeroLocus s)
    (h₂ : ((toUnit A ≫ a⁻¹) * 𝟙 A).left y ∈ Out.nonzeroLocus s) :
    ∃ u : LB.Sec (pw H 2), y ∈ Out.nonzeroLocus u := by
  obtain ⟨t, ht⟩ := hT
  let χ : Fin 4 → (Sp O ⟶ A.left) := ![(a * a⁻¹).left, a.left, (a⁻¹).left, (1 : 𝟙_ (Over (Sp O)) ⟶ A).left]
  choose i hi using fun k => exists_chart hH (χ k (IsLocalRing.closedPoint O))
  have e : ∀ k, (![((toUnit A ≫ a) * (toUnit A ≫ a⁻¹)).left, (toUnit A ≫ a).left,
      (toUnit A ≫ a⁻¹).left, (1 : A ⟶ A).left] k) = (toUnit A).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (toUnit A ≫ (a * a⁻¹)).left
      rw [MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (toUnit A ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := GlobalTheory.AbSquare.exists_gen_square hH t ht (toUnit A ≫ a) (toUnit A ≫ a⁻¹) (𝟙 A) i
    (fun k z => by
      rw [e k]
      have h : χ k ⁻¹ᵁ H.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
      show (toUnit A).left z ∈ χ k ⁻¹ᵁ H.U (i k)
      rw [h]; trivial)
  have hu' : UnitAt H _ _ y := ⟨genSec u hu, fun J hJ => by
    rw [sval_genSec u hu _ y hJ]; exact Units.isUnit _⟩
  have e1 : (toUnit A ≫ a) * (toUnit A ≫ a⁻¹) * 𝟙 A = 𝟙 A := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
  refine exists_sec_pw hH 2 y (UnitAt.congr hH (formEq_of_add fun U _ hh => ?_)
    (((unitAt_of_mem s _ y h₁).mul (unitAt_of_mem s _ y h₂)).mul hu'))
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, e1, Sum.elim_inl, Sum.elim_inr]
  simp
  module

theorem exists_secs_sq_generate : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro O K _ _ _ _ _ _ _ A _ _ hA H hH hT s hs
  obtain ⟨-, hk, hlift⟩ := GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift O K
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let t : Sp (IsLocalRing.ResidueField O) ⟶ Sp O := spMap (IsLocalRing.residue O)
  let T : Over (Sp O) := Over.mk t
  have : IsIntegral (T ⊗ A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.hom).flip
  let p : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint (IsLocalRing.ResidueField O)
  have htp : t p = IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have up : ∀ x : A.left, A.hom x = IsLocalRing.closedPoint O → ∃ z : (T ⊗ A).left, (snd T A).left z = x := by
    intro x hx
    have : x ∈ Set.range (pullback.snd t A.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨p, htp.trans hx.symm⟩
    exact this
  let W : A.left.Opens := ⨆ u : LB.Sec (pw H 2), Out.nonzeroLocus u
  have hW : W = ⊤ := by
    by_contra hne
    have hZ : ((W : Set A.left)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (SetLike.coe_injective h)
    have hc : IsClosed (A.hom '' (W : Set A.left)ᶜ) := A.hom.isClosedMap _ W.isOpen.isClosed_compl
    obtain ⟨x₀, hx₀, hx₁⟩ : IsLocalRing.closedPoint O ∈ A.hom '' (W : Set A.left)ᶜ := by
      obtain ⟨q, hq⟩ := hZ.image A.hom
      exact (IsLocalRing.specializes_closedPoint q).mem_closed hc hq
    obtain ⟨z₀, hz₀⟩ := up x₀ hx₁
    have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left :=
      inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
    have : JacobsonSpace (T ⊗ A).left :=
      LocallyOfFiniteType.jacobsonSpace (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left
    obtain ⟨c, hcZ, hcc⟩ := nonempty_inter_closedPoints
      (Z := (((snd T A).left ⁻¹ᵁ W : (T ⊗ A).left.Opens) : Set (T ⊗ A).left)ᶜ)
      ⟨z₀, by
        show ¬ (snd T A).left z₀ ∈ W
        rw [hz₀]; exact hx₀⟩ ((snd T A).left ⁻¹ᵁ W).isOpen.isClosed_compl.isLocallyClosed
    let σ := pointOfClosedPoint (X := (T ⊗ A).left) (K := IsLocalRing.ResidueField O) (fst T A).left c hcc
    have hσ : σ ≫ (fst T A).left = 𝟙 _ := pointOfClosedPoint_comp _ c hcc
    have hσp : σ p = c := pointOfClosedPoint_apply _ c hcc p
    let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
      rw [← Over.w (fst T A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
    let x : T ⟶ A := σ' ≫ snd T A
    have hx : x.left p ∉ W := by
      show (snd T A).left (σ p) ∉ W
      rw [hσp]; exact hcZ
    obtain ⟨y₀, hy₀, hy₁⟩ := hs
    obtain ⟨z₁, hz₁⟩ := up y₀ hy₁
    obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t ((snd T A).left ⁻¹ᵁ Out.nonzeroLocus s)
      ⟨z₁, by
        show (snd T A).left z₁ ∈ Out.nonzeroLocus s
        rw [hz₁]; exact hy₀⟩ x x
    obtain ⟨b, hb, hba⟩ := hlift A.left A.hom inferInstance a.left (Over.w a)
    let b' : 𝟙_ (Over (Sp O)) ⟶ A := Over.homMk b hb
    have hb' : toUnit T ≫ b' = a := Over.OverMorphism.ext hba
    have key : ∀ (d : 𝟙_ (Over (Sp O)) ⟶ A), (Out.ptSecT A ((toUnit T ≫ d) * x)).left p ∈
        (snd T A).left ⁻¹ᵁ Out.nonzeroLocus s →
        ((toUnit A ≫ d) * 𝟙 A).left (x.left p) ∈ Out.nonzeroLocus s := by
      intro d hd
      have e : x ≫ ((toUnit A ≫ d) * 𝟙 A) = Out.ptSecT A ((toUnit T ≫ d) * x) ≫ snd T A := by
        simp [Out.ptSecT, MonObj.comp_mul]
      have e' : ((toUnit A ≫ d) * 𝟙 A).left (x.left p) =
          (snd T A).left ((Out.ptSecT A ((toUnit T ≫ d) * x)).left p) :=
        congrArg (fun q => q.left p) e
      rw [e']; exact hd
    obtain ⟨u, hu⟩ := exists_sec_sq A hH hT s b' (x.left p) (key b' (by rw [hb']; exact h₁ p))
      (key b'⁻¹ (by rw [GrpObj.comp_inv, hb']; exact h₂ p))
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨u, hu⟩)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec (pw H 2) => (Out.nonzeroLocus u : Set A.left)) (fun u => (Out.nonzeroLocus u).isOpen)
    (fun y _ => by
      have : y ∈ W := by rw [hW]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i : LB.Sec (pw H 2))), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end GlobalTheory.SquareGenerated
