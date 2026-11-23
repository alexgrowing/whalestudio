import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordLocal

variable {R : Type} [CommRing R] [IsDomain R]

theorem jK_app_inj (W : (Spec (CommRingCat.of R)).Opens) : Function.Injective ((jK R).app W).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  exact (jK R).app_injective W

omit [IsDomain R] in
theorem toOpen_top_bijective : Function.Bijective (DegPre.toOpen (R := R) ⊤) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective

variable (D : DegPre R) (χ : D.X)

theorem generic_le (j : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hV hy

theorem exists_trans (j j' : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hj : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) (hj' : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j' PUnit.unit))
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (h' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j') :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ, res h ((D.psi χ).s j) = pullU (jK R) V u * res h' ((D.psi χ).s j') := by
  have l : V ≤ (D.c χ).left ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) := fun y hy => ⟨hj hy, hj' hy⟩
  refine ⟨(res l (pullU (D.c χ).left _ (D.P.L.g (j PUnit.unit) (j' PUnit.unit)))) ^ (-1 : ℤ), unit_ext fun y hy => ?_⟩
  have hy' : jK R y ∈ V := hy
  have t := gen_trans (D.psi_gen χ) (𝟙 (TK R).left) y (j := j) (j' := j') (h hy) (h' hy)
  refine (gm_res _ y h hy _).trans (t.trans (Eq.trans ?_ (map_mul _ _ _).symm))
  refine congrArg₂ (· * ·) (Eq.symm ?_) (gm_res _ y h' hy _).symm
  refine (gm_pull (𝟙 _) (jK R) y V hy' _).trans ?_
  rw [Category.id_comp]
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
  refine congrArg (· ^ (-1 : ℤ)) ((gm_res (jK R) y l hy' _).trans ?_)
  refine (gm_pull (jK R) (D.c χ).left y _ (l hy') _).trans ?_
  rw [Category.id_comp]; rfl

theorem psiUnitOn_zero (hB : D.TauBimult) : PsiUnitOn D 0 Set.univ := by
  intro j V hV _ hle h
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
  have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
    Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
  refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
    (Units.isUnit _).map _, fn_ext fun y hy => ?_⟩
  have hy' : jK R y ∈ V := hy
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 (h hy) k)
  have e := PsiZero.val_psi_zero hB hJ
  rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
  refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
    ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
  rw [Category.id_comp]
  refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
  exact congrArg Units.val ((map_inv _ _).trans e.symm)

variable {D χ}

theorem ne_zero_of_coord {r : R} (h : PsiCoord D χ r) : r ≠ 0 := by
  rintro rfl
  obtain ⟨j, -, h, e⟩ := h
  rw [map_zero, map_zero] at e
  have hu := ((D.psi χ).s j).isUnit.map ((TK R).left.presheaf.map (homOfLE h).op).hom
  rw [← e] at hu
  haveI : Nonempty (jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    ⟨⟨closedPoint (FractionRing R), trivial⟩⟩
  exact not_isUnit_zero hu

theorem exists_unit_of_coord {r r' : R} (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : ∃ u : Rˣ, r' = u * r := by
  obtain ⟨j, hj, h, e⟩ := h
  obtain ⟨j', hj', h', e'⟩ := h'
  obtain ⟨u, hu⟩ := exists_trans D χ j' j hj' hj h' h
  let φ := RingEquiv.ofBijective _ (toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, toOpen_top_bijective.1 (jK_app_inj ⊤ ?_)⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e, e']
  exact congrArg Units.val hu

theorem not_mem_of_coord {W : Set (Sp R)} {𝔭 : PrimeSpectrum R} (hW : IsOpen W) (hp : 𝔭 ∈ W) (hU : PsiUnitOn D χ W)
    {r : R} (h : PsiCoord D χ r) : r ∉ 𝔭.asIdeal := by
  obtain ⟨j, hj, h, e⟩ := h
  obtain ⟨V, hV, hpV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of R)) (x := 𝔭)
    (U := ⟨W, hW⟩) hp
  have h₂ : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := le_top.trans hj
  obtain ⟨s, hs, es⟩ := hU j V hV hle h₂ (generic_le D χ j h₂)
  have k : DegPre.toOpen (R := R) V r = s := by
    refine jK_app_inj V (Eq.trans ?_ es.symm)
    refine fn_ext fun y hy => ?_
    have hy' : jK R y ∈ V := hy
    have a := congrArg (gs (𝟙 _) y _) e
    have a₁ := gs_pull (𝟙 _) (jK R) y ⊤ trivial (DegPre.toOpen (R := R) ⊤ r)
    have a₂ := gs_res (𝟙 _) y h trivial ((D.psi χ).s j).val
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_ (gs_res (𝟙 _) y (generic_le D χ j h₂) hy _).symm)
    refine Eq.trans ?_ (a₁.symm.trans (a.trans a₂))
    rw [Category.id_comp]
    exact (gs_res (jK R) y le_top hy' _).trans (gs_res (jK R) y (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤) trivial _).symm
  rw [← k] at hs
  have b := (Spec (CommRingCat.of R)).basicOpen_of_isUnit hs
  have c : (Spec (CommRingCat.of R)).basicOpen (DegPre.toOpen (R := R) V r) =
      V ⊓ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    (Spec (CommRingCat.of R)).basicOpen_res _ _
  rw [b, basicOpen_eq_of_affine] at c
  exact (c.le hpV).2

theorem exists_chart_top [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    ∃ j : PUnit → D.P.L.ι, (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
  obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c χ).left (closedPoint R))
  exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff ((D.c χ).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)), IsIntegrallyClosed R → ∀ χ, (∃ r, PsiCoord Dg.toPre χ r ∧ r ≠ 0 ∧ (χ ≠ 0 → r ∈ maximalIdeal R) ∧ (χ = 0 → IsUnit r)) ∧ (∀ r r', PsiCoord Dg.toPre χ r → PsiCoord Dg.toPre χ r' → ∃ u : Rˣ, r' = u * r) ∧ ∀ (W : Set (Sp R)) (𝔭 : PrimeSpectrum R), IsOpen W → 𝔭 ∈ W → PsiUnitOn Dg.toPre χ W → ∀ r, PsiCoord Dg.toPre χ r → r ∉ 𝔭.asIdeal := by
  intro R _ _ _ _ Dg _ χ
  refine ⟨?_, fun _ _ => exists_unit_of_coord, fun _ _ hW hp hU _ => not_mem_of_coord hW hp hU⟩
  obtain ⟨j, hj⟩ := exists_chart_top Dg.toPre χ
  have h := generic_le Dg.toPre χ j hj
  by_cases hχ : χ = 0
  · subst hχ
    have hU := psiUnitOn_zero Dg.toPre Dg.tau_bimult
    obtain ⟨s, -, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj h
    obtain ⟨r, rfl⟩ := toOpen_top_bijective.2 s
    have hr : PsiCoord Dg.toPre 0 r := ⟨j, hj, h, e⟩
    exact ⟨r, hr, ne_zero_of_coord hr, fun h => absurd rfl h, fun _ =>
      IsLocalRing.notMem_maximalIdeal.1 (not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial hU hr)⟩
  · obtain ⟨s, hs, e⟩ := Dg.psi_pos χ hχ j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    have hr : PsiCoord Dg.toPre χ r := ⟨j, hj, h, e⟩
    exact ⟨r, hr, ne_zero_of_coord hr, fun _ => hm, fun h => absurd h hχ⟩

end GlobalTheory.PsiCoordLocal
