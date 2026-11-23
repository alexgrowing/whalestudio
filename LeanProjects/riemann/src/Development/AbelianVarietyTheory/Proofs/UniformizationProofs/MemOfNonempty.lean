import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.IotaInj

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) : (jFK (R := R) F ≫ jK R) y ∈ V := by
  have h : IsDominant (jFK (R := R) F ≫ jK R) := GC.isDominant_jFR (V := R) F
  obtain ⟨y', hy'⟩ := (jFK (R := R) F ≫ jK R).denseRange.exists_mem_open V.isOpen ⟨p, hp⟩
  have : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rwa [Subsingleton.elim y y']

theorem eq_zero_of_gs (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) (a : Γ(Spec (CommRingCat.of R), V))
    (h : gs (jFK (R := R) F ≫ jK R) y V a = 0) : a = 0 := by
  by_contra ha
  have : Nonempty V := ⟨⟨p, hp⟩⟩
  have hne : (Spec (CommRingCat.of R)).basicOpen a ≠ ⊥ := fun e => ha ((basicOpen_eq_bot_iff a).1 e)
  obtain ⟨p', hp'⟩ : ∃ p', p' ∈ (Spec (CommRingCat.of R)).basicOpen a := by
    by_contra hc
    exact hne (eq_bot_iff.2 fun z hz => (hc ⟨z, hz⟩).elim)
  have hm : y ∈ (jFK (R := R) F ≫ jK R) ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen a := mem_of_nonempty y hp'
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ y (mem_of_nonempty y hp)] at hm
  rw [gs_eq _ y V (mem_of_nonempty y hp)] at h
  exact hm.ne_zero h

theorem not_isUnit_germ {I : Ideal R} {V : (Spec (CommRingCat.of R)).Opens} {p : Spec (CommRingCat.of R)} (hp : p ∈ V)
    (hI : I ≤ p.asIdeal) {r : Γ(Spec (CommRingCat.of R), V)} (hr : r ∈ I.map (DegPre.toOpen V)) :
    ¬ IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom r) := by
  have key : I.map (DegPre.toOpen V) ≤ (maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).comap
      ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have e : ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a) =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
      TopCat.Presheaf.germ_res_apply _ _ p hp _
    have hu' : IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a)) := hu
    rw [e] at hu'
    have hm := (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (U := ⊤) _ p trivial).2 hu'
    rw [show (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = _ from
      basicOpen_eq_of_affine (R := CommRingCat.of R) a] at hm
    exact hm (hI ha)
  exact key hr

theorem exists_val_psi (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by
  have hx : D.xK χ = jK R ≫ eSec D.P.A := by
    rw [← hc]; simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j) := fun x hxV =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact hle hxV
  obtain ⟨r, hr, hψ⟩ := hχ (fun _ => j) V hV (by rw [hc]; exact hle) le'
  refine ⟨r, hr, ?_⟩
  have e := val_of (D.psi χ) (jFK (R := R) F) y J (fun _ => j) (fun _ => by
    rw [← hj]; exact congrArg J ((congrArg (jFK (R := R) F ≫ ·) hx).trans (Category.assoc _ _ _).symm))
  refine (congrArg Units.val e).trans ?_
  refine (gs_unit _ y _ (le' hy) _).symm.trans ((gs_res _ y le' hy _).symm.trans ?_)
  exact (congrArg (gs (jFK (R := R) F) y _) hψ.symm).trans (gs_pull _ (jK R) y V hy _)

theorem val_tau (D : DegPre R) (a b : D.X) {y : Spec (CommRingCat.of F)} {J} (hJ : Good D.P.L y J) :
    val (D.tau a b) (jFK (R := R) F) y J = val (D.psi (a + b)) (jFK (R := R) F) y J *
      (val (D.psi a) (jFK (R := R) F) y J)⁻¹ * (val (D.psi b) (jFK (R := R) F) y J)⁻¹ *
      (val D.rigK (jFK (R := R) F) y J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem c_left_eq (D : DegPre R) {χ : D.X} (h : cP D (TF (R := R) F) χ = 1) : (D.c χ).left = eSec D.P.A :=
  GC.vpt_ext F D.P (Over.w (D.c χ)) (Over.w η[D.P.A]) (congrArg CommaMorphism.left h)

attribute [local instance] gtGroup

theorem eq_zero_of_iota {I : Ideal R} (hI : I ≠ ⊤) (D : DegData R I) (z : D.toPre.X)
    (h : iota D.tau_bimult F z = 0) : z = 0 := by
  by_contra hz
  have hL := D.toPre.P.isLB
  have c₁ : (D.toPre.c z).left = eSec D.toPre.P.A := c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, h, zero_b])
  have c₂ : (D.toPre.c (-z)).left = eSec D.toPre.P.A :=
    c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, map_neg, h, neg_zero, zero_b])
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  let p : Spec (CommRingCat.of R) := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  obtain ⟨j, hj⟩ := exists_chart hL (eSec D.toPre.P.A p)
  obtain ⟨V, hV, hp, hle⟩ : ∃ V : (Spec (CommRingCat.of R)).Opens, IsAffineOpen V ∧ p ∈ V ∧
      V ≤ eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hp, hle⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ ((eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j : (Spec (CommRingCat.of R)).Opens) : Set _) from hj)
      (eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j).isOpen
    exact ⟨V, hV, hp, hle⟩
  let y : Spec (CommRingCat.of F) := (⊥ : PrimeSpectrum F)
  have hy := mem_of_nonempty (R := R) y hp
  obtain ⟨J, hJ, hJj⟩ := exists_good D.toPre.P.L hL y (K := PUnit)
    (fun _ => (jFK (R := R) F ≫ jK R) ≫ eSec D.toPre.P.A) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hle hy)
  obtain ⟨r, hr, e₁⟩ := exists_val_psi D.toPre (D.psi_pos z hz) c₁ j hV hle y hy J (hJj PUnit.unit)
  obtain ⟨r', -, e₂⟩ := exists_val_psi D.toPre (D.psi_pos (-z) (neg_ne_zero.2 hz)) c₂ j hV hle y hy J (hJj PUnit.unit)
  have τ : ∀ χ, val (D.toPre.tau z χ) (jFK (R := R) F) y J = 1 := fun χ => by
    have e := iota_val (F := F) D.tau_bimult z χ (y := y) hJ
    rw [h, zero_val χ hJ] at e
    exact e.symm
  have hle' : V ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => j) := fun x hx =>
    Set.mem_iInter.2 fun _ => hle hx
  obtain ⟨u, e₃⟩ : ∃ u : Γ(Spec (CommRingCat.of R), V),
      (val D.toPre.rigK (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V u := by
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.toPre.rig.s (fun _ => j)).val, ?_⟩
    have a₁ : val D.toPre.rigK (jFK (R := R) F) y J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig (jFK (R := R) F ≫ jK R) y J := val_pull hJ _ _ _
    rw [a₁, val_of _ _ y J (fun _ => j) (fun _ => hJj PUnit.unit)]
    exact (gs_unit _ y _ (hle' hy) _).symm.trans (gs_res _ y hle' hy _).symm
  have t₀ := τ 0
  have t₁ := τ (-z)
  rw [val_tau _ _ _ hJ, add_zero] at t₀
  rw [val_tau _ _ _ hJ, add_neg_cancel] at t₁
  have t : val (D.toPre.psi z) (jFK (R := R) F) y J * (val (D.toPre.psi (-z)) (jFK (R := R) F) y J *
      (val D.toPre.rigK (jFK (R := R) F) y J * val D.toPre.rigK (jFK (R := R) F) y J)) = 1 := by
    have a₀ := congrArg Additive.ofMul t₀
    have a₁ := congrArg Additive.ofMul t₁
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₀ a₁ ⊢
    linear_combination (norm := abel) -a₀ - a₁
  have t' := congrArg Units.val t
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e₁, e₂, e₃, ← gs_mul _ y V hy, ← gs_mul _ y V hy, ← gs_mul _ y V hy,
    Units.val_one] at t'
  have one : r * (r' * (u * u)) - 1 = 0 := eq_zero_of_gs y hp _ (by
    rw [gs_eq _ y V hy] at t' ⊢
    rw [map_sub, map_sub, map_one, map_one, t', sub_self])
  exact not_isUnit_germ hp hIm hr ((IsUnit.of_mul_eq_one _ (sub_eq_zero.1 one)).map _)

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (y y' : D.toPre.X) (g : GtPtF D.toPre F), GtPtF.IsIota y g → GtPtF.IsIota y' g → y = y' := by
  intro _ R _ _ _ I hA D F _ _ _ y y' g h h'
  have hI : I ≠ ⊤ := by
    rintro rfl
    have := hA.2.2.2
    exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) inferInstance)
  rw [isIota_iff_eq D.tau_bimult] at h h'
  exact sub_eq_zero.1 (eq_zero_of_iota (F := F) hI D _ (by rw [map_sub, ← h, ← h', sub_self]))

end GlobalTheory.IotaInj

end
