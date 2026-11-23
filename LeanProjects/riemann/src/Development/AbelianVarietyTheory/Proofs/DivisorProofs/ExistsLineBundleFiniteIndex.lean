import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.Mean4O.RootLine

section General

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]

theorem unitAt_of_pow {x : X} (hx : IsIntegrallyClosed (X.presheaf.stalk x)) {n : ℕ} (hn : 0 < n)
    {f : X.functionField} (h : UnitAt x (f ^ n)) : UnitAt x f := by
  have h0 : f ≠ 0 := fun e => h.ne_zero (by rw [e, zero_pow hn.ne'])
  refine (unitAt_iff h0).2 ⟨regAt_of_pow hx hn h.regAt, regAt_of_pow hx hn ?_⟩
  rw [inv_pow]
  exact h.inv.regAt

theorem unitAt_fnMap (j : Z ⟶ X) (hη : j (genericPoint Z) ⤳ genericPoint X) {z : Z} {t : X.functionField}
    (h : UnitAt (j z) t) : UnitAt z (fnMap j hη t) := by
  rw [unitAt_iff ((map_ne_zero _).2 h.ne_zero), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of j hη h.regAt, ProjSpace.regAt_fnMap_of j hη h.inv.regAt⟩

theorem unitAt_of_fnMap (j : Z ⟶ X) [IsPreimmersion j] (hη : j (genericPoint Z) ⤳ genericPoint X) {z : Z}
    {t : X.functionField} (h : UnitAt z (fnMap j hη t)) : UnitAt (j z) t := by
  have h0 : t ≠ 0 := (map_ne_zero _).1 h.ne_zero
  refine (unitAt_iff h0).2 ⟨(regAt_fnMap_iff j hη).1 h.regAt, (regAt_fnMap_iff j hη).1 ?_⟩
  rw [map_inv₀]
  exact h.inv.regAt

theorem unitAt_of_pow_of_preimmersion (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (j : Z ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Z) ⤳ genericPoint X) {n : ℕ} (hn : 0 < n) {z : Z} {f : Z.functionField}
    (h : UnitAt z (f ^ n)) : UnitAt z f := by
  obtain ⟨t, rfl⟩ := fnMap_surjective j hη f
  rw [← map_pow] at h
  exact unitAt_fnMap j hη (unitAt_of_pow (hX _).2 hn (unitAt_of_fnMap j hη h))

theorem fnOf_pull_g (B : LB X) (j : Z ⟶ X) (hη : j (genericPoint Z) ⤳ genericPoint X) (i i' : (B.pull j).ι)
    (h : genericPoint Z ∈ (B.pull j).U i ⊓ (B.pull j).U i')
    (h' : genericPoint X ∈ B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :
    fnOf _ h ((B.pull j).g i i').val = fnMap j hη (fnOf _ h' (B.g (i PUnit.unit) (i' PUnit.unit)).val) := by
  rw [InducedPull.val_pull_g B j i i' (InducedPull.inf_le B j i i')]
  exact ProjSpace.fnOf_appLE j hη _ h' h _

theorem exists_lb (j : Z ⟶ X) (hη : j (genericPoint Z) ⤳ genericPoint X) {ι : Type} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (G : ι → X.functionField) (g : ι → Z.functionFieldˣ) (hg : ∀ i, fnMap j hη (G i) = g i)
    (h : ∀ i i', ∀ x ∈ U i ⊓ U i', UnitAt x (G i / G i')) :
    ∃ a : ∀ i i', Γ(X, U i ⊓ U i')ˣ, (LB.mk ι U a).IsLB ∧
      IsRatSec ((LB.mk ι U a).pull j) fun i => g (i PUnit.unit) := by
  choose a ha using fun i i' => exists_unit_fnOf_eq (h i i')
  have h0 (i) : G i ≠ 0 := fun e => (g i).ne_zero (by rw [← hg, e, map_zero])
  refine ⟨a, ⟨hU, fun i => Units.ext (Cartier.fn_ext fun h => ?_), fun i j k => Units.ext (Cartier.fn_ext fun h => ?_)⟩,
    fun i i' hi => ?_⟩
  · rw [LB.val_res, fnOf_resG]
    refine (ha _ _ _).trans ?_
    rw [div_self (h0 _), Units.val_one, map_one]
  · simp only [Units.val_mul, map_mul, LB.val_res, fnOf_resG, ha]
    exact div_mul_div_cancel₀ (h0 _)
  · have h' : genericPoint X ∈ U (i PUnit.unit) ⊓ U (i' PUnit.unit) :=
      gen_mem (x := j (genericPoint Z)) (InducedPull.inf_le (LB.mk ι U a) j i i' hi)
    rw [fnOf_pull_g (LB.mk ι U a) j hη i i' hi h']
    refine Eq.trans ?_ (congrArg (fun t => fnMap j hη t * _) (ha _ _ h')).symm
    rw [map_div₀, hg, hg, div_mul_cancel₀ _ (Units.ne_zero _)]

end General

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h : Flat (spMap (algebraMap (𝓞 F) F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors (𝓞 F))))
  have : Flat V.j := MorphismProperty.of_isPullback (P := @Flat) V.pb.flip h
  obtain ⟨y, -, hy⟩ := Flat.generalizingMap V.j (genericPoint_specializes (V.j (genericPoint V.G)))
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem isPreimmersion_j (V : Cover Y) : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h

theorem exists_root : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : LB M.X) (m : ℕ), 0 < m → LineNorm.Add.GivenBy A.D (eqn A.D) A.lg M L m → ∃ S : Finset Y.Fn, ∀ (V : Cover Y) (ρ : V.X ⟶ M.X), V.j ≫ ρ = V.π ≫ M.j → (∀ a ∈ S, ∃ g : V.G.functionField, g ^ m = V.φ a) → ∃ B : LB V.X, B.IsLB ∧ ∃ r, V.FinInd A B r := by
  classical
  intro F _ _ C Y A M L m hm ⟨r, hL, hr, hfin⟩
  have := M.ar.isNoetherian
  have := M.ar.isIntegral
  have hcov : (Set.univ : Set M.X) ⊆ ⋃ i, (L.U i : Set M.X) := fun x _ =>
    have ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.U i : Set M.X)) (fun i => (L.U i).isOpen) hcov
  refine ⟨T.image fun i => (r fun _ => i : Y.Fn), fun V ρ hρ hS => ?_⟩
  obtain ⟨hπ, hφ⟩ := V.φ_eq_fnMap
  have hj := j_gen_specializes V
  have hM := SmallSec.j_gen_specializes M
  have := isPreimmersion_j V
  have hpt (x : V.G) : ρ (V.j x) = M.j (V.π x) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f : V.G ⟶ M.X => f x) hρ).trans
      (Scheme.Hom.comp_apply _ _ _))
  have hρη : ρ (genericPoint V.X) ⤳ genericPoint M.X := by
    refine ((genericPoint_specializes (V.j (genericPoint V.G))).map ρ.continuous).trans ?_
    rw [hpt]
    exact (hπ.map M.j.continuous).trans hM
  have hcomp (t : M.X.functionField) : fnMap V.j hj (fnMap ρ hρη t) = V.φ (fnMap M.j hM t) := by
    rw [hφ, ← ProjSpace.fnMap_comp V.j ρ hj hρη (ProjSpace.comp_genericPoint_specializes _ _ hj hρη),
      ← ProjSpace.fnMap_comp V.π M.j hπ hM (ProjSpace.comp_genericPoint_specializes _ _ hπ hM)]
    exact ProjSpace.fnMap_congr hρ _ _ t
  choose g₀ hg₀ using fun i : T => hS _ (Finset.mem_image_of_mem _ i.2)
  have h0 (i : T) : g₀ i ≠ 0 := fun e =>
    (map_ne_zero V.φ).2 (Units.ne_zero _) ((hg₀ i).symm.trans (by rw [e, zero_pow hm.ne']))
  choose G hG using fun i => fnMap_surjective V.j hj (g₀ i)
  obtain ⟨a, hB, hrat⟩ := exists_lb V.j hj (fun i : T => ρ ⁻¹ᵁ L.U i) (eq_top_iff.2 fun x _ => by
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (ρ x)))
      exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hx⟩) G (fun i => Units.mk0 (g₀ i) (h0 i)) hG (fun i i' x hx => by
      have hx' : ρ x ∈ L.U i ⊓ L.U i' := hx
      have h' := gen_mem hx'
      have h'' : genericPoint Y.X ∈ (L.pull M.j).U (fun _ => i) ⊓ (L.pull M.j).U fun _ => i' :=
        ⟨Set.mem_iInter.2 fun _ => hM.mem_open (L.U i).isOpen h'.1,
          Set.mem_iInter.2 fun _ => hM.mem_open (L.U i').isOpen h'.2⟩
      refine unitAt_of_pow (V.normal x).2 hm ?_
      have e : (G i / G i') ^ m = fnMap ρ hρη (fnOf _ h' (L.g i i').val) := by
        apply (fnMap V.j hj).injective
        rw [hcomp, ← fnOf_pull_g L M.j hM (fun _ => i) (fun _ => i') h'' h', map_pow, map_div₀, hG, hG, div_pow,
          hg₀, hg₀, ← map_div₀, hr.isRatSec _ _ h'', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      rw [e]
      exact unitAt_fnMap ρ hρη (unitAt_fnOf hx' _ _))
  have hpow (i : T) (y : Y.X) : (V.φ (genAt A.D y) * g₀ i) ^ m =
      V.φ (((eqn A.D y)⁻¹ ^ m * r (fun _ => i) : Y.Fnˣ) : Y.Fn) := by
    rw [mul_pow, hg₀, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have hu (i : T) (x : V.G) (hx : ρ (V.j x) ∈ L.U i) :
      UnitAt (V.π x) (((eqn A.D (V.π x))⁻¹ ^ m * r (fun _ => i) : Y.Fnˣ) : Y.Fn) := by
    rw [hpt] at hx
    have := ((Base.isEqn_eqn A.D (V.π x)).nsmul m).iff_unitAt.1
      (hr.isEqn (fun _ => i) (V.π x) (Set.mem_iInter.2 fun _ => hx))
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  have hu' (i : T) (x : V.G) (hx : ρ (V.j x) ∈ L.U i) : UnitAt x (V.φ (genAt A.D (V.π x)) * g₀ i) := by
    refine unitAt_of_pow_of_preimmersion V.normal V.j hj hm ?_
    rw [hpow, hφ]
    exact unitAt_fnMap V.π hπ (hu i x hx)
  refine ⟨_, hB, _, hrat, fun i x hx => hu' _ x (Set.mem_iInter.1 hx PUnit.unit), fun v e y z yt i e₁ e₂ hi => ?_⟩
  have H := hfin v e y (yt ≫ ρ) (fun _ => (i PUnit.unit).1)
    (by rw [← Category.assoc, e₂, Category.assoc, hρ, ← Category.assoc, e₁]) hi
  have hmem : ρ (V.j (below z)) ∈ L.U (i PUnit.unit).1 := by
    have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ ρ ⁻¹ᵁ L.U (i PUnit.unit).1 := by
      rw [← e₂]
      exact hi (Set.mem_univ _)
    exact h1
  have hb : V.π (below z) = below y.1 := by
    rw [← e₁]
    rfl
  have k₁ := hu _ _ hmem
  have k₂ := hu' _ _ hmem
  have k₃ := valAt_fnMap V.π hπ z k₁.regAt
  rw [← hφ, ← hpow, valAt_pow k₂.regAt, e₁, hb] at k₃
  rw [← k₃, map_pow, Real.log_pow] at H
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne') H

end GlobalTheory.Mean4O.RootLine
