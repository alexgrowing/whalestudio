import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterNumRedCloPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyHomog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegFlLamAPowVdmCl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open scoped Matrix

namespace GlobalTheory.FlagDetDeg

variable {ι : Type} [Fintype ι] {m : ι → ℕ}

def detPoly (m : ι → ℕ) : MvPolynomial (EntIx m) ℤ :=
  ∏ τ, (Matrix.of fun i j : Fin (m τ) => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)).det

theorem aeval_detPoly {R : Type} [CommRing R] (a : EntIx m → R) :
    aeval a (detPoly m) = ∏ τ, (Matrix.of fun i j : Fin (m τ) => a ⟨τ, (i, j)⟩).det := by
  rw [detPoly, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp

theorem evEnt_detPoly {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (Matrix.of fun _ _ : Fin 1 => detPoly m) A = Matrix.of fun _ _ => ∏ τ, (A τ).det := by
  ext i j
  exact aeval_detPoly _

@[reducible] def detRep (m : ι → ℕ) : PolyRep m where
  M := 1
  ent := Matrix.of fun _ _ => detPoly m
  one R _ := by
    rw [evEnt_detPoly]; ext i j; rw [Subsingleton.elim i j]; simp
  mul R _ A B := by
    simp only [evEnt_detPoly]; ext i j; simp [Matrix.mul_apply, Finset.prod_mul_distrib]
  transp R _ A := by
    simp only [evEnt_detPoly]; ext i j; simp

theorem coeff_aeval_line {σ R : Type} [Fintype σ] [CommRing R] (a b : σ → R) (P : MvPolynomial σ ℤ) :
    (aeval (fun v => Polynomial.C (a v) + Polynomial.X * Polynomial.C (b v)) P).coeff 0 = aeval a P ∧
    (aeval (fun v => Polynomial.C (a v) + Polynomial.X * Polynomial.C (b v)) P).coeff 1 =
      ∑ v, aeval a (pderiv v P) * b v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [aeval_C, aeval_C, Polynomial.algebraMap_apply]
    simp [Polynomial.coeff_C, -eq_intCast, -map_intCast, -algebraMap_int_eq]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp.1, hp.2, hq.1, hq.2, add_mul, Finset.sum_add_distrib, and_self]
  | mul_X p s hp =>
    refine ⟨by rw [map_mul, Polynomial.mul_coeff_zero, hp.1]; simp, ?_⟩
    rw [map_mul, aeval_X, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_C, hp.2, ← mul_assoc,
      Polynomial.coeff_mul_C, Polynomial.coeff_mul_X, hp.1]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul, pderiv_X]
    congr 1
    · exact Finset.sum_congr rfl fun v _ => by ring
    · rw [Finset.sum_eq_single s (fun v _ hv => by simp [Pi.single_eq_of_ne' hv]) (by simp)]
      simp

theorem lie_detRep {R : Type} [CommRing R] (A : Mat m R) (i j : Fin 1) :
    (detRep m).lie A i j = ∑ τ, (A τ).trace := by
  classical
  have h := (coeff_aeval_line (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (fun w => A w.1 w.2.1 w.2.2)
    (detPoly m)).2
  refine h.symm.trans ((congrArg (Polynomial.coeff · 1) (aeval_detPoly _)).trans ?_)
  have e (τ : ι) : (Matrix.of fun i j : Fin (m τ) => Polynomial.C ((1 : Mat m R) τ i j) +
      Polynomial.X * Polynomial.C (A τ i j)) = 1 + (Polynomial.X : Polynomial R) • (A τ).map Polynomial.C := by
    ext1 i j
    simp [Matrix.one_apply, apply_ite]
  refine (congrArg (Polynomial.coeff · 1) (Finset.prod_congr rfl fun τ _ => congrArg Matrix.det (e τ))).trans ?_
  have h0 (τ : ι) : (1 + (Polynomial.X : Polynomial R) • (A τ).map Polynomial.C).det.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det, map_add, map_one]
    refine (congrArg Matrix.det ?_).trans Matrix.det_one
    ext i j
    simp
  have key (s : Finset ι) : (∏ τ ∈ s, (1 + (Polynomial.X : Polynomial R) • (A τ).map Polynomial.C).det).coeff 0 = 1 ∧
      (∏ τ ∈ s, (1 + (Polynomial.X : Polynomial R) • (A τ).map Polynomial.C).det).coeff 1 = ∑ τ ∈ s, (A τ).trace := by
    induction s using Finset.induction_on with
    | empty => simp [Polynomial.coeff_one]
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ, Polynomial.mul_coeff_zero, h0, ih.1, Polynomial.coeff_mul,
        Finset.Nat.antidiagonal_succ]
      simp [h0, ih.1, ih.2, Matrix.coeff_det_one_add_X_smul_one, add_comm]
  exact (key Finset.univ).2

theorem interPoly_sum_pow_fibrePoint (hG : GlobalTheory.Published.GoodChernNumbers) {F : Type} [Field F] (σ : F →+* ℂ) {B Y : Var F}
    {E : Fr (ratOf B) m 0} {E' : Fr (ratOf Y) m m} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X} {gr : Root m → Y.Dv}
    (hf : Refines E E' φ f) (hg : IsGraded E' gr) (Δ : B.Dv) (u : B.Fnˣ)
    (hΔ : ∀ z, ∀ A ∈ E.S z, Δ.GeneratesAt z (u * ∏ τ, (A τ).det)) :
    Y.interPoly gr ((∑ x, X x) ^ B.dim * fibrePoint m) = B.inter fun _ => Δ := by
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety F σ B ι m E
  obtain ⟨L, hL, hLH⟩ := GlobalTheory.T.exists_polyRep_inducedBundle_and_metric F B ι m (detRep m) E
  obtain ⟨H', hH', hHH⟩ := hLH σ ⊤ H hH
  have hev (A : Mat m B.Fn) : (detRep m).ev A = Matrix.of fun _ _ => ∏ τ, (A τ).det := evEnt_detPoly A
  have hgr : IsGraded (lineFlag (ι := Unit) L) fun _ => Δ := by
    refine ⟨fun _ => Matrix.of fun _ _ => ((u⁻¹ : B.Fnˣ) : B.Fn), ?_, fun y x => ?_⟩
    · obtain ⟨A, hA⟩ := L.nonempty (genericPoint B.X)
      have hO (g : B.Fn) : g ∈ ((ratOf B).O (genericPoint B.X)).toSubring := (ratOf B).O_genericPoint.ge trivial
      refine (Fr.mem_iff hA).2 fun τ => ⟨fun _ _ => hO _, ?_, hO _, fun i j hi => absurd hi (by simp)⟩
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero ((Matrix.det_unique (n := Fin 1) _).trans_ne (u⁻¹).ne_zero) (inv_ne_zero (Fr.det_ne hA τ))
    · obtain ⟨A, hA⟩ := E.nonempty y
      have h0 := (hΔ y A hA).ne_zero
      refine ⟨_, hL y A hA, (Units.mk0 _ h0)⁻¹, ?_, CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using hΔ y A hA)⟩
      obtain ⟨⟨⟩, i⟩ := x
      rw [hev]
      rw [Subsingleton.elim i 0]
      simp [Matrix.mul_apply, Matrix.inv_def, mul_comm]
  have h₁ := hG F σ B B Unit _ L (lineFlag (ι := Unit) L) _ _ _ (refines_lineFlag _) hgr ⊤ H' hH'
    (fun y hy => absurd mem_ptsIn_top hy) (X ((), 1) ^ B.dim)
  have e₁ : chernRoots (fun _ : Unit => 1) (X ((), 1) ^ B.dim) * fibrePoint _ = ∏ _i : Fin B.dim, X ⟨(), 0⟩ := by
    simp [chernRoots, fibrePoint, esymm_one]
  erw [e₁, Var.interPoly_prod] at h₁
  have h₂ := hG F σ B Y ι m E E' φ f gr hf hg ⊤ H hH (fun y hy => absurd mem_ptsIn_top hy) ((∑ τ, X (τ, 1)) ^ B.dim)
  have e₂ : chernRoots m ((∑ τ, X (τ, 1)) ^ B.dim) = (∑ x, X x) ^ B.dim := by
    simp [chernRoots, esymm_one, Fintype.sum_sigma]
  rw [e₂] at h₂
  have h₃ := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ B ι m E ⊤ H ((∑ τ, X (τ, 1)) ^ B.dim) Unit (fun _ => (detRep m).M) (fun _ => L) (fun _ => H')
    (X ((), 1) ^ B.dim) (fun _ => 1) (fun _ => _) hH (fun _ => hH') (fun y hy c hc => ?_) fun _ => h₁
  · exact (GlobalTheory.Proportionality.hasChernIntegral_unique h₂ h₃).trans (by rw [Fintype.sum_unique, one_mul]; rfl)
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  refine ⟨A, hA, fun _ _ => (detRep m).ev A, fun _ => hL _ A hA, ?_⟩
  have hc := curvPoly_polyRep (detRep m) hH hHH hy hA c.holo hc
  simp only [chernTop, chernPoly, map_pow, map_sum, aeval_X, Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg,
    neg_neg, hc, Fintype.sum_unique, one_mul]
  rw [show Matrix.trace ((detRep m).lie _) = _ from (Matrix.trace_fin_one _).trans (lie_detRep _ 0 0)]

end GlobalTheory.FlagDetDeg

end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeDegSum

section Geo

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec GlobalTheory.ProjVar

theorem topSelf_eq_finrank_mul {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  have hχ (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
    have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
      refine ⟨fun a b x => ?_⟩
      change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
        cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
      rw [Algebra.smul_def, map_mul, map_mul, hk]
      rfl
    have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
      rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
      push_cast
      ring
    rw [chi_def, chi_def]
    simp_rw [e]
    exact (mul_finsum _ _).symm
  rw [topSelf_def, topSelf_def, interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hχ]
  ring

theorem degAt_eq_finrank_mul {k : Type} [CommRing k] {Z B : Scheme.{0}} (s : Z ⟶ Sp k)
    [IsProper (s ≫ spMap (Int.castRingHom k))] (b : B ⟶ Z) [IsClosedImmersion b] [IsIntegral B] {F : Type} [Field F]
    [NumberField F] (V : Var F) (w : V.X ⟶ Z) [IsPreimmersion w] (hg : b (genericPoint B) = w (genericPoint V.X))
    {L : LB Z} (hL : L.IsLB) {L' : LB B} (hL' : L'.IsLB) (e : LBIso L' (L.pull b)) (n : ℕ) :
    degAt (b ≫ s) L' (genericPoint B) n = (Module.finrank ℚ F : ℤ) * topSelfIntersection F (L.pull w) n := by
  have : IsProper ((b ≫ s) ≫ spMap (Int.castRingHom k)) := by rw [Category.assoc]; infer_instance
  let v : V.X ⟶ ratFibre s := (ratFibre.isPullback s).lift w (V.str ≫ spMap (algebraMap ℚ F)) (specZIsTerminal.hom_ext _ _)
  have hv₁ : v ≫ ratFibre.fst s = w := IsPullback.lift_fst _ _ _ _
  have hv₂ : v ≫ ratFibre.snd s = V.str ≫ spMap (algebraMap ℚ F) := IsPullback.lift_snd _ _ _ _
  have : IsProper (ratFibre.snd s) := MorphismProperty.of_isPullback (P := @IsProper) (ratFibre.isPullback s) ‹_›
  have : IsFinite (spMap (algebraMap ℚ F)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have : IsProper (v ≫ ratFibre.snd s) := by rw [hv₂]; infer_instance
  have : IsProper v := IsProper.of_comp v (ratFibre.snd s)
  have : IsPreimmersion (v ≫ ratFibre.fst s) := by rw [hv₁]; infer_instance
  have : IsPreimmersion (ratFibre.fst s) := MorphismProperty.of_isPullback (ratFibre.isPullback s).flip
    (IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ))
  have : IsPreimmersion v := IsPreimmersion.of_comp v (ratFibre.fst s)
  have : IsClosedImmersion v := IsClosedImmersion.of_isPreimmersion v v.isClosedMap.isClosed_range
  have : IsClosedImmersion (ratFibre.map s b) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ratFibre.isPullback_map s b) inferInstance
  obtain ⟨y, hy₁, hy₂⟩ := Scheme.exists_preimage_of_isPullback (ratFibre.isPullback_map s b) (genericPoint B)
    (v (genericPoint V.X)) (by rw [hg, ← hv₁]; rfl)
  letI : Algebra ℚ Γ(V.X, ⊤) := algebraΓOfHom (V.str ≫ spMap (algebraMap ℚ F))
  have hF := pull_isLB hL (ratFibre.fst s)
  rw [← topSelf_eq_finrank_mul ℚ F (fun a => RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ Γ(V.X, ⊤))
    ((algebraMap F Γ(V.X, ⊤)).comp (algebraMap ℚ F))) a), ← hy₁, DegRec.degAt_fst _ hL']
  have h₁ := DegRec.interNumRed_clo_pull _ (appTop_algebraΓOfHom _ _ (ratFibre.map_snd s b)) y
    (L := fun _ : Fin n => L.pull (ratFibre.fst s)) fun _ => hF
  rw [hy₂, InterModel.interNumRed_eq_interNumOn _ v _ (DegRec.range_eq_closure v),
    interNumOn_const_eq_topSelf (appTop_algebraΓOfHom _ _ hv₂) hF] at h₁
  refine Eq.trans ?_ (h₁.symm.trans ?_)
  · refine interNum_congr_cls (ι := Fin n) ℚ _ (fun _ => pull_isLB hL' _) (fun _ => pull_isLB hF _) fun _ => ?_
    rw [cls_pull hL', cls_pull hF, cls_pull hL, (cls_eq_iff hL' (pull_isLB hL b)).2 e, cls_pull hL, ← pull_comp, ← pull_comp,
      ratFibre.map_fst]
  · refine interNum_congr_cls (ι := Fin n) ℚ _ (fun _ => pull_isLB hF _) (fun _ => pull_isLB hL _) fun _ => ?_
    rw [cls_pull hF, cls_pull hL, cls_pull hL, ← pull_comp, hv₁]

end Geo

section Tied

open CategoryTheory AlgebraicGeometry NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.FlagBundle
open GlobalTheory.FlagMod (ev detChg)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {V : Var F} {j : V.X ⟶ gen Z}

theorem exists_div_detOm (hL : (FlagMod.detOm Z).IsLB) {f₀ : EigFrame Z (constF e V) (genericPt V ≫ j ≫ genι Z)}
    {S : Fr (ratOf V) Dw.mult 0} {A₀ : Mat Dw.mult V.Fn} (hT : Tied e V j f₀ S A₀) :
    ∃ (Δ : V.Dv) (u : V.Fnˣ), toPic Δ = CechPic.cls _ (pull_isLB hL (j ≫ genι Z)) ∧
      ∀ z, ∀ A ∈ S.S z, (-Δ).GeneratesAt z (u * ∏ τ, (A τ).det) := by
  classical
  have hle {y : V.X} {J : ((FlagMod.detOm Z).pull (j ≫ genι Z)).ι} (hy : y ∈ ((FlagMod.detOm Z).pull (j ≫ genι Z)).U J) :
      ⊤ ≤ (stalkPt V y ≫ j ≫ genι Z) ⁻¹ᵁ (J PUnit.unit).U := top_le_stalk_preimage y _ (mem_pull.1 hy)
  let r (J : ((FlagMod.detOm Z).pull (j ≫ genι Z)).ι) : V.X.functionFieldˣ :=
    if h : genericPoint V.X ∈ ((FlagMod.detOm Z).pull (j ≫ genι Z)).U J then
      ((isUnit_frameDet (J PUnit.unit) (hle h) f₀).unit)⁻¹ else 1
  have hr {J} (h : genericPoint V.X ∈ ((FlagMod.detOm Z).pull (j ≫ genι Z)).U J) :
      (r J : V.X.functionField) = (frameDet (J PUnit.unit) (hle h) f₀)⁻¹ := by
    simp only [r]
    rw [dif_pos h, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  have hrat : IsRatSec ((FlagMod.detOm Z).pull (j ≫ genι Z)) r := fun J J' hg => by
    have hh := GlobalTheory.FlagMod.le_preimage_inf (hle hg.1) (hle hg.2)
    have e₁ : fnOf _ hg (((FlagMod.detOm Z).pull (j ≫ genι Z)).g J J' : Γ(V.X, _)) =
        (ev (genericPt V ≫ j ≫ genι Z) _ hh (detChg (J PUnit.unit) (J' PUnit.unit)).val)⁻¹ := by
      show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
      rw [Fintype.prod_unique]
      erw [zpow_one, LB.val_res, fnOf_resG]
      have hg' : genericPoint V.X ∈ (j ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U) :=
        ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
      refine (fnOf_app_eq_ev (j ≫ genι Z) hg' hh _).trans ?_
      exact map_units_inv (ev (genericPt V ≫ j ≫ genι Z) _ hh).toMonoidHom _
    rw [hr hg.1, hr hg.2, e₁, ← ev_detChg_mul_frameDet (J PUnit.unit) (J' PUnit.unit) (hle hg.1) (hle hg.2) hh f₀, mul_inv]
    rfl
  have hP := presents_divOfRatSec (pull_isLB hL _) hrat
  have h₀ : (∏ τ, (A₀ τ).det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => Fr.det_ne hT.1 τ
  refine ⟨_, (Units.mk0 _ h₀)⁻¹, hP.toPic_eq, fun (y : V.X) A hA => ?_⟩
  obtain ⟨J, hy⟩ := exists_mem_chart hP.isLB y
  obtain ⟨φy, fy, hco⟩ := hT.2 y A hA
  obtain ⟨fy', hmap⟩ := fy.exists_isMap (algebraMap (V.X.presheaf.stalk y) V.X.functionField) hco.2.1 hco.1
  have e1 := frameDet_isMap _ hco.1.symm (J PUnit.unit) (hle hy) (hle (gen_mem hy)) fy fy' hmap
  have e2 := frameDet_change (J PUnit.unit) (hle (gen_mem hy)) fy' f₀
  have e3 (τ) : (fy'.co f₀ τ).det = (A₀ τ).det * (A τ).det⁻¹ := by
    rw [EigFrame.co_eq (T := ((A₀ * A⁻¹) τ)ᵀ) fun i => by rw [funext (hmap τ)]; exact hco.2.2 τ i, det_transpose,
      Pi.mul_apply, det_mul, Pi.inv_apply, det_nonsing_inv, Ring.inverse_eq_inv']
  have hA0 : (∏ τ, (A τ).det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => Fr.det_ne hA τ
  rw [(hP.isEqn J y hy).neg.generatesAt_iff, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr (gen_mem hy), inv_inv,
    Units.val_mk0]
  have e5 : ∏ τ, (fy'.co f₀ τ).det = (∏ τ, (A₀ τ).det) * (∏ τ, (A τ).det)⁻¹ := by
    simp only [e3, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have e4 (a b x : V.Fn) (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ * b * (x * (a * b⁻¹)) = x := by field_simp
  exact ⟨_, isUnit_frameDet (J PUnit.unit) (hle hy) fy,
    ((congrArg (_ * ·) (e2.trans (congrArg₂ (· * ·) e1 e5))).trans (e4 _ _ _ h₀ hA0)).symm⟩

end Tied

end GlobalTheory.HodgeDegSum

end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeDegSum

section Comb

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.CovTestDR GlobalTheory.VdmFibre GlobalTheory.ProjVar

theorem interPoly_aeval {F : Type} [Field F] (Y : Var F) {κ κ' : Type} [Fintype κ'] (Δ : κ' → Y.Dv) (a : κ → κ' → ℤ)
    {P : MvPolynomial κ ℝ} (hP : P.IsHomogeneous Y.dim) :
    Y.interPoly (fun x => ∑ l, a x l • Δ l) P = Y.interPoly Δ (aeval (fun x => ∑ l, C (a x l : ℝ) * X l) P) := by
  classical
  rw [P.as_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hl : d.toMultiset.toList.length = Y.dim := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hP (mem_support_iff.1 hd)]
    simp [Finsupp.weight_apply]
    rfl
  have e : (monomial d (P.coeff d) : MvPolynomial κ ℝ) =
      P.coeff d • ∏ i : Fin Y.dim, X (d.toMultiset.toList.get (i.cast hl.symm)) := by
    rw [monomial_eq, ← C_mul']
    congr 1
    rw [Fin.prod_congr' (fun i => (X (d.toMultiset.toList.get i) : MvPolynomial κ ℝ)) hl.symm]
    simp [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index, pow_add]
  rw [e, map_smul, map_smul, map_smul, Var.interPoly_prod, map_prod]
  simp only [aeval_X]
  rw [Var.interPoly_prod_sum]
  rfl

def revPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (if (x.2 : ℕ) < j then -X x else X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else x.2 - j)

theorem degFl_revPt (ι : Type) [Fintype ι] [DecidableEq ι] {N j : ℕ} (h : j ≤ N) (k : ℕ) :
    degFl ι N (lamA ι N j ^ k * revPt ι N j) = degFl ι N (lamA ι N j ^ k * fibPt ι N j) := by
  let w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j)) := fun _ => (1, Fin.revPerm)
  let s : ℝ := ∏ _τ : ι, (-1) ^ ∑ b : Fin (N - j), (b : ℕ)
  have e : rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (revPt ι N j) = C s * fibPt ι N j := by
    rw [fibPt_blocks h, revPt, Fintype.prod_prod_type, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type, map_mul, mul_left_comm, map_prod, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [blockEquiv_inl, blockPerm_inl, w]
    · rw [← sum_rev_val, ← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
      refine Fintype.prod_equiv Fin.revPerm _ _ fun b => ?_
      have hb : N - j - 1 - (N - j - (b + 1)) = b := by have := b.2; omega
      simp [blockEquiv_inr, blockPerm_inr, w, hb, ← mul_pow]
  have h₁ := degFl_rename_fibre (fun τ => blockPerm h (w τ)) (lamA ι N j ^ k * revPt ι N j)
  rw [map_mul, map_pow, rename_lamA h w, e, mul_left_comm, PPowSum.degFl_C_mul] at h₁
  have hs : (∏ τ, ((Equiv.Perm.sign (blockPerm h (w τ)) : ℤ) : ℝ)) = s :=
    Finset.prod_congr rfl fun τ _ => by rw [sign_blockPerm, Equiv.Perm.sign_one, one_mul]; exact sign_revPerm_cast _
  rw [hs] at h₁
  exact (mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun _ _ => by positivity) h₁).symm

theorem isHomogeneous_revPt (ι : Type) [Fintype ι] {N j : ℕ} (h : j ≤ N) :
    (lamA ι N j ^ dimGr ι N j * revPt ι N j).IsHomogeneous (dimFl ι N) := by
  have h₁ : (lamA ι N j).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => (IsHomogeneous.sum _ _ _ fun i _ => by simpa using isHomogeneous_X ℝ _).sub
      (IsHomogeneous.sum _ _ _ fun i _ => by simpa using isHomogeneous_X ℝ _)
  have h₂ : (revPt ι N j).IsHomogeneous (∑ x : ι × Fin N, if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else x.2 - j) :=
    IsHomogeneous.prod _ _ _ fun x _ => by
      have : (if (x.2 : ℕ) < j then -X x else X x : Pol ι N).IsHomogeneous 1 := by
        split_ifs
        exacts [(isHomogeneous_X ℝ x).neg, isHomogeneous_X ℝ x]
      simpa only [one_mul] using this.pow _
  convert (h₁.pow _).mul h₂
  rw [Fintype.sum_prod_type, one_mul, dimGr, dimFl]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← mul_add, ← (blockEquiv h).sum_comp, Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, Fin.is_lt, if_true, add_lt_iff_neg_left, not_lt_zero, if_false,
    Nat.add_sub_cancel_left, sum_rev_val]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  have g (n : ℕ) : ∑ i : Fin n, (i : ℕ) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id, Nat.choose_two_right]
  rw [g, g, Nat.add_sub_cancel_left, ← Nat.choose_two_right, Nat.add_choose_eq]
  congr 1
  simp [Finset.Nat.antidiagonal_succ]
  ring

end Comb

section Main

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.Toroidal GlobalTheory.RootSum

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

theorem exists_base (s : FinalTheorems S κ) (L : CmList A) (Φ : s.Flag) (k : s.Comp) :
    ∃ (V : Var D.what₂.LL) (i : V.X ⟶ gen s.T.Z) (f : (Φ.C k).Y.X ⟶ V.X)
      (f₀ : EigFrame s.T.Z (constF κ.e V) (genericPt V ≫ i ≫ genι s.T.Z)) (Eb : Fr (ratOf V) S.Dw.mult 0)
      (A₀ : Mat S.Dw.mult V.Fn) (E' : Fr (ratOf (Φ.C k).Y) S.Dw.mult S.Dw.mult) (φ : V.Fn →ₐ[D.what₂.LL] (Φ.C k).Y.Fn),
      LieBase.IsLieBase κ.e (Φ.C k) V i f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧
        IsGraded E' (fun x : Root S.Dw.mult => (Φ.C k).gr x.1 x.2) ∧ V.dim = dimGr D.what₂.Tau N j := by
  have hU := s.isUnf
  have hσ := κ.good_σ₀
  obtain ⟨Dw, rfl, rfl, h2, Xo, sys⟩ := S
  obtain ⟨V, i, f, f₀, Eb, A₀, E', φ, hi, hB, hR, hG⟩ :=
    LieBase.exists_base_of_flagCpt _ _ _ _ _ _ _ _ _ s.T _ κ.e κ.σ₀ (s.U κ.σ₀) hσ hU Φ k
  refine ⟨V, i, f, f₀, Eb, A₀, E', φ, hB, hR, hG, ?_⟩
  rw [← BaseDim.card_eq_dim _ _ _ _ _ _ _ _ _ s.T _ κ.e κ.σ₀ (s.U κ.σ₀) hσ hU Φ k V i f f₀ Eb A₀ hi hB, dimGr,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_congr (TrueCx.cmEquiv _ hU L.ψ k)]

theorem aeval_root (S : Sig A N j) :
    aeval (fun x : DV.Rt D.what₂.Tau N => ∑ l, C (rootExp S x l : ℝ) * (X l : MvPolynomial (Letter S.Dw) ℝ))
        (lamA D.what₂.Tau N j) = -∑ l, X l ∧
      aeval (fun x : DV.Rt D.what₂.Tau N => ∑ l, C (rootExp S x l : ℝ) * (X l : MvPolynomial (Letter S.Dw) ℝ))
        (revPt D.what₂.Tau N j) = fibrePoint S.Dw.mult := by
  have e (x : DV.Rt D.what₂.Tau N) : ∑ l, C (rootExp S x l : ℝ) * (X l : MvPolynomial (Letter S.Dw) ℝ) =
      if (x.2 : ℕ) < j then X (rootLetter S x) else -X (rootLetter S x) := by
    rw [Finset.sum_eq_single (rootLetter S x) (fun l _ hl => by simp [rootExp_eq, hl]) (by simp), rootExp_eq, if_pos rfl,
      S.p_eq]
    split_ifs <;> simp
  constructor
  · rw [← (rootLetter_bijective S).sum_comp, ← Finset.sum_neg_distrib, Fintype.sum_prod_type, lamA, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [pHigh, pLow, map_sub, map_sum, pow_one, aeval_X, Finset.sum_filter, apply_ite, map_zero, e,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < j
    · simp [hi, hi.not_ge]
    · simp [hi, not_lt.1 hi]
  · rw [revPt, fibrePoint, ← (rootLetter_bijective S).prod_comp, map_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    have hk := rootLetter_key S x
    have hp := S.p_eq
    have hr := S.rank_eq
    have hx := x.2.2
    rw [map_pow]
    by_cases hi : (x.2 : ℕ) < j
    · rw [if_pos (by omega), Prod.mk.injEq] at hk
      rw [if_pos hi, if_pos hi, map_neg, aeval_X, e, if_pos hi, hk.2, hk.1, mult_tau, hp]
    · rw [if_neg (by omega), Prod.mk.injEq] at hk
      rw [if_neg hi, if_neg hi, aeval_X, e, if_neg hi, hk.2, hk.1, mult_conj_tau]
      congr 1
      omega

theorem deg_eq (hG : GoodChernNumbers) {O : Setup D} {c : O.s.Comp} (M : DRBase O c) :
    (M.deg (genericPoint M.B) (dimGr D.what₂.Tau O.N O.j) : ℝ) = (Module.finrank ℚ D.what₂.LL : ℝ) *
      (O.var c).interPoly (fun x : DV.Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x))
        (lamA D.what₂.Tau O.N O.j ^ dimGr D.what₂.Tau O.N O.j * revPt D.what₂.Tau O.N O.j) := by
  obtain ⟨V, i, f, f₀, Eb, A₀, E', φ, ⟨hi, hf, hT⟩, hR, hgr, hd⟩ := exists_base O.s O.L O.Φ c
  have hL := O.s.isRec.isLB_detOm
  obtain ⟨Δ, u, hΔ, hu⟩ := exists_div_detOm hL hT
  have hV := (M.h 2).isVB
  have : IsProper O.s.T.Z.s := projProper _ _ _ O.s.T.Z.proj
  have : IsFinite (spMap (Int.castRingHom (𝓞 O.κ.c.F))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have h₁ : IsPreimmersion (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 O.κ.c.F) (S := O.κ.c.F) (nonZeroDivisors _)
  have : IsPreimmersion (genι O.s.T.Z) := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip h₁
  have hg : f (genericPoint (O.Φ.C c).Y.X) = genericPoint V.X := by
    have e := congrArg (fun g => g (IsLocalRing.closedPoint (O.Φ.C c).Y.Fn)) hR.hom
    exact ((congrArg f ((ratOf (O.Φ.C c).Y).pt_apply _).symm).trans e).trans ((ratOf V).pt_apply _)
  have h₂ := degAt_eq_finrank_mul O.s.T.Z.s M.b V (i ≫ genι O.s.T.Z) (by rw [M.gen, ← hf, ← hg]; rfl) hL (M.lam 2).isLB
    ((CechPic.cls_eq_iff (M.lam 2).isLB (pull_isLB hL _)).1 (by
      rw [CechPic.cls_pull hL, (CechPic.cls_eq_iff hL hV.isLB_det).2 (HodgeCech.lbIso_detOm_det _ hL hV),
        ← CechPic.cls_pull hV.isLB_det M.b (pull_isLB hV.isLB_det _)]
      exact ((CechPic.cls_eq_iff _ (M.lam 2).isLB).2 (hV.lbIso_det_pullback M.b)).symm)) V.dim
  have h₃ : V.inter (fun _ => Δ) = topSelfIntersection D.what₂.LL ((FlagMod.detOm O.s.T.Z).pull (i ≫ genι O.s.T.Z)) V.dim :=
    Var.inter_eq_of_toPic_eq (fun _ => pull_isLB hL _) fun _ => hΔ
  have h₄ := FlagDetDeg.interPoly_sum_pow_fibrePoint hG D.what₂.embLL hR hgr (-Δ) u hu
  have h₅ : V.inter (fun _ => -Δ) = (-1) ^ V.dim * V.inter fun _ => Δ := by
    simpa using V.inter_zsmul (fun _ => -1) fun _ => Δ
  have h₆ := interPoly_aeval (O.var c) (fun l : Letter O.S.Dw => (O.Φ.C c).gr l.1 l.2) (rootExp O.S)
    ((O.dim_eq c).symm ▸ isHomogeneous_revPt D.what₂.Tau O.indef.2.le)
  rw [map_mul (aeval _), map_pow (aeval _), (aeval_root O.S).1, (aeval_root O.S).2, ← hd, neg_pow, mul_assoc,
    show ((-1 : MvPolynomial (Letter O.S.Dw) ℝ) ^ V.dim) = C ((-1) ^ V.dim) by simp, C_mul', map_smul] at h₆
  rw [← hd]
  refine (congrArg Int.cast h₂).trans ?_
  rw [← h₃, Int.cast_mul, Int.cast_natCast]
  refine congrArg _ (Eq.trans ?_ (h₆.trans (congrArg _ h₄)).symm)
  rw [h₅, smul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  simp

theorem main : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ M : ∀ c, DRBase O c, ∑ c, ((M c).deg (genericPoint (M c).B) (dimGr D.what₂.Tau O.N O.j) : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ) = O.Y.chern (lamA D.what₂.Tau O.Y.N O.Y.j ^ dimGr D.what₂.Tau O.Y.N O.Y.j * vdmCl D.what₂.Tau O.Y.N O.Y.j) := by
  intro _ hP _ _ D O _ _ _ _ _ _ M
  have h0 : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp only [deg_eq hP.p16.1, mul_div_cancel_left₀ _ h0]
  rw [CompChern.chern_eq_sum hP D O _ (isHomogeneous_revPt _ O.indef.2.le)]
  show O.Y.vol * Formalism.L2.Geo.degFlL D.what₂.Tau O.N _ = O.Y.vol * Formalism.L2.Geo.degFlL D.what₂.Tau O.N
    (lamA D.what₂.Tau O.N O.j ^ dimGr D.what₂.Tau O.N O.j * vdmCl D.what₂.Tau O.N O.j)
  erw [Formalism.L2.Geo.degFlL_apply, Formalism.L2.Geo.degFlL_apply]
  rw [degFl_revPt _ O.indef.2.le, VdmFibre.degFl_lamA_pow_vdmCl _ _ _ _ O.indef.2.le]

end Main

end GlobalTheory.HodgeDegSum

end
