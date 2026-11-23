import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFractionStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.SecRat

theorem isIntegral_of_isGenOver (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C) (hx : IsGenOver k x) : IsIntegral C := by
  have : SmoothOfRelativeDimension 1 (strHom k C) := hx.1.1
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have hred : IsReduced C := isReduced_of_smooth_of_isReduced (strHom k C)
  have hd : IsDominant x := hx.2.1.1
  have hden : DenseRange x.base := hd.denseRange
  have hcl : closure {x.base default} = (Set.univ : Set C) := by
    have hr : Set.range x.base = {x.base default} := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; rw [Subsingleton.elim p default]; rfl
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]; exact hden.closure_range
  have hirr : IsIrreducible (Set.univ : Set C) := hcl ▸ isIrreducible_singleton.closure
  have : IrreducibleSpace C := { isPreirreducible_univ := hirr.2, toNonempty := ⟨x.base default⟩ }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced C).2 ⟨this, hred⟩

theorem not_isUnit_evAt {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) (hf : b (IsLocalRing.closedPoint R) ∉ X.basicOpen f) :
    ¬ IsUnit (evAt b h f) := by
  intro hu
  apply hf
  have h1 : (b.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (.of R)).inv.hom (evAt b h f) := by
    simp [evAt]
  have h2 : (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) = ⊤ ⊓ (Sp R).basicOpen ((b.app U).hom f) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
  have h3 : IsLocalRing.closedPoint R ∈ (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) := by
    rw [h1, basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  rw [h2, ← Scheme.preimage_basicOpen] at h3
  exact h3.2

theorem evAt_coord {R : Type} [CommRing R] {C : Scheme.{0}} (x : Sp R ⟶ C) {W : C.Modules} {r m : ℕ}
    (σ : (lbPow (det W r) m).Sec) (c₀ c : Chart W r) (V' : C.Opens) (h₀ : V' ≤ c₀.U) (h₁ : V' ≤ c.U)
    (hx' : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V'))
    (hM : ∀ j, resM W h₀ (c₀.e j) = ∑ i, M i j • resM W h₁ (c.e i))
    (h0 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c₀)) (h1 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c)) :
    evAt x h1 (σ.f (fun _ => c)) = (M.map (evAt x hx')).det ^ m * evAt x h0 (σ.f (fun _ => c₀)) := by
  have hV : V' ≤ (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => h₁ hy, Set.mem_iInter.2 fun _ => h₀ hy⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ ((lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀)) :=
    hx'.trans (x.preimage_mono hV)
  have hcc : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c₀.U) := hx'.trans (x.preimage_mono (le_inf h₁ h₀))
  have e := congrArg (evAt x hxV) (σ.compat (fun _ => c) (fun _ => c₀))
  rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h1 hxV, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h0 hxV] at e
  rw [e]
  congr 1
  have hd : evAt x hcc (c.isFrame.detUnit c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right).val =
      (M.map (evAt x hx')).det := by
    rw [← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (le_inf h₁ h₀) hcc hx']
    have hr := IsFrame.res_detUnit c.isFrame c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right (le_inf h₁ h₀)
    refine (congrArg (evAt x hx') (congrArg Units.val hr)).trans ?_
    rw [IsFrame.val_detUnit, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, hM]
    simp only [← IsFrame.basis_apply c.isFrame h₁]
    rw [Module.Basis.repr_sum_self]
  rw [← hd, ← map_pow, ← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) ≤ c.U ⊓ c₀.U) hcc hxV]
  congr 1
  dsimp only [lbPow, LB.LinComb]
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  erw [map_pow]
  congr 1

theorem val_lt_one {k K : Type} [Field k] [Field K] [Algebra k K] (v : Place k K) (a : v.O) (ha : ¬ IsUnit a) :
    v.1 (a : K) < 1 := by
  have h1 : v.1 (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
  refine lt_of_le_of_ne h1 fun h => ha ?_
  have h0 : (a : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hi : (a : K)⁻¹ ∈ v.O := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem sec_eq_zero {X : Scheme.{0}} {L : LB X} (σ : L.Sec) (h : ∀ j, σ.f j = 0) : σ = 0 := by
  obtain ⟨f, hc⟩ := σ
  have : f = fun _ => 0 := funext h
  subst this
  rfl

end GlobalTheory.Nef.SecRat

open GlobalTheory.Nef.SecRat in

theorem GlobalTheory.Nef.sec_detPow_rational : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s hV₀ hs m σ hσ
  haveI := isIntegral_of_isGenOver k K C x hx
  let c₀ : Chart W r := ⟨V₀, s, hs⟩
  have hUeq : ∀ c : Chart W r, (((lbPow (det W r) m).U (fun _ => c) : C.Opens) : Set C) = c.U := fun c =>
    Set.ext fun y => ⟨fun hy => Set.mem_iInter.1 hy PUnit.unit, fun hy => Set.mem_iInter.2 fun _ => hy⟩
  have hle : ∀ c : Chart W r, c.U ≤ (lbPow (det W r) m).U (fun _ => c) := fun c y hy =>
    Set.mem_iInter.2 fun _ => hy
  obtain ⟨hx0, hinj0, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 ((lbPow (det W r) m).U fun _ => c₀)
    (by rw [hUeq]; exact hV₀)
  refine ⟨evAt x hx0 (σ.f fun _ => c₀), ?_, ?_⟩
  · intro hf
    apply hσ
    have h0 : σ.f (fun _ => c₀) = 0 := hinj0 (by rw [hf, map_zero])
    refine sec_eq_zero σ fun j => ?_
    have hj : j = fun _ => j PUnit.unit := funext fun _ => rfl
    rw [hj]
    generalize j PUnit.unit = c
    by_cases hne : (((lbPow (det W r) m).U fun _ => c : C.Opens) : Set C).Nonempty
    · have hne2 : ((((lbPow (det W r) m).U fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :
          C.Opens) : Set C).Nonempty :=
        nonempty_preirreducible_inter (Opens.isOpen _) (Opens.isOpen _) hne (by rw [hUeq]; exact hV₀)
      obtain ⟨hxj, hinjj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne
      obtain ⟨hx2, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne2
      apply hinjj
      have e := congrArg (evAt x hx2) (σ.compat (fun _ => c) (fun _ => c₀))
      rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hxj hx2, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hx0 hx2, h0,
        map_zero, mul_zero] at e
      rw [e, map_zero]
    · exact eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => hne ⟨y, C.basicOpen_le _ hy⟩)
  · rintro v g ⟨b, V, t, V', h₀, h₁, hx', M, hb, hbV, ht, hM, rfl⟩
    let c : Chart W r := ⟨V, t, ht⟩
    have hbj : ⊤ ≤ b ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hbV.trans (b.preimage_mono (hle c))
    have hxj : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hx'.trans (x.preimage_mono (h₁.trans (hle c)))
    have key := evAt_coord x σ c₀ c V' h₀ h₁ hx' M hM hx0 hxj
    have hval : v.1 (evAt x hx0 (σ.f fun _ => c₀) * (M.map (evAt x hx')).det ^ m) =
        v.1 ((evAt b hbj (σ.f fun _ => c) : v.O) : K) := by
      rw [mul_comm, ← key]
      congr 1
      subst hb
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 v.O K C v.O.subtype b _ hbj hxj _
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (Valuation.mem_valuationSubring_iff _ _).1 (evAt b hbj _).2
    · intro b' hb' hout
      have e : spMap (algebraMap K K) ≫ x = x := by
        rw [Algebra.algebraMap_self, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      obtain ⟨b₀, -, huniq⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
      have hbb : b' = b := (huniq b' (hb'.trans e.symm)).trans (huniq b (hb.trans e.symm)).symm
      subst hbb
      have hnu := not_isUnit_evAt b' hbj (σ.f fun _ => c) (fun hm => hout (Opens.mem_iSup.2 ⟨_, hm⟩))
      rw [hval]
      exact val_lt_one v _ hnu
