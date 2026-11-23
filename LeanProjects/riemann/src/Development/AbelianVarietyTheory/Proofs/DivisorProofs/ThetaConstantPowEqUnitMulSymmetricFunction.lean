import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveUStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScaleThetaConstantsAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegRev

theorem isIntegralElem_of_forall {V K : Type} [CommRing V] [Field K] (i : V →+* K) {x : K}
    (h : ∀ W : ValuationSubring K, (∀ v, i v ∈ W) → x ∈ W) : i.IsIntegralElem x := by
  letI : Algebra V K := i.toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : x ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hxW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hxW (h W fun v => hW ((integralClosure V K).algebraMap_mem v))
  exact h1

theorem scale_of_prim {V K : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (N N' k : ℕ) {J : Type} (c : Fin N → K) (c' : Fin N' → K) (a : K)
    (e : Fin N → FractionRing V) (th : J → FractionRing V) (i : J) (ha : a ≠ 0) (hk : 1 ≤ k)
    (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a))
    (hP' : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a))
    (he : ∀ j, io (e j) = symTup c j) (hth1 : ∀ x, ∃ b, c' x ^ k = io (th b) ^ k)
    (hth2 : ∀ b, ∃ x, c' x ^ k = io (th b) ^ k) (hi : th i ≠ 0)
    (hdiv : ∀ b, th b / th i ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j / th i ^ N.factorial) ∧
      ∃ j, IsUnit (e' j) := by
  have hk0 : k ≠ 0 := by omega
  have hti : io (th i) ≠ 0 := (map_ne_zero io).2 hi
  have hW' : ∀ W : ValuationSubring K, (∀ v, (io.comp (algebraMap V (FractionRing V))) v ∈ W) →
      io (th i) / a ∈ W ∧ a / io (th i) ∈ W := by
    intro W hW
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hth2 i
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
      obtain ⟨b₁, hb1⟩ := hth1 x₀
      have hc0 : c' x₀ ≠ 0 := fun h => hx0 (by simp [h])
      have hb10 : io (th b₁) ≠ 0 := by
        intro h0
        apply hc0
        have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
        exact (pow_eq_zero_iff hk0).1 h2
      have h1 : a / io (th b₁) ∈ W := by
        refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
        have e0 : (a / io (th b₁)) ^ k = ((c' x₀ / a)⁻¹) ^ k := by
          rw [inv_div, div_pow, div_pow, hb1]
        rw [e0]
        exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
      have h2 : io (th b₁) / io (th i) ∈ W := by
        obtain ⟨v, hv⟩ := hdiv b₁
        have h3 := hW v
        rwa [RingHom.comp_apply, hv, map_div₀] at h3
      have e1 : a / io (th i) = a / io (th b₁) * (io (th b₁) / io (th i)) := by
        field_simp
      rw [e1]
      exact mul_mem h1 h2
  have hPt : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / io (th i)) := by
    refine ⟨fun b => isIntegralElem_of_forall _ fun W hW => ?_, ?_⟩
    · have e1 : c b / io (th i) = c b / a * (a / io (th i)) := by field_simp
      show c b / io (th i) ∈ W
      rw [e1]
      exact mul_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP.1 b)) (hW' W hW).2
    · obtain ⟨b₀, hb0, hb0i⟩ := hP.2
      have hc0 : c b₀ ≠ 0 := fun h => hb0 (by simp [h])
      refine ⟨b₀, div_ne_zero hc0 hti, isIntegralElem_of_forall _ fun W hW => ?_⟩
      have e1 : (c b₀ / io (th i))⁻¹ = io (th i) / a * (c b₀ / a)⁻¹ := by field_simp
      show (c b₀ / io (th i))⁻¹ ∈ W
      rw [e1]
      exact mul_mem (hW' W hW).1 (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hb0i)
  have hsym : ∀ j, io (e j / th i ^ N.factorial) = symTup (fun b => c b / io (th i)) j := by
    intro j
    rw [map_div₀, map_pow, he]
    have e2 : (fun b => c b / io (th i)) = fun b => (io (th i))⁻¹ * c b := by
      funext b
      rw [div_eq_inv_mul]
    rw [e2, GlobalTheory.UMin.PrimCmp.symTup_mul, inv_pow, inv_mul_eq_div]
  exact GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_primitive_unit V K io N (fun b => c b / io (th i)) (fun j => e j / th i ^ N.factorial) hPt hsym

end GlobalTheory.SiegRev

theorem GlobalTheory.SiegTh.sameScale_theta_symE : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (e : Fin (N + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv S.th → SymE ρ m e → SameScale M S.th e (N + 1).factorial := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M e hNorm hDiv hSym z i hi
  obtain ⟨-, -, -, hmo, hm3, hmu, hN, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hNorm z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have hmo' : IsUnit (m : o) := by simpa using hmu.map β
  have hNe : N + 1 = m ^ (4 * S.g) := by rw [hN, hSg]
  have hk : 1 ≤ (S.r * S.N) ^ 2 := Nat.one_le_iff_ne_zero.2
    (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)))
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        ∃ e' : Fin (N + 1) → V,
          (∀ j, algebraMap V (FractionRing V) (e' j) = emb (e j / S.th i ^ (N + 1).factorial)) ∧
          ∃ j, IsUnit (e' j) := by
    intro V _ _ _ hV φ hφ
    haveI : IsDiscreteValuationRing V := hV.1
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have hmemO : ∀ x ∈ M.O z, emb x ∈ Set.range (algebraMap V (FractionRing V)) := fun x hx =>
      ⟨φ ⟨x, hx⟩, (hemb ⟨x, hx⟩).symm⟩
    have ho : ∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V)) := fun a =>
      hmemO _ ((M.O z).algebraMap_mem a)
    obtain ⟨K, _, io, N', c, c', a, ha, hP, hP', he, h1, h2⟩ :=
      GlobalTheory.T.exists_common_scale_thetaConstants_at_trait o Ω S ρ m (N + 1) e hmo hm3 hmo' hNe hSym V hV emb ho
    have hr : ∀ b, emb (S.th b) / emb (S.th i) ∈ Set.range (algebraMap V (FractionRing V)) := fun b => by
      rw [← map_div₀]
      exact hmemO _ (hi.2 b)
    obtain ⟨e', he', j, hj⟩ := GlobalTheory.SiegRev.scale_of_prim io (N + 1) N' ((S.r * S.N) ^ 2) c c' a
      (fun j => emb (e j)) (fun b => emb (S.th b)) i ha hk hP hP' he h1 h2 ((map_ne_zero emb).2 hi.1) hr
    refine ⟨emb, hemb, e', fun j => ?_, j, hj⟩
    rw [he', map_div₀, map_pow]
  have hmem : ∀ j, e j / S.th i ^ (N + 1).factorial ∈ M.O z := by
    intro j
    obtain ⟨x, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (e j / S.th i ^ (N + 1).factorial)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ x := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian (M.O z) x s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, e', he', -⟩ := key V hV φ hφ
      have hv := he' j
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨e' j, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  haveI := hloc
  obtain ⟨emb, hemb, e', he', j, hj⟩ := key V hV φ hφ
  have hj' : e' j = φ ⟨_, hmem j⟩ := IsFractionRing.injective V (FractionRing V) (by rw [he', ← hemb]; rfl)
  have hu : IsUnit (⟨e j / S.th i ^ (N + 1).factorial, hmem j⟩ : M.O z) := isUnit_of_map_unit φ _ (hj' ▸ hj)
  obtain ⟨h0, hinv⟩ := (RatModel.isUnit_O_iff _).1 hu
  have h0' : e j / S.th i ^ (N + 1).factorial ≠ 0 := h0
  have hinv' : (e j / S.th i ^ (N + 1).factorial)⁻¹ ∈ M.O z := hinv
  have hthD : S.th i ^ (N + 1).factorial ≠ 0 := pow_ne_zero _ hi.1
  have hej : e j ≠ 0 := fun h => h0' (by simp [h])
  refine ⟨j, ⟨hej, fun k => ?_⟩, ?_, hmem j⟩
  · have e3 : e k / e j = e k / S.th i ^ (N + 1).factorial * (e j / S.th i ^ (N + 1).factorial)⁻¹ := by
      field_simp
    rw [e3]
    exact mul_mem (hmem k) hinv'
  · simpa only [inv_div] using hinv'

end
