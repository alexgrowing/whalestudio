import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InducesIsom

section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

theorem exists_isRatSec_pull {X G : Scheme.{0}} [IsIntegral G] (j : G ⟶ X) {L M : LB X} (hL : L.IsLB) (hM : M.IsLB)
    (w : ∀ a b, Γ(X, M.U a ⊓ L.U b)ˣ)
    (hw : ∀ (z : G) a a' b b', j z ∈ M.U a → j z ∈ M.U a' → j z ∈ L.U b → j z ∈ L.U b' → gm j z _ (w a b) =
      gm j z _ (M.g a a') * (gm j z _ (L.g b b'))⁻¹ * gm j z _ (w a' b'))
    {r : (L.pull j).ι → G.functionFieldˣ} (hr : IsRatSec (L.pull j) r) :
    ∃ r' : (M.pull j).ι → G.functionFieldˣ, IsRatSec (M.pull j) r' ∧
      ∀ (a : (M.pull j).ι) (b : L.ι) (h : genericPoint G ∈ j ⁻¹ᵁ (M.U (a PUnit.unit) ⊓ L.U b)),
        (r' a : G.functionField) = fnOf _ h (pullU j _ (w (a PUnit.unit) b)).val * r (fun _ => b) := by
  classical
  obtain ⟨b₀, h₀⟩ := exists_chart hL (j (genericPoint G))
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : G.functionFieldˣ := gm j (genericPoint G) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint G ∈ j ⁻¹ᵁ U) :
      (F U u : G.functionField) = fnOf _ hU (pullU j U u).val := gm_val j _ U hU u
  have hg (N : LB X) (a a' : (N.pull j).ι) (h : genericPoint G ∈ (N.pull j).U a ⊓ (N.pull j).U a') :
      fnOf _ h ((N.pull j).g a a').val = (F _ (N.g (a PUnit.unit) (a' PUnit.unit)) : G.functionField) :=
    (gm_val (𝟙 G) _ _ h _).symm.trans (congrArg Units.val
      ((gm_pull_g N j (𝟙 G) (genericPoint G) a a' h.1 h.2).trans (by rw [Category.id_comp])))
  have hw' (a a' b b') (h₁ : j (genericPoint G) ∈ M.U a) (h₂ : j (genericPoint G) ∈ M.U a')
      (h₃ : j (genericPoint G) ∈ L.U b) (h₄ : j (genericPoint G) ∈ L.U b') :
      F _ (w a b) = F _ (M.g a a') * (F _ (L.g b b'))⁻¹ * F _ (w a' b') := hw _ a a' b b' h₁ h₂ h₃ h₄
  have hM' (a) (h₁ : j (genericPoint G) ∈ M.U a) : F _ (M.g a a) = 1 := gm_self hM j _ h₁
  have hL' : F _ (L.g b₀ b₀) = 1 := gm_self hL j _ h₀
  refine ⟨fun a => F _ (w (a PUnit.unit) b₀) * r (fun _ => b₀), fun a a' h' => ?_, fun a b h' => ?_⟩
  · beta_reduce
    rw [hg M a a' h', ← Units.val_mul, hw' _ (a' PUnit.unit) b₀ b₀ (mem_pull.1 h'.1) (mem_pull.1 h'.2) h₀ h₀, hL',
      inv_one, mul_one, mul_assoc]
  · have e := hr (fun _ => b) (fun _ => b₀) (memInf (mem_pull.2 h'.2) (mem_pull.2 h₀))
    replace e : ((r fun _ => b : G.functionFieldˣ) : G.functionField) =
        (F _ (L.g b b₀) : G.functionField) * (r fun _ => b₀ : G.functionFieldˣ) :=
      e.trans (congrArg (· * _) (hg L (fun _ => b) (fun _ => b₀) _))
    beta_reduce
    rw [← hF, e, ← Units.val_mul, ← Units.val_mul, hw' _ _ b b₀ h'.1 h'.1 h'.2 h₀,
      hM' _ h'.1, one_mul, mul_comm (F _ (L.g b b₀))⁻¹, mul_assoc, inv_mul_cancel_left]

theorem w_valAt_pullU {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} [IsIntegral G] (j : G ⟶ X)
    {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ G) (yt : Sp e.O ⟶ X)
    (h : spMap e.O.subtype ≫ yt = z ≫ j) {U : X.Opens} (hU : ⊤ ≤ yt ⁻¹ᵁ U) (u : Γ(X, U)ˣ)
    (hg : genericPoint G ∈ j ⁻¹ᵁ U) : e.w (valAt z (fnOf (j ⁻¹ᵁ U) hg (pullU j U u).val)) = 1 := by
  have ht : ⊤ ≤ z ⁻¹ᵁ (j ⁻¹ᵁ U) := fun p _ => by
    change (z ≫ j) p ∈ U
    rw [← h]
    exact hU (x := spMap e.O.subtype p) trivial
  have hb : below z ∈ j ⁻¹ᵁ U := ht trivial
  have hev := OfModel.eval_pull e.O.subtype j z yt h (U := U) (W := j ⁻¹ᵁ U) le_rfl ht hU u.val
  have e₁ : (pullU j U u).val = (j.appLE U (j ⁻¹ᵁ U) le_rfl).hom u.val := by
    rw [← Scheme.Hom.app_eq_appLE]
    rfl
  rw [OfModel.valAt_fnOf _ hb ht, e₁, hev]
  exact OfModel.w_unit e (u.isUnit.map _)

theorem induces_of_isometric {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}
    (V : Cover Y) (A : Adl C Y) (L M : HermLB V.p) (k : ℕ) (h : V.Induces A L k) (hi : L.Isometric M) :
    V.Induces A M k := by
  obtain ⟨r, hr, hu, hc, hf⟩ := h
  obtain ⟨w, hw, hφ⟩ := hi.exists_units
  obtain ⟨r', hr', key⟩ := exists_isRatSec_pull V.j L.isLB M.isLB w (hw _ V.j) hr
  have key' (c : V.G.functionField) (a : (M.B.pull V.j).ι) (b : L.B.ι)
      (h : genericPoint V.G ∈ V.j ⁻¹ᵁ (M.B.U (a PUnit.unit) ⊓ L.B.U b)) :
      c * (r' a : V.G.functionField) =
        fnOf _ h (pullU V.j _ (w (a PUnit.unit) b)).val * (c * r (fun _ => b)) := by
    rw [key a b h, mul_left_comm]
  refine ⟨r', hr', fun a x hx => ?_, fun σ z y y' a e₁ e₂ ha => ?_, fun v e y z yt a e₁ e₂ ha => ?_⟩
  · obtain ⟨b, hb⟩ := exists_chart L.isLB (V.j x)
    have hm : x ∈ V.j ⁻¹ᵁ (M.B.U (a PUnit.unit) ⊓ L.B.U b) := ⟨mem_pull.1 hx, hb⟩
    rw [key' _ a b (gen_mem hm)]
    exact (unitAt_fnOf hm _ _).mul (hu (fun _ => b) x (mem_pull.2 hb))
  · obtain ⟨b, hb⟩ := exists_chart L.isLB (V.j (under z))
    have hm : under z ∈ V.j ⁻¹ᵁ (M.B.U (a PUnit.unit) ⊓ L.B.U b) := ⟨mem_pull.1 ha, hb⟩
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hun : under y' = V.j (under z) := by
      change y'.1 _ = _
      rw [e₂]
      rfl
    have hy' : y' ∈ ptsIn V.p _ (M.B.U (a PUnit.unit) ⊓ L.B.U b) := mem_ptsIn.2 (by
      change under y' ∈ _
      rw [hun]
      exact hm)
    have hU := hu (fun _ => b) _ (mem_pull.2 hb)
    rw [hπ] at hU
    have hev : ev (V.π ≫ Y.str) σ _ (pullU V.j _ (w (a PUnit.unit) b)).val z =
        ev V.p _ _ (w (a PUnit.unit) b).val y' := by
      rw [ev, ev, e₂]
      exact (valR_comp z.1 V.j _ _).symm
    have h0 : 0 < ‖ev V.p _ _ (w (a PUnit.unit) b).val y'‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (ev_ne_zero hy' (Units.isUnit _))) 2
    rw [hc σ z y y' (fun _ => b) e₁ e₂ (mem_pull.2 hb), key' _ a b (gen_mem hm),
      ratVal_mul (regAt_fnOf hm _ _) hU.regAt, ratVal_fnOf (mem_ptsIn.2 hm), hev,
      hφ _ _ b y' (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2, logSq, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log h0, norm_mul, mul_pow]
    have h1 := h0.ne'
    generalize ‖ev V.p _ _ (w (a PUnit.unit) b).val y'‖ ^ 2 = t at h1 ⊢
    field_simp
  · obtain ⟨b, hb⟩ := exists_chart L.isLB (yt (IsLocalRing.closedPoint e.O))
    have hb' : ⊤ ≤ yt ⁻¹ᵁ L.B.U b := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of e.O) yt hb).ge
    have hab : ⊤ ≤ yt ⁻¹ᵁ (M.B.U (a PUnit.unit) ⊓ L.B.U b) := fun p hp => ⟨ha hp, hb' hp⟩
    have hm : below z ∈ V.j ⁻¹ᵁ (M.B.U (a PUnit.unit) ⊓ L.B.U b) := by
      change (z ≫ V.j) _ ∈ M.B.U (a PUnit.unit) ⊓ L.B.U b
      rw [← e₂]
      exact hab (x := spMap e.O.subtype _) trivial
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu (fun _ => b) _ (mem_pull.2 hm.2)
    rw [hπ] at hU
    rw [hf v e y z yt (fun _ => b) e₁ e₂ hb', key' _ a b (gen_mem hm),
      OfModel.valAt_mul z (regAt_fnOf hm _ _) hU.regAt, map_mul, w_valAt_pullU V.j e z yt e₂ hab, one_mul]

end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

theorem main : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} {Yv : ProjVar.Var F}
    (V : Cover Yv) (A : TrueGeo.Adl C Yv) (L M : HermLB V.p) (k : ℕ),
    V.Induces A L k → L.Isometric M → V.Induces A M k :=
  fun V A L M k h hi => induces_of_isometric V A L M k h hi

end GlobalTheory.InducesIsom
