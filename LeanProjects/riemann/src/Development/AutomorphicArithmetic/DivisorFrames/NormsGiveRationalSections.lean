import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
import Development.AutomorphicArithmetic.DivisorFrames.ArithmeticFunctionInducedBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.CovCmp
open scoped Classical

open private UpperTheory.VertGlob.exists_lift from Development.AutomorphicArithmetic.DivisorFrames.ArithmeticFunctionInducedBound

theorem UpperTheory.norms_give_rational_sections :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (V : Mean4O.Cover Y) (L : HermLB V.p) (m : ℕ) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), Norms V L (fun x => genAt A.D x ^ m) a (fun v e y => (m : ℝ) * A.lg v e y) → ∃ s : L.B.ι → V.X.functionFieldˣ, ∀ v, CRead V v L.B s fun e y => (m : ℝ) * VertCmp.lam A v e y := by
  intro F _ _ Y C A V L m a h
  obtain ⟨s, hs, hR, -⟩ := UpperTheory.VertGlob.exists_lift V L h
  obtain ⟨W, hW, hE⟩ := (A.D.isEqn_genericPoint 1).exists_nhds
  have hu (x : Y.X) (hx : x ∈ W) : UnitAt x (eqn A.D x : Y.Fn) := by
    simpa using (hE x hx).iff_unitAt.1 (Base.isEqn_eqn A.D x)
  have hf (x : Y.X) (hx : x ∈ W) : UnitAt x (genAt A.D x ^ m) := by
    rw [genAt, Units.val_inv_eq_inv_val]
    clear hR h
    induction m with
    | zero => simpa using unitAt_one x
    | succ n ih => rw [pow_succ]; exact ih.mul (hu x hx).inv
  refine ⟨s, fun v => ⟨hs, W, hW, fun e y z yt i hy e₁ e₂ hU _ => ?_⟩⟩
  haveI := CoverHt.isPreimmersion_j V
  obtain ⟨hw, H⟩ := hR v e y z yt i e₁ e₂ hU
  obtain ⟨hπ, eφ⟩ := V.φ_eq_fnMap
  have hb : V.π (below z) = below y.1 := by rw [← e₁]; rfl
  have hfy := hf _ hy
  have hfz : UnitAt (below z) (V.φ (genAt A.D (below y.1) ^ m)) := by
    rw [eφ]
    exact unitAt_fnMap_of V.π hπ (by rw [hb]; exact hfy)
  have hs' := hfz.inv.mul hw
  rw [inv_mul_cancel_left₀ hfz.ne_zero] at hs'
  have hval : TrueGeo.valAt z (V.φ (genAt A.D (below y.1) ^ m)) =
      TrueGeo.valAt y.1 (genAt A.D (below y.1) ^ m) := by
    rw [eφ, SmallSec.valAt_fnMap V.π hπ z (by rw [hb]; exact hfy.regAt), e₁]
  rw [SmallSec.valAt_mul hfz.regAt hs'.regAt, map_mul,
    Real.log_mul (e.w.pos (Res.valAt_ne_zero hfz)).ne' (e.w.pos (Res.valAt_ne_zero hs')).ne', hval,
    genAt, Units.val_inv_eq_inv_val, Res.valAt_pow (hu _ hy).inv.regAt, LineNorm.Neg.valAt_inv (hu _ hy),
    AbsoluteValue.map_pow, map_inv₀, Real.log_pow, Real.log_inv] at H
  beta_reduce at H ⊢
  rw [VertCmp.lam, ModelFn.valAt_comp V.j (Isom.j_gen_specializes V) z, mul_add, H]
  ring
