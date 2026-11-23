import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.Pull

open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

theorem matrix_map_inv {K L : Type} [Field K] [Field L] (f : K →+* L) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) : (A.map f)⁻¹ = A⁻¹.map f := by
  rw [Matrix.inv_def, Matrix.inv_def]
  have h1 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (RingHom.map_adjugate f A).symm
  rw [h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i k
  simp [Matrix.smul_apply]

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

theorem fnMap_algebraMap (y : Y) (a : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (j.stalkMap y a) := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [algebraMap_germ hx s, fnMap_fnOf j hη _ (gen_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem regAt_fnMap {y : Y} {t : X.functionField} (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, (fnMap_algebraMap j hη y a).symm⟩

theorem unitAt_fnMap {y : Y} {t : X.functionField} (h : UnitAt (j y) t) : UnitAt y (fnMap j hη t) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, ha.map _, (fnMap_algebraMap j hη y a).symm⟩

theorem zeroAt_fnMap {y : Y} {t : X.functionField} (h : ZeroAt (j y) t) : ZeroAt y (fnMap j hη t) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨_, ?_, (fnMap_algebraMap j hη y a).symm⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  exact fun hu => ha (isUnit_of_map_unit (j.stalkMap y).hom a hu)

theorem not_isUnit_natCast (p : ℕ) {y : Y} (h : ¬ IsUnit (p : Y.presheaf.stalk y)) :
    ¬ IsUnit (p : X.presheaf.stalk (j y)) := by
  intro hu
  apply h
  have := hu.map (j.stalkMap y).hom
  simpa using this

end

end GlobalTheory.FrameGlue.Pull

theorem GlobalTheory.FrameGlue.modPFrames_pull : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (p : ℕ)
    (ι : Type) (N : ℕ) (U : ι → X.Opens) (M : ι → Matrix (Fin N) (Fin N) X.functionField) (c : ι → Fin N → X.functionFieldˣ),
    GlobalTheory.FrameGlue.ModPFrames p U M c →
    GlobalTheory.FrameGlue.ModPFrames p (fun a => π ⁻¹ᵁ U a) (fun a => (M a).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ))
      (fun a i => Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c a i)) := by
  intro X X' _ _ π hπ p ι N U M c hF
  obtain ⟨h1, h2, h3⟩ := hF
  open GlobalTheory.FrameGlue.Pull in
  refine ⟨fun x hx => ?_, fun a x hx hp => ?_, fun a b x hxa hxb hp i => ?_⟩
  · obtain ⟨a, ha⟩ := h1 (π x) (not_isUnit_natCast π p hx)
    exact ⟨a, ha⟩
  · obtain ⟨hr, hd⟩ := h2 a (π x) hx (not_isUnit_natCast π p hp)
    refine ⟨fun i k => regAt_fnMap π hπ (hr i k), ?_⟩
    have e : ((M a).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ)).det = GlobalTheory.TrueGeo.SmallSec.fnMap π hπ (M a).det :=
      (RingHom.map_det _ _).symm
    show UnitAt x ((M a).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ)).det
    rw [e]
    exact unitAt_fnMap π hπ hd
  · obtain ⟨hu, hz, hd⟩ := h3 a b (π x) hxa hxb (not_isUnit_natCast π p hp) i
    have hm : ((M a).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ))⁻¹ * (M b).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ) =
        ((M a)⁻¹ * M b).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ) := by
      rw [matrix_map_inv, Matrix.map_mul]
    have hc : ((Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c a i) /
        Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c b i) : X'.functionFieldˣ) : X'.functionField) =
        GlobalTheory.TrueGeo.SmallSec.fnMap π hπ ((c a i / c b i : X.functionFieldˣ) : X.functionField) := by
      rw [← map_div]; rfl
    refine ⟨hc ▸ unitAt_fnMap π hπ hu, fun k hk => ?_, ?_⟩
    · rw [hm]
      exact zeroAt_fnMap π hπ (hz k hk)
    · rw [hm, hc, Matrix.map_apply, ← map_sub]
      exact zeroAt_fnMap π hπ hd

end
