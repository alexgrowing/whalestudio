import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.Gal.Int.Geo

theorem repEx_of (h1 : GrEx) (h2 : ContGL) (h3 : MatEx) (h4 : MatConj) (h5 : PieceStab) (h6 : HtotFin) (h7 : ExtCont)
    (h8 : TotCont) (h9 : KunnethLefschetz.ProjBC) : RepEx := by
  intro E Ω _ _ _ _ _ l _ H θ hnice
  obtain ⟨hsm, hproj, hfet⟩ := hnice
  have hlE : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hlΩ : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : Smooth H.q := hsm
  have hsm' : Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap E Ω)))) := inferInstance
  have hproj' := h9.1 E Ω (algebraMap E Ω) H.q hproj
  haveI hfin : FiniteDimensional ℚ_[l] (Htot l (sch.obj (H.geomZ Ω))) := h6 l Ω hlΩ _ hsm' hproj'
  let U := piece l H Ω (Qbar l) θ
  let a : Gal(Ω/E) → _ := fun σ => galV l H Ω (Qbar l) σ
  have ha1 : a 1 = LinearMap.id := by
    simp only [a, galV, GlobalTheory.GalV.galTot_one, LinearMap.baseChange_id]
  have hamul : ∀ g h, a (g * h) = a g ∘ₗ a h := by
    intro g h
    simp only [a, galV, GlobalTheory.GalV.galTot_mul, LinearMap.baseChange_comp]
  have hU : ∀ g, ∀ x ∈ U, a g x ∈ U := fun g x hx => h5 l E hlE H hfet Ω (Qbar l) θ g x hx
  let b := Module.finBasis (Qbar l) U
  obtain ⟨ρ₀, hmat, hμ⟩ := h3 (Gal(Ω/E)) (Qbar l) _ a ha1 hamul U hU _ b
  have hM : IsMat l H Ω (Qbar l) θ ρ₀ := ⟨b, hmat⟩
  obtain ⟨P, ρ, hgr, hss⟩ := h1 (Gal(Ω/E)) (Qbar l) _ ρ₀
  have hM' := h4 l E H Ω (Qbar l) θ _ ρ₀ P hM
  have hT := h8 l E Ω hlE H.q (h9.2 E H.q hproj)
  have hcont0 : ∀ i j, Continuous fun g => (ρ₀ g).val i j := by
    intro i j
    obtain ⟨μ, hμij⟩ := hμ i j
    have hE := h7 (Gal(Ω/E)) ℚ_[l] (Qbar l) (continuous_algebraMap ℚ_[l] (Qbar l)) _
      (galTot l Ω H.q) hT (b j : _) μ
    refine hE.congr fun g => ?_
    rw [hμij g]
    rfl
  refine ⟨_, ρ, ?_, hss, cj P ρ₀, hM', hgr⟩
  obtain ⟨c, hc⟩ := hgr
  refine (h2 _ (Qbar l) _ ρ).2 fun i j => ?_
  have hfun : (fun g => (ρ g).val i j) = fun g => if c i = c j then (cj P ρ₀ g).val i j else 0 :=
    funext fun g => (hc g).2 i j
  rw [hfun]
  split_ifs
  · simp only [cj_apply, Units.val_mul, Matrix.mul_apply]
    refine continuous_finset_sum _ fun x _ => ?_
    refine Continuous.mul ?_ continuous_const
    refine continuous_finset_sum _ fun y _ => ?_
    exact continuous_const.mul (hcont0 y x)
  · exact continuous_const

end UpperTheory.Gal.Int.Geo

end
