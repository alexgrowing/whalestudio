import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoboundaryRoots

@[ext] structure CocExt (X A : Type) where
  fst : X
  snd : A

variable {X : Type} [AddCommGroup X] {A : Type} [CommGroup A]

theorem coc_zero_left (f : X → X → A)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) (c : X) : f 0 c = f 0 0 := by
  have h := hc 0 0 c
  simp only [add_zero, zero_add] at h
  exact (mul_left_cancel h).symm

theorem mul_mul_mul_inv_inv' (x y z : A) : x * y * z * x⁻¹ * y⁻¹ = z := by
  calc x * y * z * x⁻¹ * y⁻¹ = z * (x * x⁻¹) * (y * y⁻¹) := by ac_rfl
    _ = z := by simp

def extGroup (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (CocExt X A) :=
  letI : Add (CocExt X A) := ⟨fun p q => ⟨p.fst + q.fst, p.snd * q.snd * f p.fst q.fst⟩⟩
  letI : Zero (CocExt X A) := ⟨⟨0, (f 0 0)⁻¹⟩⟩
  letI : Neg (CocExt X A) := ⟨fun p => ⟨-p.fst, (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹⟩⟩
  { add_assoc := fun p q r => by
        refine CocExt.ext (add_assoc p.fst q.fst r.fst) ?_
        show p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
          = p.snd * (q.snd * r.snd * f q.fst r.fst) * f p.fst (q.fst + r.fst)
        calc p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
            = p.snd * q.snd * r.snd * (f (p.fst + q.fst) r.fst * f p.fst q.fst) := by ac_rfl
          _ = p.snd * q.snd * r.snd * (f p.fst (q.fst + r.fst) * f q.fst r.fst) := by rw [hc]
          _ = _ := by ac_rfl
    zero_add := fun p => by
        refine CocExt.ext (zero_add p.fst) ?_
        show (f 0 0)⁻¹ * p.snd * f 0 p.fst = p.snd
        rw [coc_zero_left f hc p.fst, mul_comm (f 0 0)⁻¹ p.snd, inv_mul_cancel_right]
    add_zero := fun p => by
        refine CocExt.ext (add_zero p.fst) ?_
        show p.snd * (f 0 0)⁻¹ * f p.fst 0 = p.snd
        rw [hs p.fst 0, coc_zero_left f hc p.fst, inv_mul_cancel_right]
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
        refine CocExt.ext (neg_add_cancel p.fst) ?_
        show (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹ * p.snd * f (-p.fst) p.fst = (f 0 0)⁻¹
        rw [hs (-p.fst) p.fst]; group
    add_comm := fun p q => by
        refine CocExt.ext (add_comm p.fst q.fst) ?_
        show p.snd * q.snd * f p.fst q.fst = q.snd * p.snd * f q.fst p.fst
        rw [hs, mul_comm p.snd q.snd] }

end GlobalTheory.CoboundaryRoots

namespace GlobalTheory

theorem symm_cocycle_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  intro X _ _ A _ f hs hc
  letI : AddCommGroup (GlobalTheory.CoboundaryRoots.CocExt X A) := GlobalTheory.CoboundaryRoots.extGroup f hs hc
  let bs := Module.Free.chooseBasis ℤ X
  let s : X →ₗ[ℤ] GlobalTheory.CoboundaryRoots.CocExt X A := bs.constr ℤ (fun i => ⟨bs i, 1⟩)
  let π : GlobalTheory.CoboundaryRoots.CocExt X A →+ X :=
    { toFun := GlobalTheory.CoboundaryRoots.CocExt.fst, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : π.toIntLinearMap.comp s = LinearMap.id :=
    bs.ext (fun i => by
      show π (s (bs i)) = bs i
      rw [show s (bs i) = ⟨bs i, 1⟩ from bs.constr_basis ℤ _ i]
      rfl)
  have hπ : ∀ x, (s x).fst = x := fun x => LinearMap.congr_fun hcomp x
  refine ⟨fun x => (s x).snd, fun a b => ?_⟩
  have h : (s (a + b)).snd = (s a).snd * (s b).snd * f (s a).fst (s b).fst :=
    congrArg GlobalTheory.CoboundaryRoots.CocExt.snd (s.map_add a b)
  rw [hπ, hπ] at h
  show f a b = (s (a + b)).snd * ((s a).snd)⁻¹ * ((s b).snd)⁻¹
  rw [h, GlobalTheory.CoboundaryRoots.mul_mul_mul_inv_inv']

end GlobalTheory
