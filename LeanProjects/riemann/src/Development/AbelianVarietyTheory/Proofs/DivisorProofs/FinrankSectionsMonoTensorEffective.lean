import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TensMul

variable {K : Type} [Field K] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of K))

def mulSec {L D : LB Y} (s : LB.Sec D) (σ : LB.Sec L) : LB.Sec (tens L D) where
  f := fun p : L.ι × D.ι => rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) (σ.f p.1) *
      rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)
  compat := fun (p q : L.ι × D.ι) => by
    obtain ⟨i, j⟩ := p
    obtain ⟨k, l⟩ := q
    have c₁ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ L.U k :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have c₂ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ D.U j ⊓ D.U l :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h₁ : rs Y (inf_le_left : L.U i ⊓ L.U k ≤ L.U i) (σ.f i) =
        (L.g i k).val * rs Y (inf_le_right : L.U i ⊓ L.U k ≤ L.U k) (σ.f k) := σ.compat i k
    have h₂ : rs Y (inf_le_left : D.U j ⊓ D.U l ≤ D.U j) (s.f j) =
        (D.g j l).val * rs Y (inf_le_right : D.U j ⊓ D.U l ≤ D.U l) (s.f l) := s.compat j l
    have h₁' := congrArg (rs Y c₁) h₁
    have h₂' := congrArg (rs Y c₂) h₂
    rw [map_mul, rs_rs, rs_rs] at h₁' h₂'
    change rs Y (inf_le_left : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ D.U j)
        (rs Y (inf_le_left : L.U i ⊓ D.U j ≤ L.U i) (σ.f i) * rs Y (inf_le_right : L.U i ⊓ D.U j ≤ D.U j) (s.f j)) =
      (rs Y c₁ (L.g i k).val * rs Y c₂ (D.g j l).val) *
        rs Y (inf_le_right : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U k ⊓ D.U l)
          (rs Y (inf_le_left : L.U k ⊓ D.U l ≤ L.U k) (σ.f k) * rs Y (inf_le_right : L.U k ⊓ D.U l ≤ D.U l) (s.f l))
    rw [map_mul, map_mul, rs_rs, rs_rs, rs_rs, rs_rs, h₁', h₂']
    ring

def mulLin {L D : LB Y} (s : LB.Sec D) : SecOnR f L ⊤ →ₗ[K] SecOnR f (tens L D) ⊤ :=
  GlobalTheory.VeryAmpleGrowth.linTop f (fun a => mulSec s (SecOnR.topEquiv f L a))
    (fun a b (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y _ ((SecOnR.topEquiv f L (a + b)).f p.1) * rs Y inf_le_right (s.f p.2))
        (rs Y inf_le_left ((SecOnR.topEquiv f L a).f p.1) * rs Y inf_le_right (s.f p.2) +
          rs Y inf_le_left ((SecOnR.topEquiv f L b).f p.1) * rs Y inf_le_right (s.f p.2))
      rw [GlobalTheory.VeryAmpleGrowth.top_add, map_add]
      exact add_mul _ _ _)
    (fun c a (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y inf_le_left ((SecOnR.topEquiv f L (c • a)).f p.1) * rs Y inf_le_right (s.f p.2))
        (cst f (L.U p.1 ⊓ D.U p.2) c * (rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) ((SecOnR.topEquiv f L a).f p.1) *
          rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)))
      rw [GlobalTheory.VeryAmpleGrowth.top_smul, map_mul, rs_cst]
      exact _root_.mul_assoc _ _ _)

theorem top_mulLin {L D : LB Y} (s : LB.Sec D) (a : SecOnR f L ⊤) :
    SecOnR.topEquiv f (tens L D) (mulLin f s a) = mulSec s (SecOnR.topEquiv f L a) :=
  GlobalTheory.VeryAmpleGrowth.top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral Y] {L D : LB Y} (hL : L.IsLB) (s : LB.Sec D) {x : Y}
    (hx : x ∈ Out.nonzeroLocus s) : Function.Injective (mulLin f (L := L) s) := by
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hxL : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hxL
  let W : Y.Opens := L.U i₀ ⊓ Y.basicOpen (s.f j₀)
  have hWB : W ≤ Y.basicOpen (s.f j₀) := inf_le_right
  have hBD : Y.basicOpen (s.f j₀) ≤ D.U j₀ := Y.basicOpen_le _
  have hWL : W ≤ L.U i₀ := inf_le_left
  have hWT : W ≤ L.U i₀ ⊓ D.U j₀ := le_inf hWL (hWB.trans hBD)
  haveI : Nonempty W := ⟨⟨x, hi₀, hj₀⟩⟩
  have hu : IsUnit (rs Y (hWB.trans hBD) (s.f j₀)) := by
    rw [← rs_rs hBD hWB]
    exact (Y.toRingedSpace.isUnit_res_basicOpen (s.f j₀)).map _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : (mulSec s (SecOnR.topEquiv f L a)).f (i₀, j₀) = 0 := by
    have e := top_mulLin f s a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (tens L D) => σ.f (i₀, j₀)) e).symm.trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f (M := tens L D) (i₀, j₀))
  have h' := congrArg (rs Y hWT) h
  change rs Y hWT (rs Y (inf_le_left : L.U i₀ ⊓ D.U j₀ ≤ L.U i₀) ((SecOnR.topEquiv f L a).f i₀) *
    rs Y (inf_le_right : L.U i₀ ⊓ D.U j₀ ≤ D.U j₀) (s.f j₀)) = rs Y hWT 0 at h'
  rw [map_mul, map_zero, rs_rs, rs_rs, hu.mul_left_eq_zero] at h'
  exact GlobalTheory.VeryAmpleGrowth.top_ext f fun k =>
    (GlobalTheory.SecGrowth.sec_eq_zero (M := L) (SecOnR.topEquiv f L a) (k₀ := i₀) hWL h' k).trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f k).symm

end GlobalTheory.TensMul

theorem GlobalTheory.TensMul.finite_finrank_le_tens : ∀ {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) {L D : LB Y}, L.IsLB → D.IsLB → ∀ (s : LB.Sec D) {x : Y}, x ∈ Out.nonzeroLocus s → Module.Finite K (SecOnR f (tens L D) ⊤) → Module.Finite K (SecOnR f L ⊤) ∧ Module.finrank K (SecOnR f L ⊤) ≤ Module.finrank K (SecOnR f (tens L D) ⊤) := by
  intro K _ Y _ f L D hL _ s x hx hfin
  have hinj := GlobalTheory.TensMul.mulLin_injective f hL s hx
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩
