import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightShiftEqDetMul
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SumExpAt

theorem mem_locP {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem locIncl_of_equiv {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (N D : Submodule (𝓞 K) V) (N' D' : Submodule (𝓞 K) V')
    (hN : N.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = N')
    (hD : D.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = D')
    (h : ∀ x ∈ N', a • x ∈ Formalism.HermitianLatticesTheory.localization₂ p D') : ∀ v ∈ N, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p D := by
  intro v hv
  set f : V →ₗ[𝓞 K] V' := (e : V →ₗ[K] V').restrictScalars (𝓞 K) with hf
  have hx : f v ∈ N' := hN ▸ Submodule.mem_map_of_mem hv
  obtain ⟨s, hs, hsD⟩ := (mem_locP p D' _).1 (h _ hx)
  refine (mem_locP p D _).2 ⟨s, hs, ?_⟩
  rw [← hD] at hsD
  obtain ⟨y, hy, hye⟩ := hsD
  have hinj : Function.Injective f := e.injective
  have : y = s • a • v := hinj (by rw [hye, map_smul, map_smul])
  rw [← this]
  exact hy

theorem cutLat_locIncl {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.DIV.CSD K) {d : ℕ}
    (E : Matrix (Fin S.dim) (Fin d) K) (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (h : ∀ c, ∀ v ∈ S.Nab c, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (S.Del c)) :
    ∀ z ∈ Formalism.DivisionValues.cutLat E S.nabLat, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ p (Formalism.DivisionValues.cutLat E S.delLat) := by
  classical
  intro z hz
  have hz' : ∀ c, S.I (E.mulVec z) c ∈ S.Nab c := fun c => hz c (Set.mem_univ c)
  have hlin : ∀ (r : 𝓞 K) (y : Fin d → K), S.I (E.mulVec (r • y)) = r • S.I (E.mulVec y) := fun r y => by
    have h1 := ((Matrix.mulVecLin E).restrictScalars (𝓞 K)).map_smul r y
    have h2 := (S.I.restrictScalars (𝓞 K)).map_smul r (E.mulVec y)
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at h1 h2
    rw [h1, h2]
  choose s hs hsD using fun c => (mem_locP p (S.Del c) _).1 (h c _ (hz' c))
  refine (mem_locP p _ _).2 ⟨∏ c, s c, prod_mem fun c _ => hs c, ?_⟩
  intro c _
  show S.I (E.mulVec ((∏ c, s c) • a • z)) c ∈ S.Del c
  rw [hlin, hlin, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ c), Pi.smul_apply, Pi.smul_apply, mul_comm,
    mul_smul]
  exact Submodule.smul_mem _ _ (hsD c)

end GlobalTheory.SumExpAt

namespace GlobalTheory.SumExpAt

open Formalism.CohomologicalDescent.LD in

theorem exZ_res_eq_natW (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) (f : ℕ → ℕ) (c : ℤ)
    (hc : ∀ a : Fin n, (f a : ℤ) = lam.w a + c) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl (res n f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl lam.natW l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · congr 1
    funext a
    exact a.elim0
  · let m : Fin n := ⟨n - 1, by omega⟩
    have hds : lam.detShift = lam.w m := by
      simp only [Formalism.BasicNotions.DomWeight.detShift, dif_pos hn]
      rfl
    have hres : res n f = fun a => lam.natW a + f m := by
      funext a
      have h1 := hc a
      have h2 := hc m
      have h3 : lam.w m ≤ lam.w a := lam.anti (Fin.le_def.2 (by simp only [m]; omega))
      have h4 : ((lam.w a - lam.w m).toNat : ℤ) = lam.w a - lam.w m := Int.toNat_of_nonneg (by omega)
      change f a.val = (lam.w a - lam.detShift).toNat + f m
      rw [hds]
      omega
    have hanti : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      exact Int.toNat_le_toNat (by omega)
    rw [hres]
    exact Formalism.CohomologicalDescent.LA.exact_z_twist_by_det n lam.natW (f m) l hanti hl

theorem exZ_res_congr {N n : ℕ} (h : N = n) (f : ℕ → ℕ) (l : ℕ) :
    Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Formalism.CohomologicalDescent.LD.res N f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl (Formalism.CohomologicalDescent.LD.res n f) l := by
  subst h
  rfl

end GlobalTheory.SumExpAt

namespace GlobalTheory.ExpTie

open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lIncl_sumExp (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (hD : Dict L j P W) (t : p.P.T)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, -, -, hNab, hDel⟩ := hT.coefL j t
  have hJ : W.JA P (Formalism.EigenvalueLevelCeiling.plc w) = ∑ τ, Formalism.CohomologicalDescent.LA.exZ (Vc D j).rank (Vc D j).rank le_rfl
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).natW (Formalism.EigenvalueLevelCeiling.plc w) := by
    unfold Wts.JA Wts.ex
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [exZ_res_congr hD.Nr]
    obtain ⟨c, hc⟩ := hD.lam τ
    exact exZ_res_eq_natW _ _ _ c hc _ (Formalism.EigenvalueLevelCeiling.plc_prime w)
  intro z hz
  rw [hJ]
  refine cutLat_locIncl (blk p j t).S _ w.asIdeal _ (fun c => ?_) z hz
  refine locIncl_of_equiv e w.asIdeal _ _ _ _ _ (hNab c) (hDel c) ?_
  exact GlobalTheory.T.sum_exactExponents_smul_mem_localizedCoeffLattice _ _ _ _ _ _ _ (GlobalTheory.RepsCompare.isLattice_hLat _ _) w

end Point

theorem sumExpSt : SumExpSt :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => EvPt.of_forall fun _ _ _ p _ _ j P W hD _ t w => lIncl_sumExp p j P W hD t w⟩⟩
end GlobalTheory.ExpTie

end
