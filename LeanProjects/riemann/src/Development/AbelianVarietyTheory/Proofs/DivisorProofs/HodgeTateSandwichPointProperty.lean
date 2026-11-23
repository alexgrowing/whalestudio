import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTLat.KerShape

theorem bLie_mem_W_and_tateGt (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
    [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ]
    (P : Point p v O Λ) [IsDomain O] (ε : PreTilt O p)
    (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε) (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie)
    (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (φ : G ⟶ G.dual)
    (hζ : Function.Bijective (fun a : ℤ_[p] => a • ζ))
    (hc : ∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ)
    (hl : ∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x)
    (hφ : ∀ s s' : G.Tate, pairing G O s (tateMap G G.dual O φ s') =
      pairT P.A P.eps (e s : P.T) (e s' : P.T) • ζ)
    (x : LieG P.Gt) : P.bLie x ∈ P.W ∧ P.bLie x ∈ P.tateGt.baseChange C := by
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.PointGroup.exists_form P.integers G ζ hζ
  have hk : GlobalTheory.PointGroup.KerIsLie G B :=
    (GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear p C v O ε hε H G ζ B P.integers hζ hB).1
  obtain ⟨ξ, hξ0, hξ⟩ := GlobalTheory.PointGroup.exists_ker_of_lie P.integers hB1.2 hk (l x)
  let j : G.Tate →ₗ[ℤ_[p]] P.T := P.tateGt.subtype ∘ₗ e.toLinearMap
  have hBc : ∀ s t, B s (c t) = pairT P.A P.eps (j s) t := fun s t =>
    hζ.1 ((hB s (c t)).symm.trans (hc s t))
  have hcφ : ∀ s, c (j s) = tateMap G G.dual O φ s := fun s =>
    hB2.1 (LinearMap.ext fun s' => hζ.1
      ((hB s' _).symm.trans ((hc s' (j s)).trans ((hφ s' s).symm.trans (hB s' _)))))
  have h1 : ∀ (z : O ⊗[ℤ_[p]] G.Tate) t, P.pairV (P.inclT (j.baseChange O z)) (1 ⊗ₜ t) =
      algebraMap O C (TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O z)) := fun z t => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, Point.inclT_tmul, Point.pairV_tmul, LinearMap.baseChange_tmul,
        LinearMap.flip_apply, hBc, TensorProduct.rid_tmul, _root_.mul_one, Algebra.smul_def,
        Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have h2 : P.bLie x = P.inclT (j.baseChange O ξ) := P.eq_of_pairV fun t => by
    rw [h1, hξ, hl, Point.pairV_bLie]
  have h3 : ∀ χ, dlog G χ = omegaMap _ _ G.bidual.hom (hodgeTate G.dual χ) := fun χ => by
    rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap, ← LinearMap.comp_apply,
      ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  have h4 : ∀ (z : O ⊗[ℤ_[p]] G.Tate) x', (P.al (j.baseChange O z)).1 x' =
      l x' (omegaMap _ _ G.bidual.hom (omegaDualMap G G.dual φ (G.hodgeTateLinear z))) :=
    fun z x' => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, Submodule.coe_add, Pi.add_apply, hx, hy]
      | tmul a s =>
        rw [LinearMap.baseChange_tmul, Point.al_tmul, hodgeTateLinear_tmul, map_smul, map_smul,
          map_smul, ← hodgeTate_tateMap, ← h3, ← hcφ, hl]
        rfl
  have h5 : P.al (j.baseChange O ξ) = 0 := Subtype.ext (funext fun x' => by
    rw [h4, hξ0, map_zero, map_zero, map_zero]
    rfl)
  rw [h2]
  refine ⟨?_, ?_⟩
  · change P.alC _ = 0
    rw [Point.alC_inclT, h5, map_zero]
  · clear hξ0 hξ h2 h5
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, Point.inclT_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ (e s).2

end GlobalTheory.HTLat.KerShape
