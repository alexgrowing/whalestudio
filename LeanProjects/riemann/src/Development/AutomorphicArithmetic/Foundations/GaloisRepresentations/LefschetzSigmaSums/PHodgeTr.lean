import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeTr_of :
    GroupTop → FnDecomp → HopWord → AltLin → GeoStep → CxLin → UpperTheory.Gal.G3.HodgeGood → HodgeTr := by
  classical
  intro hTop hFD hHW hAL hGS hCL hHG p _ D G L lam i₀ h hh
  obtain ⟨k₀, hk'⟩ := hTop p D G L lam i₀ h hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk' k hkk
  refine ⟨c, fun hSc gb hStd T N d hsm V _ _ _ ξ hξ f hfn hG y => ?_⟩
  have hcard : 0 < Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} := by
    have e : G.a = 1 := hSc.ga
    have e' : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} = 1 := e
    omega
  obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.1 hcard
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N.1 (by have := N.2.1; omega)
  have hK := T.K_eq N
  obtain ⟨hHecke, m, g, cc, hΔ, hdec, hsupp⟩ := (hFD _ _ T.X (T.lev N) f).1 hfn
  rw [hK] at hHecke hdec hsupp
  have hreg : ∀ i x, ind ℂ (L.KN N.1) (g i)⁻¹ x ≠ 0 → RegAf G x := fun i x hx => hG.reg x (hsupp i x hx)
  have hfnu : ∀ i, T.X.IsFn (T.lev N) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i => by
    have e := (UpperTheory.Gal.G3.pFnRing T.X ℂ (T.lev N)).1 _ (hΔ i)
    rwa [hK] at e
  have hgeo := fun i α hα => hGS p D G L hSc gb hStd i₀ v hv k T N d hsm (g i) (hΔ i) (hreg i) α hα
  have hfin : ∀ i, CxFin G v (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i =>
    (hgeo i (fun _ => 2) (fun _ => ⟨two_ne_zero, dvd_rfl⟩)).1
  have hhk : ∀ a b, hk T N f a b = ∑ i, cc i • hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b := fun a b => by
    have e := ((hHW _ _ T.X (hodge ℂ a b) (hHG ℂ a b) (T.lev N)).1 m _ cc hfnu).2
    rw [← hdec] at e
    exact e
  have e1 : altTr (qAt T N) d (fun a b => hk T N f a b ∘ₗ cutD T N c a b) y =
      ∑ i, cc i * c.sum fun α r => r * cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) (Kp G) (oneP G) := by
    have e := hAL _ (qAt T N) d m (Fin k → 𝓞 D.F) (fun i a b => hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b) cc c
      (fun α a b => hodgePull (al_q T N α) a b) y
    simp only [hhk, cutD]
    rw [e]
    refine Finset.sum_congr rfl fun i _ => congrArg (cc i * ·) (Finsupp.sum_congr fun α hα => ?_)
    rw [(hgeo i α (hc1 α hα)).2 y]
  have e2 := hCL p G v (L.KN N.1) m _ cc hfin (Fin k → 𝓞 D.F) c (fun α => cW L i₀ v α y)
  rw [← hdec] at e2
  have e3 := hc2 hSc.a1 hSc.ga hSc.odd v hv V ξ hξ Lv f
  rw [hLv] at e3
  rw [e1, ← e2]
  exact e3 hHecke hG y
