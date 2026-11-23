import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.CovolRank

theorem comap_val_finite {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) [FiniteDimensional K C] :
    FiniteDimensional K (C.comap A.val.toLinearMap) ∧
      Module.finrank K (C.comap A.val.toLinearMap) ≤ Module.finrank K C := by
  let f : C.comap A.val.toLinearMap →ₗ[K] C :=
    LinearMap.codRestrict C (A.val.toLinearMap ∘ₗ (C.comap A.val.toLinearMap).subtype)
      fun y => Submodule.mem_comap.1 y.2
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg (fun z : C => (z : B)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : FiniteDimensional K (C.comap A.val.toLinearMap) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

theorem finrank_span_le_of_map {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) (hC : C ≤ Subalgebra.toSubmodule A) {O : Type} [CommRing O] [Module O C]
    (L : Submodule O C) (N : Submodule K A) [FiniteDimensional K N]
    (hL : ∀ F ∈ L, (⟨(F : B), hC F.2⟩ : A) ∈ N) :
    Module.finrank K (Submodule.span K (L : Set C)) ≤ Module.finrank K N := by
  let Φ : C →ₗ[K] A := LinearMap.codRestrict (Subalgebra.toSubmodule A) C.subtype fun y => hC y.2
  have hΦ : Function.Injective Φ := fun a b hab => by
    have h := congrArg (fun z : A => (z : B)) hab
    exact Subtype.ext h
  have hle : Submodule.span K (L : Set C) ≤ N.comap Φ := by
    rw [Submodule.span_le]
    intro F hF
    exact hL F hF
  let ψ : Submodule.span K (L : Set C) →ₗ[K] N :=
    LinearMap.codRestrict N (Φ ∘ₗ (Submodule.span K (L : Set C)).subtype) fun y => hle y.2
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext (hΦ (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hψ

end GlobalTheory.CovolRank

namespace GlobalTheory.CovolRank

theorem card_mul_rkK_chiLat_le_rankW : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E), Even G.2 → Even W.2 → KeepsCusp U G → KeepsCusp U W → GoodW U x V dict G → GoodW U x V dict (G + W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ rankW U (G + W) := by
  classical
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hKG hKW hgG hgGW χ u hdet
  have hsec : ∀ G' : WTZ E, cuspW Xo c U G' ≤ Subalgebra.toSubmodule (secRing Xo c) :=
    fun G' f hf => GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ G' hf)
  have hfin : ∀ G' : WTZ E, GlobalTheory.AllWt.GoodW U x V dict G' → FiniteDimensional c.F (cuspW Xo c U G') := by
    intro G' hg
    obtain ⟨n, ⟨b, _⟩, _⟩ := hg.1.some
    exact Module.Finite.of_basis b
  haveI := hfin G hgG
  haveI := hfin (G + W) hgGW
  obtain ⟨hVs, -⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U G)
  obtain ⟨hVp, hVp'⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U (G + W))
  let uR : secRing Xo c := ⟨u, hsec W u.2⟩
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) uR).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have hc := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA uR
    refine mem_nonZeroDivisors_iff_left.mpr fun y hy => ?_
    apply Subtype.ext
    have h0 : levDet Xo c S u * (y : Rul Xo c) = 0 := by
      rw [← hc]; exact congrArg Subtype.val hy
    exact hdet _ y.2 h0

  let ι : secRing Xo c →ₗ[c.F] Rul Xo c := (secRing Xo c).val.toLinearMap
  let N : Submodule c.F (secRing Xo c) :=
    (cuspW Xo c U G).comap ι ⊓ GlobalTheory.LevDesc.eigen (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) χ
  have key := (GlobalTheory.finrank_le_card_mul_finrank_eigenspace_le S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ uR hdet'
    ⊥ ((cuspW Xo c U G).comap ι) ((cuspW Xo c U (G + W)).comap ι) N
    (fun h y hy => hKG h _ hy)
    (fun h y hy => by
      rw [Submodule.mem_bot] at hy
      subst hy
      rw [zero_mul]; exact Submodule.zero_mem _)
    (fun h y hy => GlobalTheory.SlopeRec.mul_mem_cuspW hG hW hy (hKW h _ u.2))
    (fun y => Submodule.mem_inf)).2
  haveI : FiniteDimensional c.F N := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ Module.finrank c.F N :=
    finrank_span_le_of_map (secRing Xo c) (cuspW Xo c U G) (hsec G) _ N fun F hF =>
      ⟨F.2, fun h => Subtype.ext (hF.2 h)⟩
  have e : rankW U (G + W) = Module.finrank c.F (cuspW Xo c U (G + W)) := by
    rw [rankW, Formalism.HN.rkK, hgGW.2.2, finrank_top]
  calc Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ)
      ≤ Fintype.card S * Module.finrank c.F N := Nat.mul_le_mul_left _ h1
    _ ≤ Module.finrank c.F ((cuspW Xo c U (G + W)).comap ι) := key
    _ ≤ rankW U (G + W) := e ▸ hVp'

end GlobalTheory.CovolRank
