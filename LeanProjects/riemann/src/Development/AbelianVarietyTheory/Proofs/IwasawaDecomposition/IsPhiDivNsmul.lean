import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolScale

theorem eval_comb_mul {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (ψ φ : InvFun O) (a b u : ℕ) (B : X → X → ℝ) :
    (comb (u * a) ψ (u * b) φ).eval X B = u * (comb a ψ b φ).eval X B := by
  simp only [InvFun.eval, comb]
  push_cast
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTwInv_comb {ψ φ : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hφ : IsTwInv H φ) (a b : ℕ) :
    IsTwInv H (comb a ψ b φ) := fun σ hσ n B => by
  simp only [comb]
  rw [hψ σ hσ n B, hφ σ hσ n B]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isPhiDiv_nsmul {ψ φ : InvFun (𝓞 E)} {a b : ℕ} {Z : Model Xo c β} {BD : EffCartierData Z.X}
    (h : IsPhiDiv (comb a ψ b φ) Z BD) (u : ℕ) : IsPhiDiv (comb (u * a) ψ (u * b) φ) Z (BD.nsmul u) := by
  intro W _ _ _ hW ϖ hϖ χ t ht P hχ be hbe hmon
  obtain ⟨n, hn, hI⟩ := h W hW ϖ hϖ χ t ht P hχ be hbe hmon
  refine ⟨u * n, ?_, ?_⟩
  · rw [InvFun.evalZ, eval_comb_mul, ← InvFun.evalZ, ← hn]
    push_cast
    ring
  · obtain ⟨i, hi⟩ := BD.exists_mem (χ (closedPoint W))
    unfold idlAlong at hI ⊢
    rw [BD.stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton] at hI
    rw [(BD.nsmul u).stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton]
    change Ideal.span {(Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ _ _ hi).hom (BD.f i ^ u))} = _
    rw [map_pow, map_pow, ← Ideal.span_singleton_pow, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm]

theorem isPol_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : GMod Xo c) (ψ φ : InvFun (𝓞 E)) (a b u m : ℕ) (BD BD' : EffCartierData Z.X),
    IsTwInv H ψ → IsTwInv H φ → 0 < u → IsPol (comb a ψ b φ) m Z BD → IsPhiDiv (comb (u * a) ψ (u * b) φ) Z BD' →
    IsPol (comb (u * a) ψ (u * b) φ) (u * m) Z BD' := by
  intro E _ _ _ H D l Xo c Z ψ φ a b u m BD BD' hψ hφ hu hP hB'
  obtain ⟨hβ, hft, -⟩ := CoeffRings.coeff_isDedFrac E H l c
  have hI : BD'.idealSheaf = (BD.nsmul u).idealSheaf := by
    have := PolDiv.idealSheaf_eq_comap E H D l l Xo Xo c c _ _ _ _ Z Z (BD.nsmul u) BD' (comb (u * a) ψ (u * b) φ)
      (RingEquiv.refl _) (𝟙 _) ((TwMap.reflEquiv _ _ _).symm (ObjComp.sabMapId _)) hβ hβ hft
      (isTwInv_comb hψ hφ _ _) rfl (isPhiDiv_nsmul hP.1 u) hB' (𝟙 _) (by simp)
    rwa [Scheme.IdealSheafData.comap_id] at this
  refine ⟨hB', ?_⟩
  have hA := hP.2
  have hd : (FlagMod.detOm Z).IsLB := CechPic.isLB_dual (PolFin.isLB_detLie_of_polOf hA.isLB)
  have cl : ∀ (k : ℕ) (B : EffCartierData Z.X) (h : (polOf Z k B).IsLB),
      CechPic.cls _ h = k • CechPic.cls _ hd + -CechPic.cls _ B.isLB_lb := fun k B h => by
    have e := CechPic.cls_tens (isLB_lbPow hd k) (CechPic.isLB_dual B.isLB_lb) h
    refine e.trans ?_
    rw [CechPic.cls_lbPow hd, CechPic.cls_dual B.isLB_lb]
  have hBc : CechPic.cls _ BD'.isLB_lb = u • CechPic.cls _ BD.isLB_lb := by
    rw [(CechPic.cls_eq_iff BD'.isLB_lb (BD.nsmul u).isLB_lb).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _ hI),
      (CechPic.cls_eq_iff (BD.nsmul u).isLB_lb (isLB_lbPow BD.isLB_lb u)).2 (BD.lbIso_nsmul u), CechPic.cls_lbPow BD.isLB_lb]
  have hP' : (polOf Z (u * m) BD').IsLB := CechPic.isLB_tens (isLB_lbPow hd _) (CechPic.isLB_dual BD'.isLB_lb)
  have hPu := (isAmpleLB_pow_iff hA.isLB hu).2 hA
  refine hPu.of_lbIso hP' ((CechPic.cls_eq_iff hP' (isLB_lbPow hA.isLB u)).1 ?_)
  rw [cl _ _ hP', CechPic.cls_lbPow hA.isLB, cl _ _ hA.isLB, hBc, smul_add, smul_neg, mul_smul]

end GlobalTheory.PolScale
