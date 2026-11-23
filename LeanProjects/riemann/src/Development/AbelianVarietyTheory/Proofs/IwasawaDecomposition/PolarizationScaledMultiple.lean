import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem isLB_of_chartPull {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X)) (hc : ⨆ i, A.U i = ⊤) :
    A.IsLB where
  cover := hc
  g_self i := by
    apply unit_ext
    intro x hx
    rw [gm_res (𝟙 X) x _ hx, map_one, a.g x i i hx hx]
    exact gm_self hB (𝟙 X) x (a.le i hx)
  cocycle i j k := by
    apply unit_ext
    intro x hx
    have hi : x ∈ A.U i := hx.1.1
    have hj : x ∈ A.U j := hx.1.2
    have hk : x ∈ A.U k := hx.2
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      a.g x i j hi hj, a.g x j k hj hk, a.g x i k hi hk]
    exact gm_cocycle hB (𝟙 X) x (a.le i hi) (a.le j hj) (a.le k hk)

theorem nsmul_trans (D : EffCartierData X) (n : ℕ) (i j : D.ι) :
    (D.nsmul n).trans i j = D.trans i j ^ n := by
  symm
  apply (D.nsmul n).eq_trans i j
  show resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i ^ n) =
    ((D.trans i j ^ n : Γ(X, D.U i ⊓ D.U j)ˣ) : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j ^ n)
  rw [map_pow, map_pow, D.trans_spec i j, mul_pow, Units.val_pow_eq_pow_val]

theorem gm_lbPow (L : LB X) (k : ℕ) (y : X) (j j' : PUnit → L.ι) (hj : (𝟙 X) y ∈ (lbPow L k).U j)
    (hj' : (𝟙 X) y ∈ (lbPow L k).U j') :
    gm (𝟙 X) y ((lbPow L k).U j ⊓ (lbPow L k).U j') ((lbPow L k).g j j') =
      gm (𝟙 X) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)) ^ k := by
  dsimp only [lbPow, LB.LinComb]
  have hy : (𝟙 X) y ∈ L.wchart (fun _ => 𝟙 X) j ⊓ L.wchart (fun _ => 𝟙 X) j' := ⟨hj, hj'⟩
  have hy' : (𝟙 X) ((𝟙 X) y) ∈ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    ⟨Set.mem_iInter.1 hj PUnit.unit, Set.mem_iInter.1 hj' PUnit.unit⟩
  simp only [Fintype.prod_unique, zpow_natCast]
  refine (map_pow (gm (𝟙 X) y _) _ k).trans ?_
  congr 1
  refine (gm_res (𝟙 X) y _ hy _).trans ((gm_pull (𝟙 X) (𝟙 X) y _ hy' _).trans ?_)
  rw [Category.comp_id]

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

theorem evalZ_comb_mul {O : Type} [CommRing O] (ψ φ : InvFun O) (x y n : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (be : LinearMap.BilinForm ℤ M) :
    (comb (n * x) ψ (n * y) φ).evalZ be = n * (comb x ψ y φ).evalZ be := by
  simp only [InvFun.evalZ, InvFun.eval, comb]
  push_cast
  ring

def scaleChart (Dm : LB X) (D : EffCartierData X) (m n : ℕ) :
    ChartPull (CechPic.tens (lbPow Dm (n * m)) (CechPic.dual (D.nsmul n).lb))
      (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n) (𝟙 X) where
  idx p := fun _ => p
  le _ _ hy := Set.mem_iInter.2 fun _ => hy
  g y p q hp hq := by
    have hp' : (𝟙 X) y ∈ (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n).U (fun _ => p) :=
      Set.mem_iInter.2 fun _ => hp
    have hq' : (𝟙 X) y ∈ (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n).U (fun _ => q) :=
      Set.mem_iInter.2 fun _ => hq
    rw [gm_lbPow _ n y _ _ hp' hq', CechPic.gm_tens _ _ (𝟙 X) y p q hp hq,
      CechPic.gm_tens (lbPow Dm m) (CechPic.dual D.lb) (𝟙 X) y p q hp hq,
      gm_lbPow Dm (n * m) y _ _ hp.1 hq.1, gm_lbPow Dm m y _ _ hp.1 hq.1]
    have e₁ : gm (𝟙 X) y _ ((CechPic.dual (D.nsmul n).lb).g p.2 q.2) = (gm (𝟙 X) y _ (D.trans p.2 q.2) ^ n)⁻¹ := by
      refine (map_inv (gm (𝟙 X) y _) _).trans (congrArg (·⁻¹) ?_)
      refine (congrArg (gm (𝟙 X) y _) (nsmul_trans D n p.2 q.2)).trans ?_
      exact map_pow _ _ _
    have e₂ : gm (𝟙 X) y _ ((CechPic.dual D.lb).g p.2 q.2) = (gm (𝟙 X) y _ (D.trans p.2 q.2))⁻¹ :=
      map_inv (gm (𝟙 X) y _) _
    rw [e₁, e₂, mul_pow, inv_pow, ← pow_mul, mul_comm n m]

theorem scale_pol {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (ψ φ : InvFun (𝓞 E)) (x y m n : ℕ) (BD : EffCartierData Z.X) : 0 < n → IsPol (comb x ψ y φ) m Z BD →
    ∃ BD' : EffCartierData Z.X, IsPol (comb (n * x) ψ (n * y) φ) (n * m) Z BD' := by
  intro hn h
  refine ⟨BD.nsmul n, ?_, ?_⟩
  · intro W _ _ _ hW ϖ hϖ χ t s P hr be hbe hmono
    obtain ⟨k, hk, hI⟩ := h.1 W hW ϖ hϖ χ t s P hr be hbe hmono
    refine ⟨k * n, ?_, ?_⟩
    · rw [evalZ_comb_mul, ← hk]
      push_cast
      ring
    · rw [idlAlong_nsmul, hI, Ideal.span_singleton_pow, pow_mul]
  · have hA : GlobalTheory.IsAmpleLB (polOf Z m BD) := h.2
    have hpow : GlobalTheory.IsAmpleLB (lbPow (polOf Z m BD) n) := (isAmpleLB_basic.2.1 hA.isLB hn).2 hA
    have hc : ⨆ p, (polOf Z (n * m) (BD.nsmul n)).U p = ⊤ := by
      apply top_unique
      intro z _
      have hz : z ∈ (⊤ : Z.X.Opens) := trivial
      rw [← hpow.isLB.cover, TopologicalSpace.Opens.mem_iSup] at hz
      obtain ⟨J, hJ⟩ := hz
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨J PUnit.unit, Set.mem_iInter.1 hJ PUnit.unit⟩
    have hQ : (polOf Z (n * m) (BD.nsmul n)).IsLB :=
      isLB_of_chartPull hpow.isLB (scaleChart (GlobalTheory.FlagMod.detOm Z) BD m n) hc
    exact (isAmpleLB_congr hQ hpow.isLB
      (CechPic.iso_of_chart hpow.isLB (scaleChart (GlobalTheory.FlagMod.detOm Z) BD m n))).2 hpow

end GlobalTheory.TorRef.Scale
