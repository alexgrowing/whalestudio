import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CoordsOfCommonEigenvector
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeMatrices.HodgeMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst
open UpperTheory.Gal.Int.Geo

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

def hOp {k : Type} [Field k] (H : HTower k) (g : H.Γ) (h1 : IsFinite (H.s g)) (h2 : Etale (H.s g)) (a b : ℕ) :
    hodgeH H.q a b →ₗ[k] hodgeH H.q a b :=
  hodgeTrace (s := H.q) (s' := H.s g ≫ H.q) (f := H.s g) rfl a b ∘ₗ hodgePull (s := H.q) (s' := H.s g ≫ H.q) (H.comm g) a b

theorem hOp_cover (hTr : TraceSplit) {k : Type} [Field k] (H : HTower k) (g : H.Γ) (h1 : IsFinite (H.s g)) (h2 : Etale (H.s g))
    {W : Scheme.{0}} (c : W ⟶ H.Z) [IsFinite c] [Etale c] {I : Type} [Fintype I] (σ : I → (W ⟶ H.Y g))
    (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q) (hS : Splits (H.s g) c σ) (a b : ℕ) :
    hodgePull (s := H.q) (s' := c ≫ H.q) rfl a b ∘ₗ hOp H g h1 h2 a b = ∑ i, (1 : ℤ) • hodgePull (hσ i) a b := by
  have hσ' : ∀ i, σ i ≫ (H.s g ≫ H.q) = c ≫ H.q := fun i => by rw [← Category.assoc, hS.1 i]
  ext x
  simp only [hOp, LinearMap.comp_apply, one_smul, LinearMap.sum_apply]
  rw [hTr _ H.q (H.s g) c σ hσ' hS]
  exact Finset.sum_congr rfl fun i _ => hodgePull_comp (H.comm g) (hσ' i) (hσ i) a b x

theorem eig_bc (hBC : HodgeBC) {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (H : HTower k) [IsProper H.q] (H' : HTower k')
    (ι' : H.Γ → H'.Γ) (bc : TowerBC φ H H' id ι') (h1 : ∀ g, IsFinite (H.s g)) (h2 : ∀ g, Etale (H.s g)) (θ' : H'.Γ → k')
    (a b : ℕ) (x : hodgeH H'.q a b) (hx0 : x ≠ 0) (hx : IsHEig H' θ' a b x) {I : Type} [Fintype I] [DecidableEq I]
    (c : Module.Basis I k (hodgeH H.q a b)) :
    ∃ y : I → k', y ≠ 0 ∧ ∀ g, (LinearMap.toMatrix c c (hOp H g (h1 g) (h2 g) a b)).map φ *ᵥ y = θ' (ι' g) • y := by
  obtain ⟨β, hβ1, hβ2⟩ := hBC _ _ φ
  obtain ⟨c', hc'⟩ := hβ1 H.q H'.q bc.z bc.hz a b c
  choose f1 f2 hx' using hx
  refine coords_of_common_eigenvector φ (β H.q H'.q bc.z bc.hz a b) c c' hc' _ (fun g => hOp H' (ι' g) (f1 _) (f2 _) a b) (fun g v => ?_) _ x hx0
    fun g => hx' (ι' g)
  have hp := (bc.hs g).paste_vert bc.hz
  have := h1 g; have := h2 g; have := f1 (ι' g); have := f2 (ι' g)
  have e1 := (hβ2 H.q H'.q bc.z bc.hz _ _ (bc.y g) hp (H.s g) rfl (H'.s (ι' g)) rfl (bc.hs g).w a b).2
  have e2 := (hβ2 H.q H'.q bc.z bc.hz _ _ (bc.y g) hp (H.t g) (H.comm _) (H'.t (ι' g)) (H'.comm _) (bc.ht g) a b).1
  exact (e1 _).trans (congrArg _ (e2 v))

set_option maxHeartbeats 1000000 in
theorem locE_of : LocEOf := by
  classical
  intro hBC hTr hOpE l _ K ιC H H' ι' bc θ θ' a hθ hN hops hcov hocc d ρ hρ
  obtain ⟨b, x, hx0, hx⟩ := hocc
  obtain ⟨F, Φ, hΦ, hj⟩ := hcov (a + b)
  obtain ⟨bV, hbV⟩ := hρ
  have h1 : ∀ g, IsFinite (H.s g) := fun g => (hN.2.2 g).choose_spec.1
  have h2 : ∀ g, Etale (H.s g) := fun g => (hN.2.2 g).choose_spec.2.1
  have : IsProper H.q := GlobalTheory.CommonModel.isProper_of_isProjOver hN.2.1
  let lof := DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l (sch.obj (H.geomZ (Qbar l))) n 0) ((a + b : ℕ) : ℤ)
  let MH : H.Γ → ∀ r : Fin (a + b + 1), Matrix (Fin (F.e r)) (Fin (F.e r)) ↥K.1 := fun g r =>
    LinearMap.toMatrix (F.c r) (F.c r) (hOp H g (h1 g) (h2 g) r (a + b - r))
  have key : ∀ g, ∃ T : EtV (K := K) H.q (a + b) →ₗ[ℚ_[l]] EtV (K := K) H.q (a + b),
      (∀ v, hop l H (Qbar l) g (lof v) = lof (T v)) ∧
      (LinearMap.toMatrix F.b F.b T).map (algebraMap ℚ_[l] ℂ_[l]) * Φ = Φ * (blockDiagonal' (MH g)).map (toC K) := by
    intro g
    obtain ⟨W, c, G, _, _, act, I, _, σ, hσ, hG, hS, F', Φ', np, nt⟩ := hj g
    have := h1 g; have := h2 g; have := hG.1; have := hG.2.1
    obtain ⟨hinj, T, hT1, hT2⟩ := hOpE l K H g W c G act I σ hσ hG hS (hops g) (a + b)
    exact ⟨T, hT1, CrystallineSemistableComparison.Jump.corr_ht F F' Φ Φ' rfl hσ (fun _ => 1) np nt hinj T
      (fun r => hOp H g (h1 g) (h2 g) r (a + b - r)) (hT2.trans (Finset.sum_congr rfl fun i _ => (one_smul _ _).symm))
      fun r => hOp_cover hTr H g (h1 g) (h2 g) c σ hσ hS r (a + b - r)⟩
  choose TV hTV hint using key
  let r₀ : Fin (a + b + 1) := ⟨a, by omega⟩
  have hex : ∀ m, m = b → ∃ x : hodgeH H'.q a m, x ≠ 0 ∧ IsHEig H' θ' a m x := by rintro _ rfl; exact ⟨x, hx0, hx⟩
  obtain ⟨x', hx0', hx'⟩ := hex (a + b - a) (by omega)
  obtain ⟨y', hy0, hy'⟩ := eig_bc hBC _ H H' ι' bc h1 h2 θ' a (a + b - a) x' hx0' hx' (F.c r₀)
  let i := algebraMap ↥K.1 (Qbar l)
  have hy : ∀ g, (MH g r₀).map i *ᵥ (fun p => ιC.symm (y' p)) = θ g • fun p => ιC.symm (y' p) := fun g => funext fun p => by
    apply ιC.injective
    have := congrFun (hy' g) p
    rw [hθ] at this
    simpa [mulVec, dotProduct, MH, i] using this
  obtain ⟨Y, hY1, hY2, hY3⟩ := block_eig (fun r => (0 : Matrix (Fin (F.e r)) (Fin (F.e r)) (Qbar l))) r₀
    (fun p => ιC.symm (y' p)) 0 (by simp)
  obtain ⟨E, hE, hEc⟩ := exists_emb (L := Qbar l) F.b lof (DirectSum.of_injective _)
  obtain ⟨⟨Ψ, -, hΨ⟩, hΦ2⟩ := hΦ
  have hmm : ∀ {m n : Type} (M : Matrix m n ℚ_[l]),
      (M.map (algebraMap ℚ_[l] (Qbar l))).map (algebraMap (Qbar l) ℂ_[l]) = M.map (algebraMap ℚ_[l] ℂ_[l]) := fun M => by
    ext p q; exact (IsScalarTower.algebraMap_apply ℚ_[l] (Qbar l) ℂ_[l] (M p q)).symm
  obtain ⟨S, z, hz, hz'⟩ := occE (k := Qbar l) (C := ℂ_[l]) (Γ := ↥(GK K)) (fun σ => Formalism.Per.σC (σ : GQ l))
    (fun σ => (LinearMap.toMatrix F.b F.b (etAct H.q (a + b) σ)).map (algebraMap ℚ_[l] (Qbar l))) Φ
    (fun u v h => by
      have := congrArg (Ψ *ᵥ ·) h
      simpa only [mulVec_mulVec, hΨ, one_mulVec] using this)
    (fun σ j => chiPow (σ : GQ l) (-((j.1 : ℕ) : ℤ))) (fun σ => by rw [hmm]; exact hΦ2 σ)
    (fun g => (LinearMap.toMatrix F.b F.b (TV g)).map (algebraMap ℚ_[l] (Qbar l)))
    (fun g => blockDiagonal' fun r => (MH g r).map i)
    (fun g => by
      rw [hmm, hint g]
      congr 1
      rw [← blockDiagonal'_map _ _ (map_zero i)]
      rfl)
    θ Y (fun h0 => hy0 (funext fun p => by
      have := (hY1 p).symm.trans (congrFun h0 _)
      simpa using this))
    (fun σ => chiPow (σ : GQ l) (-(a : ℤ))) (fun σ p hp => by rw [hY2 p hp])
    (fun g => hY3 _ _ (hy g)) E hE (fun g => (hop l H (Qbar l) g).baseChange (Qbar l)) (fun g => hEc _ _ (hTV g))
    (fun σ => galV l H (Qbar l) (Qbar l) (IntermediateField.fixingSubgroupEquiv K.1 σ))
    (fun σ => hEc _ _ fun v => DirectSum.lmap_lof _ _ _) _ rfl bV _ fun σ => hbV _
  refine ⟨S, z, hz, fun σ hS => hz' σ fun t ht => ?_⟩
  exact (GlobalTheory.RingBasics.σC_coe _ t).trans (congrArg _ (hS t ht))

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
