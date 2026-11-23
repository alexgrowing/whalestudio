import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellOfIsFrameMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

theorem frameVector_isCombination_tangentBasis_flagCover_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}
    (X : GlobalTheory.FlagMod.FlagCover Y) (U : Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (h1 : ∀ i, IsTanAtG Y.t (LogKS.chart U) (v i))
    (h2 : ∀ w', IsTanAtG Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (LogKS.chart U) v cf w')
    (h3 : ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (Y.t.act.act a).left))
    (k : X.F.J) (S : Type) [CommRing S] (z' : Sp S ⟶ X.YY) (x : Sp S ⟶ Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ z' ⁻¹ᵁ X.F.U k) (hx : z' ≫ X.π = x) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG Y.t x (fun j => spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i)
        (tv (X.F.vecAt k z' hk hx σ i)).left := by
  classical
  subst hx
  have hxψ : spMap (ev (z' ≫ X.π) U.1 hU) ≫ LogKS.chart U = z' ≫ X.π := GlobalTheory.FlagMod.spMap_ev _ U.2 hU
  obtain ⟨b1, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (ev (z' ≫ X.π) U.1 hU) (LogKS.chart U) n v h1 h2
  rw [hxψ] at b1 b2

  set ψ := ev (z' ≫ X.π) U.1 hU with hψ
  let φ : c.F →+* S := (ev ((z' ≫ X.π) ≫ Y.s) ⊤ le_top).comp (toΓ c.F)
  have hφ : z' ≫ X.π ≫ Y.s = spMap φ := by
    rw [GlobalTheory.FlagMod.spMap_ev_top, Category.assoc]
  have hφψ : ∀ r : c.F, ψ (algX Y.s U.1 r) = φ r := fun r =>
    GlobalTheory.FlagMod.ev_appLE (z' ≫ X.π) Y.s (by simp) hU le_top (toΓ c.F r)
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z' ≫ X.π) Y.t.G := fun m => GlobalTheory.LieMet.tanOf (b1 m)
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)) = φ (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H Y.X Y.t _ S ψ (LogKS.chart U) _ hxψ).2 n v _ _ (h3 a τ j)
    have e1 : (fun i => ψ ((Pi.single (e ⟨τ, j⟩) (algX Y.s U.1 (embK c τ a)) : Fin n → Γ(Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (φ (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [Pi.single_apply, hi]
    rw [e1] at h
    have e2 : spMap (dualMap ψ) ≫ v (e ⟨τ, j⟩) ≫ (Y.t.act.act a).left =
        (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  letI : Algebra c.F S := φ.toAlgebra
  have hs := GlobalTheory.FlagEmb.EigSpread.splits (E := E) c
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act) (embK c z.1) (V (e z)) :=
    fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  have key : ∀ σ i, ∃ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • V (e ⟨σ, j⟩) = X.F.vecAt k z' hk rfl σ i :=
    fun σ i => (GlobalTheory.FlagEmb.EigSpread.block_basis hs (fun z => V (e z)) hu hb' σ _
      (fun a => GlobalTheory.VarFlag.actR_vecAt X φ z' k hk hφ σ i a)).exists
  choose C hC using key
  refine ⟨fun σ => Matrix.of fun i j => C σ i j, fun σ i => ?_⟩
  exact (GlobalTheory.LieMet.isComb_iff (fun j => V (e ⟨σ, j⟩)) (C σ i) _).2 (hC σ i).symm

theorem isCombAtG_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx
  exact frameVector_isCombination_tangentBasis_flagCover_point TF.X U e v hv.1 hv.2.1 hv.2.2 k S (z ≫ inc₀ TF.X Z) (z ≫ toBase TF Z) hU hk hx

end GlobalTheory.LogPole
