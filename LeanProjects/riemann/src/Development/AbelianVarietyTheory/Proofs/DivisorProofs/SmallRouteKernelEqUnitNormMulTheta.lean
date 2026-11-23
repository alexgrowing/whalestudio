import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKernel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram blkU conjU xiV xiV₁ boxB alpha beta)
open GlobalTheory.RouteSeesaw
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem end_finsupp_sum_apply {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    A (fun x => Θ.sum fun d c => c * f d x) w = Θ.sum fun d c => c * A (f d) w := by
  have e : (fun x => Θ.sum fun d c => c * f d x) = ∑ d ∈ Θ.support, Θ d • f d := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (m + n) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), add_comm, pow_add, mul_assoc, hm, mul_one]

theorem data_theta_small {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ'.support,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vT_is t (i : ℕ) (j : ℕ) i.2.le j.2).2.theta
  have v2 := (ρ.vX_is (i : ℕ) (j : ℕ) i.2 j.2.le).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

set_option maxHeartbeats 1000000 in

theorem seesaw_swapped {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin (spW₁ G i j).rank)
    (e₂ : Fin S'.rank ≃ Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank)
    (hT' : T'.gramᵀ = -((spW₁ G i j).gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ.submatrix e₂ e₂))
    (ω : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ))
    (hω : IsWeilDatumO W.ψ S' T' (alpha G t i j / beta G i j) (alpha G t i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂)
    (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt _ u).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt _ (GlobalTheory.SquareComm.blk _ _ (g, g₁))⁻¹).submatrix e₂ e₂)ᵀ) :
    W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
      xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') (fun x => box2 f₁ (GlobalTheory.SeesawSmall.adjFn (spW₁ G i j) (spV₁ G i j) f₂)
        (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) ((spW₁ G i j).gram.map (incA D)) :
          Matrix (Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank) (Fin (spW₁ G i j).rank) (AE D))) 0 := by
  have r₁ : T'.rank = (spW₁ G i j).rank := by simpa using Fintype.card_congr e₁
  have r₂ : S'.rank = (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank := by simpa using Fintype.card_congr e₂
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (spW₁ G i j)
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j) (alpha G t i j / beta G i j)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT hω.hecS (r₁ ▸ hω.resT) (r₂ ▸ hω.resS)
  obtain ⟨hbox, hker⟩ := GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωA hA f₁ f₂ hf₁ hf₂
  rw [hker g u g₁, GlobalTheory.BigSeesaw.swap_eq _ _ S' T' e₁ e₂ hT' hS' hA hω hbox u _ g' h' hh hg]
  rfl

set_option maxHeartbeats 1000000 in

theorem kerSmall_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv Φ hΦ
  refine ⟨fun x => xiV G i j x.1 * xiV₁ G t i j x.2, fun x => ?_, fun g u => ?_⟩
  · simp only [xiV, xiV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.flatDet, norm_mul, Circle.norm_coe, mul_one]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D Bs hTr.base _ Γ.V' _ _ hTr.geo.hV'
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V'.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))) Γ.V' Γ.W _ _ _ _
    hTr.geo.hV' hTr.geo.hW eA eB
    Γ.M' hTr.geo.hM' X.α (X.α / X.β) hTr.chars.heckeα (isHecke_div hTr.chars.heckeα hTr.chars.heckeβ) hTr.chars.resα
    (resEtaPow_div hTr.chars.resα hTr.chars.resβ) om' hTr.weil'
  rw [h.ψ, h.α, h.β] at hω
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))) Γ.V'.J Γ.W.J (-1) eA eB
    (conjU (spW₁ G i j) (-1) h.JW₁ u) (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M'.co Bs.ψ Φ =
      fun w => Θ'.sum fun d c => c * boxB e d w := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    rfl
  refine Eq.trans ?_ (congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z)
    (end_finsupp_sum_apply (ω (g', h')) Θ' (boxB e) 0).symm)
  rw [kerSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := data_theta_small W B ρ t i j hΘ d hd
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ' : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))).gramᵀ =
      -((spW₁ G i j).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [← eA]
    show Γ.V'.J = -(spW₁ G i j).gram
    rw [h.JW₁, neg_one_smul]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e1.trans ?_
    rw [hJ', smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ0, neg_one_smul]
  have k := seesaw_swapped hL W t i j
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0)))
    (Equiv.refl (Fin (spW₁ G i j).rank)) e₂ hT' hS' ω hω d.1.2 d.2 t1 t2 g u g₁
    g' h' hh' (by
      rw [hg', ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine (congrArg (fun z => Θ' d * z) k).trans ?_
  rw [mul_left_comm]
  refine congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * (Θ' d * ω (g', h') f 0)) ?_
  funext x
  exact (GlobalTheory.SeesawSmall.thetaSquareProductRouteB_eq_externalProduct e d x).symm

end GlobalTheory.SmallKernel

end
