import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscFlatEquiFB

variable {D : D7} {σ : ℕ}

abbrev bx (B : BesL D σ) : Mx D B.V.rank (σ + 1) := xLast B.d (vecB B.o B.ζ)

theorem bx_cs (B : BesL D σ) (i : Fin B.V.rank) (j : Fin σ) : bx B i (Fin.castSucc j) = B.d.jX i j := by
  simp [bx, xLast, Fin.snoc_castSucc]

theorem bx_last (B : BesL D σ) (i : Fin B.V.rank) : bx B i (Fin.last σ) = (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i := by
  simp [bx, xLast, Fin.snoc_last]

theorem mul_bx_cs (B : BesL D σ) {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) (j : Fin σ) :
    (M ⬝ bx B) i (Fin.castSucc j) = (M ⬝ B.d.jX) i j := by
  simp only [Matrix.mul_apply, bx_cs]

theorem mul_bx_last (B : BesL D σ) {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) :
    (M ⬝ bx B) i (Fin.last σ) = (M *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, bx_last]

theorem embA_bx (B : BesL D σ) (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ bx B = bx B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_bx_last, bx_last, embA_apply, Matrix.mulVec_mulVec, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec,
      Matrix.mulVec_mulVec (ratV B.ζ), show rat B.o.iB = B.o.jB from rfl, B.o.emb_jB, mt_one, Matrix.mul_one]
  · rw [mul_bx_cs, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, bx_cs]

theorem pX_bx (B : BesL D σ) (i : Fin σ) (k : Fin (σ + 1)) : (B.d.pX ⬝ bx B) i k = if k = Fin.castSucc i then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [mul_bx_last, Matrix.mulVec_mulVec, B.d.pX_j0, Matrix.zero_mulVec, if_neg (Fin.castSucc_lt_last i).ne']
    rfl
  · rw [mul_bx_cs, B.d.pX_jX, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e).symm)]

theorem pX_bx_mul (B : BesL D σ) (U : Mx D (σ + 1) (σ + 1)) (i : Fin σ) (k : Fin (σ + 1)) :
    (B.d.pX ⬝ (bx B ⬝ U)) i k = U (Fin.castSucc i) k := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [pX_bx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem simpleSum_eq_upSum (B : BesL D σ) {n : GA D B.V} {U : Mx D (σ + 1) (σ + 1)} (e : mt B.V n ⬝ bx B = bx B ⬝ U) :
    simpleSum B.d (vecB B.o B.ζ) n = upSum U := by
  have hb : blockX B.d n = fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j) := by
    ext i j
    have h := mul_bx_cs B (B.d.pX ⬝ mt B.V n) i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [blockX, ← pX_bx_mul B U i, ← e, h]
  have hc : coefX B.d (vecB B.o B.ζ) n = fun i => U (Fin.castSucc i) (Fin.last σ) := by
    ext i
    have h := mul_bx_last B (B.d.pX ⬝ mt B.V n) i
    rw [Matrix.mul_assoc] at h
    rw [coefX, ← pX_bx_mul B U i, ← e, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [simpleSum, hb, hc, GlobalTheory.Unf.FB.UniRad.upSum_succ]

theorem psiBes_eq_psiUni (B : BesL D σ) (ψ : AddChar (AF D.host.F) ℂ) {n : GA D B.V} (u : GL (Fin (σ + 1)) (AE D))
    (e : mt B.V n ⬝ bx B = bx B ⬝ u.1) : psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u := by
  rw [psiBes, simpleSum_eq_upSum B e, map_one, one_mul, psiUni]

theorem flagN_bx (B : BesL D σ) (n : GA D B.V) (hn : n ∈ flagN B.d) :
    ∃ γ ∈ UX D (σ + 1), mt B.V n ⬝ bx B = bx B ⬝ γ.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine (GlobalTheory.Unf.FB.snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V _)).2 ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

end GlobalTheory.AscFlatEquiFB

namespace GlobalTheory.AscFlatEquiFB

open GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def bxRat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem rat_bxRat (B : BesL D σ) : rat (bxRat B) = bx B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [bxRat, bx, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [bxRat, bx, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_bxRat (B : BesL D σ) :
    (bxRat B)ᴴ * B.V.gram * bxRat B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [bxRat, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem linearIndependent_bxRat (B : BesL D σ) : LinearIndependent D.host.E (bxRat B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : bxRat B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * bxRat B = selFirst D σ := by
    rw [bxRat, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_bxRat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

end GlobalTheory.AscFlatEquiFB

namespace GlobalTheory.AscFlatEquiFB

open GlobalTheory.Unf.FB

variable {D : D7}

theorem evalAt_eq (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (om₁ : Om J.W₀ B.V) (hom₁ : IsWeilDatumO ψ J.W₀ B.V s.χV s.χW om₁) (Ψ : WO J.W B.V → ℂ) (hΨ : IsThetaFunO ψ J.W B.V Ψ)
    (g : GA D J.W₀) (n : GA D B.V) (hn : n ∈ flagN B.d) (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)) :
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 =
        s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  have hS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om₁ s.weil hom₁ s.vS.μ s.vS.𝓕 s.vS.covol
  have hT := GlobalTheory.T.mixedModelFormulas_wittTarget D ψ J.W₀ B.V B.V₀ σ B.d s.χV s.χW om₁ s.om₀ hom₁ s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol
  have hV := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ
  have hΨk := s.weil.om_pres (1, n * embA B.d B.o h) Ψ hΨ
  simp only [evalAt]
  rw [show s.om (J.d.emb0 g, n * embA B.d B.o h) = s.om (J.d.emb0 g, 1) * s.om (1, n * embA B.d B.o h) by
    rw [← map_mul]; simp]
  rw [Module.End.mul_apply, (hS _ hΨk).core, (hS _ hΨ).target]
  have hFt := hV (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x)
  generalize J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) = F at hFt ⊢
  have hF1 := hom₁.om_pres (1, B.d.emb0 (B.o.emb (h, 1))) F hFt
  have hF2 := hom₁.om_pres (1, n) _ hF1
  rw [show om₁ (1, n * embA B.d B.o h) = om₁ (1, n) * om₁ (1, B.d.emb0 (B.o.emb (h, 1))) by
    rw [← map_mul, embA_apply]; simp]
  rw [Module.End.mul_apply, (hT _ hF2).source, Matrix.mul_zero,
    mixT_zero_flagN B.d ψ s.χV om₁ s.om₀ s.vT.μ s.vT.𝓕 hom₁.om_pres hT _ hF1 n hn, (hT _ hFt).core,
    show s.om₀ (g, B.o.emb (h, 1)) = s.om₀ (g, 1) * s.om₀ (1, B.o.emb (h, 1)) by rw [← map_mul]; simp,
    Module.End.mul_apply]

theorem flFB_flagN (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (om₁ : Om J.W₀ B.V) (hom₁ : IsWeilDatumO ψ J.W₀ B.V s.χV s.χW om₁) (Ψ : WO J.W B.V → ℂ) (hΨ : IsThetaFunO ψ J.W B.V Ψ)
    (n : GA D B.V) (hn : n ∈ flagN B.d) :
    flFB s (s.om (1, n) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flFB s Ψ := by
  obtain ⟨γ, hγ, hnγ⟩ := flagN_bx B n hn
  have hψ : psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ γ := psiBes_eq_psiUni B ψ γ hnγ
  have h1 : mt B.V n⁻¹ ⬝ (bx B ⬝ γ.1) = bx B := by
    rw [← hnγ, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hev : ∀ M : Mx D B.V.rank (σ + 1), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n) Ψ) M 0 =
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ M) 0 := by
    intro M
    have := evalAt_eq ψ σ J B s om₁ hom₁ Ψ hΨ 1 n hn 1 M
    simp only [map_one, mul_one] at this
    rw [this, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  simp only [flFB, flatS, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, hev]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨γ, hγ⟩ : UX D (σ + 1))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hm : mt B.V n⁻¹ ⬝ (bx B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1) = bx B ⬝ u.1.1 := by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (bx B), h1]
  change star (psiUni ψ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D))) *
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ (bx B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1)) 0 w = _
  rw [hm, Subgroup.coe_mul, GlobalTheory.Unf.FB.UnipAct.psiUni_mul_of_mem ψ J.d hγ u.2, star_mul', hψ, mul_assoc]

end GlobalTheory.AscFlatEquiFB

namespace GlobalTheory.AscFlatEquiFB

open GlobalTheory.Unf.FB GlobalTheory.Unf.FlatComm

variable {D : D7}

set_option maxHeartbeats 600000 in

theorem flFB_om (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (om₁ : Om J.W₀ B.V) (hom₁ : IsWeilDatumO ψ J.W₀ B.V s.χV s.χW om₁) (Ψ : WO J.W B.V → ℂ) (hΨ : IsThetaFunO ψ J.W B.V Ψ)
    (g : GA D J.W₀) (h : GA D B.A) :
    flFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flFB s Ψ) := by
  have hx := linearIndependent_bxRat B
  have hx0 := rat_bxRat B
  set x := bxRat B
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D (σ + 1)
  haveI : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := sFinite_of_haar k1 k2 _ s.vU.unit.1
  have hstd := s.weil.std
  set p : GA D J.W × GA D B.V := (J.d.emb0 g, embA B.d B.o h) with hp
  let F : (WO J.W B.V → ℂ) → UX D (σ + 1) → WO J.W₀ B.V₀ → ℂ := fun Φ u w =>
    flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) 0 Φ w u
  have hF : ∀ Φ u, F Φ u = star (psiUni ψ u.1) •
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (bx B ⬝ u.1.1) 0 := fun Φ u => by
    rw [← hx0]; rfl
  have hflat : ∀ Φ, flFB s Φ = fun w => ∫ u, F Φ u w ∂s.vU.ν := fun Φ => by
    simp only [F, hx0]; rfl
  have key : ∀ u, s.om₀ (g, B.o.emb (h, 1)) (F Ψ u) = F (s.om p Ψ) u := fun u => by
    have e := evalAt_eq ψ σ J B s om₁ hom₁ Ψ hΨ g 1 (one_mem _) h (bx B ⬝ u.1.1)
    rw [one_mul, ← map_inv, ← Matrix.mul_assoc, embA_bx] at e
    rw [hF, hF, map_smul, ← e]
  have hv : Continuous (fun u : UX D (σ + 1) => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hc : ∀ q, Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => F (s.om q Ψ) r.1 r.2 := fun q => by
    have c := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2
    have c2 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ =>
        (q, (rat x : Mx D B.V.rank (σ + 1)) ⬝ r.1.1.1, (0 : Mx D J.W₀.rank σ), r.2) :=
      continuous_const.prodMk ((continuous_const.matrix_mul (hv.comp continuous_fst)).prodMk
        (continuous_const.prodMk continuous_snd))
    have c3 := c.comp c2
    have c4 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => star (psiUni ψ r.1.1) :=
      ((continuous_psiUni hstd.1.1 _).comp continuous_fst).star
    have c5 := c4.mul c3
    simp only [Function.comp_def] at c5
    exact c5
  have h1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  obtain ⟨M, hM, hb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil s.vU x hx Ψ hΨ
    {1, p} (Set.toFinite _).isCompact
  have hth : ∀ u, IsThetaFunO ψ J.W₀ B.V₀ (F Ψ u) := fun u => by
    obtain ⟨mS, mT⟩ := GlobalTheory.MixValues.mixed_values D ψ hstd
    rw [hF]
    exact GlobalTheory.OrientedHeis.theta_smul _ (mT _ _ _ _ B.d _ _ s.vT.covol _ (mS _ _ _ _ J.d _ _ s.vS.covol _ hΨ _) _)
  have main := GlobalTheory.CommInt.om_integral_comm D ψ J.W₀ B.V₀ _ _ s.om₀ s.weil₀ (UX D (σ + 1)) s.vU.ν (F Ψ) (g, B.o.emb (h, 1)) M hth
    (by have := hc 1; rwa [h1] at this) (by simp only [key]; exact hc p) hM
    (fun u w => ⟨by have := hb 1 (by simp) 0 w u; rwa [h1] at this, by rw [key]; exact hb p (by simp) 0 w u⟩)
    (GlobalTheory.Unf.Flat.flatLaw D ψ hstd J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT s.vU x hx 0 Ψ hΨ).2
  rw [hflat, hflat]
  funext w
  rw [main w]
  simp only [key]

theorem flFB_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ Ψ, IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀), ∀ n ∈ flagN B.d, ∀ h : GA D B.A, flFB s (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • s.om₀ (g, B.o.emb (h, 1)) (flFB s Ψ) := by
  intro D ψ σ J B s Ψ hΨ g n hn h
  obtain ⟨om₁, hom₁⟩ := (GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D) ψ _ _ _ _ s.om s.weil).1 J.W₀ (σ + 1) J.d
  have e : s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ = s.om (1, n) (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, flFB_flagN ψ σ J B s om₁ hom₁ _ (s.weil.om_pres _ _ hΨ) n hn, flFB_om ψ σ J B s om₁ hom₁ Ψ hΨ g h]

end GlobalTheory.AscFlatEquiFB

end
