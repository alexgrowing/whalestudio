import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem intAf_mul' {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem pairA_mul' (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl

theorem mul_ePl {v : GlobalTheory.FinPl.Pl D} {α : Af D.host.F} (h : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * GlobalTheory.FinPlLoc.ePl D (· = v) = α := by
  classical
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (α * _) = evalV D.host.F w α
  rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · rw [if_pos hw, mul_one]
  · rw [if_neg hw, mul_zero, h w hw]

theorem smul_mem_homLat {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    {c : D.host.E} (hc : c ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹)
    {X : Matrix (Fin m) (Fin n) D.host.E} (hX : X ∈ 𝔪 • homLat Λ Λ') : c • X ∈ homLat Λ Λ' := by
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun x y hx hy => ?_)
  · have h1 : c * algebraMap (𝓞 D.host.E) D.host.E r ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hne]
      exact FractionalIdeal.mul_mem_mul hc (FractionalIdeal.mem_coeIdeal_of_mem _ hr)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have e : c • (r • Y) = o • Y := by
      rw [← algebraMap_smul D.host.E r Y, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact Submodule.smul_mem _ o hY
  · rw [smul_add]; exact add_mem hx hy

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {v : GlobalTheory.FinPl.Pl D}
    {z : AE D} (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) {x : Mx D m n}
    (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : z • x ∈ hatMx (homLat Λ Λ') := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, X, hX, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨α * β, intAf_mul' hα hβ, c • X, smul_mem_homLat h𝔪 hc hX, ?_⟩
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul']
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha

theorem val_le_one_of_mem_inv {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {a : D.host.E} (ha : a ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹) :
    Valued.v (algebraMap D.host.E (Kw Q) a) ≤ 1 := by
  obtain ⟨m, hm, hmQ⟩ := Set.not_subset.1 hQ
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h1 : a * algebraMap (𝓞 D.host.E) D.host.E m ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [← inv_mul_cancel₀ hne]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  rw [show Valued.v (algebraMap D.host.E (Kw Q) a) = Q.valuation D.host.E a from
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q a]
  have hm1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E m) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (Q.intValuation_le_one m)
      (not_lt.1 fun h => hmQ ((Q.intValuation_lt_one_iff_mem m).1 h))
  have ho1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤ 1 := Q.valuation_le_one o
  rw [ho, map_mul, hm1, mul_one] at ho1
  exact ho1

end GlobalTheory.DepthMap

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem val_cpt_le_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {v : GlobalTheory.FinPl.Pl D} {z : AE D}
    (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) :
    Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D z)) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    have e : pairA D.host.F 0 α ⊗ₜ[D.host.F] c =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c := by
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      show GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (incA D c)) = algebraMap D.host.E (Kw Q) c from Comparison₂.cpt_tmul Q c]
    have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
    exact mul_le_one' (((GlobalTheory.StdFrames.comp_toAd D).int _).1 hi Q) (val_le_one_of_mem_inv h𝔪 hQ hc)
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add, RingHom.map_add]; exact Valuation.map_add_le _ hx hy
  | neg x _ hx => rw [RingHom.map_neg, RingHom.map_neg, Valuation.map_neg]; exact hx

theorem cpt_idemSum_of_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P, Finset.sum_eq_single Q]
  · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
  · intro b hb hbQ; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q (Ne.symm hbQ)
  · intro h; exact absurd hQ h

theorem cpt_idemSum_of_not_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∉ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P]
  exact Finset.sum_eq_zero fun b hb => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q fun h => hQ (h ▸ hb)

theorem modul_not_le {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : Q ∉ P.W0) : ¬ P.modul sc ≤ Q.asIdeal := by
  classical
  intro h
  unfold Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le hle
  have h2 : P.w v = Q := HeightOneSpectrum.ext ((P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1)
  exact hQ (h2 ▸ Finset.mem_image_of_mem P.w hv)

end GlobalTheory.DepthMap
set_option maxHeartbeats 800000 in

open GlobalTheory.DepthMap in

theorem GlobalTheory.DepthMap.smul_mulVec_mem_latV : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  intro D hD T L μ0 hL sc G W M hM i hi u hu v hv y hy s hs
  classical
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  have P7 := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hm0 : G.pl.modul sc ≠ ⊥ := G.pl.modul_ne_bot sc
  have hmF : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hm0
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨-, -, -, -, -, P6, P7'⟩ := P7
  have key : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
        (G.Λ (.grid i 0) : Set _) (· = v) := by
    intro z hz
    obtain ⟨g, hg, g', hg', hid, hiff⟩ := P6 _ (inv_ne_zero hmF)
    have hzA : z ∈ idAt D (· = v) := ((hiff z).1 hz).1
    have hsplit : z • u = (e * z) • u + ((1 - e) * z) • u := by
      rw [← add_smul]; congr 1; ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
      have h2 := smul_mem_hatMx hm0 hz h1
      have h3 : (e * z) • u = z • (e • u) := by rw [mul_comm, mul_smul]
      rw [h3]
      have hhalf : IsHalf e (z • (e • u)) := fun a b => by
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_comm e z, mul_assoc, ← mul_assoc e e, GlobalTheory.PlaceDatum.idemSum_mul_self he]
      have h4 := GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hD hL G) hhalf h2
      refine (GlobalTheory.AscFinWit.mem_latO_at (fun a b => ?_)).1 h4
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hzA
    · have hint : finPart D ((1 - e) * z) ∈ intAE D := by
        refine ((GlobalTheory.StdFrames.comp_toAd D).int _).2 fun Q => ?_
        show Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D ((1 - e) * z))) ≤ 1
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
        by_cases hQ : Q ∈ G.pl.W0
        · rw [cpt_idemSum_of_mem he hQ, sub_self, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hc := cpt_idemSum_of_not_mem he hQ
          have hb := val_cpt_le_one hm0 (modul_not_le G.pl sc hQ) hz
          simp only [hc, sub_zero, one_mul]
          exact hb
      have hI : (1 - e) * z ∈ intAt D (· = v) := by
        refine ⟨?_, hint⟩
        exact Ideal.mul_mem_left _ _ hzA
      have hS := GlobalTheory.RowInt.smul_mem_latO_at D hD T L μ0 hL sc G W M hM
      exact hS i hi v _ hI u hu
  have hlatA : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • (u *ᵥ y) ∈ latA (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
    intro z hz
    rw [← Matrix.smul_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hsd (key z hz) hy
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, hsupp, a, ha, rfl⟩ := hs
    refine FractionalIdeal.mul_induction_on
      (C := fun a => (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) • (u *ᵥ y) ∈
        GlobalTheory.FinPl.latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v)) ha (fun b hb c hc => ?_)
      (fun x x' hx hx' => ?_)
    · have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] b) *
          (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul', mul_ePl hsupp]
      have hz : pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c ∈
          GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v :=
        AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPlLoc.ePl_int _, fun w hw => by
          rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw], c, hc, rfl⟩
      have hs' : pairA D.host.F 0 α ⊗ₜ[D.host.F] b ∈ GlobalTheory.SeeSaw.idV D.host.AA⁻¹ v :=
        AddSubgroup.subset_closure ⟨α, hα, hsupp, b, hb, rfl⟩
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c)) • (u *ᵥ y) ∈ _
      rw [e1, mul_smul]
      exact ((P7' _ _ _).1 (hlatA _ hz)).2 _ hs'
    · show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x + x')) • (u *ᵥ y) ∈ _
      rw [TensorProduct.tmul_add, add_smul]; exact add_mem hx hx'
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha
