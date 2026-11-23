import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinPartIdemSumMulInvMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

section SlopeTestRemainingChoices

open GlobalTheory.LatVac GlobalTheory.SplitScalar

def stO (x : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨star (x : D.host.E), (show IsIntegral ℤ (x : D.host.E) from x.2).map (starRingEnd D.host.E).toIntAlgHom⟩

theorem coe_stO (x : 𝓞 D.host.E) : ((stO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem mem_of_mem_conjI {P : Ideal (𝓞 D.host.E)} {x : 𝓞 D.host.E} (hx : x ∈ conjI P) : stO x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, hab⟩ := ha
    have : stO a = b := by
      apply RingOfIntegers.ext
      rw [coe_stO, show (a : D.host.E) = star (b : D.host.E) from hab, star_star]
    rw [this]; exact hb
  | zero =>
    have : stO (0 : 𝓞 D.host.E) = 0 := RingOfIntegers.ext (by rw [coe_stO]; simp)
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : stO (a + b) = stO a + stO b := RingOfIntegers.ext (by
      show star ((a : D.host.E) + b) = star (a : D.host.E) + star (b : D.host.E)
      exact star_add _ _)
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : stO (r • a) = stO r * stO a := RingOfIntegers.ext (by
      show star ((r : D.host.E) * a) = star (r : D.host.E) * star (a : D.host.E)
      exact star_mul' _ _)
    rw [this]; exact Ideal.mul_mem_left _ _ ha

theorem smul_mem_tens {n r : ℕ} {Λ : Lt D.host.E n} {L L' : Lt D.host.E r} (c : 𝓞 D.host.E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) D.host.E} (hy : y ∈ tens Λ L) :
    (c : D.host.E) • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_hatA_of_int {S T : HSp D} {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    (hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ A, (o : D.host.E) • y ∈ A) {z : AE D} (hz : finPart D z ∈ intAE D)
    {u : WO S T} (hu : u ∈ hatA S T A) : z • u ∈ hatA S T A := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => z • u ∈ hatA S T A) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    have key : ∀ x ∈ intAE D,
        (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D (x * (α ⊗ₜ[D.host.F] (yᵀ i j)))) ∈ hatA S T A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, o, rfl⟩ := hx
        have e1 : (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D
            ((a ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] (yᵀ i j)))) =
            GlobalTheory.LatVac.finTens (a * α) (((o : D.host.E) • y)ᵀ) := by
          ext i j
          rw [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.TensLatMove.emb_tmul]
          rfl
        rw [e1]
        exact GlobalTheory.Ker.SignVac.finTens_mem (mul_mem_intAf ha hα) (hA o y hy)
      | zero =>
        convert zero_mem (hatA S T A) using 1
        ext i j
        rw [Matrix.of_apply, zero_mul, LinearMap.map_zero, Matrix.zero_apply]
      | add x x' _ _ hx hx' =>
        convert add_mem hx hx' using 1
        ext i j
        rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, add_mul, LinearMap.map_add]
      | neg x _ hx =>
        convert neg_mem hx using 1
        ext i j
        rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, neg_mul, LinearMap.map_neg]
    convert key _ hz using 1
    ext i j
    rw [Matrix.of_apply, GlobalTheory.TensLatMove.emb_mul, GlobalTheory.TensLatMove.emb_tmul]
    rfl
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

end SlopeTestRemainingChoices

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (x : WO S T) : partAt c x = c • x := by
  ext i j; rfl

theorem partAt_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ hPg _ e he a k₀ Λ' _ hMv hGen hMov Lv hLv u hu

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hMov
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have hu' : actO S T k₀ 1 (actO S T k₀⁻¹ 1 u) = u := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k₀ 1 u
    rwa [inv_one] at this
  generalize actO S T k₀⁻¹ 1 u = w at hw hu'

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hs : stO t ∈ conjI Lv.𝔪 := Ideal.subset_span ⟨t, ht, rfl⟩
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPg
    intro h
    apply htP PP (Finset.mem_union_left _ hPP)
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _
  have hs0 : ((stO t : 𝓞 D.host.E) : D.host.E) ≠ 0 := by rw [coe_stO]; exact star_ne_zero.2 ht0

  have hsL : ∀ v ∈ Lv.sh C.X.Λ, stO t • v ∈ Lv.𝔪 • C.X.Λ := fun v hv => hv _ hs
  have h0 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w ∈
      hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)) := by
    refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)))
      ?_ ?_ ?_ ?_ hw
    · intro α hα y hy
      rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
      exact GlobalTheory.Ker.SignVac.finTens_mem hα (smul_mem_tens _ hsL hy)
    · rw [smul_zero]; exact zero_mem _
    · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
    · intro x hx; rw [smul_neg]; exact neg_mem hx

  have hz1 : finPart D (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    have h7 := (GlobalTheory.FinPl.FrameLat.cA_int_iff (e * incA D ((t : D.host.E))⁻¹)).2
      (GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP)
    rwa [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, star_inv₀] at h7
  have hA' : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ),
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ) :=
    fun o y hy => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hy
  have hx0 : partAt (cA D e) w ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
    have e1 : partAt (cA D e) w = (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) •
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w := by
      rw [smul_smul, mul_assoc]
      have e2 : incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) *
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hs0]
      rw [e2, mul_smul, GlobalTheory.Ker.SignVac.one_smul_hatA hw, partAt_eq_smul]
    rw [e1, ← hLv]
    exact smul_mem_hatA_of_int hA' hz1 h0

  have hidem : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : IsHalf (cA D e) (partAt (cA D e) w) := fun i j => by
    change cA D e * (cA D e * w i j) = cA D e * w i j
    rw [← mul_assoc, hidem]
  obtain ⟨hI, hR⟩ := ((hGen _ hhalf).2).2 hx0
  have hmv := hMv.2.2 _ hhalf
  have hcomm : partAt (cA D e) u = actO S T k₀ 1 (partAt (cA D e) w) := by
    rw [partAt_eq_smul, partAt_eq_smul, ← hu']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  rw [hcomm]
  refine ⟨GlobalTheory.WeilVacMove.isHalf_actO _ _ _ hhalf, ?_, fun PP hPP => ?_⟩
  · rw [hmv]; exact hI
  · rw [hmv]; exact hR PP hPP

end GlobalTheory.LiftLevel

end
