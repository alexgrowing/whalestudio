import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelUnitValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistScalarField

open NumberField IsDedekindDomain

theorem val_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (χ₁ * χ₂).val v = χ₁.val v * χ₂.val v :=
  Formalism.L2.Host.HChar.loc_mul χ₁ χ₂ v _

theorem onId_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := by
  unfold Formalism.L2.Host.HChar.onId
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := L) I)
  have hs : ∀ χ : Formalism.L2.Host.HChar L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v I).Finite :=
    fun χ => hfin.subset fun v hv h0 => hv (by show χ.val v ^ _ = 1; rw [h0, zpow_zero])
  rw [← finprod_mul_distrib (hs χ₁) (hs χ₂)]
  exact finprod_congr fun v => by rw [val_mul, mul_zpow]

theorem onId_mem_range {L C : Type} [Field L] [NumberField L] [Field C] (emb : C →+* ℂ) (ξ : Formalism.L2.Host.HChar L)
    (h : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ emb.range) (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    ((ξ.onId I : ℂˣ) : ℂ) ∈ emb.range := by
  let S : Subgroup ℂˣ :=
    { carrier := {u | (u : ℂ) ∈ emb.range}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul]⟩
      one_mem' := ⟨1, by rw [map_one, Units.val_one]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨x, hx⟩ := ha
        exact ⟨x⁻¹, by rw [map_inv₀, hx, Units.val_inv_eq_inv_val]⟩ }
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), ξ.val v ∈ S := fun v => h _
  exact finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) (fun v => S.zpow_mem (hv v) _)

set_option maxHeartbeats 1000000 in

theorem twist_scalar_mem_range : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∃ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv htup hQG hF0 hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h N hU hTb hTl hLevOK hconj e Ps yd hh he hPs hPsO hs hy hcard
  classical
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.p.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.J.toCore.good_σ₀).1
  have hInR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hlev := hT.sh.dLev _ hInR (Vc D i).rank
  obtain ⟨pp, -, hpd⟩ := hT.sh.dPd
  have hpd1 := hRun.2.1
  rw [hpd _ hInR] at hpd1
  have hpd2 : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).pd = ownAt D v := by rw [hpd _ hInR, hpd1]
  have hL := hC.lev
  have hstd := hO.2.lift.std
  have hbadO := hO.2.bad ()
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad () := ⟨_, rfl⟩
  have hbPs : ∀ PP ∈ Ps, ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP hm => by
    rw [hb, Nat.cast_mul (badN D * _)] at hm
    rcases PP.isPrime.mem_or_mem hm with h1 | h1
    · exact hPs PP hP h1
    · exact hPsO PP hP h1
  have h2b : 2 ∣ b := hb ▸ dvd_mul_of_dvd_right hbadO.2.1 _
  have hMb' : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∣ b := hb ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have g := GlobalTheory.AdTh.SerOne.guard_of_splitOffBad (Vc D i) hstd.1 hstd.2 _ h2b hMb' ⟨hh, e, Ps, he, hbPs, hs⟩
  obtain ⟨gU, ⟨k, hk1, hk2, hk3⟩, gS⟩ := g
  have gT : (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank).TrivAt ((O i).bad ()) :=
    ⟨k, Nat.Coprime.coprime_dvd_right (hb ▸ dvd_mul_left _ _) hk1, hk2, hk3⟩
  have hΛ : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) := by
    cases Λ with
    | mk La => congr 1; ext w; exact hconj w
  have memb : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((b : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := fun Q hQ => by
    rw [hb, hlev.2.1, hpd2, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hQ))
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal (Vc D i) hstd.1 hstd.2 h e Ps yd he hs hy b hbPs
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹)
    (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) hK.chr hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ hbadO.2.2.2.2)
        rw [hb, hu]
        simp only [Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hj))
      have a2 : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt Q := by
        by_contra hn
        rcases (hK.ram Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (memb Q (Finset.mem_filter.1 a).2)
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (memb Q' (Finset.mem_filter.1 a).2)
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, hK.triv.1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.2.ep ()).2 _ cc gU gT gS c1 c3
  have c2' : cc ⊔ Ideal.span {(((O i).bad () : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    refine top_le_iff.1 (c2 ▸ sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 ?_) _)
    rw [hb]; exact Nat.cast_dvd_cast (dvd_mul_left _ _)
  have hB := (hO.2.tuple ()).B cc c0 c2'
  have hxi : R.xiH A.μ0 = 1 := hL.xi_base
  have S1 : ∀ (χ₁ χ₂ : Formalism.L2.Host.HChar D.host.E) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := fun χ₁ χ₂ I => onId_mul χ₁ χ₂ I
  have S2 : ∀ (ξ : Formalism.L2.Host.HChar D.host.E), (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) →
      ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, ((ξ.onId I : ℂˣ) : ℂ) ∈ D.what₂.embLL.range :=
    fun ξ hξ I => onId_mem_range D.what₂.embLL ξ hξ I
  have e1 : R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹ =
      (R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹) * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) := by
    rw [hxi, mul_one, mul_right_comm]
  rw [e1, S1, Units.val_mul] at c4
  obtain ⟨a3, ha3⟩ := S2 _ hdel (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  have hF := hO.1
  have memF : ∀ x : (O i).c'.F, ∃ a : D.what₂.LL, D.what₂.embLL a = (x : ℂ) := fun x => by
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 ((SetLike.ext_iff.1 hF (x : ℂ)).1 x.2)
    exact ⟨a, ha⟩
  obtain ⟨a1, ha1⟩ := memF (incF T.Q.c (O i).c' (O i).hle (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))
  obtain ⟨a2, ha2⟩ := memF ((O i).B () cc)
  have hi : GlobalTheory.ClassScalarCompare.stdIndex Λ =
      GlobalTheory.ClassScalarCompare.stdIndex (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank) := by
    rw [hΛ]; exact GlobalTheory.ClassScalarCompare.stdIndex_conjLat _
  have q1' : (q : ℝ) ^ 2 * ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) := by
    rw [hi, hpq]; exact_mod_cast q1
  have hsq : ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ) =
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) * ((q : ℂ))⁻¹ := by
    have hq : (0:ℝ) < q := by exact_mod_cast q0
    have e2 : ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) / (q : ℝ) ^ 2 := by
      rw [← q1']; field_simp
    rw [e2, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hq.le, Complex.ofReal_div, div_eq_mul_inv,
      Complex.ofReal_ratCast]
  have h1 : (O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ) = D.what₂.embLL a1 := ha1.symm
  beta_reduce at hB
  have h2 := ha2.trans hB
  refine ⟨a1⁻¹ * a2 * a3 * ((q⁻¹ : ℚ) : D.what₂.LL), ?_⟩
  change _ = _ * _ * ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ)
  rw [h1, c4, hsq, map_mul, map_mul, map_mul, map_inv₀, map_ratCast, h2, ha3]
  push_cast
  ring

end GlobalTheory.TwistScalarField
