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
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime

namespace GlobalTheory.TwistedKernelChar

section General

open NumberField IsDedekindDomain Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem inf_triv [IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem hasInf_mul_inv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n m : I → ℤ} {α β γ : HChar L}
    (ha : α.HasInf φ n) (hb : ∀ k, β.inf k = 1) (hc : γ.HasInf φ m) : (α * β * γ⁻¹).HasInf φ (fun i => n i - m i) := by
  intro k
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, hb, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, ha k, hc k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have h1 : φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1, div_eq_mul_inv (_ ^ _)]

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem frame_char (D : D7) (C : Formalism.L2.Host.CharFrame D) (i : Fin D.R.m) (l : ℕ) :
    ∃ (b : ℕ) (n : D.R.Psi → ℤ), b ≠ 0 ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ Q.asIdeal → ((badN D : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → (C.mu0 i * C.delAt l * C.eta⁻¹).UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        ∀ k : D.host.Fˣ, (C.mu0 i * C.delAt l * C.eta⁻¹).resFin (Q.under (𝓞 D.host.F)) k = 1) ∧
      (∀ Q, (C.mu0 i * C.delAt l * C.eta⁻¹).TameAt Q) ∧
      (C.mu0 i * C.delAt l * C.eta⁻¹).HasInf (Formalism.L2.Host.embPsi D.host) n := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨p, hp, hpl, hδ⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ D.host.levelPrimes ∧ Formalism.L2.Host.IsDelta (H := D.host) p (C.delAt l) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    · exact ⟨_, D.host.pde'_prime, D.host.pde_level.2, C.isDel'⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_level.1, C.isDel⟩
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ∀ a b : ℕ, a ∣ b → (a : 𝓞 D.host.E) ∈ Q.asIdeal →
      (b : 𝓞 D.host.E) ∈ Q.asIdeal := by
    rintro Q a b ⟨u, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have lev : ∀ a ∈ D.host.levelPrimes, a ∣ badN D := fun a ha =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) ha) _
  obtain ⟨n, -, hn⟩ := (C.isMu0 i).inf
  obtain ⟨o, ho, hod⟩ := hδ.fin
  refine ⟨D.host.g 0 * D.host.g 1 * p, fun τ => n τ - 1,
    mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) hp.ne_zero, fun Q hQ => ?_,
    fun Q hQ x hx => ?_, fun Q hQ x => ?_, fun Q x hx hx' => ?_,
    hasInf_mul_inv hn (inf_triv _ ho hod) C.isEta.inf⟩
  · rw [Nat.cast_mul, Nat.cast_mul] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · exact key Q _ _ (lev _ (D.host.g_level 0)) h
      · exact key Q _ _ (lev _ (D.host.g_level 1)) h
    · exact key Q _ _ (lev _ hpl) h
  · have a1 : (C.mu0 i).UnrAt Q := (C.isMu0 i).unr Q fun j hj => hQ (key Q _ _ (by
      refine Dvd.dvd.mul_right ?_ p
      rw [← Fin.prod_univ_two D.host.g]
      exact Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)) hj)
    have a2 : (C.delAt l).UnrAt Q := hδ.unr Q fun hj => hQ (key Q _ _ (Dvd.intro_left _ rfl) hj)
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
      C.isEta.unr Q x hx, inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
      (C.isMu0 i).triv.1, hδ.triv.1, C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
      Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, (C.isMu0 i).tame Q x hx hx',
      hδ.tame Q x hx hx', C.isEta.unr Q x hx, inv_one, one_mul, one_mul]

set_option maxHeartbeats 800000 in

theorem twisted_kernel_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i _ v _ _ _ _ _ _ _ _ ℓ _ _ χ ξR ω φ hK Λ h N _ _ _ _ _ e Ps yd _ _ hb
  obtain ⟨b, n, h0, h1, h2, h3, h4, h5⟩ := frame_char D R.C i (Formalism.EigenvalueLevelCeiling.plc v)
  refine ⟨_, b, _, _, _, n, h0, fun Q hQ hm => hb Q hQ ?_,
    GlobalTheory.ClassScalarValue.chrEq_mul_inv (hC.lev.mu0 i) hK.chr hC.lev.eta, h2, h3, h4, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (h1 Q hm)

end GlobalTheory.TwistedKernelChar
