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
import Development.AbelianVarietyTheory.Definitions.Divisors.ReadsOnlyOmegaFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryInGam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHalfOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstEqInvChar

noncomputable section

namespace GlobalTheory.CoverDatum

section Ideals

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.IndefR.Datum

variable {E : Type} [Field E] [NumberField E]

theorem prod_le_of_sq {I : Ideal (𝓞 E)} {p : 𝓞 E} (hp : p ∈ I) (hp0 : p ≠ 0) (Q : Finset (Pl E))
    (hQ : ∀ P : Pl E, I ≤ P.asIdeal → P ∈ Q) (hsq : ∀ P ∈ Q, p ∉ P.asIdeal ^ 2) : ∏ P ∈ Q, P.asIdeal ≤ I := by
  have hI : I ≠ 0 := fun h => hp0 (by rw [h] at hp; exact hp)
  have hs : Squarefree I := (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI).2 fun J hJ hd => by
    have hJ' := UniqueFactorizationMonoid.irreducible_iff_prime.1 hJ
    let P : Pl E := ⟨J, Ideal.isPrime_of_prime hJ', hJ'.ne_zero⟩
    have h1 := Ideal.le_of_dvd hd
    exact hsq P (hQ P (h1.trans Ideal.mul_le_left)) (by rw [pow_two]; exact h1 hp)
  have hr : ∏ P ∈ Q, P.asIdeal ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J hJ => ?_
    have h1 : I ≤ J := hJ.1
    have h2 : J.IsPrime := hJ.2
    have h3 : J ≠ ⊥ := fun h => hp0 (Ideal.mem_bot.1 (h.le (h1 hp)))
    exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun P : Pl E => P.asIdeal) (hQ ⟨J, h2, h3⟩ h1))
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr (IsNoetherian.noetherian _)
  exact Ideal.le_of_dvd (hs.isRadical m _ (Ideal.dvd_iff_le.2 hm))

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {r : ℕ} (τ : 𝓞 E ≃+* 𝓞 E) (ρ : ∀ P : Pl E, Fin r → La →+ kP P)
  (hs : ∀ (P : Pl E) (a : Fin r) (t : 𝓞 E) (x : La), ρ P a (t • x) = Ideal.Quotient.mk P.asIdeal (τ t) * ρ P a x)

include hs in

theorem rho_eq_zero {J : Ideal (𝓞 E)} {P : Pl E} (hJ : J ≤ P.asIdeal) (hτ : ∀ t, τ (τ t) = t) {x : La}
    (hx : x ∈ (J.map (τ : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) La)) (a : Fin r) : ρ P a x = 0 := by
  refine Submodule.smul_induction_on (p := fun x => ρ P a x = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (τ : 𝓞 E →+* 𝓞 E) τ.surjective).1 hc
    rw [hs, show τ ((τ : 𝓞 E →+* 𝓞 E) b) = b from hτ b, Ideal.Quotient.eq_zero_iff_mem.2 (hJ hb), zero_mul]
  · rw [map_add, hx, hy, add_zero]

include hs in

theorem mem_of_rho_eq_zero (hτ : ∀ t, τ (τ t) = t) {S U : Finset (Pl E)} (hSU : S ⊆ U)
    (hker : ∀ x, (∀ P ∈ U, ∀ a, ρ P a x = 0) → x ∈ ((∏ P ∈ U, P.asIdeal).map (τ : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) La))
    (x : La) (hx : ∀ P ∈ S, ∀ a, ρ P a x = 0) :
    x ∈ ((∏ P ∈ S, P.asIdeal).map (τ : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) La) := by
  classical
  obtain ⟨t, ht⟩ := GlobalTheory.BasePoint.crt_places U fun P => if P ∈ S then 1 else 0
  have h1 := hker (τ.symm t • x) fun P hP a => by
    rw [hs, τ.apply_symm_apply, ht P hP]
    split_ifs with h
    · rw [hx P h, mul_zero]
    · rw [zero_mul]
  have h2 : τ (1 - τ.symm t) ∈ ∏ P ∈ S, P.asIdeal := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime fun x _ y _ h => HeightOneSpectrum.isCoprime_of_ne _ _ h]
    simp only [Submodule.mem_iInf]
    intro P hP
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, τ.apply_symm_apply, map_sub, map_one, ht P (hSU hP), if_pos hP,
      sub_self]
  have h3 := Ideal.mem_map_of_mem (τ : 𝓞 E →+* 𝓞 E) h2
  rw [show (τ : 𝓞 E →+* 𝓞 E) (τ (1 - τ.symm t)) = 1 - τ.symm t from hτ _] at h3
  have h4 := add_mem (Submodule.smul_mono_left (Ideal.map_mono (Ideal.le_of_dvd
    (Finset.prod_dvd_prod_of_subset S U (fun P => P.asIdeal) hSU))) h1) (Submodule.smul_mem_smul h3 (Submodule.mem_top (x := x)))
  rwa [← add_smul, add_sub_cancel, one_smul] at h4

include hs in

theorem rank_eq {n : ℕ} {P : Pl E} (N : Submodule (𝓞 E) La) (hN : ∀ x ∈ N, ∀ a, ρ P a x = 0)
    (hon : ∀ t : Fin r → kP P, ∃ x, ∀ a, ρ P a x = t a) (x : Fin n → La)
    (hx : Submodule.span (𝓞 E) (Set.range x) ⊔ N = ⊤) : (Matrix.of fun b a => ρ P a (x b)).rank = r := by
  haveI := P.isMaximal
  letI : Field (kP P) := Ideal.Quotient.field _
  have h : Submodule.span (kP P) (Set.range (Matrix.of fun b a => ρ P a (x b)).row) = ⊤ := by
    refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨y, hy⟩ := hon t
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hx.ge (Submodule.mem_top (x := y)))
    obtain ⟨co, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hu
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun b => Ideal.Quotient.mk P.asIdeal (τ (co b)), funext fun a => ?_⟩
    rw [← hy, map_add, hN w hw, add_zero, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (hs P a _ _).symm
  rw [Matrix.rank_eq_finrank_span_row, h, finrank_top, Module.finrank_fin_fun]

open Classical in
theorem topDatum_congr {n : ℕ} (Q : Finset (Pl E)) (ξ : ∀ P : Pl E, (kP P)ˣ →* ℂˣ)
    (y y' : ∀ P : Pl E, Matrix (Fin n) (Fin r) (kP P)) (hq : ∀ P ∈ Q, y P = y' P) :
    (if h : ∀ P ∈ Q, IsUnit (topL r (y P)).det then ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) else 0) =
      if h : ∀ P ∈ Q, IsUnit (topL r (y' P)).det then ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) else 0 := by
  by_cases H : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · have H' : ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det := fun PP hp => (hq PP hp) ▸ H PP hp
    rw [dif_pos H, dif_pos H']
    refine Finset.prod_congr rfl fun PP _ => ?_
    have : (H PP.1 PP.2).unit = (H' PP.1 PP.2).unit := by
      ext; simp [hq PP.1 PP.2]
    rw [this]
  · have H' : ¬ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det := fun H' =>
      H fun PP hp => (hq PP hp).symm ▸ H' PP hp
    rw [dif_neg H, dif_neg H']

end Ideals

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option maxHeartbeats 1000000 in

theorem psi_value_full {D : D7} (T : Full D) (hT : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) (V : HSp D)
    (hV : T.J.V j T.J.toCore.σ₀ = V) (hr : V.rank = D.R.r) (N : ℕ) (hN : 0 < N)
    (hxN : ∀ h : GA D V, T.xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hrat : ∀ γ ∈ GQ V, T.xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (ψ : (LaI (T.Q.Xo j) T.Q.c (T.dδ j n) ≃ₗ[𝓞 D.host.E] LaI (T.Q.Xo j) T.Q.c (T.dδ j n)) →* T.Q.c.Fˣ) (hψ : (T.dδ j n).PsiTie ψ)
    (k : LaI (T.Q.Xo j) T.Q.c (T.dδ j n) ≃ₗ[𝓞 D.host.E] LaI (T.Q.Xo j) T.Q.c (T.dδ j n))
    (s : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim (T.Q.Dw j)) (hs : s.InGam T.Q.l (T.dδ j n).l₂)
    (hk : ∀ a, (Submodule.Quotient.mk (s.f (T.dδ j n).l₂.M a) : LaI (T.Q.Xo j) T.Q.c (T.dδ j n)) = k (Submodule.Quotient.mk a))
    (u : GA D V) (hu : Formalism.L2.Pj.gLat V u = latHat V)
    (hlift : ∀ a, ∃ w ∈ latGHat V 1, (finHom V u).1.mulVec (finVec V
      ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.J.iota j) a)) =
      finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.J.iota j) (s.f (T.dδ j n).l₂.M a)) +
        (T.dδ j n).l₂.M • w) :
    (((ψ k : T.Q.c.Fˣ) : T.Q.c.F) : ℂ) = (T.xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) := by
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T.J hT.j j hj _ T.J.toCore.good_σ₀ V hV hr
  subst hV
  obtain ⟨hr', U₂, dict₂, c0, ⟨m, hm, hc0⟩, hv⟩ := hT.xiVal j hj n
  exact psi_value _ (T.dδ j n) hr _ hio (GlobalTheory.ShortMove.rank_eq hT.j.pins hj) _ hx₀ (hT.sh.dLev j hj n) (hT.lvA j hj n) T.xi
    (m * N) (Nat.mul_pos hm hN) (fun h => by rw [mul_comm, pow_mul, hxN, one_pow]) hrat (U₂ ()) (dict₂ ()) c0
    (by rw [pow_mul, hc0, one_pow]) (hv ()) ψ hψ k s hs hk u hu hlift

theorem res_mem {D : D7} {ξ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c : (kP P)ˣ →* ℂˣ} (h : IsRes ξ P c) (K : Set ℂ)
    (hK : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ K) (u : (kP P)ˣ) : ((c u : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := fun h0 => u.ne_zero (by
    rw [← ha, RingOfIntegers.coe_eq_zero_iff.1 h0, map_zero])
  rw [h a (Units.mk0 _ h0) u rfl ha.symm]
  exact hK _

theorem places_half {D : D7} (C : Formalism.L2.Host.CharFrame D) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {I : Ideal (𝓞 D.host.E)} (hp : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ I)
    (hI : I ⊔ I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤) (Q : Finset (Pl D.host.E)) (hQ : ∀ P ∈ Q, I ≤ P.asIdeal)
    (hpl : IsTwistPlaces D.host.g Q)
    (hram : ∀ P, ¬ (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt P → P ∈ Q ∨ ∃ P' ∈ Q, IsConjPl P' P) :
    ∏ P ∈ Q, P.asIdeal ≤ I := by
  have hδ : (ownAt D v).Prime ∧ Formalism.L2.Host.IsDelta (H := D.host) (ownAt D v) (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) := by
    unfold ownAt Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [⟨D.host.pde'_prime, C.isDel'⟩, ⟨D.host.pde_prime, C.isDel⟩]
  refine prod_le_of_sq hp (Nat.cast_ne_zero.2 hδ.1.ne_zero) Q (fun P hP => ?_) fun P hP => ?_
  · have hu : ¬ (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt P := fun hu => by
      have h15 := (hδ.2.ine P (hP hp) 1).1 (fun x hx => by rw [pow_one]; exact hu x hx)
      exact absurd (Nat.le_of_dvd one_pos h15) (by norm_num)
    refine (hram P hu).resolve_right ?_
    rintro ⟨P', hP', hc⟩
    refine P.isPrime.ne_top (top_le_iff.1 (hI ▸ sup_le hP (Ideal.map_le_iff_le_comap.2 fun t ht => ?_)))
    obtain ⟨t', h1, h2⟩ := hc t (hQ P' hP' ht)
    rwa [Ideal.mem_comap, show (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) t = t' from
      RingOfIntegers.ext ((H.bar_eq t).trans h2.symm)]
  · obtain ⟨⟨q, hq, hcard, hsq, -⟩, -⟩ := hpl P hP
    obtain ⟨p', hp', hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
    have hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
      exact card_nsmul_eq_zero'
    rw [← (Nat.prime_dvd_prime_iff_eq hp' hδ.1).1 ((hpP _).1 (hQ P hP hp)),
      (Nat.prime_dvd_prime_iff_eq hp' hq).1 ((hpP _).1 hqP)]
    exact hsq

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem datum_eq_hat_free : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), AdmX (l := T.Q.l) true x₀ → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (ζ : ℂ) (φc : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ ζ ∈ D.what₂.embLL.range ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc = (fun q => ζ * (O i).s0 ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q))) ∧ PhiOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) (iotaW T.J i) (Mfr (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ • ⊤) φc ∧ (∀ PP, PP ∈ R.Pg ∨ PP ∈ (placesOver R (R.mu v) (ownAt D v)) → (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ (∀ PP, PP ∈ R.Pg ∨ PP ∈ (placesOver R (R.mu v) (ownAt D v)) → ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO hβV v _ _ hG _ _ hdel hMb hrun ℓ _ _ χ ξR ω φ hker x₀ hadm
  classical
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL := hC.lev
  have hd := hT.sh.dLev _ hj (Vc D i).rank
  have hA₂ := hT.lvA _ hj (Vc D i).rank
  have hhalf := hT.halfI _ hj (Vc D i).rank
  obtain ⟨ph, ψ, xJ, -, hpin, htie⟩ := hT.sh.dPhi _ hj (Vc D i).rank (r_le_V i)
  have hpd : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).pd = ownAt D v := by
    obtain ⟨p, -, hp⟩ := hT.sh.dPd
    exact (hp _ hj _).trans ((hp _ hj _).symm.trans hrun.2.1)
  obtain ⟨-, -, hQI, χ', hχ', hxi⟩ := hrun
  rw [← hhalf] at hQI
  have hpsi := psi_value_full T hT _ hj (Vc D i).rank (Wc D i) (hT.j.spaceW _ hj _ T.J.toCore.good_σ₀) (rank_Wc i)
  obtain ⟨hio, -⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T.J hT.j _ hj _ T.J.toCore.good_σ₀ (Wc D i)
    (hT.j.spaceW _ hj _ T.J.toCore.good_σ₀) (rank_Wc i)
  change GlobalTheory.Member.IotaOK (T.Q.Dw ((i : ℕ) + 1)) (Wc D i) (iotaW T.J i) at hio
  have hpq : (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank :=
    (GlobalTheory.Member.exists_iotaOK D T.J.Q hT.j.pins _ hj).2.1.trans (rank_Wc i).symm
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := GlobalTheory.ShortMove.rank_eq hT.j.pins hj
  have hguard : ∀ PP, PP ∈ R.Pg ∨ PP ∈ placesOver R (R.mu v) (ownAt D v) →
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    rintro PP (h | h)
    · exact (hO.2.tuple ()).half.2.2 PP (Or.inl h)
    · exact hG.2 _ PP (Finset.mem_filter.1 h).1
  have hV : (Vc D i).gram = 1 := hO.2.lift.std.1
  change T.Q.l.Mb = _ at hMb
  change ∃ y₀ ζ φc, _ ∧ _ ∧ _ ∧ _ = (fun q => ζ * (((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm
    ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q) : T.Q.c.F) : ℂ)) ∧ _
  obtain ⟨N, hN, ho⟩ := hker.fin
  obtain ⟨xi', hx1, -, hx3, hx4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) χ' _ hχ' N hN ho hker.triv hker.tame
  have hxx : ∀ g : GA D (Wc D i), T.xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨z, hz⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g z hz).trans (hx1 g z hz).symm)
  replace hpsi := hpsi N hN (fun g => by rw [hxx, hx4]) (fun γ hγ => (hxx γ).trans (hx3 γ hγ)) ψ htie
  obtain ⟨-, e, he, -⟩ := hker.vec
  have hi : ∀ x a, GlobalTheory.LevelDatum.rowP (Wc D i) (R.βW i) e (iotaW T.J i x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun x a => GlobalTheory.LevelDatum.rowP_int _ _ _ (hL.βW i) e _ he (fun PP h => hguard PP (Finset.mem_union.1 h)) _
      (hio.emb.2.le (LinearMap.mem_range_self _ x)) a
  have hrow : ∀ (x : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) b a,
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => iotaW T.J i (x b)) b a =
        GlobalTheory.LevelDatum.rowP (Wc D i) (R.βW i) e (iotaW T.J i (x b)) a := fun x b a => by
    rw [GlobalTheory.LevelDatum.uMat_eq _ _ hV, hβV, inv_one, Units.val_one]
    exact congrFun (Matrix.one_mulVec fun b' => GlobalTheory.LevelDatum.rowP (Wc D i) (R.βW i) e (iotaW T.J i (x b')) a) b
  have hint : ∀ x : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La,
      IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => iotaW T.J i (x b)) := fun x b a => by
    rw [hrow]; exact hi _ _
  have hmove := exists_move (Vc D i) (Wc D i) (R.βV i) (R.βW i) (hL.βW i) e _ (iotaW T.J i) hio hpos hd hA₂ hint T.xi hχ' hxi
    hker.tame _ ξR hker.res hQI (fun P => (hker.ram P).1) ψ hpsi
  have hτ : ∀ c, ((T.Q.H.bar c : 𝓞 D.host.E) : D.host.E) = D.sp.cm.sig (c : D.host.E) := fun c => T.Q.H.bar_eq c
  obtain ⟨ρ, hred, hs, hon, hk0⟩ : ∃ ρ : ∀ P : Pl D.host.E, Fin (Wc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La →+ kP P,
      (∀ P (x : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La),
        redM P (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => iotaW T.J i (x b)) = Matrix.of fun b a => ρ P a (x b)) ∧
      (∀ P a t x, ρ P a (t • x) = Ideal.Quotient.mk P.asIdeal (T.Q.H.bar t) * ρ P a x) ∧
      (∀ t : ∀ P : Pl D.host.E, Fin (Wc D i).rank → kP P, ∃ x, ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ a,
        ρ P a x = t P a) ∧
      ∀ x, (∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ a, ρ P a x = 0) →
        x ∈ ((∏ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), P.asIdeal).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • ⊤ :
          Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La) :=
    ⟨GlobalTheory.BasePoint.rho (Wc D i) (R.βW i) e (iotaW T.J i) hi, fun P x => Matrix.ext fun b a => by
                 rw [redM, dif_pos (hint x b a)]
                 exact congrArg _ (Subtype.ext (hrow x b a)),
      fun P a t x => GlobalTheory.BasePoint.rho_smul _ _ _ _ hi P a t _ (hτ t) x,
      GlobalTheory.BasePoint.rho_onto _ _ _ _ hi (hL.βW i) hio.emb he fun PP h h' =>
        hguard PP (Finset.mem_union.1 h) (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h'),
      GlobalTheory.BasePoint.rho_ker _ _ _ _ hi (hL.βW i) hio.emb he (fun PP h => hguard PP (Finset.mem_union.1 h)) _ hτ⟩
  have hM := hd.2.1
  have hMb₂ := hd.2.2.2.1
  have hpI := GlobalTheory.CharacterFunction.natCast_mem_half hM hMb₂
  have hQprod := places_half R.C v T.Q.H (hpd ▸ hpI) hd.2.2.2.2.1 _ hQI hker.pl fun P => (hker.ram P).1
  have hres := hker.res
  clear hker hpsi hrow hi htie hA₂ hhalf hpd
  generalize T.dδ ((i : ℕ) + 1) (Vc D i).rank = d at *
  generalize placesOver R (R.mu v) (ownAt D v) = Q at *
  have hbb := LevelPairing.bar_bar T.Q.H
  have hPg : ∀ P ∈ R.Pg, T.Q.l.Mb ≤ P.asIdeal := fun P hP => hMb.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hP))
  have hle : ∀ P, P ∈ R.Pg ∨ P ∈ Q → d.l₂.Mb ≤ P.asIdeal := by
    rintro P (h | h)
    · exact (hMb₂.le.trans Ideal.mul_le_left).trans (hPg P h)
    · exact (hMb₂.le.trans Ideal.mul_le_right).trans (hQI P h)
  have hpJ := Ideal.mem_map_of_mem (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hpI
  rw [map_natCast] at hpJ
  have hMM : (T.Q.l.M : 𝓞 D.host.E) ∈ Mfr T.Q.l := (GlobalTheory.ClassSumRule.natCast_mem T.Q.l).2
  obtain ⟨α, β, hαβ⟩ := Nat.Coprime.cast (R := 𝓞 D.host.E) hd.2.2.1
  have hsplit : ∀ x : (T.Q.Dw ((i : ℕ) + 1)).La, x = α • d.pd • x + β • T.Q.l.M • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul, smul_smul, ← add_smul, hαβ,
      one_smul]
  have hpmem : ∀ x : (T.Q.Dw ((i : ℕ) + 1)).La, d.pd • x ∈ (d.I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • ⊤ :
      Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La) := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]; exact Submodule.smul_mem_smul hpJ trivial
  have hMmem : ∀ x : (T.Q.Dw ((i : ℕ) + 1)).La, T.Q.l.M • x ∈ (Mfr T.Q.l • ⊤ :
      Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La) := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]; exact Submodule.smul_mem_smul hMM trivial
  obtain ⟨u, hu⟩ := GlobalTheory.PinCoord.exists_const_eq_inv_char _ _ _ _ _ _ _ d hd ph ψ xJ hpin _ hpq (rank_W_le_V i) Q ξR (fun P a => T.Q.l.M • ρ P a)
    (fun P a t x => by rw [AddMonoidHom.nsmul_apply, AddMonoidHom.nsmul_apply, hs, mul_smul_comm])
    (fun x => ⟨fun hx P hP a => by
        rw [AddMonoidHom.nsmul_apply, rho_eq_zero T.Q.H.bar ρ hs (hQI P hP) hbb hx, smul_zero],
      fun hx => by
        have h1 := Submodule.smul_mono_left (Ideal.map_mono hQprod) (mem_of_rho_eq_zero T.Q.H.bar ρ hs hbb
          Finset.subset_union_right hk0 (T.Q.l.M • x) fun P hP a => (map_nsmul _ _ _).trans (hx P hP a))
        rw [hsplit x]
        exact add_mem (Submodule.smul_mem _ _ (hpmem x)) (Submodule.smul_mem _ _ h1)⟩)
    (fun t => by
      obtain ⟨x, hx⟩ := hon t
      refine ⟨β • x, fun P hP a => ?_⟩
      rw [← hx P (Finset.mem_union_right _ hP) a, AddMonoidHom.nsmul_apply, ← map_nsmul, smul_comm]
      conv_rhs => rw [hsplit x, map_add,
        rho_eq_zero T.Q.H.bar ρ hs (hQI P hP) hbb (Submodule.smul_mem _ _ (hpmem x)), zero_add])
    (fun k => by
      obtain ⟨f, y, h1, h2, h3, h4⟩ := hmove k
      refine ⟨f, y, h1, h2, fun P hP x => ?_, h4⟩
      have := (hred P fun b => T.Q.l.M • x b).symm.trans ((h3 P hP fun b => T.Q.l.M • x b).trans
        (congrArg (· * (y P).val) (hred P fun b => f (T.Q.l.M • x b))))
      refine Eq.trans (Matrix.ext fun b a => (map_nsmul (ρ P a) _ _).symm) (this.trans (congrArg (· * (y P).val)
        (Matrix.ext fun b a => (congrArg (ρ P a) (map_nsmul f _ _)).trans (map_nsmul (ρ P a) _ _)))))
  let y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) :=
    fun P => Matrix.of fun b a => ρ P a (d.pd • x₀ b)
  let φc : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) d.l₂) → ℂ :=
    fun q => omegaFree R i Q ξR y₀ fun P => Matrix.of fun b a => ρ P a (qRep (q b))
  have hφ : ∀ x : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La, φc (fun b => Submodule.Quotient.mk (x b)) =
      omegaFree R i Q ξR y₀ fun P => Matrix.of fun b a => ρ P a (x b) := fun x =>
    readsOnly_omegaFree R i Q ξR y₀ _ _ fun P hP => Matrix.ext fun b a => by
      have h1 := rho_eq_zero T.Q.H.bar ρ hs (hle P (Finset.mem_union.1 hP)) hbb
        ((Submodule.Quotient.eq _).1 (GlobalTheory.DatumInverseCharacter.qRep_spec
          (Submodule.Quotient.mk (x b) : LevQc (T.Q.Dw ((i : ℕ) + 1)) d.l₂))) a
      rwa [map_sub, sub_eq_zero] at h1
  refine ⟨y₀, ∏ P ∈ Q, (((ξR P (u P))⁻¹ : ℂˣ) : ℂ), φc, fun P hP => ?_, ?_, ?_, ?_, ⟨e, he, fun x => ⟨hint x, ?_⟩⟩,
    fun P hP => ⟨hle P hP, hguard P hP⟩, fun P hP => ?_⟩
  · refine rank_eq T.Q.H.bar ρ hs (Mfr T.Q.l • ⊤) (fun x hx a => rho_eq_zero T.Q.H.bar ρ hs (hPg P hP) hbb hx a) (fun t => ?_) _ ?_
    · obtain ⟨x, hx⟩ := hon (Pi.single P t)
      exact ⟨x, fun a => by rw [hx P (Finset.mem_union_left _ hP), Pi.single_eq_same]⟩
    · refine eq_top_iff.2 (hadm.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, -, rfl⟩
      rw [hsplit (x₀ b)]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)) (Submodule.smul_mem _ _ (hMmem _))
  · exact prod_mem fun P hP => by
      rw [← map_inv]
      exact res_mem (hres P hP) _ hdel _
  · rw [← Units.coe_prod]
    have : IsOfFinOrder (∏ P ∈ Q, (ξR P (u P))⁻¹) := Finset.prod_induction _ _ (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one
      fun P _ => by
        haveI : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
        exact ((ξR P).isOfFinOrder (isOfFinOrder_of_finite _)).inv
    obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 this
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]⟩
  · refine GlobalTheory.CoverTransform.hatC_eq_datum _ _ _ _ _ _ _ d hd ph ψ xJ hpin x₀ _ φc (fun z => ?_) fun x hx b => ?_
    · rw [hφ, ← hu z, omegaFree, if_pos, one_mul]
      · convert topDatum_congr Q ξR _ _ fun P hP => Matrix.ext fun b a => ?_
        rw [Matrix.of_apply, Matrix.of_apply, map_add, rho_eq_zero T.Q.H.bar ρ hs (hQI P hP) hbb (hpmem _), zero_add, map_nsmul,
          AddMonoidHom.nsmul_apply]
      · intro P hP
        ext b a
        rw [Matrix.of_apply, map_add, rho_eq_zero T.Q.H.bar ρ hs (hPg P hP) hbb (hMmem _), add_zero]
        rfl
    · rw [hφ, omegaFree] at hx
      have h1 : ∀ P ∈ R.Pg, (Matrix.of fun b a => ρ P a (x b)) = y₀ P := by
        by_contra h
        exact hx (by rw [if_neg h, zero_mul])
      rw [Mfr, hMb]
      refine mem_of_rho_eq_zero T.Q.H.bar ρ hs hbb Finset.subset_union_left hk0 _ fun P hP a => ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun (h1 P hP) b) a
  · exact (hφ x).trans (congrArg _ (funext fun P => (hred P x).symm))
  · rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (hle P hP (GlobalTheory.PinnedClassSum.natCast_mem_Mb _))

end Main

end GlobalTheory.CoverDatum
