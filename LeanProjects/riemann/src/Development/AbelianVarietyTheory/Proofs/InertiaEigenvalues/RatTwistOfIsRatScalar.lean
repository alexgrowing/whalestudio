import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastMemConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.TwistRat

open Classical in

theorem exists_level : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → (D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), TwOK i k Q ψ → ClsQ (D := D) Q → ∃ pd : ℕ, IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) pd ∧ pd.Coprime (D.ntw.l i) ∧ (∀ PP ∈ (ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ (∀ PP ∈ (ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) := by
  intro D ρ hρ hde i j b k Q ψ htw hcls
  obtain ⟨N, -, hNl, haux, hNQ⟩ := UnivRat.exists_auxiliary_squarefree_level_twistPlaces hρ hde i Q hcls htw.2.1
  have hmem : ∀ PP ∈ (ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q,
      ((UnivRat.pDel D (D.ntw.l i) * N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_mul]
    rcases Finset.mem_union.1 hPP with h | h
    · rw [hρ.delta i j b] at h
      exact Ideal.mul_mem_right _ _ ((UnivRat.mem_pD_iff i PP).1 (mem_half.1 h).1)
    · exact Ideal.mul_mem_left _ _ (hNQ PP (mem_half.1 h).1)
  refine ⟨_, haux, Nat.Coprime.mul_left ?_ hNl, hmem, fun PP hPP =>
    GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top haux.2.2.2.2 (hmem PP hPP)⟩
  unfold UnivRat.pDel
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime (D.ntw.lPrime i).out).2 fun e' => D.host.pde_ne (e.symm.trans e'.symm)
  · exact (Nat.coprime_primes D.host.pde_prime (D.ntw.lPrime i).out).2 fun e' => e e'.symm

open Classical in

theorem exists_field_roots : ∀ (L : IntermediateField ℚ ℂ) (K : Subfield ℂ), FiniteDimensional ℚ L → IsGalois ℚ L → L.toSubfield ≤ K → ∀ n : ℕ, 0 < n → ∃ L' : IntermediateField ℚ ℂ, FiniteDimensional ℚ L' ∧ Normal ℚ L' ∧ L ≤ L' ∧ L'.toSubfield ≤ K ∧ ∀ z ∈ K, z ^ n = 1 → z ∈ L' := by
  intro L K h1 h2 h3 n hn
  haveI := h2.to_normal
  exact BaseRat.exists_normal_roots L h3 hn.ne'

open Classical in

theorem exists_order : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ρ.LevelOf D.nexp → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), TwOK i k Q ψ → ∃ n : ℕ, 0 < n ∧ (∀ x, (ρ.B i j b).de.chi x ^ n = 1 ∧ (((ρ.B i j b).de.chi x : Circle) : ℂ) ∈ (ρ.ek i b k).fieldRange) ∧ (∀ x, (ρ.tw i b k Q ψ).chi x ^ n = 1 ∧ (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) ∈ (ρ.ek i b k).fieldRange) ∧ (∀ p, (ρ.B i j b).G.P.chi p ^ n = 1 ∧ (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ (ρ.ek i b k).fieldRange) := by
  intro D ρ hρ hU i j b k Q ψ htw
  obtain ⟨n, hn, hde⟩ := BaseRat.de_values hρ i j b
  have hle := GlobalTheory.RayInFrac.range_e_le_ek D ρ hρ i b k
  have hl : D.ntw.l i ^ k ≠ 0 := pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero
  have hc : Nat.card (ρ.B i j b).G.P.H ≠ 0 := Nat.card_pos.ne'
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := htw.2.2.2.2.1 σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨n * D.ntw.l i ^ k * Nat.card (ρ.B i j b).G.P.H, Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hn hl) hc),
    fun x => ⟨?_, hle (hde x).2⟩, fun x => ?_, fun p => ⟨?_, hle (UnivRat.type_mem_range i j b hU p)⟩⟩
  · have : (ρ.B i j b).de.chi x ^ n = 1 := Circle.ext (by rw [Circle.coe_pow, (hde x).1, Circle.coe_one])
    rw [mul_assoc, pow_mul, this, one_pow]
  · obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    have e : (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k (ψ σ : (D.ntw.Ok i k)ˣ) :=
      charOf_eq ρ.rc (ρ.eOk i b k) htw.2.2.1 hσ hl (hpow σ)
    have : (ρ.tw i b k Q ψ).chi x ^ (D.ntw.l i ^ k) = 1 := Circle.ext (by
      rw [Circle.coe_pow, e, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, Circle.coe_one])
    exact ⟨by rw [mul_comm n, mul_assoc, pow_mul, this, one_pow], e ▸ ⟨_, rfl⟩⟩
  · rw [pow_mul', ← map_pow, pow_card_eq_one', map_one, one_pow]

open Classical in

theorem mu_mem_small : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (ρ : Setup D.ntw), ρ.Good → RealPin Rl cG ρ → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ PP ∈ (ρ.B i j b).G.Pg, ∀ u, (((ρ.B i j b).G.mu PP u : Circle) : ℂ) ∈ (embLL0 D).fieldRange := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F ρ hρ hpin hT hcore hgal hval hroots i j b PP hPP u
  obtain ⟨a, ha⟩ := hρ.Pg i j b PP hPP
  exact UnivRat.char_mem_of_over hroots ha ((ρ.B i j b).G.muC PP) u

open Classical in

theorem isLevDatum_flat : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (t : Twist D Circle), t.Good → B.admitted t.Q → ∀ (N : ℕ) (k : Subfield ℂ), (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ t.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ t.Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ p, ((B.G.P.chi p : ℂˣ) : ℂ) ∈ k) → (∀ PP ∈ B.G.Pg, ∀ u, ((B.G.mu PP u : Circle) : ℂ) ∈ k) → (∀ x, ((B.de.chi x : Circle) : ℂ) ∈ k) → (∀ x, ((t.chi x : Circle) : ℂ) ∈ k) → IsLevDatum B.F.ψ S T B.F.ΛS B.F.ΛT N k B.F.f₀ (B.vecFlat t) := by
  intro D S T B hB t ht hQ N k hN h2 hP hmu hde htk
  have key : ∀ {s : Twist D Circle}, s.Good → (∀ x, ((s.chi x : Circle) : ℂ) ∈ k) → ∀ PP ∈ s.Q, ∀ x,
      ((s.resC PP x : ℂˣ) : ℂ) ∈ k := by
    intro s hs hk PP hPP u
    obtain ⟨x, hx⟩ := exists_isLocUnit (hs.split.isIdemAt hPP) u
    have := hk x
    rw [hx.eq (hs.res PP hPP)] at this
    exact this
  refine UnivRat.isLevDatum_vecAt hB hQ h2 N hN k hP hmu (key hB.de hde) _ fun PP y => ?_
  unfold flat
  split_ifs with h
  · exact key ht htk PP.1 PP.2 _
  · exact zero_mem _

open Classical in

theorem exists_coef_sum : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (F : Face D A3.A) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw), ρ.Good → RealPin Rl cG ρ → GlobalTheory.Hk3.Core Rl.toRealDat F → IoExt Rl.toRealDat → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → ∀ (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ), (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) → ∀ (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W) (c : ℂ), c ≠ 0 → IsScaleAt Rl (ρ.B i j b) u c0 c → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank), P ∈ ρ.lat i j b (ρ.eO i b).range h → ∃ (m : ℕ) (o : Fin m → ℂ) (v : Fin m → VsV D j D.what₂.LL), (∀ t, o t ∈ (ρ.eO i b).range) ∧ (∀ t mm, D.what₂.embLL (MvPolynomial.coeff mm (v t : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈ (embLL0 D).fieldRange) ∧ c • P = ∑ t, o t • Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 (v t)) := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG F v₀ ρ hρ hpin hcore hio i j b hv u hu c0 c hc hs h P hP
  have hB := hρ.base i j b
  have hBo := BaseRat.baseOf_of_realPin hcore.lev hρ hpin i j b
  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  obtain ⟨hP1, hP2⟩ := (mem_harmLat _ _ _).1 hP
  obtain ⟨m, o, φ, hsum⟩ := Submodule.mem_span_set'.1 hP2
  choose G _ hG using fun t => (φ t).2
  choose v hv1 hv2 using fun t => UnivRat.exists_vec_of_small j hBo.lam (G t)
  refine ⟨m, fun t => o t, v, fun t => (o t).2, hv1, sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm _
    (sub_mem (Submodule.smul_mem _ _ hP1) (sum_mem fun t _ => Submodule.smul_mem _ _
      (BaseRat.ioP_mem_valSpace hcore hio hv hB hBo hu _))) ?_)⟩
  rw [map_sub, map_smul, map_sum, ← hsum, Finset.smul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hs (v t), ← hv2 t, ← hG t, smul_comm]
  rfl

open Classical in

theorem exists_sum_read : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → FWTie T Rl.toRealDat κ v₀ → TieIn T Rl.toRealDat κ v₀ → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → ∀ (C : Cover T ((j : ℕ) + 1) T.σ₀), GoodCover T Rl.toRealDat j C (κ j).n → ∀ (φ : GA D (Wc D j) → ℂ), IsRat T j hV C (κ j) φ → (∀ k : GA D (Wc D j), Lev.IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) 1 k → ∀ g, φ (g * k) = φ g) → ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, a t ∈ C.σ₂.fieldRange) ∧ φ = ∑ t, a t • evW YS v₀ j (y t).1 := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O hnV hT hcore hfw hti j hV hpins C hC φ hφ hinv
  have hpb : T.pb = Rl.toRealDat.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev (hpins.2.tuple ()).half
  have hev := hfw.evaluates (GlobalTheory.CuspValues.jEvExists_and_jEvBar D Γ Pl0 T0 A3.A T Rl.toRealDat κ v₀ hcore.lev hcore.models hti hpb).1
  obtain ⟨n, z, x, hz, e⟩ := BaseRat.exists_sum_evW YS hti hnV hcore.lev hpb (BaseRat.readsAs_one YS hfw hev hV) hC hφ hinv
  exact ⟨n, z, x, hz, by rw [e, one_smul]⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

def Readable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (K : Subfield ℂ) (φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, a t ∈ K) ∧
    φ = ∑ t, a t • evW YS v₀ j (y t).1

section Read
variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {j : Fin D.R.m} {K : Subfield ℂ}

theorem Readable.zero : Readable YS v₀ j K 0 := ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, by simp⟩

theorem Readable.add {φ ψ : GA D (Wc D j) → ℂ} (h : Readable YS v₀ j K φ) (h' : Readable YS v₀ j K ψ) :
    Readable YS v₀ j K (φ + ψ) := by
  obtain ⟨m, a, y, ha, rfl⟩ := h
  obtain ⟨m', a', y', ha', rfl⟩ := h'
  refine ⟨m + m', Fin.append a a', Fin.append y y', fun t => ?_, ?_⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact ha t
    · rw [Fin.append_right]; exact ha' t
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem Readable.smul {φ : GA D (Wc D j) → ℂ} (h : Readable YS v₀ j K φ) {c : ℂ} (hc : c ∈ K) :
    Readable YS v₀ j K (c • φ) := by
  obtain ⟨m, a, y, ha, rfl⟩ := h
  exact ⟨m, fun t => c * a t, y, fun t => mul_mem hc (ha t), by rw [Finset.smul_sum]; simp only [smul_smul]⟩

theorem Readable.sum {ι : Type} (s : Finset ι) {φ : ι → GA D (Wc D j) → ℂ} (h : ∀ t ∈ s, Readable YS v₀ j K (φ t)) :
    Readable YS v₀ j K (∑ t ∈ s, φ t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Readable.zero YS v₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add YS v₀ (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

theorem Readable.mono {φ : GA D (Wc D j) → ℂ} (h : Readable YS v₀ j K φ) {K' : Subfield ℂ} (hK : K ≤ K') :
    Readable YS v₀ j K' φ := by
  obtain ⟨m, a, y, ha, rfl⟩ := h
  exact ⟨m, a, y, fun t => hK (ha t), rfl⟩

end Read

section Range
variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem inv_smul_mem_range_of_readable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) (k : ℕ)
    {φ : GA D (Wc D j) → ℂ} (h : Readable YS v₀ j (ρ.ek i b k).fieldRange φ) :
    ν⁻¹ • φ ∈ Set.range (rdK (realRd YS v₀ hρ i j b ν) hρ k) := by
  obtain ⟨m, a, y, ha, rfl⟩ := h
  have key : ∀ t, ∃ x, rdK (realRd YS v₀ hρ i j b ν) hρ k x = ν⁻¹ • (a t • evW YS v₀ j (y t).1) := by
    intro t
    obtain ⟨z, hz⟩ := ha t
    obtain ⟨p, d, hd, hzd⟩ := D.ntw.Ok_gen i k z
    refine ⟨Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p ⊗ₜ (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm
      (((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) d)⁻¹ : FractionRing (D.ntw.O i)) ⊗ₜ[S.Ks] (y t)), ?_⟩
    rw [rdK_tmul]
    erw [realRd_tmul YS v₀ hρ i j b ν (((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) d)⁻¹ : FractionRing (D.ntw.O i))) (y t)]
    have h1 : ρ.eOk i b k (Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p) =
        a t * ρ.e i b (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) d) := by
      have e1 := congrArg (ρ.ek i b k) hzd
      rw [map_mul, hz] at e1
      rw [Setup.eOk, RingHom.comp_apply, ← e1]
      congr 1
      have e2 := hρ.ek_e i b k d
      rw [Setup.eOk, Setup.eO, RingHom.comp_apply, RingHom.comp_apply] at e2
      exact e2
    have h0 : ρ.e i b (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) d) ≠ 0 := by
      rw [map_ne_zero]
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd))
    rw [smul_smul, smul_smul, map_inv₀, h1]
    congr 1
    field_simp
  choose x hx using key
  refine ⟨∑ t, x t, ?_⟩
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => hx t

end Range

section Inv
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem gen_inv {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {t : Twist D Circle} (ht : t.Good)
    (hQ : (ρ.B i j b).admitted t.Q) (s : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) {k : GA D (Wc D j)}
    (hk : Lev.IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) 1 k) (g : GA D (Wc D j)) :
    (ρ.B i j b).gen (ρ.om i j b 1) t s P (g * k) = (ρ.B i j b).gen (ρ.om i j b 1) t s P g := by
  obtain ⟨hk1, hk2, hk3⟩ := hk
  refine DualType.gen_mul_right_of_red (hρ.base i j b) (D.sp.V_sig _) ht hQ (hρ.weil_base i j b) hk1 ?_ ?_ s P g
  · rw [hpin.frT i j b]; exact parLev_St hk2
  · intro PP hPP
    rw [hpin.frT i j b]
    have hPP' : PP ∈ (Rl.datWp j Rl.triv).Pg := by rw [hpin.Pg i j b] at hPP; exact hPP
    have h1 := congrFun hk3 ⟨PP, hPP'⟩
    exact (GlobalTheory.PrincipalLevel.upperLeftBlock_eq_one_iff_of_mem_blockTri _ (FWT.rank_Wc j).symm _).1 h1

end Inv

section Lemmas

open Classical in

theorem exists_cover (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (hU : ρ.LevelOf D.nexp) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hti : TieIn T Rl.toRealDat κ v₀)
    (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsplit : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (htw : TwOK i k Q ψ)
    (hcls : ClsQ (D := D) Q) :
    ∃ C : Cover T ((j : ℕ) + 1) T.σ₀, GoodCover T Rl.toRealDat j C (κ j).n ∧ (embLL0 D).fieldRange ≤ C.σ₂.fieldRange ∧
      C.σ₂.fieldRange ≤ (ρ.ek i b k).fieldRange ∧
      (∀ PP ∈ (ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q, ((C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
      (∀ x, (((ρ.B i j b).de.chi x : Circle) : ℂ) ∈ C.σ₂.fieldRange) ∧
      (∀ x, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) ∈ C.σ₂.fieldRange) ∧
      (∀ p, (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange) ∧
      (∀ PP ∈ (ρ.B i j b).G.Pg, ∀ u, (((ρ.B i j b).G.mu PP u : Circle) : ℂ) ∈ C.σ₂.fieldRange) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ x, ((ρ.B i j b).de.chi * (ρ.tw i b k Q ψ).chi) x ^ n = 1) ∧
      (∀ PP ∈ (ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q,
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :=  by
  obtain ⟨pd, haux, hpl, hpd, h2q⟩ := exists_level D ρ hρ hsplit i j b k Q ψ htw hcls
  obtain ⟨n, hn, hde, ht, hP⟩ := exists_order D ρ hρ hU i j b k Q ψ htw
  have hmu := mu_mem_small D Γ Pl0 I0 T0 A3 T Rl cG S YS F ρ hρ hpin hT hcore hgal hval hroots i j b
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hpd0 : pd ≠ 0 := haux.1.pos.ne'
  obtain ⟨L₀, hfin₀, hgal₀, h1, h2, h3, h4, -⟩ := (GlobalTheory.RayInFrac.exists_rayField_le D ρ hρ i b hRF hray
    (D.host.g 0 * D.host.g 1) pd dvd_rfl (by rw [mul_assoc _ D.host.pde]; exact dvd_mul_right _ _) hpd0 hpl).2 k
  obtain ⟨L, hfin, hnor, hL, hLK, hrt⟩ := exists_field_roots L₀ _ hfin₀ (hgal₀ hgal) h2 n hn
  have hLL : (embLL0 D).fieldRange ≤ L.toSubfield := fun z hz => hL (h1 hz)
  rw [← hMg] at haux h3 h4
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT pd haux
  have hle : T.Q.c.F ≤ L := by
    intro a ha'
    refine hLL ⟨S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩), ?_⟩
    have e1 : res T D.what₂.embLL = T.σ₀ := res_embLL T hti.alg hT.pins.2.2.1
    change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩) : ↥D.LL0) : D.what₂.LL) = a
    rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
    exact RingHom.congr_fun e1 ⟨a, ha'⟩
  have hM0 : T.Q.l.M * pd ≠ 0 := mul_ne_zero (by have := T.Q.l.three_le; omega) hpd0
  have hz : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (T.Q.l.M * pd) ∈ L :=
    hL (h4 _ (Complex.isPrimitiveRoot_exp _ hM0).pow_eq_one)
  have hsm : SmallIn Rl.toRealDat j (L.val : L →+* ℂ) := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hval.mu0 j v hv
      exact ⟨⟨embLL0 D y, hLL ⟨y, rfl⟩⟩, hy⟩
    · obtain ⟨y, hy⟩ := hval.eta v hv
      exact ⟨⟨embLL0 D y, hLL ⟨y, rfl⟩⟩, hy⟩
  have hrayL : RayIn D (T.Q.l.M * pd) L.toSubfield := by
    obtain ⟨H, i1, i2, i3, i4, hH, jj, hjj, hv⟩ := h3
    exact ⟨H, i1, i2, i3, i4, hH, jj, hjj, fun x => hL (hv x)⟩
  obtain ⟨C, hCpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j ⟨by omega, j.2⟩ (κ j).n pd I
    haux hK hprod hsup L hle hz hsm hrayL
  refine ⟨C, hG, hfr ▸ hLL, hfr ▸ hLK, hCpd ▸ hpd, fun x => ?_, fun x => ?_, fun p => ?_, fun PP hPP u => ?_,
    ⟨n, hn, fun x => by rw [MonoidHom.mul_apply, mul_pow, (hde x).1, (ht x).1, one_mul]⟩, h2q⟩ <;> rw [hfr]
  · exact hrt _ (hde x).2 (by rw [← Circle.coe_pow, (hde x).1, Circle.coe_one])
  · exact hrt _ (ht x).2 (by rw [← Circle.coe_pow, (ht x).1, Circle.coe_one])
  · exact hrt _ (hP p).2 (by rw [← Units.val_pow_eq_pow_val, (hP p).1, Units.val_one])
  · exact hLL (hmu PP hPP u)

open Classical in

theorem exists_isTwist (t t' : Twist D Circle) (ht : t.Good) (ht' : t'.Good) (hdisj : SplitSet (t.Q ∪ t'.Q))
    (hd : Disjoint t.Q t'.Q) (pd : ℕ) {k : Type} [Field k] (σ : k →+* ℂ)
    (hord : ∃ n : ℕ, 0 < n ∧ ∀ x, (t.chi * t'.chi) x ^ n = 1)
    (hpd : ∀ PP ∈ t.Q ∪ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hval : ∀ x, (((t.chi * t'.chi) x : Circle) : ℂ) ∈ σ.fieldRange) :
    ∃ δ : Formalism.L2.Host.HChar D.host.E, IsTwist pd σ δ (t.chi * t'.chi) := GlobalTheory.TwistProduct.isTwist_mul D t t' ht ht' hdisj hd pd k σ hord hpd hval

open Classical in

theorem isLevDatum_vecFlat {S T : HSp D} (B : Base S T) (hB : B.Good) (t : Twist D Circle) (ht : t.Good)
    (hQ : B.admitted t.Q) (N : ℕ) (k : Subfield ℂ)
    (hN : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ t.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (h2 : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ t.Q →
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hP : ∀ p, ((B.G.P.chi p : ℂˣ) : ℂ) ∈ k) (hmu : ∀ PP ∈ B.G.Pg, ∀ u, ((B.G.mu PP u : Circle) : ℂ) ∈ k)
    (hde : ∀ x, ((B.de.chi x : Circle) : ℂ) ∈ k) (htk : ∀ x, ((t.chi x : Circle) : ℂ) ∈ k) :
    IsLevDatum B.F.ψ S T B.F.ΛS B.F.ΛT N k B.F.f₀ (B.vecFlat t) := isLevDatum_flat D S T B hB t ht hQ N k hN h2 hP hmu hde htk

theorem exists_coef {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {F : Face D A3.A} (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hio : IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ)
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W} {c : ℂ} (hc : c ≠ 0) (hs : IsScaleAt Rl (ρ.B i j b) u c0 c)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    ∃ (m : ℕ) (o : Fin m → ℂ) (v : Fin m → VsV D j D.what₂.LL), (∀ t, o t ∈ (ρ.eO i b).range) ∧
      (∀ t mm, D.what₂.embLL (MvPolynomial.coeff mm (v t : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈
        (embLL0 D).fieldRange) ∧
      c • P = ∑ t, o t • Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 (v t)) := exists_coef_sum D Γ Pl0 I0 T0 A3 T Rl cG F v₀ ρ hρ hpin hcore hio i j b hv u hu c0 c hc hs h P hP

theorem readable_of_isRat {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : FWTie T Rl.toRealDat κ v₀)
    (hti : TieIn T Rl.toRealDat κ v₀) (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j)
    (hpins : OMPins T Rl.toRealDat κ v₀ O j) (C : Cover T ((j : ℕ) + 1) T.σ₀) (hC : GoodCover T Rl.toRealDat j C (κ j).n)
    {φ : GA D (Wc D j) → ℂ} (hφ : IsRat T j hV C (κ j) φ)
    (hinv : ∀ k : GA D (Wc D j), Lev.IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) 1 k → ∀ g, φ (g * k) = φ g) :
    Readable YS v₀ j C.σ₂.fieldRange φ := exists_sum_read D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O hnV hT hcore hfw hti j hV hpins C hC φ hφ hinv

end Lemmas

section Main

theorem natM_mem_Mb (T : CoreJ D) : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
  have hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb := Ideal.mul_le_left
  rw [T.Q.l.prod] at hle
  exact hle (Ideal.mem_span_singleton_self _)

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem harmVec_eq {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ) (w : (Rl.cV j).W)
    (f : WO (Vc D j) (Wc D j) → ℂ) :
    harmVec Rl.toRealDat j u w f = (ρ.B i j b).F.fock f (Rl.ioP j (PiTensorProduct.tprod ℂ u) w) := by
  rw [GlobalTheory.ExportSeries.Frame.fock, hpin.psi, hpin.inf, hpin.cartT, hpin.onbT, funext (hpin.onbS i j b)]
  rfl

end Main

section Thm

open Classical in

theorem ratTwist_of_isRatScalar (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    {F : Face D A3.A} (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) (hU : ρ.LevelOf D.nexp) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0))
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hfw : FWTie T Rl.toRealDat κ v₀) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (hpins : OMPins T Rl.toRealDat κ v₀ O j) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsplit : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν) :
    RatTwist hρ (realRd YS v₀ hρ i j b ν) := by
  intro k Q ψ htw hcls s h P hd x hx
  obtain ⟨hQ', hQs, rfl⟩ := hx
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D D.nd D.ntw ρ hρ i j b k Q ψ htw
  obtain ⟨gramR, c0R, c0L, hft, u, hu, c, ph, hc0, hph1, rfl, hsc, hrat⟩ := hν
  obtain ⟨C, hgood, hLL0, hLe, hpd, hdeC, htC, hPC, hmuC, hord, h2q⟩ :=
    exists_cover hRF YS κ v₀ hρ hpin hU i j b hT hcore hti hgal hval hray hroots hsplit k Q ψ htw hcls

  have hQG : hQ' ∈ GfC (Vc D j) := by
    refine GlobalTheory.WeilProduct.mem_GfC_of_supp ?_ hQs
    have hIS := ht.split.isIdemSum
    rw [RingHom.map_add, GlobalTheory.PlaceDatum.infPart_idemSum hIS,
      GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum hIS), add_zero]
  have hs : h * hQ' ∈ GfC (Vc D j) := mul_mem hd.fin hQG

  have hsplitQ : SplitSet ((ρ.B i j b).de.Q ∪ (ρ.tw i b k Q ψ).Q) := by
    obtain ⟨P0, -, h2, h3⟩ := hadm.1.split
    exact h3.mono h2
  obtain ⟨δ, hδ⟩ := exists_isTwist (ρ.B i j b).de (ρ.tw i b k Q ψ) (hρ.base i j b).de ht hsplitQ hadm.2 C.d.pd C.σ₂ hord hpd
    (fun x => by rw [MonoidHom.mul_apply, Circle.coe_mul]; exact mul_mem (hdeC x) (htC x))

  have hMPg : ∀ PP ∈ Rl.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hhalf := (hpins.2.tuple ()).half
    have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
      rw [hhalf.1]
      exact Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    exact h2 (natM_mem_Mb T)
  have hdat0 := isLevDatum_vecFlat (ρ.B i j b) (hρ.base i j b) (ρ.tw i b k Q ψ) ht hadm (T.Q.l.M * C.d.pd)
    C.σ₂.fieldRange (fun PP hPP => by
      rw [Nat.cast_mul]
      rcases hPP with h1 | h1
      · rw [hpin.Pg i j b] at h1
        exact Ideal.mul_mem_right _ _ (hMPg PP h1)
      · exact Ideal.mul_mem_left _ _ (hpd PP h1))
    (fun PP hPP => by
      rcases hPP with h1 | h1
      · rw [hpin.Pg i j b] at h1
        exact (hpins.2.tuple ()).half.2.2 PP (Or.inl h1)
      · exact h2q PP h1) hPC hmuC hdeC htC
  have hdat : IsLevDatum Rl.ψ (Vc D j) (Wc D j) (Rl.ΛV j) (Rl.ΛW j) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (Rl.vacP j)
      ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) := by
    rw [hpin.psi i j b, hpin.latS i j b, hpin.latT i j b, hpin.vac i j b] at hdat0
    exact hdat0

  have hmuV := muVal_detChar (Vc D j) ht.real
  have hmuW := muVal_detChar (Wc D j) ht.real
  have hw1 : (ρ.B i j b).IsWeil 1 (ρ.om i j b 1) := hρ.weil_base i j b
  obtain ⟨om', hom', -⟩ := GlobalTheory.SplitChange.exists_twist hw1 ht.isHeckeChar ht.real hmuV hmuW
  have hom'' : IsWeilDatumO Rl.toRealDat.ψ (Vc D j) (Wc D j)
      (Lift.chrTh (Lift.tup Rl.toRealDat.mu0 ((ρ.B i j b).de.chi * (ρ.tw i b k Q ψ).chi)) Rl.toRealDat.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.toRealDat.mu0 ((ρ.B i j b).de.chi * (ρ.tw i b k Q ψ).chi)) Rl.toRealDat.eta ((j : ℕ) + 1)).2
      om' := by
    have e0 : (ρ.B i j b).F.ψ = Rl.toRealDat.ψ := hpin.psi i j b
    have e1 : (ρ.B i j b).mu * 1 * (ρ.tw i b k Q ψ).chi =
        (Lift.chrTh (Lift.tup Rl.toRealDat.mu0 ((ρ.B i j b).de.chi * (ρ.tw i b k Q ψ).chi)) Rl.toRealDat.eta
          ((j : ℕ) + 1)).1 := by
      simp only [Lift.chrTh, Lift.tup, Base.mu, hpin.mu0 i j b, mul_one, mul_assoc]
    have e2 : (ρ.B i j b).mu * 1 * (ρ.B i j b).eta⁻¹ * (ρ.tw i b k Q ψ).chi =
        (Lift.chrTh (Lift.tup Rl.toRealDat.mu0 ((ρ.B i j b).de.chi * (ρ.tw i b k Q ψ).chi)) Rl.toRealDat.eta
          ((j : ℕ) + 1)).2 := by
      simp only [Lift.chrTh, Lift.tup, Base.mu, hpin.mu0 i j b, hpin.eta i j b, mul_one]
      rw [mul_assoc, mul_assoc, mul_comm _ (ρ.tw i b k Q ψ).chi, ← mul_assoc, ← mul_assoc, mul_assoc _ (ρ.B i j b).de.chi]
    rw [← e0, ← e1, ← e2]
    exact hom'

  obtain ⟨m, o, v, ho, hv, hcP⟩ := exists_coef v₀ hρ hpin hcore hio i j b (hti.hv₀ j _) hu hc0 hsc hd.mem
  have hgen : ∀ (P' : PolF D (Wc D j).rank (Vc D j).rank) g,
      (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') P' g =
        ((detChar (Wc D j) (ρ.tw i b k Q ψ).chi g : Circle) : ℂ) *
          thetaKO (ρ.om i j b 1) (h * hQ') g ((ρ.B i j b).F.fock ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) P') :=
    fun _ _ => rfl

  have hterm : ∀ t', Readable YS v₀ j (ρ.ek i b k).fieldRange
      (ph • (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ')
        (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t')))) := by
    intro t'
    have hw : c0L j (v t') ∈ ratVec Rl.toRealDat j (c0L j) C.σ₂.fieldRange :=
      Submodule.subset_span ⟨v t', fun mm => hLL0 (hv t' mm), rfl⟩
    have hser := hrat C hgood hLL0 (h * hQ') hs _ hdat (c0L j (v t')) hw
    have hX := (hser.2 δ _ hδ).2 om' hom''
    have hY := isRat_mul hX (htC (detRoot (Vc D j) (h * hQ')))
    have heq : (fun g => (((ρ.tw i b k Q ψ).chi (detRoot (Vc D j) (h * hQ')) : Circle) : ℂ) *
        (ph * thetaKO om' (h * hQ') g (harmVec Rl.toRealDat j u (c0L j (v t'))
          ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ))))) =
        ph • (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ')
          (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t'))) := by
      funext g
      erw [harmVec_eq hpin i j b u]
      have hth : IsThetaFunO (ρ.B i j b).F.ψ (Vc D j) (Wc D j) ((ρ.B i j b).F.fock ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ))
          (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t')))) :=
        Base.isThetaFunO_fock_vecAt (hρ.base i j b) hadm _ _
      rw [GlobalTheory.SplitChange.thetaKO_twist hw1 ht.isHeckeChar ht.real hom' hmuV hmuW _ _ hth, Pi.smul_apply, smul_eq_mul, hgen]
      have hn : (((ρ.tw i b k Q ψ).chi (detRoot (Vc D j) (h * hQ')) : Circle) : ℂ) ≠ 0 := by
        intro e
        have := Circle.norm_coe ((ρ.tw i b k Q ψ).chi (detRoot (Vc D j) (h * hQ')))
        rw [e, norm_zero] at this
        exact zero_ne_one this
      change _ * (ph * (((detChar (Wc D j) (ρ.tw i b k Q ψ).chi g : Circle) : ℂ) *
        (((ρ.tw i b k Q ψ).chi (detRoot (Vc D j) (h * hQ')) : Circle) : ℂ)⁻¹ * _)) = _
      field_simp
    rw [heq] at hY
    refine (readable_of_isRat YS κ v₀ O hnV hT hcore hfw hti j hV hpins C hgood hY fun k' hk' g => ?_).mono YS v₀ hLe
    simp only [Pi.smul_apply]
    rw [gen_inv hρ hpin i j b ht hadm _ _ hk']

  have hph0 : ph ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1
  have hoK : ∀ t', o t' ∈ (ρ.ek i b k).fieldRange := by
    intro t'
    obtain ⟨y, hy⟩ := hρ.range_le i b k (ho t')
    rw [← hy]
    exact ⟨_, rfl⟩
  have hsum := Readable.sum YS v₀ Finset.univ fun t' _ => (hterm t').smul YS v₀ (hoK t')
  have hLP : (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') P = (ph * c)⁻¹ • ∑ t', o t' • (ph •
      (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t')))) := by
    have e : c • (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') P = ∑ t', o t' •
        (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t'))) := by
      rw [← map_smul, hcP, map_sum]
      exact Finset.sum_congr rfl fun t' _ => map_smul _ _ _
    have e2 : ∑ t', o t' • (ph • (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ')
        (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t')))) = ph • ∑ t', o t' •
        (ρ.B i j b).gen (ρ.om i j b 1) (ρ.tw i b k Q ψ) (h * hQ') (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j (v t'))) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun t' _ => smul_comm _ _ _
    rw [e2, ← e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hph0 hc0), one_smul]
  rw [hLP]
  exact inv_smul_mem_range_of_readable YS v₀ hρ i j b (ph * c) k hsum

end Thm

open GlobalTheory.BigOn.Exp in

theorem ratTwist : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → (D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) → RatHyp T Rl F κ v₀ O i j hV → ∀ ν, IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν → RatTwist hρ (realRd YS v₀ hρ i j b ν) := by
  intro _ hRF _ D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hU hde H ν hν
  obtain ⟨fw⟩ := H.fw
  exact ratTwist_of_isRatScalar hRF YS κ v₀ hρ hpin hU i j b hV O H.size H.laws H.core fw H.tieIn H.io H.pins H.galois
    H.small.val H.small.ray H.small.roots hde hν

end GlobalTheory.SeriesTie.TwistRat
