import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeToStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriplesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTripleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTripleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbourStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationCommHeisenbergIntertwinerStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section
namespace GlobalTheory.InertSign

theorem Iop_smul (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (a : ℂ) (F : VC D N N' → ℂ) :
    Iop D T A B (a • F) = a • Iop D T A B F := by
  funext z
  simp only [Iop, U, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm a, ← smul_eq_mul a, smul_finsum]
  congr 1
  exact finsum_congr fun q => by rw [smul_eq_mul]; ring

theorem ThSp_smul {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (a : ℂ) {F : VC D N N' → ℂ}
    (h : F ∈ ThSp D T A) : a • F ∈ ThSp D T A := by
  refine ⟨h.1.const_smul a, fun x hx z => ?_⟩
  have := h.2 x hx z
  simp only [U, Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [← this]; ring

theorem moves_unique {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L L' : Lat D n} (h : Moves D g L) (h' : Moves D g L') :
    L = L' := by
  ext x; rw [h x, h' x]

theorem sd_of_moves {D : D7} {n : ℕ} {g : GA D n} {L : Lat D n} (h : Moves D (g : GL (Fin n) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D n
  rw [moves_unique h (h1 g).1]; exact (h1 g).2

theorem moves_one (D : D7) (n : ℕ) : Moves D ((1 : GA D n) : GL (Fin n) (AE D)) (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 1).1

theorem intG_of_moves {D : D7} {n : ℕ} {g g' : GA D n} {L : Lat D n} (h : Moves D (g : GL (Fin n) (AE D)) L)
    (h' : Moves D (g' : GL (Fin n) (AE D)) L) : IntG D ((g⁻¹ * g' : GA D n) : GL (Fin n) (AE D)) := by
  obtain ⟨Lt, h1, -, h3, -⟩ := exists_lattice_of_adelic_point D n
  exact AdLattice.intG_of_mem D n _ ((h3 g g').1 ((moves_unique (h1 g).1 h).trans (moves_unique h' (h1 g').1)))

theorem eqAt_of_moves {D : D7} {n p : ℕ} (hp : p.Prime) {g : GA D n} {L : Lat D n}
    (h : Moves D (g : GL (Fin n) (AE D)) L) (ht : TrivAt D p (g : GL (Fin n) (AE D))) : EqAt D p (stdL D n) L := by
  obtain ⟨Lt, h1, -, -, -, h5⟩ := exists_lattice_of_adelic_point D n
  rw [moves_unique h (h1 g).1]; exact h5 p g hp ht

theorem suppInert_one (D : D7) (n : ℕ) : SuppInert D ((1 : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq _ => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).1

theorem suppInert_mul {D : D7} {n : ℕ} {g h : GA D n} (hg : SuppInert D (g : GL (Fin n) (AE D)))
    (hh : SuppInert D (h : GL (Fin n) (AE D))) : SuppInert D ((g * h : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq hi => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).2.1 _ _ (hg q hq hi) (hh q hq hi)

theorem suppInert_inv {D : D7} {n : ℕ} {g : GA D n} (hg : SuppInert D (g : GL (Fin n) (AE D))) :
    SuppInert D ((g⁻¹ : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq hi => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).2.2 _ (hg q hq hi)

theorem stable_of_inert {D : D7} {q : ℕ} (hq : q.Prime) (hi : InertQ D q) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal)
    (hqP : (q : 𝓞 D.host.E) ∈ P) : ∀ a ∈ P, sgO D a ∈ P := by
  intro a ha
  have h0 : P ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have := Ideal.smul_mem_pointwise_smul D.host.conj a P ha
  rw [hi P hP.isPrime h0 hqP] at this
  exact this

theorem exists_move {D : D7} {n q : ℕ} (hq : q.Prime) (hi : InertQ D q) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal)
    (hqP : (q : 𝓞 D.host.E) ∈ P) {B : Lat D n} {x : Fin n → D.host.E} (hB : SD D B) (hx : NbD D P B x) :
    ∃ (g : GA D n) (w : Fin n → D.host.E), SuppInert D (g : GL (Fin n) (AE D)) ∧ NbD D P B w ∧
      (∀ h : GA D n, Moves D (h : GL (Fin n) (AE D)) B → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) (nbr D B x)) ∧
      (∀ h : GA D n, Moves D (h : GL (Fin n) (AE D)) (nbr D B w) →
        Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) (nbr D B w)) ∧
      (SD D (nbr D B w) → SD D (nbr D B x) → Tri D P (nbr D B w) B (nbr D B x)) := by
  have hst := stable_of_inert hq hi hP hqP
  obtain ⟨b, x', lam, m, hb, hx', hp, hθ, hw, hM, hl, hm, h1, h2⟩ := GlobalTheory.T.exists_transvection_vectors_neighbour D n q hq P hP hqP hst B x hB hx
  have hA : nbr D B (b + x') = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b + x'} := by rw [nbr, hM]
  obtain ⟨s, hs, hsA, hsB⟩ := GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime D n q P hst (nbM D B x) b x' lam m hp
    (fun y hy => by rw [← hM] at hy; exact hy.2) hw.2.2 hl hm h1 h2
  rw [← hA] at hsA
  rw [← hb, ← hx'] at hsB
  obtain ⟨g, hg, hmv⟩ := GlobalTheory.T.exists_local_component_unitary_matrix D n q hq s hs
  have hqs : ∀ (v : Fin n → D.host.E) (L : Lat D n), (∀ p ∈ P, p • v ∈ nbM D B x) →
      L = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {v} → ∀ y ∈ L, ((q : D.host.E) ^ 1) • y ∈ nbM D B x := by
    intro v L hv hL y hy
    rw [hL] at hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hc
    have e : ∀ u : Fin n → D.host.E, ((q : D.host.E) ^ 1) • u = (q : 𝓞 D.host.E) • u := by
      intro u; rw [pow_one, ← algebraMap_smul D.host.E (q : 𝓞 D.host.E) u, map_natCast]
    rw [e, smul_add, smul_comm]
    exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ (hv _ hqP))
  refine ⟨g, b + x', fun p hp hn => hg p hp (fun h => hn (h ▸ hi)), hw, fun h hh => hmv h B _ hh ⟨1, ?_, ?_⟩ hsB,
    fun h hh => hmv h _ _ hh ⟨0, by simp, by simp⟩ hsA, fun a c => ⟨a, hB, c, nbM D B x, b, x', hA, hb, hx', hp, hθ⟩⟩
  · intro y hy
    exact (le_sup_left : nbM D B x ≤ nbr D B x) (hqs b B (fun p h => (hp p h).1) hb y hy)
  · intro y hy
    exact (hqs x' _ (fun p h => (hp p h).2) hx' y hy).1

section Core

variable {D : D7} {T : Tor D} {N N' n : ℕ} (Λ : Lat D n → AddSubgroup (VC D N N'))
  (ω : GA D n → (VC D N N' → ℂ) → (VC D N N' → ℂ)) (e0 : VC D N N' → ℂ) (σ : ℂ)

theorem core (hσ : σ * σ = 1) (hnz : e0 ≠ 0) (he0 : e0 ∈ ThSp D T (Λ (stdL D n)))
    (hI : ∀ L₁ L₂, SD D L₁ → SD D L₂ → ∀ e ∈ ThSp D T (Λ L₁), Iop D T (Λ L₁) (Λ L₂) e ∈ ThSp D T (Λ L₂) ∧
      Iop D T (Λ L₂) (Λ L₁) (Iop D T (Λ L₁) (Λ L₂) e) = e)
    (hII : ∀ L, SD D L → ∀ e ∈ ThSp D T (Λ L), Iop D T (Λ L) (Λ L) e = e)
    (hline : ∀ L, SD D L → ∀ F ∈ ThSp D T (Λ L), ∀ G ∈ ThSp D T (Λ L), G ≠ 0 → ∃ c : ℂ, F = c • G)
    (hmul : ∀ g h, ω (g * h) e0 = ω g (ω h e0))
    (hsm : ∀ g L, SD D L → ∀ F ∈ ThSp D T (Λ L), ∀ a : ℂ, ω g (a • F) = a • ω g F)
    (hin : ∀ k : GA D n, IntG D (k : GL (Fin n) (AE D)) → SuppInert D (k : GL (Fin n) (AE D)) → ω k e0 = e0)
    (hth : ∀ (h : GA D n) L, Moves D (h : GL (Fin n) (AE D)) L → ω h e0 ∈ ThSp D T (Λ L))
    (heq : ∀ (g h k : GA D n) L₁ L₂ M₁ M₂, Moves D (h : GL (Fin n) (AE D)) L₁ →
      Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) L₂ → Moves D (k : GL (Fin n) (AE D)) M₁ →
      Moves D ((g * k : GA D n) : GL (Fin n) (AE D)) M₂ → ∀ F ∈ ThSp D T (Λ L₁),
        ω g (Iop D T (Λ L₁) (Λ M₁) F) = Iop D T (Λ L₂) (Λ M₂) (ω g F))
    (hbet : ∀ L₁ L₂ L₃, SD D L₁ → SD D L₂ → SD D L₃ → Bet D L₁ L₂ L₃ → ∀ e ∈ ThSp D T (Λ L₁), e ≠ 0 →
      Iop D T (Λ L₂) (Λ L₃) (Iop D T (Λ L₁) (Λ L₂) e) = Iop D T (Λ L₁) (Λ L₃) e)
    (htri : ∀ (P : Ideal (𝓞 D.host.E)) A B C, P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) →
      Tri D P A B C → ∀ e ∈ ThSp D T (Λ A), e ≠ 0 →
      Iop D T (Λ B) (Λ C) (Iop D T (Λ A) (Λ B) e) = σ • Iop D T (Λ A) (Λ C) e) :
    ∀ (h : GA D n) L, SuppInert D (h : GL (Fin n) (AE D)) → Moves D (h : GL (Fin n) (AE D)) L →
      ω h e0 = σ ^ lenQ D (stdL D n) L • Iop D T (Λ (stdL D n)) (Λ L) e0 := by
  have hsd0 : SD D (stdL D n) := sd_of_moves (moves_one D n)
  have hwd : ∀ (h₁ h₂ : GA D n) L, SuppInert D (h₁ : GL (Fin n) (AE D)) → SuppInert D (h₂ : GL (Fin n) (AE D)) →
      Moves D (h₁ : GL (Fin n) (AE D)) L → Moves D (h₂ : GL (Fin n) (AE D)) L → ω h₂ e0 = ω h₁ e0 := by
    intro h₁ h₂ L s₁ s₂ m₁ m₂
    have := hmul h₁ (h₁⁻¹ * h₂)
    rwa [mul_inv_cancel_left, hin _ (intG_of_moves m₁ m₂) (suppInert_mul (suppInert_inv s₁) s₂)] at this
  have hone : ω 1 e0 = e0 := by
    have := intG_of_moves (moves_one D n) (moves_one D n)
    rw [inv_one, one_mul] at this
    exact hin 1 this (suppInert_one D n)
  have hne : ∀ h, ω h e0 ≠ 0 := by
    intro h h0
    have h1 := hmul h⁻¹ h
    have h2 := hsm h⁻¹ _ hsd0 e0 he0 0
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone, h0, h2] at h1
    exact hnz h1
  have hstep : ∀ (q : ℕ) (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) (h : GA D n), q.Prime → InertQ D q →
      P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → NbD D P B x → SuppInert D (h : GL (Fin n) (AE D)) →
      Moves D (h : GL (Fin n) (AE D)) B → ∃ k : GA D n, SuppInert D (k : GL (Fin n) (AE D)) ∧
        Moves D (k : GL (Fin n) (AE D)) (nbr D B x) ∧ ω h e0 = σ • Iop D T (Λ (nbr D B x)) (Λ B) (ω k e0) := by
    intro q P B x h hq hi hP hqP hx sh mh
    have hB := sd_of_moves mh
    obtain ⟨g, w, sg, hw, mC, mA, htr⟩ := exists_move hq hi hP hqP hB hx
    obtain ⟨g₂, -, sg₂, -, mA₂, -⟩ := exists_move hq hi hP hqP hB hw
    have mhA := mA₂ h mh
    have shA := suppInert_mul sg₂ sh
    set hA := g₂ * h
    have hAsd := sd_of_moves mhA
    have hCsd := sd_of_moves (mC h mh)
    obtain ⟨w0, -, hw0⟩ := GlobalTheory.T.exists_traceOne_integer_conj_diff_prime_to D q hq
    have eA := hth hA _ mhA
    have hIA := hI _ _ hAsd hB _ eA
    have hIne : Iop D T (Λ (nbr D B w)) (Λ B) (ω hA e0) ≠ 0 := by
      intro h0
      have h2 := hIA.2
      have h3 := Iop_smul D T (Λ B) (Λ (nbr D B w)) 0 0
      rw [zero_smul, zero_smul] at h3
      rw [h0, h3] at h2
      exact hne hA h2.symm
    obtain ⟨c, hc⟩ := hline B hB _ (hth h B mh) _ hIA.1 hIne
    have hfix : ω g (ω hA e0) = ω hA e0 := by
      rw [← hmul]; exact hwd _ _ _ shA (suppInert_mul sg shA) mhA (mA hA mhA)
    have hC : ω (g * h) e0 = c • Iop D T (Λ (nbr D B w)) (Λ (nbr D B x)) (ω hA e0) := by
      rw [hmul, hc, hsm g B hB _ hIA.1, heq g hA h _ _ _ _ mhA (mA hA mhA) mh (mC h mh) _ eA, hfix]
    have hT := htri P _ _ _ hP (stable_of_inert hq hi hP hqP) ⟨w0, hw0 P hP.isPrime hqP⟩ (htr hAsd hCsd) _ eA (hne hA)
    have hBC : Iop D T (Λ B) (Λ (nbr D B x)) (ω h e0) = σ • ω (g * h) e0 := by
      rw [hC, hc, Iop_smul, hT, smul_comm]
    refine ⟨g * h, suppInert_mul sg sh, mC h mh, ?_⟩
    rw [← Iop_smul, ← hBC, (hI _ _ hB hCsd _ (hth h B mh)).2]
  intro h L
  induction hl : lenQ D (stdL D n) L generalizing h L with
  | zero =>
    intro sh mh
    by_cases hL : stdL D n = L
    · subst hL
      rw [pow_zero, one_smul, hII _ hsd0 _ he0, hwd 1 h _ (suppInert_one D n) sh (moves_one D n) mh, hone]
    · obtain ⟨P, q, x, -, -, -, -, -, hlen⟩ := GlobalTheory.T.self_dual_lattices_neighbour_chain D n _ L hsd0 (sd_of_moves mh) hL
      omega
  | succ k ih =>
    intro sh mh
    have hL : stdL D n ≠ L := by
      intro hL
      rw [← hL, lenQ, Submodule.comap_subtype_self, Module.length_eq_zero] at hl
      simp at hl
    obtain ⟨P, q, x, hP, hq, hqP, hx0, hx, hlen⟩ := GlobalTheory.T.self_dual_lattices_neighbour_chain D n _ L hsd0 (sd_of_moves mh) hL
    have hi : InertQ D q := by
      by_contra hi
      obtain ⟨s, hs, h1, -⟩ := eqAt_of_moves hq mh (sh q hq hi)
      have h2 := h1 x hx0
      have h3 := hx.2.1 _ hqP
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hs
      apply hx.1
      have e1 : (s : D.host.E) • x = (s : 𝓞 D.host.E) • x := by
        rw [← algebraMap_smul D.host.E (s : 𝓞 D.host.E) x, map_natCast]
      rw [e1] at h2
      have e2 : x = (u : 𝓞 D.host.E) • (s : 𝓞 D.host.E) • x + (v : 𝓞 D.host.E) • (q : 𝓞 D.host.E) • x := by
        rw [smul_smul, smul_smul, ← add_smul]
        have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
        push_cast at this
        rw [this, one_smul]
      rw [e2]
      exact add_mem (L.smul_mem _ h2) (L.smul_mem _ h3)
    obtain ⟨g, sg, mg, hg⟩ := hstep q P L x h hq hi hP hqP hx sh mh
    have hbt : Bet D (stdL D n) (nbr D L x) L := by
      refine ⟨sup_le ?_ ?_, fun y hy => (le_sup_left : nbM D L x ≤ nbr D L x) ⟨hy.2, ?_⟩⟩
      · exact le_sup_of_le_right (le_inf le_sup_left fun y hy => hy.1)
      · exact le_sup_of_le_left (le_inf ((Submodule.span_singleton_le_iff_mem _ _).2 hx0) le_sup_right)
      · exact (((sd_iff D _).1 hsd0).2.2 y).1 hy.1 x hx0
    rw [hg, ih g _ (by omega) sg mg, Iop_smul, hbet _ _ _ hsd0 (sd_of_moves mg) (sd_of_moves mh) hbt _ he0 hnz,
      smul_smul, pow_succ']

end Core

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) : δ ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  rintro rfl
  have h1 := (hL L.ω₁).2 L.ω₁_mem_lattice
  have h2 : lamOf D cc 0 ≤ ⊥ := by
    rw [lamOf, AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  exact L.indep.ne_zero 0 (by simpa using h2 h1)

end GlobalTheory.InertSign

open GlobalTheory.InertSign in

theorem GlobalTheory.InertSign.vacuum_inert : ∀ D : D7, odd3 D := by
  intro D cc δ hc N N' _ e0 he0 W g g' L₁ L₁' sg sg' mg mg'
  have hδ := delta_ne_zero hc
  have hK : ∀ {L : Lat D N} {L' : Lat D N'}, SD D L → SD D L' → KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
    fun h h' => Or.inr ⟨_, _, h, h', rfl⟩
  obtain ⟨-, -, hII, htp⟩ := GlobalTheory.T.kernelLattices_form_selfDual_triples D cc δ hc N N'
  obtain ⟨hTT, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hc N N'
  obtain ⟨d1, d2, d3⟩ := GlobalTheory.T.thetaLattice_triples_distributive D cc δ N N'
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N'
  have hline := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N'
  have s0 : SD D (stdL D N) := sd_of_moves (moves_one D N)
  have s0' : SD D (stdL D N') := sd_of_moves (moves_one D N')
  have m1 : Moves D ((1 * 1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by rw [one_mul]; exact moves_one D N
  have m1' : Moves D ((1 * 1 : GA D N') : GL (Fin N') (AE D)) (stdL D N') := by rw [one_mul]; exact moves_one D N'
  have i1 : IntG D ((1 : GA D N) : GL (Fin N) (AE D)) := by
    have := intG_of_moves (moves_one D N) (moves_one D N)
    rwa [inv_one, one_mul] at this
  have i1' : IntG D ((1 : GA D N') : GL (Fin N') (AE D)) := by
    have := intG_of_moves (moves_one D N') (moves_one D N')
    rwa [inv_one, one_mul] at this
  have he0T := hTT _ _ s0 s0' e0 he0
  have hdist : ∀ A₁ A₂ A₃, KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → Dist A₁ A₂ A₃ →
      ∀ e ∈ ThSp D (tor0 D cc δ) (N := N) (N' := N') A₁, e ≠ 0 →
      Iop D (tor0 D cc δ) A₂ A₃ (Iop D (tor0 D cc δ) A₁ A₂ e) = Iop D (tor0 D cc δ) A₁ A₃ e := by
    intro A₁ A₂ A₃ k₁ k₂ k₃ hd e he hne
    obtain ⟨μ, hμ⟩ := htp A₁ A₂ A₃ k₁ k₂ k₃ e he hne
    have h1 := GlobalTheory.T.thetaTripleConstant_eq_one_distributive D _ N N' _ _ _ e μ hμ hd
    rw [hμ.2.2.2.2.2.2.2.2.2, h1]
    funext z; rw [one_mul]
  have htr : ∀ A₁ A₂ A₃, KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ →
      ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) →
      TriDat D (tor0 D cc δ) A₁ A₂ A₃ P r → ∀ e ∈ ThSp D (tor0 D cc δ) (N := N) (N' := N') A₁, e ≠ 0 →
      Iop D (tor0 D cc δ) A₂ A₃ (Iop D (tor0 D cc δ) A₁ A₂ e) = ((-1 : ℂ) ^ r) • Iop D (tor0 D cc δ) A₁ A₃ e := by
    intro A₁ A₂ A₃ k₁ k₂ k₃ P r hP hst ha hd e he hne
    obtain ⟨μ, hμ⟩ := htp A₁ A₂ A₃ k₁ k₂ k₃ e he hne
    have h1 := GlobalTheory.T.thetaTripleConstant_eq_neg_one_pow D _ N N' _ _ _ e μ hμ P r hP hst ha hd
    rw [hμ.2.2.2.2.2.2.2.2.2, h1]
    rfl
  have hsq : ∀ r : ℕ, (-1 : ℂ) ^ r * (-1) ^ r = 1 := fun r => by rw [← mul_pow]; simp
  have c1 := core (T := tor0 D cc δ) (fun L => La D (tor0 D cc δ) L (stdL D N')) (fun h => W.Om h 1) e0 ((-1) ^ N') (hsq _) W.nz he0
    (fun _ _ a b e he => ⟨(huni _ _ (hK a s0') (hK b s0') e he).2.1, (huni _ _ (hK a s0') (hK b s0') e he).2.2.2⟩)
    (fun _ a => hII _ (hK a s0')) (fun _ a => (hline _ (hK a s0')).1)
    (fun a b => by rw [← W.mul a b 1 1 e0 he0T, one_mul])
    (fun a L hL F hF c => W.smul a 1 c F (hTT _ _ hL s0' F hF))
    (fun k a b => W.inert k 1 a i1' b (suppInert_one D N'))
    (fun h L a => GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W h 1 1 1 _ _ _ _ (moves_one D N) (moves_one D N') (by rwa [mul_one]) m1' e0 he0)
    (fun a h k _ _ _ _ b c d e F hF => GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W a h k 1 1 1 _ _ _ _ _ _ _ _ b (moves_one D N') c m1' d
      (moves_one D N') e m1' F hF)
    (fun _ _ _ a b c d => hdist _ _ _ (hK a s0') (hK b s0') (hK c s0') (d2 _ _ _ _ a c d))
    (fun P A B C a b c d => htr _ _ _ (hK d.1 s0') (hK d.2.1 s0') (hK d.2.2.1 s0') P N' a b c
      (GlobalTheory.T.thetaTripleDiagonalData_of_selfDualNeighbourTriple D cc δ hc.1.1 hδ N N' P a b A B C d)) g L₁ sg mg
  have c2 := core (T := tor0 D cc δ) (fun L => La D (tor0 D cc δ) (stdL D N) L) (fun h => W.Om 1 h) e0 ((-1) ^ N) (hsq _) W.nz he0
    (fun _ _ a b e he => ⟨(huni _ _ (hK s0 a) (hK s0 b) e he).2.1, (huni _ _ (hK s0 a) (hK s0 b) e he).2.2.2⟩)
    (fun _ a => hII _ (hK s0 a)) (fun _ a => (hline _ (hK s0 a)).1)
    (fun a b => by rw [← W.mul 1 1 a b e0 he0T, one_mul])
    (fun a L hL F hF c => W.smul 1 a c F (hTT _ _ s0 hL F hF))
    (fun k a b => W.inert 1 k i1 a (suppInert_one D N) b)
    (fun h L a => GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W 1 1 h 1 _ _ _ _ (moves_one D N) (moves_one D N') m1 (by rwa [mul_one]) e0 he0)
    (fun a h k _ _ _ _ b c d e F hF => GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W 1 1 1 a h k _ _ _ _ _ _ _ _ (moves_one D N) b m1 c
      (moves_one D N) d m1 e F hF)
    (fun _ _ _ a b c d => hdist _ _ _ (hK s0 a) (hK s0 b) (hK s0 c) (d1 _ _ _ _ a c d))
    (fun P A B C a b c d => htr _ _ _ (hK s0 d.1) (hK s0 d.2.1) (hK s0 d.2.2.1) P N a b c
      (GlobalTheory.T.thetaTripleData_of_neighbourTriple D cc δ hc.1.1 hδ N N' P a A B C d)) g' L₁' sg' mg'
  have sL := sd_of_moves mg
  have sL' := sd_of_moves mg'
  have h1 : W.Om g g' e0 = W.Om 1 g' (W.Om g 1 e0) := by rw [← W.mul 1 g g' 1 e0 he0T, one_mul, mul_one]
  have hI1 := (huni _ _ (hK s0 s0') (hK sL s0') e0 he0).2.1
  have h2 := GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W 1 1 g g' 1 1 _ _ _ _ _ _ _ _ (moves_one D N) (moves_one D N') m1
    (by rw [mul_one]; exact mg') mg (moves_one D N') (by rw [one_mul]; exact mg) (by rw [mul_one]; exact mg') e0 he0
  rw [h1, c1, W.smul 1 g' _ _ (hTT _ _ sL s0' _ hI1), h2, c2, Iop_smul,
    hdist _ _ _ (hK s0 s0') (hK s0 sL') (hK sL sL') (d3 _ _ _ _ s0' sL') e0 he0 W.nz]
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, La0, pow_add, pow_mul]
  ring
