import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
open ValuativeRel Matrix

namespace GlobalTheory.LagVac

open GlobalTheory.WeilM GlobalTheory.VacLoc

theorem exists_fixed {A B X : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup X] [Module ℂ X]
    (π : A → X →ₗ[ℂ] X) (hπ : ∀ a b x, π (a + b) x = π a (π b x)) (S : B → X →ₗ[ℂ] X)
    (hS : ∀ b x, S b x = 0 → x = 0) (β : A → B → ℂ) (hβ1 : ∀ a a' b, β (a + a') b = β a b * β a' b)
    (hβ2 : ∀ a b b', β a (b + b') = β a b * β a b') (hconj : ∀ a b x, π a (S b x) = S b (β a b • π a x))
    (K : AddSubgroup A) (hK : ∀ a, a ∈ K ↔ ∀ b, β a b = 1) [Finite (A ⧸ K)] (P : Submodule ℂ X)
    (hPπ : ∀ a, ∀ x ∈ P, π a x ∈ P) (hPS : ∀ b, ∀ x ∈ P, S b x ∈ P) (φ : X) (hφ : φ ∈ P) (hφ0 : φ ≠ 0)
    (hfix : ∀ a ∈ K, π a φ = φ) : ∃ f ∈ P, f ≠ 0 ∧ ∀ a, π a f = f := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite _
  have hper : ∀ (b : B) (a : A), β (Quotient.out (a : A ⧸ K)) b = β a b := by
    intro b a
    have h : -a + Quotient.out (a : A ⧸ K) ∈ K :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (a : A ⧸ K)).symm
    rw [show Quotient.out (a : A ⧸ K) = a + (-a + Quotient.out (a : A ⧸ K)) by abel, hβ1, (hK _).mp h b, mul_one]
  have hout0 : Quotient.out (0 : A ⧸ K) ∈ K :=
    (QuotientAddGroup.eq_zero_iff _).mp (QuotientAddGroup.out_eq' 0)
  let θ : B → AddChar (A ⧸ K) ℂ := fun b =>
    { toFun := fun q => β (Quotient.out q) b
      map_zero_eq_one' := (hK _).mp hout0 b
      map_add_eq_mul' := by
        intro q q'
        induction q using QuotientAddGroup.induction_on with | H a => ?_
        induction q' using QuotientAddGroup.induction_on with | H a' => ?_
        rw [← QuotientAddGroup.mk_add, hper, hper, hper, hβ1] }
  have hθ : ∀ w q, θ w q = β (Quotient.out q) w := fun _ _ => rfl
  have hθadd : ∀ w w', θ (w + w') = θ w * θ w' := by
    intro w w'
    ext q
    rw [AddChar.mul_apply, hθ, hθ, hθ, hβ2]
  have hθsep : ∀ q, (∀ w, θ w q = 1) → q = 0 := by
    intro q hq
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    refine (QuotientAddGroup.eq_zero_iff a).mpr ((hK a).mpr fun w => ?_)
    have := hq w
    rwa [hθ, hper] at this
  have hc0 : π (Quotient.out (0 : A ⧸ K)) φ ≠ 0 := by rw [hfix _ hout0]; exact hφ0
  obtain ⟨w, hw⟩ := exists_twisted_sum_ne_zero θ hθadd hθsep (fun q => π (Quotient.out q) φ) hc0
  have hx : ∀ h ∈ K, π h (S w φ) = S w φ := by
    intro h hh
    rw [hconj, hfix h hh, (hK h).mp hh w, one_smul]
  refine ⟨∑ q : A ⧸ K, π (Quotient.out q) (S w φ), Submodule.sum_mem _ fun q _ => hPπ _ _ (hPS _ _ hφ),
    fun h0 => hw (hS w _ ?_), avg_fixed K π hπ _ hx⟩
  rw [map_sum, ← h0]
  exact Finset.sum_congr rfl fun q _ => (hconj _ _ _).symm

section Lin

variable {k : Type} [Field k] {κ : Type} [Fintype κ]

theorem eq_zero_of_symp (D : (κ → k) × (κ → k)) (h : ∀ w : (κ → k) × (κ → k), D.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ D.2 = 0) : D = 0 := by
  classical
  ext i
  · simpa using h (0, Pi.single i 1)
  · simpa using h (Pi.single i 1, 0)

theorem map_smul_of_pair {M : Type} [AddCommGroup M] [Module k M] (wT wM : M →+ (κ → k) × (κ → k)) (p : M → M → k)
    (hp : ∀ (c : k) Y z, p (c • Y) z = c * p Y z)
    (hT : ∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0)
    (hTM : ∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = p Y z)
    (hsp : ∀ w, ∃ Y z, wT Y + wM z = w) (c : k) (Y : M) : wT (c • Y) = c • wT Y := by
  refine sub_eq_zero.mp (eq_zero_of_symp _ fun w => ?_)
  obtain ⟨Y', z, rfl⟩ := hsp w
  have h1 := hT (c • Y) Y'
  have h2 := hT Y Y'
  have h3 := hTM (c • Y) z
  have h4 := hTM Y z
  rw [hp] at h3
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, sub_dotProduct,
    dotProduct_sub, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination h1 - c * h2 + h3 - c * h4

end Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_denom {ι : Type} [Fintype ι] (c : ι → k) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  have h : ∀ i, ∃ N : ℕ, 0 < N ∧ (N : k) * c i ∈ 𝒪[k] := by
    intro i
    by_cases hc : c i = 0
    · exact ⟨1, one_pos, by rw [hc, mul_zero]; exact zero_mem _⟩
    · obtain ⟨N, hN, h⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer (c i)⁻¹ (inv_ne_zero hc)
      exact ⟨N, hN, by rwa [inv_inv, mul_comm] at h⟩
  choose N hN h using h
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

theorem exists_denom_lin {ι Y Y' : Type} [Fintype ι] [Fintype Y] [Fintype Y'] (l : ι → Matrix Y Y' k →+ k)
    (hl : ∀ i (c : k) u, l i (c • u) = c * l i u) :
    ∃ N : ℕ, 0 < N ∧ ∀ i (u : Matrix Y Y' k), (∀ r q, u r q ∈ 𝒪[k]) → (N : k) * l i u ∈ 𝒪[k] := by
  classical
  obtain ⟨N, hN, h⟩ := exists_denom (fun t : ι × Y × Y' => l t.1 (Matrix.single t.2.1 t.2.2 1))
  refine ⟨N, hN, fun i u hu => ?_⟩
  rw [Matrix.matrix_eq_sum_single u, map_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun r _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun q _ => ?_
  rw [show Matrix.single r q (u r q) = u r q • Matrix.single r q (1 : k) by simp, hl, mul_left_comm]
  exact mul_mem (hu r q) (h (i, r, q))

variable {κ : Type} [Fintype κ]

theorem ind_mem_SB : Set.indicator {y : κ → k | ∀ r, y r ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈ SB (κ → k) := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have e : {y : κ → k | ∀ r, y r ∈ 𝒪[k]} = Set.pi Set.univ fun _ : κ => (𝒪[k] : Set k) := by
    ext y; exact ⟨fun h r _ => h r, fun h r => h r trivial⟩
  have hK : IsCompact {y : κ → k | ∀ r, y r ∈ 𝒪[k]} := by
    rw [e]; exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have ho : IsOpen {y : κ → k | ∀ r, y r ∈ 𝒪[k]} := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hK fun x hx => ?_⟩
  · by_cases hx : x ∈ {y : κ → k | ∀ r, y r ∈ 𝒪[k]}
    · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨_, hK.isClosed.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact Set.indicator_of_notMem hx _

variable [Invertible (2 : k)] (ψ : AddChar k ℂ)

theorem schr_mem_SB (hψ : ∀ y ∈ 𝒪[k], ψ y = 1) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have hl : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => y - x) ⁻¹' (𝒪[k] : Set k),
      (Valuation.isOpen_integer (v := valuation k)).preimage (by fun_prop), by simp, fun y hy => ?_⟩
    rw [show y = x + (y - x) by ring, AddChar.map_add_eq_mul, hψ _ hy, mul_one]
  have hc : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  exact ⟨(hl.comp_continuous hc).mul (hφ.1.comp_continuous (f := fun t => t + w.1) (by fun_prop)),
    HasCompactSupport.mul_left (f := fun x : κ → k => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)))
      (hφ.2.comp_homeomorph (Homeomorph.addRight w.1))⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem schr_ind (hψ : ∀ y ∈ 𝒪[k], ψ y = 1) (w : (κ → k) × (κ → k)) (h1 : ∀ i, w.1 i ∈ 𝒪[k])
    (h2 : ∀ i, ⅟(2 : k) * w.2 i ∈ 𝒪[k]) :
    schr ψ w (Set.indicator {y : κ → k | ∀ r, y r ∈ 𝒪[k]} (fun _ => (1 : ℂ))) =
      Set.indicator {y : κ → k | ∀ r, y r ∈ 𝒪[k]} (fun _ => (1 : ℂ)) := by
  funext x
  have h3 : ∀ i, w.2 i ∈ 𝒪[k] := fun i => by
    have := add_mem (h2 i) (h2 i)
    rwa [← add_mul, invOf_two_add_invOf_two, one_mul] at this
  unfold schr
  by_cases hx : x ∈ {y : κ → k | ∀ r, y r ∈ 𝒪[k]}
  · have hx' : x + w.1 ∈ {y : κ → k | ∀ r, y r ∈ 𝒪[k]} := fun r => add_mem (hx r) (h1 r)
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', mul_one]
    refine hψ _ (add_mem (Subring.sum_mem _ fun i _ => mul_mem (hx i) (h3 i)) ?_)
    rw [dotProduct, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_left_comm]
    exact mul_mem (h1 i) (h2 i)
  · have hx' : x + w.1 ∉ {y : κ → k | ∀ r, y r ∈ 𝒪[k]} := fun h => hx fun r => by
      simpa using sub_mem (h r) (h1 r)
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fix_ind (hψ : ∀ y ∈ 𝒪[k], ψ y = 1) {Y Y' : Type} [Fintype Y] [Fintype Y']
    (w : Matrix Y Y' k →+ (κ → k) × (κ → k)) (hw : ∀ (c : k) u, w (c • u) = c • w u) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) →
      schr ψ (w (N • u)) (Set.indicator {y : κ → k | ∀ r, y r ∈ 𝒪[k]} (fun _ => (1 : ℂ))) =
        Set.indicator {y : κ → k | ∀ r, y r ∈ 𝒪[k]} (fun _ => (1 : ℂ)) := by
  let l : κ ⊕ κ → Matrix Y Y' k →+ k := Sum.elim
    (fun i => AddMonoidHom.mk' (fun u => (w u).1 i) fun a b => by simp)
    (fun i => AddMonoidHom.mk' (fun u => ⅟(2 : k) * (w u).2 i) fun a b => by simp [mul_add])
  obtain ⟨N, hN, h⟩ := exists_denom_lin l (by
    rintro (i | i) c u
    · simp [l, hw]
    · simp [l, hw, mul_left_comm])
  refine ⟨N, hN, fun u hu => schr_ind ψ hψ _ (fun i => ?_) fun i => ?_⟩
  · simpa [l] using h (Sum.inl i) u hu
  · have := h (Sum.inr i) u hu
    simpa [l, mul_left_comm] using this

open GlobalTheory.IrredSB in
omit [Invertible (2 : k)] in

theorem finite_quot [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] {N : ℕ} (hN : 0 < N) :
    Finite ((intMat k Y Y' × intMat k Y Y') ⧸
      (nsmulAddMonoidHom N : intMat k Y Y' × intMat k Y Y' →+ intMat k Y Y' × intMat k Y Y').range) := by
  obtain ⟨ι, hι, x, hx, h⟩ := GlobalTheory.exists_finite_integer_residues k N hN
  let g : (Y → Y' → ι) → intMat k Y Y' := fun f => ⟨Matrix.of fun r q => x (f r q), fun r q => hx _⟩
  have hg : ∀ t : intMat k Y Y', ∃ f u, t = g f + N • u := by
    intro t
    choose f u hu hf using fun r q => h (t.1 r q) (t.2 r q)
    refine ⟨f, ⟨Matrix.of u, hu⟩, Subtype.ext ?_⟩
    ext r q
    simpa [g] using hf r q
  refine Finite.of_surjective (fun f : (Y → Y' → ι) × (Y → Y' → ι) => QuotientAddGroup.mk (g f.1, g f.2)) fun q => ?_
  induction q using QuotientAddGroup.induction_on with | H a => ?_
  obtain ⟨f, u, h1⟩ := hg a.1
  obtain ⟨f', u', h2⟩ := hg a.2
  refine ⟨(f, f'), QuotientAddGroup.eq.mpr ⟨(u, u'), ?_⟩⟩
  ext1
  · simp [h1]
  · simp [h2]

end GlobalTheory.LagVac

open GlobalTheory.WeilM GlobalTheory.VacLoc GlobalTheory.IrredSB in

theorem GlobalTheory.LagVac.exists_vacuum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ f₀ ∈ GlobalTheory.WeilM.SB (κ → k), f₀ ≠ 0 ∧
      (∀ u : Matrix (Fin n) (Fin d) k, (∀ r q, u r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wT u) f₀ = f₀) ∧
      (∀ z : Matrix (Fin n) (Fin d) k, (∀ r q, z r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wM z) f₀ = f₀) := by
  intro k _ _ _ _ _ _ κ _ n d ψ _ hcond wT wM hT hM hTM hsp
  classical
  have hψ : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => by simpa using (hcond 1).2 (one_mem _) y hy
  have hTM' : ∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = pair Y z := hTM
  have hlT : ∀ (c : k) Y, wT (c • Y) = c • wT Y :=
    map_smul_of_pair wT wM pair (fun c Y z => by simp [pair, Finset.mul_sum, mul_assoc]) hT hTM' hsp
  have hlM : ∀ (c : k) z, wM (c • z) = c • wM z :=
    map_smul_of_pair wM wT (fun z Y => -pair Y z) (fun c Y z => by simp [pair, Finset.mul_sum, mul_left_comm]) hM
      (fun z Y => by rw [← hTM']; ring) fun w => by
        obtain ⟨Y, z, h⟩ := hsp w
        exact ⟨z, Y, by rw [add_comm, h]⟩
  obtain ⟨N₁, hN₁, hf₁⟩ := exists_fix_ind ψ hψ wT hlT
  obtain ⟨N₂, hN₂, hf₂⟩ := exists_fix_ind ψ hψ wM hlM
  have hN : 0 < N₁ * N₂ := Nat.mul_pos hN₁ hN₂
  set N := N₁ * N₂ with hNdef
  have hN' : (N : k) ≠ 0 := by exact_mod_cast hN.ne'
  have hpint : ∀ u z : intMat k (Fin n) (Fin d), pair u.1 z.1 ∈ 𝒪[k] := fun u z =>
    Subring.sum_mem _ fun r _ => Subring.sum_mem _ fun q _ => mul_mem (u.2 r q) (z.2 r q)
  have hpl : ∀ u u' z : Matrix (Fin n) (Fin d) k, pair (u + u') z = pair u z + pair u' z := fun u u' z => by
    simp [pair, add_mul, Finset.sum_add_distrib]
  have hpc : ∀ u z : Matrix (Fin n) (Fin d) k, pair u z = pair z u := fun u z => by
    simp [pair, mul_comm]
  have hps : ∀ (c : k) (u z : Matrix (Fin n) (Fin d) k), pair (c • u) z = c * pair u z := fun c u z => by
    simp [pair, Finset.mul_sum, mul_assoc]
  have hp0 : ∀ z : Matrix (Fin n) (Fin d) k, pair 0 z = 0 := fun z => by simp [pair]
  have hlin : ∀ (w : (κ → k) × (κ → k)) (c : ℂ) (f : (κ → k) → ℂ),
      schr ψ w (c • f) = c • schr ψ w f := fun w c f => (schrL ψ w).map_smul c f
  have hTT : ∀ u u' φ, schr ψ (wT (u + u')) φ = schr ψ (wT u) (schr ψ (wT u') φ) := fun u u' φ => by
    rw [schr_schr, hT, map_add]; simp
  have hMM : ∀ u u' φ, schr ψ (wM (u + u')) φ = schr ψ (wM u) (schr ψ (wM u') φ) := fun u u' φ => by
    rw [schr_schr, hM, map_add]; simp
  have hMT : ∀ (u z : intMat k (Fin n) (Fin d)) φ,
      schr ψ (wT u) (schr ψ (wM z) φ) = schr ψ (wM z) (schr ψ (wT u) φ) := fun u z φ => by
    rw [schr_comm, hTM', hψ _ (hpint u z), one_smul]
  haveI := finite_quot (k := k) (Fin n) (Fin d) hN
  obtain ⟨f, hf, hf0, hfix⟩ := exists_fixed
    (A := intMat k (Fin n) (Fin d) × intMat k (Fin n) (Fin d))
    (B := intMat k (Fin n) (Fin d) × intMat k (Fin n) (Fin d))
    (fun a => schrL ψ (wT a.1) ∘ₗ schrL ψ (wM a.2))
    (fun a b x => by
      show schr ψ (wT (a.1 + b.1)) (schr ψ (wM (a.2 + b.2)) x) =
        schr ψ (wT a.1) (schr ψ (wM a.2) (schr ψ (wT b.1) (schr ψ (wM b.2) x)))
      rw [hTT, hMM, hMT b.1 a.2])
    (fun b => schrL ψ ((N : k)⁻¹ • (wT b.1 + wM b.2)))
    (fun b x h => by
      have h' : schr ψ ((N : k)⁻¹ • (wT b.1 + wM b.2)) x = 0 := h
      rw [← schr_neg_schr ψ ((N : k)⁻¹ • (wT b.1 + wM b.2)) x, h']
      exact (schrL ψ _).map_zero)
    (fun a b => ψ ((N : k)⁻¹ * (pair a.1.1 b.2.1 - pair b.1.1 a.2.1)))
    (fun a a' b => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, hpl, pair_add_right]
      ring)
    (fun a b b' => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, hpl, pair_add_right]
      ring)
    (fun a b x => by
      show schr ψ (wT a.1) (schr ψ (wM a.2) (schr ψ ((N : k)⁻¹ • (wT b.1 + wM b.2)) x)) =
        schr ψ ((N : k)⁻¹ • (wT b.1 + wM b.2)) (_ • schr ψ (wT a.1) (schr ψ (wM a.2) x))
      rw [schr_comm ψ (wM a.2), hlin, schr_comm ψ (wT a.1), hlin, smul_smul, ← AddChar.map_add_eq_mul]
      congr 2
      have h1 := hT a.1 b.1
      have h2 := hM a.2 b.2
      have h3 := hTM' a.1 b.2
      have h4 := hTM' b.1 a.2
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      linear_combination (N : k)⁻¹ * (h1 + h2 + h3 - h4))
    (nsmulAddMonoidHom N).range
    (fun a => by
      constructor
      · rintro ⟨a', rfl⟩ b
        have e1 : ((nsmulAddMonoidHom N a').1 : Matrix (Fin n) (Fin d) k) = (N : k) • a'.1.1 := by
          rw [Nat.cast_smul_eq_nsmul]; rfl
        have e2 : ((nsmulAddMonoidHom N a').2 : Matrix (Fin n) (Fin d) k) = (N : k) • a'.2.1 := by
          rw [Nat.cast_smul_eq_nsmul]; rfl
        rw [e1, e2, hps, hpc b.1.1, hps, ← mul_sub, inv_mul_cancel_left₀ hN']
        exact hψ _ (sub_mem (hpint _ _) (hpint _ _))
      · intro h
        have hs : ∀ r q, ∀ y ∈ 𝒪[k], Matrix.single r q y ∈ intMat k (Fin n) (Fin d) := fun r q y hy r' q' => by
          rw [Matrix.single_apply]
          split_ifs
          · exact hy
          · exact zero_mem _
        have h1 : (N : k)⁻¹ • a.1.1 ∈ intMat k (Fin n) (Fin d) := fun r q => (hcond _).1 fun y hy => by
          have := h (0, ⟨_, hs r q y hy⟩)
          simp only [AddSubgroup.coe_zero, hp0, sub_zero] at this
          rw [hpc, pair_single] at this
          rw [← this, Matrix.smul_apply, smul_eq_mul]
          congr 1; ring
        have h2 : (N : k)⁻¹ • a.2.1 ∈ intMat k (Fin n) (Fin d) := fun r q => (hcond _).1 fun y hy => by
          have := h (⟨_, hs r q (-y) (neg_mem hy)⟩, 0)
          simp only [AddSubgroup.coe_zero] at this
          rw [hpc a.1.1, hp0, pair_single] at this
          rw [← this, Matrix.smul_apply, smul_eq_mul]
          congr 1; ring
        have hinv : ∀ v : Matrix (Fin n) (Fin d) k, N • (N : k)⁻¹ • v = v := fun v => by
          rw [← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ hN', one_smul]
        exact ⟨(⟨_, h1⟩, ⟨_, h2⟩), Prod.ext (Subtype.ext (hinv _)) (Subtype.ext (hinv _))⟩)
    (SB (κ → k))
    (fun a x hx => schr_mem_SB ψ hψ _ (schr_mem_SB ψ hψ _ hx))
    (fun b x hx => schr_mem_SB ψ hψ _ hx)
    _ ind_mem_SB
    (fun h => by
      have := congrFun h 0
      rw [Set.indicator_of_mem (by intro r; exact zero_mem _)] at this
      exact one_ne_zero this)
    (by
      rintro _ ⟨a, rfl⟩
      show schr ψ (wT (N • a.1.1)) (schr ψ (wM (N • a.2.1)) _) = _
      have e1 : N • a.1.1 = N₁ • (N₂ • a.1).1 := mul_smul _ _ _
      have e2 : N • a.2.1 = N₂ • (N₁ • a.2).1 := by rw [hNdef, mul_comm]; exact mul_smul _ _ _
      rw [e1, e2, hf₂ _ (N₁ • a.2).2, hf₁ _ (N₂ • a.1).2])
  refine ⟨f, hf, hf0, fun u hu => ?_, fun z hz => ?_⟩
  · have h : schr ψ (wT u) (schr ψ (wM 0) f) = f := hfix (⟨u, hu⟩, 0)
    rwa [map_zero, schr_zero_vec] at h
  · have h : schr ψ (wT 0) (schr ψ (wM z) f) = f := hfix (0, ⟨z, hz⟩)
    rwa [map_zero, schr_zero_vec] at h
