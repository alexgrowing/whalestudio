import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem norm_mul_le_of_loc {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  by_cases h0 : f z = 0
  · simp [h0]
  have hp : 0 < ‖f z‖ := norm_pos_iff.2 h0
  have hx : ‖f x‖ ≤ 1 := by
    by_contra hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) (not_le.1 hx)
    have h1 := hf (x ^ n * z) (Ideal.mul_mem_left _ _ hz)
    rw [map_mul, map_pow, norm_mul, norm_pow] at h1
    have h2 := mul_lt_mul_of_pos_right hn hp
    rw [inv_mul_cancel₀ hp.ne'] at h2
    exact lt_asymm h1 h2
  exact mul_le_of_le_one_left hp.le hx

private theorem exists_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsm : ∀ z ∈ s, z ∈ maximalIdeal R := fun z hz => hs ▸ Submodule.subset_span hz
  have hlt : (s.sup fun z => ‖f z‖₊) < 1 :=
    (Finset.sup_lt_iff (by norm_num)).2 fun z hz => hf z (hsm z hz)
  refine ⟨(s.sup fun z => ‖f z‖₊ : NNReal), NNReal.coe_nonneg _, hlt, fun z hz => ?_⟩
  have key : ∀ x : R, ‖f (x * z)‖ ≤ (s.sup fun z => ‖f z‖₊ : NNReal) := by
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro x
      exact (norm_mul_le_of_loc hf x (hsm z hz)).trans (Finset.le_sup (f := fun z => ‖f z‖₊) hz)
    | zero => intro x; simp
    | add a b _ _ ha hb =>
      intro x
      rw [mul_add, map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha x) (hb x))
    | smul a b _ hb =>
      intro x
      rw [smul_eq_mul, ← mul_assoc]
      exact hb _
  simpa using key 1

private theorem exists_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, h0, h1, h⟩ := exists_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (h b hb) (norm_nonneg _) (pow_nonneg h0 _)
      · rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨n + 1, fun z hz => (key n z hz).trans_lt
    ((pow_le_pow_of_le_one h0 h1.le (Nat.le_succ n)).trans_lt hn)⟩

private theorem eq_of_dense {f f' : R →ₐ[O] K} (hf : IsLocPt f) (hf' : IsLocPt f') (s : K) (x : R)
    (T : Set R) (hT : ∀ y ∈ T, f' y = s * f y)
    (h : ∀ n : ℕ, ∃ y ∈ Submodule.span O T, x - y ∈ maximalIdeal R ^ n) : f' x = s * f x := by
  have hsp : ∀ y ∈ Submodule.span O T, f' y = s * f y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hT z hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, mul_add]
    | smul a b _ hb => rw [map_smul, map_smul, hb, mul_smul_comm]
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hs : 0 < ‖s‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow hf (div_pos hε hs)
  obtain ⟨n', hn'⟩ := exists_pow hf' (div_pos hε hs)
  obtain ⟨y, hy, hxy⟩ := h (max n n')
  have e : f' x - s * f x = f' (x - y) - s * f (x - y) := by
    rw [map_sub, map_sub, hsp y hy]; ring
  have a1 := hn _ (Ideal.pow_le_pow_right (le_max_left _ _) hxy)
  have a2 := hn' _ (Ideal.pow_le_pow_right (le_max_right _ _) hxy)
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have a3 := mul_le_mul_of_nonneg_left a1.le (norm_nonneg s)
  have a4 : ε / (‖s‖ + 1) + ‖s‖ * (ε / (‖s‖ + 1)) = ε := by field_simp; ring
  linarith

end SlopeTestRemainingChoices

section Mon

variable {O R K Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field K] [Algebra O K] [Group Γ]

private theorem mon_zero (r : Γ →* GG 3 R) (f : R →ₐ[O] K) (e : ℤ)
    (h : ∀ g a b, e * wt a b < 0 → f ((r g).mat a b) = 0) (j : ℤ) (hj : e * j < 0) :
    ∀ y ∈ entMon r j, f y = 0 := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp at hj
  | cons s L ih =>
    rw [List.map_cons, List.sum_cons, mul_add] at hj
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hs : e * wt s.2.1 s.2.2 < 0
    · rw [h _ _ _ hs, zero_mul]
    · rw [ih (by omega), mul_zero]

private theorem mon_tor (r : Γ →* GG 3 R) (f f' : R →ₐ[O] K) (t : Kˣ)
    (h : ∀ g a b, f' ((r g).mat a b) = ((t ^ wt a b : Kˣ) : K) * f ((r g).mat a b)) (j : ℤ) :
    ∀ y ∈ entMon r j, f' y = ((t ^ j : Kˣ) : K) * f y := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.prod_cons, map_mul, map_mul, h, ih, _root_.zpow_add,
      Units.val_mul]
    ring

private theorem mat_ker (η : Γ →* ℤˣ) (r : Γ →* GG 3 R) (c : Γ) (hc : η c = -1) (h1 : (r c).mat = 1) (g : Γ) :
    ∃ g' ∈ η.ker, (r g).mat = (r g').mat := by
  rcases Int.units_eq_one_or (η g) with h | h
  · exact ⟨g, h, rfl⟩
  · refine ⟨g * c⁻¹, by simp [MonoidHom.mem_ker, h, hc], ?_⟩
    have hl : (r c).left = 1 := Units.ext h1
    have e : g = g * c⁻¹ * c := by simp
    conv_lhs => rw [e]
    rw [map_mul r _ c, GG.mat, GG.mat, SemidirectProduct.mul_left, hl, map_one, mul_one]

end Mon

theorem UpperTheory.V.U3.model_signs :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f →
        (NegZero M.𝒜 (f.comp M.q) ↔ Upper η (push f S.r.hom)) ∧ (PosZero M.𝒜 (f.comp M.q) ↔ Lower η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → ∀ t : (PadicAlgCl l)ˣ,
          push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) → f'.comp M.q = act M.𝒜 (tz t) (f.comp M.q) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M _ hM f hf
  have h1 : (S.r.hom cc).mat = 1 := ((S.rep S.R).1 (AlgHom.id _ _)).1.atc
  have key : ∀ e : ℤ, (∀ j, e * j < 0 → ∀ x ∈ M.𝒜 j, f (M.q x) = 0) ↔
      ∀ g ∈ η.ker, ∀ a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
    intro e
    constructor
    · intro h g _ a b hab
      obtain ⟨x, hx, hq⟩ := M.ent g a b
      rw [← hq]
      exact h _ hab x hx
    · intro h j hj x hx
      have h' : ∀ g a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
        intro g a b hab
        obtain ⟨g', hg', e'⟩ := mat_ker η S.r.hom cc hM.ηc h1 g
        rw [e']
        exact h g' hg' a b hab
      have := eq_of_dense hf hf 0 (M.q x) (entMon S.r.hom j)
        (fun y hy => by rw [mon_zero _ f e h' j hj y hy, zero_mul]) (M.dense j x hx)
      rwa [zero_mul] at this
  refine ⟨?_, ?_, fun f' hf' t ht => ?_⟩
  · have := key 1
    simp only [one_mul] at this
    exact this
  · have := key (-1)
    simp only [neg_mul, one_mul, neg_lt_zero] at this
    exact this
  · have h' : ∀ g a b, f' ((S.r.hom g).mat a b) =
        ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * f ((S.r.hom g).mat a b) := by
      intro g a b
      have := (conjBy_tor (push f S.r.hom) t).1 g a b
      rw [← ht] at this
      exact this
    refine AlgHom.ext fun x => ?_
    induction x using DirectSum.Decomposition.inductionOn M.𝒜 with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | @homogeneous j x =>
      rw [act_of_mem M.𝒜 _ _ x.2]
      exact eq_of_dense hf hf' _ (M.q x) (entMon S.r.hom j) (mon_tor _ f f' t h' j) (M.dense j x x.2)
