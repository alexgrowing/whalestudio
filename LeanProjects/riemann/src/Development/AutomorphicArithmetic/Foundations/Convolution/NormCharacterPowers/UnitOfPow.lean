import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

section

variable {E : Type} [Field E] [NumberField E]

private theorem val_pow' (χ : HChar E) (j : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (χ ^ j).val w = χ.val w ^ j :=
  MonoidHom.pow_apply χ.1 j _

private theorem unr_pow {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) (j : ℕ) : (χ ^ j).UnrAt w := by
  intro x hx
  have e : (χ ^ j).loc w x = χ.loc w x ^ j := MonoidHom.pow_apply χ.1 j _
  rw [e, h x hx, one_pow]

private theorem unr_inv {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  intro x hx
  have e : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
  rw [e, h x hx, inv_one]

private theorem unit_of_pow {χ : HChar E} {l : ℕ} (hl : l ≠ 0) (h : χ ^ l = 1) : χ.IsUnitary := by
  intro x
  have e : χ.1 x ^ l = 1 := by
    have e1 : (χ ^ l).1 x = χ.1 x ^ l := MonoidHom.pow_apply χ.1 l _
    rw [← e1, h]; rfl
  have e2 : ((χ.1 x : ℂˣ) : ℂ) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e2 hl

variable [IsTotallyComplex E]

private theorem unit_twist {n : ℕ} {π : CG E n} (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) :
    (π.twist χ).IsUnitary := by
  obtain ⟨ω, hω, hc⟩ := h
  refine ⟨_, fun x => ?_, hc.twist χ⟩
  have e : (ω * χ ^ n).1 x = ω.1 x * χ.1 x ^ n := congrArg (ω.1 x * ·) (MonoidHom.pow_apply χ.1 n _)
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hω x, hχ x, one_pow, one_mul]

private theorem sat_untw {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    (h : ∃ B, (π.twist χ).HasSat w B) : ∃ B, π.HasSat w B := by
  obtain ⟨B, hB⟩ := h
  have := satake_twist_holds E n _ χ⁻¹ w B (unr_inv hχ) hB
  rw [← CG.twist_mul, mul_inv_cancel, CG.twist_one] at this
  exact ⟨_, this⟩

private theorem sat_key {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {α : Fin n → ℂˣ} (hα : π.HasSat w (Finset.univ.val.map α)) {B : Multiset ℂˣ} (hB : (π.twist χ).HasSat w B) :
    B.map (fun u : ℂˣ => (u : ℂ)) = Finset.univ.val.map fun a => (α a : ℂ) * (χ.val w : ℂ) := by
  rw [hB.unique (satake_twist_holds E n π χ w _ hχ hα), Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ => by simp

end

private theorem ev_sat {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (HeightOneSpectrum (𝓞 M))} {u : Off M T → Off K S}
    {f : Off M T → ℕ} (hu : ∀ w, (u w).1 = w.1.under (𝓞 K)) (hf : ∀ w, normV w.1 = normV (u w).1 ^ f w)
    (hs : Function.Surjective u) {sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop}
    {satE : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop} (h : WeakBC sat satE) :
    (∀ᶠ v in Filter.cofinite, ∃ B, sat v B) ∧ ∀ᶠ w in Filter.cofinite, ∃ B, satE w B := by
  constructor
  · have h' := Filter.eventually_cofinite.1 h
    have h2 := (h'.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)).eventually_cofinite_notMem
    filter_upwards [h2, S.eventually_cofinite_notMem] with v hv hvS
    obtain ⟨w, hw⟩ := hs ⟨v, hvS⟩
    have e : w.1.under (𝓞 K) = v := (hu w).symm.trans (congrArg Subtype.val hw)
    by_contra hc
    refine hv ⟨w.1, fun hg => hc ?_, e⟩
    obtain ⟨B, hB, -⟩ := hg (f w) (by rw [← hu w]; exact hf w)
    exact ⟨B, e ▸ hB⟩
  · filter_upwards [h, T.eventually_cofinite_notMem] with w hw hwT
    obtain ⟨B, -, hB⟩ := hw (f ⟨w, hwT⟩) (by have := hf ⟨w, hwT⟩; rwa [hu] at this)
    exact ⟨_, hB⟩

private theorem lift_eq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsTotallyComplex K] [IsTotallyComplex M] {n : ℕ} {π : CG K n} {ν : HChar K} {t : ℝ} (hν : ν.IsAbsPow t)
    {ι : Type} [Fintype ι] {m : ι → ℕ} {P : ∀ i, CG M (m i)} {ν' : ι → HChar M} {s : ι → ℝ}
    (hν' : ∀ i, (ν' i).IsAbsPow (s i)) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} {f : ℕ}
    {α : Fin n → ℂˣ} (hα : π.HasSat v (Finset.univ.val.map α)) {β : ∀ i, Fin (m i) → ℂˣ}
    (hβ : ∀ i, (P i).HasSat w (Finset.univ.val.map (β i)))
    (h : ∃ B, (π.twist ν).HasSat v B ∧ sumSat (fun i => (P i).twist (ν' i)) w (B.map (· ^ f))) :
    ∑ i, Finset.univ.val.map (fun a => (β i a : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s i : ℂ))) =
      Finset.univ.val.map fun a => ((α a : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(t : ℂ))) ^ f := by
  obtain ⟨B, hB, B', hB', e⟩ := h
  have e1 := sat_key (hν.1 v) hα hB
  have e2 := fun i => sat_key ((hν' i).1 w) (hβ i) (hB' i)
  simp only [(hν' _).2.1 w] at e2
  rw [hν.2.1 v] at e1
  have e3 := congrArg (Multiset.map fun u : ℂˣ => (u : ℂ)) e
  have e4 : Multiset.map (fun u : ℂˣ => (u : ℂ)) (∑ i, B' i) = ∑ i, Multiset.map (fun u : ℂˣ => (u : ℂ)) (B' i) :=
    map_sum (Multiset.mapAddMonoidHom fun u : ℂˣ => (u : ℂ)) B' Finset.univ
  have e5 := congrArg (Multiset.map fun c : ℂ => c ^ f) e1
  rw [Multiset.map_map, Multiset.map_map] at e5
  rw [e4, Multiset.map_map] at e3
  simp only [e2] at e3
  rw [← e3]
  exact Eq.trans (Multiset.map_congr rfl fun a _ => by simp) e5

theorem UpperTheory.ConvolutionTheory.R.count :
    AbsCount → SysEx → CoverEx → Count := by
  intro hA hS hC K M _ _ _ _ _ _ _ _ hl η hη n π π₁ ι _ m P hn hm hπ hπ₁
  classical
  obtain ⟨ν, hν, hU⟩ := unit_exponent_holds K
  obtain ⟨ν', hν', hU'⟩ := unit_exponent_holds M
  obtain ⟨π0, t, hu0, rfl⟩ := hU n π hn
  obtain ⟨π1, t1, hu1, rfl⟩ := hU n π₁ hn
  choose P0 s huP hP using fun i => hU' (m i) (P i) (hm i)
  obtain rfl : P = fun i => (P0 i).twist (ν' (s i)) := funext hP
  have hηl : η ^ Module.finrank K M = 1 := hη.1.2.1
  have hηu : ∀ j : ℕ, (η ^ j).IsUnitary := fun j =>
    unit_of_pow hl.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hηl, one_pow])
  obtain ⟨S1, T1, u1, f1, -, -, hu1', hunr1, hf1, hc1⟩ := hC K M hl η hη ∅ ∅
  have hs1 : Function.Surjective u1 := fun v => by
    have : Nat.card {w // u1 w = v} ≠ 0 := by
      rcases hc1.fib v with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  obtain ⟨e0, eP⟩ := ev_sat hu1' hf1 hs1 hπ
  obtain ⟨e1, -⟩ := ev_sat hu1' hf1 hs1 hπ₁
  let X : Set (Σ a, CG K a) := insert ⟨n, π1⟩ (Set.range fun j : ℕ => ⟨n, π0.twist (η ^ j)⟩)
  let X' : Set (Σ a, CG M a) := Set.range fun i => ⟨m i, P0 i⟩
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (((Set.finite_lt_nat (Module.finrank K M)).image
      fun j : ℕ => (⟨n, π0.twist (η ^ j)⟩ : Σ a, CG K a)).subset ?_)
    rintro _ ⟨j, rfl⟩
    exact ⟨j % Module.finrank K M, Nat.mod_lt _ hl.pos, by
      beta_reduce; rw [← pow_eq_pow_mod j hηl]⟩
  obtain ⟨S0, hS0⟩ := hS K X hXf (by
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact ⟨hn, hu1, e1.mono fun v hv => sat_untw ((hν _).1 v) hv⟩
    · refine ⟨hn, unit_twist hu0 (hηu j), ?_⟩
      filter_upwards [e0, S1.eventually_cofinite_notMem] with v hv hvS
      obtain ⟨B, hB⟩ := sat_untw ((hν _).1 v) hv
      exact ⟨_, satake_twist_holds K n π0 _ v B (unr_pow (hunr1 ⟨v, hvS⟩) j) hB⟩)
  obtain ⟨T0, hT0⟩ := hS M X' (Set.finite_range _) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨hm i, huP i, eP.mono fun w ⟨B, B', hB', _⟩ => sat_untw ((hν' _).1 w) ⟨_, hB' i⟩⟩)
  have hbad := Filter.eventually_cofinite.1 (hπ.and hπ₁)
  obtain ⟨S, T, u, f, hS0S, hT0T, hu, hunr, hf, hc⟩ := hC K M hl η hη S0 (T0 ∪ hbad.toFinset)
  obtain ⟨α, hα, hsys⟩ := hS0 S hS0S
  obtain ⟨β, hβ, hsys'⟩ := hT0 T (Finset.subset_union_left.trans hT0T)
  have hgood : ∀ w : Off M T, (∃ B, (π0.twist (ν t)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))) ∧ ∃ B, (π1.twist (ν t1)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w)) := fun w => by
    have h1 := hf w
    rw [hu] at h1 ⊢
    have h2 : w.1 ∉ hbad.toFinset := fun h => w.2 (hT0T (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact ⟨h2.1 _ h1, h2.2 _ h1⟩
  let x : X := ⟨⟨n, π1⟩, Or.inl rfl⟩
  let y : ℕ → X := fun j => ⟨⟨n, π0.twist (η ^ j)⟩, Or.inr ⟨j, rfl⟩⟩
  let z : ι → X' × ℝ := fun i => (⟨⟨m i, P0 i⟩, i, rfl⟩, s i)
  have hy0 : ∀ v : Off K S, π0.HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := fun v => by
    have : (π0.twist (η ^ 0)).HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := hα (y 0) v
    rwa [pow_zero, CG.twist_one] at this
  obtain ⟨ht, hs, hcount⟩ := hA _ _ _ nq nq u f _ hl.pos hc X X' _ _ _ _ hsys hsys' ι x y z t1 t
    (fun j v => by
      have := sat_key (unr_pow (hunr v) j) (hy0 v) (hα (y j) v)
      rw [Multiset.map_map, val_pow', Units.val_pow_eq_pow_val] at this
      rw [Multiset.map_map]
      exact this)
    (fun w => lift_eq (hν t1) (fun i => hν' (s i)) (hα x (u w)) (fun i => hβ (z i).1 w) (hgood w).2)
    (fun w => lift_eq (hν t) (fun i => hν' (s i)) (hy0 (u w)) (fun i => hβ (z i).1 w) (hgood w).1)
  subst ht
  have hs' : ∀ i, s i = t1 := hs
  have key : ∀ {a b : ℕ} (σ : CG M a) (σ' : CG M b) (χ : HChar M),
      (⟨a, σ.twist χ⟩ : Σ a, CG M a) = ⟨b, σ'.twist χ⟩ ↔ (⟨a, σ⟩ : Σ a, CG M a) = ⟨b, σ'⟩ := by
    intro a b σ σ' χ
    constructor
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      exact congrArg _ (CG.twist_injective χ (eq_of_heq (Sigma.mk.inj e).2))
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      rw [eq_of_heq (Sigma.mk.inj e).2]
  refine Eq.trans (congrArg Finset.card (Finset.ext fun j => ?_))
    (hcount.trans (congrArg Finset.card (Finset.ext fun p => ?_)))
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [← CG.twist_mul, mul_comm, CG.twist_mul, Subtype.ext_iff]
    constructor
    · intro e
      exact congrArg (Sigma.mk n) (CG.twist_injective _ e)
    · intro e
      rw [eq_of_heq (Sigma.mk.inj e).2]
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [Subtype.ext_iff, hs' p.1, hs' p.2, key]
