import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.SR Formalism.L2.Host

private theorem cg_sat_ev {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : CG E m) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B := by
  induction π using Quotient.inductionOn with
  | h π =>
    exact (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep UpperTheory.V.Af.formsFiniteGL E m π).mono
      fun w ⟨B, hB⟩ => ⟨B, hB⟩

private theorem list_of_multiset {d : ℕ} (B : Multiset ℂˣ) (hB : Multiset.card B = d) :
    ∃ f : Fin d → ℂˣ, Finset.univ.val.map f = B := by
  induction B using Quot.inductionOn with
  | h l =>
    have hl : l.length = d := by simpa using hB
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

private theorem power_sum_map {d : ℕ} (f : Fin d → ℂˣ) (k : ℕ) :
    ((Finset.univ.val.map f).map fun z : ℂˣ => (z : ℂ) ^ k).sum = ∑ a, (f a : ℂ) ^ k := by
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

open PositivityTheory.RgJS in
private theorem sat_pow {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : CG E m) (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w) (hB : π.HasSat w B) (i : ℕ) :
    (π.twist (χ ^ i)).HasSat w (B.map (· * χ.val w ^ i)) := by
  induction i with
  | zero => simpa [CG.twist_one] using hB
  | succ i ih =>
    have h := satake_twist_holds E m _ χ w _ hχ ih
    rw [← CG.twist_mul, Multiset.map_map] at h
    rw [pow_succ]
    simpa [Function.comp_def, pow_succ, mul_assoc] using h

open PositivityTheory.RgJS in
theorem UpperTheory.V.Z.Tf.SR.splitRigid_of (hSh : ShareBd) (hAS : AbsShare) (hTw : AntiTw) : SplitRigid := by
  intro E _ _ _ hE n hn π hπu J _ a P ha1 hPu hev
  classical
  obtain ⟨χ, hπt, hχ⟩ := hTw E hE
  obtain ⟨hχu, hχi⟩ := hχ n π hn hπu
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 16 * (Fintype.card J + 1) ^ 2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.succ_le_of_lt (by positivity)
  have e00 : π.twist (χ ^ 0) = π := by rw [pow_zero, CG.twist_one]
  have hRSU : RSU := rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole
  have hBd : GlobalTheory.Published.JacquetShalikaBound := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
  let u : Fin M ⊕ J → Σ m, CG E m := Sum.elim (fun i => ⟨n, π.twist (χ ^ i.val)⟩) fun j => ⟨a j, P j⟩
  let X : Type := ↥(Set.range u)
  have : Fintype X := Fintype.ofFinite X
  have hX : ∀ x : X, 1 ≤ x.1.1 ∧ x.1.2.IsUnitary := by
    rintro ⟨p, ⟨o, rfl⟩⟩
    cases o with
    | inl i => exact ⟨hn, hχu i.val⟩
    | inr j => exact ⟨ha1 j, hPu j⟩
  let z : Fin M → X := fun i => ⟨u (.inl i), .inl i, rfl⟩
  let x₀ : X := z ⟨0, hM1⟩
  let y : J → X := fun j => ⟨u (.inr j), .inr j, rfl⟩
  choose S0 hS0 using fun x y : X => hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x).1 (hX y).1 (hX x).2 (hX y).2
  let S1 : Finset (HeightOneSpectrum (𝓞 E)) := (Filter.eventually_cofinite.1 hev).toFinset
  let S2 : Finset (HeightOneSpectrum (𝓞 E)) := (Filter.eventually_cofinite.1 hπt).toFinset
  let S3 : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.biUnion fun x : X => (Filter.eventually_cofinite.1 (cg_sat_ev x.1.2)).toFinset
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    S1 ∪ S2 ∪ S3 ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2)
  have hS1 : ∀ w : Off E S, IsSplitAt w.1 →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w.1 (b j)) ∧ π.HasSat w.1 (∑ j, b j) := by
    intro w
    by_contra h
    refine w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))
    rw [Set.Finite.mem_toFinset]
    exact h
  have hS2 : ∀ w : Off E S, χ.UnrAt w.1 ∧ ‖((χ.val w.1 : ℂˣ) : ℂ)‖ = 1 ∧ (¬ IsSplitAt w.1 → χ.val w.1 = 1) := by
    intro w
    by_contra h
    refine w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)))
    rw [Set.Finite.mem_toFinset]
    exact h
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    intro x w
    have hw : ∃ B, x.1.2.HasSat w.1 B := by
      by_contra h
      refine w.2 (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, ?_⟩)))
      rw [Set.Finite.mem_toFinset]
      exact h
    obtain ⟨B, hB⟩ := hw
    obtain ⟨f, hf⟩ := list_of_multiset B hB.card
    exact ⟨f, hf ▸ hB⟩
  choose α hα using hex
  let d : X → ℕ := fun x => x.1.1
  let A : ∀ x : X, Off E S → Fin (d x) → ℂ := fun x w i => (α x w i : ℂ)
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩)
  have hSys : Sys nq X d A := by
    refine ⟨prime_sum_converges_and_diverges E S, fun x => (hX x).1, fun x w i => ?_, fun x w => ?_, fun x y => ?_⟩
    · have h := (hBd E x.1.1 x.1.2 (hX x).2 w.1 _ (hα x w) (α x w i)
        (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
      show ‖((α x w i : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
      rw [Real.sqrt_eq_rpow]
      exact h.le
    · have h := determinant_one_condition_holds E x.1.1 x.1.2 w.1 _ (hX x).2 (hα x w)
      rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
      exact h
    · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
      refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
      rw [hFe σ hσ]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
        rfl
  let I : Set (Off E S) := {w | ¬ IsSplitAt w.1}
  have hx₀ : ∀ w : Off E S, π.HasSat w.1 (Finset.univ.val.map (α x₀ w)) := fun w => by
    have h : (π.twist (χ ^ 0)).HasSat w.1 (Finset.univ.val.map (α x₀ w)) := hα x₀ w
    rwa [e00] at h
  have hz : Function.Injective z := fun i i' h => by
    have h1 : (⟨n, π.twist (χ ^ i.val)⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ i'.val)⟩ := congrArg Subtype.val h
    exact Fin.ext (hχi (eq_of_heq (Sigma.mk.inj h1).2))
  have hzp : ∀ (i : Fin M) (w : Off E S) (k : ℕ),
      ∑ b, A (z i) w b ^ k = ((χ.val w.1 : ℂˣ) : ℂ) ^ (i.val * k) * ∑ a, A x₀ w a ^ k := by
    intro i w k
    have h1 : (π.twist (χ ^ i.val)).HasSat w.1 (Finset.univ.val.map (α (z i) w)) := hα (z i) w
    have h2 := h1.unique (sat_pow π χ w.1 _ (hS2 w).1 (hx₀ w) i.val)
    have h3 := congrArg (fun M : Multiset ℂˣ => (M.map fun t : ℂˣ => (t : ℂ) ^ k).sum) h2
    simp only [Multiset.map_map] at h3
    rw [Finset.mul_sum]
    refine h3.trans ?_
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
    exact mul_comm _ _
  obtain ⟨C, hC⟩ := hSh (Off E S) nq X d A hSys x₀ I M z (fun w => ((χ.val w.1 : ℂˣ) : ℂ)) hM1 hz (fun w => (hS2 w).2.1)
    (fun w hw => by rw [(hS2 w).2.2 hw, Units.val_one]) hzp
  have hpow : ∀ w, w ∉ I → ∀ k : ℕ, ∑ i, A x₀ w i ^ k = ∑ j, ∑ i, A (y j) w i ^ k := by
    intro w hwI k
    have hsp : IsSplitAt w.1 := by
      by_contra h
      exact hwI h
    obtain ⟨b, hb, hπb⟩ := hS1 w hsp
    have e1 : ∀ j, b j = Finset.univ.val.map (α (y j) w) := fun j => (hb j).unique (hα (y j) w)
    have e0 : ∑ j, b j = Finset.univ.val.map (α x₀ w) := hπb.unique (hx₀ w)
    let φ : Multiset ℂˣ →+ ℂ :=
      Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ) ^ k)
    have hφ : ∀ M : Multiset ℂˣ, φ M = (M.map fun z : ℂˣ => (z : ℂ) ^ k).sum := fun M => rfl
    have h := congrArg φ e0
    rw [map_sum] at h
    simp only [hφ, e1, power_sum_map] at h
    exact h.symm
  obtain ⟨j, hj⟩ := hAS (Off E S) nq X d A hSys x₀ I J y M C hM.ge hC hpow
  have h1 : (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ 0)⟩ := congrArg Subtype.val hj
  exact ⟨j, by rw [h1, e00]⟩
