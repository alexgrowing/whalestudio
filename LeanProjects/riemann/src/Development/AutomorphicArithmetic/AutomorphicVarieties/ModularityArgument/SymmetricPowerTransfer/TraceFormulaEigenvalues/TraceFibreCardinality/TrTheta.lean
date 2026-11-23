import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

open Module

private theorem trTheta_nil {Λ M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (n : Λ → Module.End ℂ M) (T : Module.End ℂ M) (σ : Λ → Λ)
    (hc : ∀ a b, Commute (n a) (n b)) (hn : ∀ a, IsNilpotent (n a))
    (hT : ∀ a, T * n a = n (σ a) * T) (a : Λ) : LinearMap.trace ℂ M (n a * T) = 0 := by
  classical
  have key : ∀ F : Submodule ℂ M, (∀ b, F.map (n b) ≤ F) → F ≤ ⨆ b, F.map (n b) → F = ⊥ := by
    intro F hinv hle
    obtain ⟨G0, ⟨t, rfl⟩, hmax⟩ := (wellFounded_gt (α := Submodule ℂ M)).has_min
      {G | ∃ t : Finset Λ, G = t.sup fun b => F.map (n b)} ⟨⊥, ∅, rfl⟩
    have hall : ∀ b, F.map (n b) ≤ t.sup fun b => F.map (n b) := by
      intro b
      by_contra hb
      apply hmax _ ⟨insert b t, rfl⟩
      rw [Finset.sup_insert]
      exact lt_of_le_of_ne le_sup_right (fun h => hb (by rw [h]; exact le_sup_left))
    have hF : F ≤ t.sup fun b => F.map (n b) := hle.trans (iSup_le hall)
    clear hmax hall hle
    induction t using Finset.induction_on with
    | empty => simpa using hF
    | insert c t hct ih =>
      apply ih
      have Gmap : (t.sup fun b => F.map (n b)).map (n c) ≤ t.sup fun b => F.map (n b) := by
        refine Finset.sup_induction (p := fun P : Submodule ℂ M => P.map (n c) ≤ t.sup fun b => F.map (n b))
          (by simp) (fun P1 h1 P2 h2 => ?_) (fun b hb => ?_)
        · rw [Submodule.map_sup]
          exact sup_le h1 h2
        · have e : (F.map (n b)).map (n c) = (F.map (n c)).map (n b) := by
            rw [← Submodule.map_comp, ← Submodule.map_comp]
            congr 1
            exact (hc c b).eq
          show (F.map (n b)).map (n c) ≤ _
          rw [e]
          exact (Submodule.map_mono (hinv c)).trans (Finset.le_sup (f := fun b => F.map (n b)) hb)
      rw [Finset.sup_insert] at hF
      generalize t.sup (fun b => F.map (n b)) = G at hF Gmap ⊢
      have powinv : ∀ k : ℕ, ∀ z ∈ G, (n c ^ k) z ∈ G := by
        intro k
        induction k with
        | zero => intro z hz; simpa using hz
        | succ k ihk =>
          intro z hz
          rw [pow_succ', Module.End.mul_apply]
          exact Gmap (Submodule.mem_map_of_mem (ihk z hz))
      have step : ∀ k : ℕ, ∀ x ∈ F, ∃ y ∈ F, ∃ g ∈ G, x = (n c ^ k) y + g := by
        intro k
        induction k with
        | zero => intro x hx; exact ⟨x, hx, 0, zero_mem _, by simp⟩
        | succ k ihk =>
          intro x hx
          obtain ⟨y, hy, g, hg, rfl⟩ := ihk x hx
          obtain ⟨y1, hy1, g1, hg1, rfl⟩ := Submodule.mem_sup.mp (hF hy)
          obtain ⟨y2, hy2, rfl⟩ := Submodule.mem_map.mp hy1
          refine ⟨y2, hy2, (n c ^ k) g1 + g, G.add_mem (powinv k g1 hg1) hg, ?_⟩
          rw [map_add, show (n c ^ k) (n c y2) = (n c ^ (k + 1)) y2 by
            rw [pow_succ, Module.End.mul_apply], add_assoc]
      obtain ⟨m, hm⟩ := hn c
      intro x hx
      obtain ⟨y, _, g, hg, rfl⟩ := step m x hx
      rw [hm, LinearMap.zero_apply, zero_add]
      exact hg
  let F : ℕ → Submodule ℂ M := fun j => Nat.rec ⊤ (fun _ P => ⨆ b, P.map (n b)) j
  have Fsucc : ∀ j, F (j + 1) = ⨆ b, (F j).map (n b) := fun j => rfl
  have F0 : F 0 = ⊤ := rfl
  have anti : ∀ j, F (j + 1) ≤ F j := by
    intro j
    induction j with
    | zero => rw [F0]; exact le_top
    | succ j ih =>
      rw [Fsucc (j + 1), Fsucc j]
      exact iSup_mono fun b => Submodule.map_mono ih
  have ninv : ∀ j b, (F j).map (n b) ≤ F (j + 1) := fun j b => by
    rw [Fsucc]
    exact le_iSup (fun b => (F j).map (n b)) b
  have Tinv : ∀ j, (F j).map T ≤ F j := by
    intro j
    induction j with
    | zero => rw [F0]; exact le_top
    | succ j ih =>
      rw [Fsucc, Submodule.map_iSup]
      refine iSup_le fun b => ?_
      rw [← Submodule.map_comp]
      have e : T.comp (n b) = (n (σ b)).comp T := hT b
      rw [e, Submodule.map_comp]
      exact (Submodule.map_mono ih).trans (le_iSup (fun b => (F j).map (n b)) (σ b))
  obtain ⟨_, ⟨j, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ M)).has_min (Set.range F) ⟨_, 0, rfl⟩
  have hstab : F j ≤ F (j + 1) := by
    rcases (anti j).lt_or_eq with hlt | heq
    · exact absurd hlt (hmin _ ⟨j + 1, rfl⟩)
    · exact heq.ge
  have hbot : F j = ⊥ := key (F j) (fun b => (ninv j b).trans (anti j)) (hstab.trans (Fsucc j).le)
  have hpow : ∀ k x, ((n a * T) ^ k) x ∈ F k := by
    intro k
    induction k with
    | zero => intro x; rw [F0]; exact Submodule.mem_top
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact ninv k a (Submodule.mem_map_of_mem (Tinv k (Submodule.mem_map_of_mem (ih x))))
  have hnil : IsNilpotent (n a * T) := ⟨j, LinearMap.ext fun x => by
    have hx := hpow j x
    rw [hbot, Submodule.mem_bot] at hx
    exact hx⟩
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero

private theorem trTheta_ext {ι M : Type} [AddCommGroup M] [Module ℂ M] {V : ι → Submodule ℂ M}
    (htop : ⨆ i, V i = ⊤) {f g : Module.End ℂ M} (h : ∀ i, ∀ x ∈ V i, f x = g x) : f = g := by
  ext x
  have hx : x ∈ ⨆ i, V i := by rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction V (motive := fun x => f x = g x) hx (fun i y hy => h i y hy)
    (by simp) (fun y z hy hz => by simp only [map_add, hy, hz])

private theorem trTheta_proj {ι M : Type} [AddCommGroup M] [Module ℂ M] {V : ι → Submodule ℂ M}
    (hind : iSupIndep V) (htop : ⨆ i, V i = ⊤) (i : ι) :
    ∃ P : Module.End ℂ M, (∀ x ∈ V i, P x = x) ∧ (∀ j, j ≠ i → ∀ x ∈ V j, P x = 0) ∧
      ∀ x, P x ∈ V i := by
  have hcompl : IsCompl (V i) (⨆ j, ⨆ (_ : j ≠ i), V j) := by
    refine ⟨hind i, codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
    rw [← htop]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst hj
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  refine ⟨(V i).subtype ∘ₗ (V i).projectionOnto _ hcompl, ?_, ?_, ?_⟩
  · intro x hx
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hcompl ⟨x, hx⟩)
  · intro j hj x hx
    exact congrArg Subtype.val
      (Submodule.linearProjOfIsCompl_apply_right hcompl
        ⟨x, (le_iSup₂_of_le (f := fun j (_ : j ≠ i) => V j) j hj le_rfl : V j ≤ ⨆ j, ⨆ (_ : j ≠ i), V j) hx⟩)
  · intro x
    exact ((V i).projectionOnto _ hcompl x).2

theorem UpperTheory.V.Z.Sym.Tf.trTheta :
    UpperTheory.V.Z.Sym.Tf.TrTheta := by
  intro Λ M _ _ _ u Θ σ hc hΘ
  classical
  let V : (Λ → ℂ) → Submodule ℂ M := fun χ => ⨅ a, (u a).maxGenEigenspace (χ a)
  have memV : ∀ χ x, x ∈ V χ ↔ ∀ b, ∃ k : ℕ, ((u b - χ b • (1 : End ℂ M)) ^ k) x = 0 :=
    fun χ x => Module.End.mem_iInf_maxGenEigenspace_iff u χ x
  have hmaps : ∀ a b φ, Set.MapsTo (u a) ((u b).maxGenEigenspace φ) ((u b).maxGenEigenspace φ) :=
    fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) φ
  have hind : iSupIndep V := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo u hmaps
  have htop : ⨆ χ, V χ = ⊤ := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo u hmaps
    (fun a => Module.End.iSup_maxGenEigenspace_eq_top (u a))
  have hfin : {χ | V χ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hint : DirectSum.IsInternal V :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).mpr ⟨hind, htop⟩
  choose P hP1 hP2 hP3 using trTheta_proj hind htop
  have uV : ∀ a χ, ∀ x ∈ V χ, u a x ∈ V χ := by
    intro a χ x hx
    simp only [V, Submodule.mem_iInf] at hx ⊢
    exact fun b => hmaps a b (χ b) (hx b)
  have ΘV : ∀ χ ψ : Λ → ℂ, (∀ b, ψ b = χ (σ.symm b)) → ∀ x ∈ V χ, Θ x ∈ V ψ := by
    intro χ ψ hψ x hx
    rw [memV] at hx ⊢
    intro b
    obtain ⟨k, hk⟩ := hx (σ.symm b)
    refine ⟨k, ?_⟩
    rw [hψ b]
    have hs : SemiconjBy Θ (u (σ.symm b) - χ (σ.symm b) • (1 : End ℂ M))
        (u b - χ (σ.symm b) • (1 : End ℂ M)) := by
      unfold SemiconjBy
      rw [mul_sub, sub_mul, hΘ, σ.apply_symm_apply, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    have h2 := LinearMap.congr_fun (hs.pow_right k) x
    rw [Module.End.mul_apply, Module.End.mul_apply, hk, map_zero] at h2
    exact h2.symm
  have fixOK : ∀ χ : Λ → ℂ, (∀ b, χ (σ b) = χ b) → ∀ b, χ b = χ (σ.symm b) :=
    fun χ h b => by rw [← h (σ.symm b), σ.apply_symm_apply]
  have nfix : ∀ χ : Λ → ℂ, ¬ (∀ b, χ (σ b) = χ b) → (fun b => χ (σ.symm b)) ≠ χ := by
    intro χ h he
    apply h
    intro b
    have h3 := congrFun he (σ b)
    simp only [Equiv.symm_apply_apply] at h3
    exact h3.symm
  set F := hfin.toFinset with hF
  have sumP : ∑ χ ∈ F, P χ = 1 := by
    apply trTheta_ext htop
    intro ψ x hx
    rw [LinearMap.sum_apply, Module.End.one_apply]
    by_cases hψ : ψ ∈ F
    · rw [Finset.sum_eq_single ψ (fun χ _ hne => hP2 χ ψ (Ne.symm hne) x hx) (fun h => absurd hψ h)]
      exact hP1 ψ x hx
    · have hb : V ψ = ⊥ := by
        rw [hF, Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      have hx0 : x = 0 := by
        have hx' := hx
        rw [hb, Submodule.mem_bot] at hx'
        exact hx'
      subst hx0
      simp
  have hPΘ : ∀ χ, Set.MapsTo (P χ * Θ) (V χ) (V χ) := fun χ x _ => hP3 χ (Θ x)
  refine ⟨F.filter (fun χ => ∀ b, χ (σ b) = χ b),
    fun χ => LinearMap.trace ℂ (V χ) ((P χ * Θ).restrict (hPΘ χ)), ?_, ?_⟩
  · intro χ hχ
    rw [Finset.mem_filter, hF, Set.Finite.mem_toFinset] at hχ
    exact ⟨hχ.1, hχ.2⟩
  · intro a
    have decomp : u a * Θ = ∑ χ ∈ F, u a * Θ * P χ := by
      rw [← Finset.mul_sum, sumP, mul_one]
    rw [decomp, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    split_ifs with hfix
    · have hg : ∀ ψ, Set.MapsTo (u a * Θ * P χ) (V ψ) (V ψ) := by
        intro ψ x hx
        by_cases h : ψ = χ
        · subst h
          show u a (Θ (P ψ x)) ∈ V ψ
          rw [hP1 ψ x hx]
          exact uV a ψ _ (ΘV ψ ψ (fixOK ψ hfix) x hx)
        · show u a (Θ (P χ x)) ∈ V ψ
          rw [hP2 χ ψ h x hx, map_zero, map_zero]
          exact zero_mem _
      rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hg]
      rw [Finset.sum_eq_single χ ?_ (fun h => absurd hχ h)]
      · have hN : ∀ b, Set.MapsTo (u b - χ b • (1 : End ℂ M)) (V χ) (V χ) := by
          intro b x hx
          rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
          exact (V χ).sub_mem (uV b χ x hx) ((V χ).smul_mem _ hx)
        let N : Λ → Module.End ℂ (V χ) := fun b => (u b - χ b • (1 : End ℂ M)).restrict (hN b)
        let T : Module.End ℂ (V χ) := (P χ * Θ).restrict (hPΘ χ)
        have hEq : (u a * Θ * P χ).restrict (hg χ) = (χ a • 1 + N a) * T := by
          apply LinearMap.ext
          intro y
          apply Subtype.ext
          have hΘy : Θ y ∈ V χ := ΘV χ χ (fixOK χ hfix) y y.2
          change u a (Θ (P χ y)) = χ a • P χ (Θ y) + (u a - χ a • (1 : End ℂ M)) (P χ (Θ y))
          rw [hP1 χ _ y.2, hP1 χ _ hΘy, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
          abel
        have hcN : ∀ b b', Commute (N b) (N b') := by
          intro b b'
          have h0 : Commute (u b - χ b • (1 : End ℂ M)) (u b' - χ b' • (1 : End ℂ M)) :=
            Commute.sub_left ((hc b b').sub_right ((Commute.one_right (u b)).smul_right (χ b')))
              ((Commute.one_left _).smul_left (χ b))
          show N b * N b' = N b' * N b
          apply LinearMap.ext
          intro y
          apply Subtype.ext
          simp only [N, Module.End.mul_apply, LinearMap.restrict_coe_apply]
          exact LinearMap.congr_fun h0.eq y
        have hnN : ∀ b, IsNilpotent (N b) := fun b =>
          Module.End.isNilpotent_restrict_of_le (iInf_le (fun a => (u a).maxGenEigenspace (χ a)) b)
            (Module.End.isNilpotent_restrict_genEigenspace_top (u b) (χ b))
        have hTN : ∀ b, T * N b = N (σ b) * T := by
          intro b
          have hE : Θ * (u b - χ b • (1 : End ℂ M)) = (u (σ b) - χ (σ b) • (1 : End ℂ M)) * Θ := by
            rw [hfix b, mul_sub, sub_mul, hΘ, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
          apply LinearMap.ext
          intro y
          apply Subtype.ext
          have m1 : Θ ((u b - χ b • (1 : End ℂ M)) y) ∈ V χ :=
            ΘV χ χ (fixOK χ hfix) _ (hN b y.2)
          have m2 : Θ y ∈ V χ := ΘV χ χ (fixOK χ hfix) y y.2
          change P χ (Θ ((u b - χ b • (1 : End ℂ M)) y)) = (u (σ b) - χ (σ b) • (1 : End ℂ M)) (P χ (Θ y))
          rw [hP1 χ _ m1, hP1 χ _ m2]
          exact LinearMap.congr_fun hE y
        rw [hEq, add_mul, map_add, smul_mul_assoc, one_mul, map_smul, smul_eq_mul,
          trTheta_nil N T σ hcN hnN hTN a, add_zero, mul_comm]
      · intro ψ _ hne
        have hz : (u a * Θ * P χ).restrict (hg ψ) = 0 := by
          apply LinearMap.ext
          intro y
          apply Subtype.ext
          change u a (Θ (P χ y)) = 0
          rw [hP2 χ ψ hne y.1 y.2, map_zero, map_zero]
        rw [hz, map_zero]
    · apply LinearMap.trace_eq_zero_of_mapsTo_ne hint
        (fun ψ => if ψ = χ then (fun b => χ (σ.symm b)) else χ)
      · intro ψ
        by_cases h : ψ = χ
        · subst h
          rw [if_pos rfl]
          exact nfix ψ hfix
        · rw [if_neg h]
          exact fun e => h e.symm
      · intro ψ x hx
        by_cases h : ψ = χ
        · subst h
          rw [if_pos rfl]
          show u a (Θ (P ψ x)) ∈ V _
          rw [hP1 ψ x hx]
          exact uV a _ _ (ΘV ψ _ (fun b => rfl) x hx)
        · rw [if_neg h]
          show u a (Θ (P χ x)) ∈ V χ
          rw [hP2 χ ψ h x hx, map_zero, map_zero]
          exact zero_mem _
