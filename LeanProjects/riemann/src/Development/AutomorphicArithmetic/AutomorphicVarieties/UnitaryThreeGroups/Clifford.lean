import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

private theorem common_eigen {κ E ι : Type*} [Field κ] [IsAlgClosed κ] [AddCommGroup E] [Module κ E]
    [FiniteDimensional κ E] (f : ι → Module.End κ E) (S : Submodule κ E) (hS : S ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ S, f i v ∈ S) (hc : ∀ i j, ∀ v ∈ S, f i (f j v) = f j (f i v)) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ i, ∃ c : κ, f i v = c • v := by
  obtain ⟨F, ⟨hF0, hFS, hFst⟩, hmin⟩ := (wellFounded_lt (α := Submodule κ E)).has_min
    {F | F ≠ ⊥ ∧ F ≤ S ∧ ∀ i, ∀ v ∈ F, f i v ∈ F} ⟨S, hS, le_rfl, hst⟩
  obtain ⟨v, hvF, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF0
  refine ⟨v, hFS hvF, hv0, fun i => ?_⟩
  haveI : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr hF0
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue ((f i).restrict (hFst i) : Module.End κ F)
  obtain ⟨w, hw⟩ := hc'.exists_hasEigenvector
  have hw1 : f i w = c • (w : E) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : E) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have key : ¬ F ⊓ Module.End.eigenspace (f i) c < F := by
    refine hmin _ ⟨?_, inf_le_left.trans hFS, ?_⟩
    · exact (Submodule.ne_bot_iff _).mpr ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩, hw0⟩
    · rintro j u ⟨huF, hu⟩
      refine ⟨hFst j u huF, Module.End.mem_eigenspace_iff.mpr ?_⟩
      rw [hc i j u (hFS huF), Module.End.mem_eigenspace_iff.mp hu, map_smul]
  have h2 : F ⊓ Module.End.eigenspace (f i) c = F := (eq_or_lt_of_le inf_le_left).resolve_right key
  have : v ∈ F ⊓ Module.End.eigenspace (f i) c := by rw [h2]; exact hvF
  exact ⟨c, Module.End.mem_eigenspace_iff.mp this.2⟩

private theorem exists_compl {Γ κ V : Type*} [Group Γ] [Field κ] [AddCommGroup V] [Module κ V]
    [FiniteDimensional κ V] (σ : Γ →* Module.End κ V) (H : Subgroup Γ) [H.Normal]
    (hirr : ∀ W : Submodule κ V, (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W₀ : Submodule κ V) (h0 : ∀ g ∈ H, ∀ v ∈ W₀, σ g v ∈ W₀) (hb : W₀ ≠ ⊥) (ht : W₀ ≠ ⊤) :
    ∃ U W : Submodule κ V, IsCompl U W ∧ U ≠ ⊥ ∧ W ≠ ⊥ ∧ (∀ g ∈ H, ∀ v ∈ U, σ g v ∈ U) ∧
      (∀ g ∈ H, ∀ v ∈ W, σ g v ∈ W) := by
  have hmul : ∀ a b v, σ a (σ b v) = σ (a * b) v := fun a b v => by rw [map_mul]; rfl
  have hcom : ∀ (X : Submodule κ V) (g : Γ), (∀ h ∈ H, ∀ v ∈ X, σ h v ∈ X) →
      ∀ h ∈ H, ∀ v ∈ X.comap (σ g), σ h v ∈ X.comap (σ g) := by
    intro X g hX h hh v hv
    have := hX (g * h * g⁻¹) (Subgroup.Normal.conj_mem ‹_› h hh g) _ hv
    rw [hmul, inv_mul_cancel_right, ← hmul] at this
    exact this
  obtain ⟨W, ⟨hW0, hWst⟩, hmin⟩ := (wellFounded_lt (α := Submodule κ V)).has_min
    {F | F ≠ ⊥ ∧ ∀ g ∈ H, ∀ v ∈ F, σ g v ∈ F} ⟨W₀, hb, h0⟩
  obtain ⟨U, ⟨hU0, hUt, hUst⟩, hmax⟩ := (wellFounded_gt (α := Submodule κ V)).has_min
    {F | F ≠ ⊥ ∧ F ≠ ⊤ ∧ ∀ g ∈ H, ∀ v ∈ F, σ g v ∈ F} ⟨W₀, hb, ht, h0⟩
  have hex : ∃ g, ¬ W ≤ U.comap (σ g) := by
    by_contra hne
    push_neg at hne
    rcases hirr (⨅ g, U.comap (σ g)) (fun g v hv => by
      rw [Submodule.mem_iInf] at hv ⊢
      intro k
      have := hv (k * g)
      rw [Submodule.mem_comap, ← hmul] at this
      exact this) with h | h
    · exact hW0 (le_bot_iff.mp (h ▸ le_iInf hne))
    · apply hUt
      rw [eq_top_iff]
      intro v _
      have : v ∈ ⨅ g, U.comap (σ g) := by rw [h]; trivial
      simpa using (Submodule.mem_iInf _).mp this 1
  obtain ⟨g, hg⟩ := hex
  have hU' := hcom U g hUst
  have hback : ∀ u ∈ U, σ g⁻¹ u ∈ U.comap (σ g) := fun u hu => by
    rw [Submodule.mem_comap, hmul]; simpa using hu
  refine ⟨U.comap (σ g), W, ⟨?_, ?_⟩, ?_, hW0, hU', hWst⟩
  · rw [disjoint_iff]
    by_contra hne
    refine hmin _ ⟨hne, fun h hh v hv => ⟨hU' h hh v hv.1, hWst h hh v hv.2⟩⟩ ?_
    exact lt_of_le_of_ne inf_le_right fun h => hg (inf_eq_right.mp h)
  · rw [codisjoint_iff]
    by_contra hne
    have hX : ∀ h ∈ H, ∀ v ∈ U.comap (σ g) ⊔ W, σ h v ∈ U.comap (σ g) ⊔ W := by
      intro h hh v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.add_mem_sup (hU' h hh a ha) (hWst h hh b hb)
    have hle : U ≤ (U.comap (σ g) ⊔ W).comap (σ g⁻¹) := fun u hu =>
      Submodule.mem_sup_left (hback u hu)
    refine hmax ((U.comap (σ g) ⊔ W).comap (σ g⁻¹)) ⟨?_, ?_, hcom _ _ hX⟩ ?_
    · exact fun h => hU0 (le_bot_iff.mp (h ▸ hle))
    · intro h
      apply hne
      rw [eq_top_iff]
      intro v _
      have : σ g v ∈ (U.comap (σ g) ⊔ W).comap (σ g⁻¹) := by rw [h]; trivial
      rw [Submodule.mem_comap, hmul] at this
      simpa using this
    · refine lt_of_le_of_ne hle fun h => hg fun w hw => ?_
      rw [Submodule.mem_comap, h, Submodule.mem_comap, hmul]
      simpa using Submodule.mem_sup_right hw
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    refine (Submodule.ne_bot_iff _).mpr ⟨_, hback u hu, fun h => hu0 ?_⟩
    have := congrArg (σ g) h
    rw [hmul] at this
    simpa using this

private theorem exists_traceless {Γ κ V : Type*} [Group Γ] [Field κ] [CharZero κ] [AddCommGroup V]
    [Module κ V] [FiniteDimensional κ V] (σ : Γ →* Module.End κ V) (H : Subgroup Γ)
    (U W : Submodule κ V) (hc : IsCompl U W) (hU0 : U ≠ ⊥) (hW0 : W ≠ ⊥)
    (hU : ∀ g ∈ H, ∀ v ∈ U, σ g v ∈ U) (hW : ∀ g ∈ H, ∀ v ∈ W, σ g v ∈ W) :
    ∃ P : Module.End κ V, P ≠ 0 ∧ LinearMap.trace κ V P = 0 ∧ ∀ h ∈ H, σ h * P = P * σ h := by
  let Q : Module.End κ V := U.subtype ∘ₗ U.linearProjOfIsCompl W hc
  have hQU : ∀ u ∈ U, Q u = u := fun u hu => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)
  have hQW : ∀ u ∈ W, Q u = 0 := fun u hu => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨u, hu⟩)
  have hQ : ∀ h ∈ H, σ h * Q = Q * σ h := by
    intro h hh
    ext v
    have : v ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    simp [hQU a ha, hQW b hb, hQU _ (hU h hh a ha), hQW _ (hW h hh b hb)]
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  haveI : Nontrivial V := ⟨u, 0, hu0⟩
  have hn : (Module.finrank κ V : κ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ⟨(Module.finrank κ V : κ) • Q - LinearMap.trace κ V Q • 1, fun h => ?_, ?_, ?_⟩
  · have h1 := congrArg (fun T : Module.End κ V => T w) h
    have h2 := congrArg (fun T : Module.End κ V => T u) h
    simp [hQW w hw, hw0] at h1
    simp [hQU u hu, h1, hu0] at h2
    exact hn (by simp [h2])
  · simp [mul_comm]
  · intro h hh
    simp [mul_sub, sub_mul, hQ h hh]

private theorem exists_twist {Γ κ V : Type*} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ]
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (σ : Γ →* Module.End κ V)
    (H : Subgroup Γ) [H.Normal] (hab : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (P : Module.End κ V) (hP0 : P ≠ 0) (hPt : LinearMap.trace κ V P = 0)
    (hP : ∀ h ∈ H, σ h * P = P * σ h) :
    ∃ T : Module.End κ V, T ≠ 0 ∧ LinearMap.trace κ V T = 0 ∧ (∀ h ∈ H, σ h * T = T * σ h) ∧
      ∀ g, ∃ c : κ, σ g * T = c • (T * σ g) := by
  let S : Submodule κ (Module.End κ V) :=
    { carrier := {T | LinearMap.trace κ V T = 0 ∧ ∀ h ∈ H, σ h * T = T * σ h}
      add_mem' := fun ha hb => ⟨by simp [ha.1, hb.1], fun h hh => by
        rw [mul_add, add_mul, ha.2 h hh, hb.2 h hh]⟩
      zero_mem' := by simp
      smul_mem' := fun c a ha => ⟨by simp [ha.1], fun h hh => by simp [ha.2 h hh]⟩ }
  let f : Γ → Module.End κ (Module.End κ V) := fun g =>
    LinearMap.mulLeft κ (σ g) ∘ₗ LinearMap.mulRight κ (σ g⁻¹)
  have hf : ∀ g T, f g T = σ g * (T * σ g⁻¹) := fun _ _ => rfl
  have hff : ∀ a b T, f a (f b T) = f (a * b) T := fun a b T => by
    simp only [hf, _root_.mul_inv_rev, map_mul, mul_assoc]
  have hH : ∀ h ∈ H, ∀ T ∈ S, f h T = T := fun h hh T hT => by
    rw [hf, ← mul_assoc, hT.2 h hh, mul_assoc, ← map_mul]; simp
  have hst : ∀ g, ∀ T ∈ S, f g T ∈ S := by
    intro g T hT
    refine ⟨?_, fun h hh => ?_⟩
    · rw [hf, LinearMap.trace_mul_comm, mul_assoc, ← map_mul]; simpa using hT.1
    · have h1 := hT.2 (g⁻¹ * h * g) (by simpa using Subgroup.Normal.conj_mem ‹_› h hh g⁻¹)
      have e1 : σ h * σ g = σ g * σ (g⁻¹ * h * g) := by
        rw [← map_mul, ← map_mul]; congr 1; group
      have e2 : σ g⁻¹ * σ h = σ (g⁻¹ * h * g) * σ g⁻¹ := by
        rw [← map_mul, ← map_mul]; congr 1; group
      rw [hf, ← mul_assoc, e1, mul_assoc, ← mul_assoc _ T, h1, mul_assoc, ← e2]
      simp only [mul_assoc]
  obtain ⟨T, hT, hT0, hTc⟩ := common_eigen f S ((Submodule.ne_bot_iff _).mpr ⟨P, ⟨hPt, hP⟩, hP0⟩) hst
    (fun a b T hT => by
      rw [← hH _ (hab a b) _ (hst b _ (hst a T hT)), hff, hff, hff]
      congr 2; group)
  refine ⟨T, hT0, hT.1, hT.2, fun g => ?_⟩
  obtain ⟨c, hc⟩ := hTc g
  refine ⟨c, ?_⟩
  rw [← smul_mul_assoc, ← hc, hf, mul_assoc, mul_assoc, ← map_mul]; simp

theorem UpperTheory.V.U3.exists_selfTwist :
    ∀ {Γ κ : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] {m : ℕ} (ρ : Γ →* GL (Fin m) κ) (H : Subgroup Γ) [H.Normal],
      (∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H) → MatIrr ⊤ (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) → ¬ MatIrr H (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) →
      ∃ φ : Γ →* κˣ, φ ≠ 1 ∧ H ≤ φ.ker ∧ φ ^ m = 1 ∧
        MatIso ⊤ (fun g => ((φ g : κˣ) : κ) • (ρ g : Matrix (Fin m) (Fin m) κ)) (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) := by
  intro Γ κ _ _ _ _ m ρ H _ hab hirr hred
  let σ : Γ →* Module.End κ (Fin m → κ) :=
    { toFun := fun g => Matrix.toLin' (ρ g : Matrix (Fin m) (Fin m) κ)
      map_one' := by simp [Module.End.one_eq_id]
      map_mul' := fun a b => by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp] }
  have hσ : ∀ g v, σ g v = (ρ g : Matrix (Fin m) (Fin m) κ) *ᵥ v := fun g v => Matrix.toLin'_apply _ _
  have hirr' : ∀ W : Submodule κ (Fin m → κ), (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun g _ v hv => hσ g v ▸ hW g v hv
  unfold MatIrr at hred
  push_neg at hred
  obtain ⟨W₀, h0, hb, ht⟩ := hred
  obtain ⟨U, W, hc, hU0, hW0, hU, hW⟩ := exists_compl σ H hirr' W₀
    (fun g hg v hv => by rw [hσ]; exact h0 g hg v hv) hb ht
  obtain ⟨P, hP0, hPt, hP⟩ := exists_traceless σ H U W hc hU0 hW0 hU hW
  obtain ⟨T, hT0, hTt, hTH, hT⟩ := exists_twist σ H hab P hP0 hPt hP
  choose c hc using hT
  have hunit : ∀ g, IsUnit (σ g) := fun g => (Group.isUnit g).map σ
  have hne : ∀ g, T * σ g ≠ 0 := fun g h => hT0 ((hunit g).mul_left_eq_zero.mp h)
  have hc0 : ∀ g, c g ≠ 0 := fun g h => hT0 ((hunit g).mul_right_eq_zero.mp (by rw [hc, h, zero_smul]))
  have huniq : ∀ g d, σ g * T = d • (T * σ g) → c g = d := fun g d h =>
    smul_left_injective κ (hne g) ((hc g).symm.trans h)
  let φ : Γ →* κˣ :=
    { toFun := fun g => Units.mk0 (c g) (hc0 g)
      map_one' := Units.ext (huniq 1 1 (by simp))
      map_mul' := fun a b => Units.ext (huniq _ _ (by
        rw [map_mul, mul_assoc, hc b, mul_smul_comm, ← mul_assoc, hc a, smul_mul_assoc, smul_smul,
          mul_assoc, mul_comm (c b)]
        rfl)) }
  have hφ : ∀ g, (φ g : κ) = c g := fun _ => rfl
  have hker : LinearMap.ker T = ⊥ := by
    refine (hirr' _ fun g v hv => ?_).resolve_right fun h => hT0 (LinearMap.ker_eq_top.mp h)
    have := congrArg (fun A : Module.End κ (Fin m → κ) => A v) (hc g)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mem_ker.mp hv, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 g)
  have hTu : IsUnit T := (LinearMap.isUnit_iff_ker_eq_bot T).mpr hker
  have hdet : (LinearMap.toMatrix' T).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (hTu.map LinearMap.det).ne_zero
  have hM : ∀ g, LinearMap.toMatrix' T * (c g • (ρ g : Matrix (Fin m) (Fin m) κ)) =
      (ρ g : Matrix (Fin m) (Fin m) κ) * LinearMap.toMatrix' T := fun g => by
    have := congrArg LinearMap.toMatrix' (hc g)
    rw [map_smul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul] at this
    simpa [σ] using this.symm
  refine ⟨φ, fun h1 => ?_, fun h hh => ?_, ?_, ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, fun g _ => hM g⟩⟩
  · haveI : Nontrivial (Fin m → κ) := by
      obtain ⟨u, -, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      exact ⟨u, 0, hu0⟩
    obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
    have htop : Module.End.eigenspace T a = ⊤ := by
      refine (hirr' _ fun g v hv => ?_).resolve_left ha
      have := congrArg (fun A : Module.End κ (Fin m → κ) => A v) (hc g)
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      simp only [Module.End.mul_apply, LinearMap.smul_apply, hv, map_smul, ← hφ, h1] at this
      simpa using this.symm
    have hTa : T = a • 1 := by
      refine LinearMap.ext fun v => ?_
      exact Module.End.mem_eigenspace_iff.mp (by rw [htop]; trivial)
    have hn : (Module.finrank κ (Fin m → κ) : κ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [hTa, map_smul, LinearMap.trace_one, smul_eq_mul, mul_eq_zero] at hTt
    exact hT0 (by rw [hTa, hTt.resolve_right hn, zero_smul])
  · exact Units.ext (huniq h 1 (by rw [one_smul, hTH h hh]))
  · ext g
    have := congrArg Matrix.det (hM g)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, mul_comm _ (LinearMap.toMatrix' T).det] at this
    have h2 := mul_left_cancel₀ hdet this
    have h3 : (ρ g : Matrix (Fin m) (Fin m) κ).det ≠ 0 := (ρ g).det_ne_zero
    simpa [hφ, h3] using h2
