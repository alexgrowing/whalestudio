import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DualInvariantFiltration

section Filt

variable {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]

private def Ch (ρ : Representation E G V) (S : Set (G →* Eˣ)) (W : Submodule E V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span E {x} ∧ ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ F i

private theorem ch_step {ρ : Representation E G V} {S : Set (G →* Eˣ)} {U : Submodule E V} (hU : Ch ρ S U)
    {κ : G →* Eˣ} (hκ : κ ∈ S) (x : V) (hx : ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ U) :
    Ch ρ S (U ⊔ Submodule.span E {x}) := by
  obtain ⟨n, F, h0, hn, hF⟩ := hU
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span E {x}, by simp [h0], by simp, ?_⟩
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
  · have h1 : i ≤ n := h.le
    have h2 : i + 1 ≤ n := h
    simp only [h1, h2, if_true]
    exact hF i h
  · simp only [le_refl, if_true, Nat.add_one_le_iff, lt_irrefl, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem ch_step2 [FiniteDimensional E V] {ρ : Representation E G V} {S : Set (G →* Eˣ)}
    {U W : Submodule E V} (hU : Ch ρ S U) (hUW : U ≤ W)
    {κ : G →* Eˣ} (hκ : κ ∈ S) (hx : ∀ x ∈ W, ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ U) :
    Ch ρ S W := by
  classical
  obtain ⟨t, ht⟩ : W.FG := IsNoetherian.noetherian W
  have key : ∀ s : Finset V, (∀ x ∈ s, x ∈ W) → Ch ρ S (U ⊔ Submodule.span E (s : Set V)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hU
    | insert a s ha ih =>
      intro h
      have h1 := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
      have h2 := ch_step h1 hκ a fun g =>
        Submodule.mem_sup_left (hx a (h a (Finset.mem_insert_self _ _)) g)
      rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span E {a}), ← sup_assoc]
      exact h2
  have := key t fun x hx => ht ▸ Submodule.subset_span hx
  rwa [ht, sup_eq_right.2 hUW] at this

private theorem h0dual_bot {ρ : Representation E G V} {S : Set (G →* Eˣ)} (h : FiltBy ρ S) (χ : G →* Eˣ)
    (hS : ∀ κ ∈ S, ∃ g, (κ g : E) ≠ χ g) : H0dual χ ρ = ⊥ := by
  obtain ⟨n, F, h0, hn, hF⟩ := h
  rw [eq_bot_iff]
  intro f hf
  have key : ∀ i ≤ n, F i ≤ LinearMap.ker f := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ i ih =>
      intro hi
      obtain ⟨-, κ, hκ, x, hx, hg⟩ := hF i hi
      have h1 := ih (Nat.le_of_succ_le hi)
      rw [hx, sup_le_iff, Submodule.span_singleton_le_iff_mem]
      refine ⟨h1, ?_⟩
      obtain ⟨g, hne⟩ := hS κ hκ
      have h2 := h1 (hg g)
      rw [LinearMap.mem_ker, map_sub, map_smul, hf g x, smul_eq_mul, ← sub_mul] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (sub_eq_zero.1 h3).symm hne
      · exact h3
  have := key n le_rfl
  rw [hn, top_le_iff, LinearMap.ker_eq_top] at this
  simp [this]

private theorem filt_tri {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A] (π : A →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) {n : ℕ} (ρ : Representation E G (Fin n → A)) (S : Set (G →* Eˣ))
    (ψ : Fin n → G → A) (hψ : ∀ i, ∃ κ ∈ S, ∀ g, (κ g : E) = π (ψ i g))
    (hρ : ∀ g (i : Fin n) (x : Fin n → A), (∀ j, i < j → x j = 0) →
      (∀ j, i < j → ρ g x j = 0) ∧ ρ g x i = ψ i g * x i) : FiltBy ρ S := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower E inferInstance
  set m : Ideal A := RingHom.ker (π : A →+* E) with hm
  obtain ⟨N, hN⟩ : IsNilpotent m := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian m)]
    exact fun a ha => hπ a ha
  let U : ℕ → Submodule E (Fin n → A) := fun i =>
    { carrier := {x | ∀ j : Fin n, i ≤ j.val → x j = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      smul_mem' := fun c x hx j hj => by simp [hx j hj] }
  have key : ∀ i ≤ n, Ch ρ S (U i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : U 0 = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact funext fun j => hx j (Nat.zero_le _)
      rw [this]
      exact ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      have h1 := ih (Nat.le_of_succ_le hi)
      let i' : Fin n := ⟨i, hi⟩
      let W : ℕ → Submodule E (Fin n → A) := fun k =>
        U (i + 1) ⊓ ((m ^ k).restrictScalars E).comap (LinearMap.proj i')
      have hWN : W N = U i := by
        ext x
        simp only [W, hN, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem,
          LinearMap.proj_apply, Submodule.zero_eq_bot, Submodule.mem_bot]
        constructor
        · rintro ⟨a, b⟩ j hj
          rcases hj.lt_or_eq with h | h
          · exact a j h
          · have : j = i' := Fin.ext h.symm
            rw [this]; exact b
        · intro a
          exact ⟨fun j hj => a j (Nat.le_of_succ_le hj), a i' le_rfl⟩
      have hW0 : W 0 = U (i + 1) := by simp [W]
      obtain ⟨κ, hκ, hκψ⟩ := hψ i'
      have step : ∀ k, Ch ρ S (W (k + 1)) → Ch ρ S (W k) := by
        intro k hk
        refine ch_step2 hk (inf_le_inf_left _ (Submodule.comap_mono ?_)) hκ ?_
        · exact fun a ha => Ideal.pow_le_pow_right (Nat.le_succ k) ha
        · rintro x ⟨hx1, hx2⟩ g
          obtain ⟨a, b⟩ := hρ g i' x fun j hj => hx1 j hj
          refine ⟨fun j hj => ?_, ?_⟩
          · have := hx1 j hj
            simp [a j hj, this]
          · change ρ g x i' - (κ g : E) • x i' ∈ m ^ (k + 1)
            rw [b, Algebra.smul_def, ← sub_mul, pow_succ']
            refine Ideal.mul_mem_mul ?_ hx2
            simp [hm, RingHom.mem_ker, hκψ]
      rw [← hW0]
      exact Nat.decreasingInduction (motive := fun k _ => Ch ρ S (W k)) (fun k _ h => step k h)
        (hWN ▸ h1) (Nat.zero_le N)
  have := key n le_rfl
  have hn : U n = ⊤ := by
    rw [eq_top_iff]
    intro x _ j hj
    exact absurd j.2 (not_lt.2 hj)
  rw [hn] at this
  exact this

end Filt

section Mat

variable {G A : Type} [Group G] [CommRing A]

private noncomputable def mrep {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) : Representation A G (Fin n → A) where
  toFun g := Matrix.toLin' (M g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

private theorem mrep_apply {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) (g : G) (x : Fin n → A) (i : Fin n) :
    mrep M g x i = ∑ j, M g i j * x j := rfl

private def topBlock {n : ℕ} (M : G →* Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (h : ∀ g i j, j < i → M g i j = 0) : G →* Matrix (Fin n) (Fin n) A where
  toFun g := (M g).submatrix Fin.castSucc Fin.castSucc
  map_one' := by rw [map_one, Matrix.submatrix_one _ (Fin.castSucc_injective n)]
  map_mul' g k := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, h k (Fin.last n) j.castSucc (Fin.castSucc_lt_last j)]

private def ext0 (n : ℕ) : (Fin n → A) →ₗ[A] (Fin (n + 1) → A) :=
  LinearMap.pi fun i => Fin.lastCases 0 (fun j => LinearMap.proj j) i

@[simp] private theorem snocZeroLastCoordinate_last (n : ℕ) (x : Fin n → A) : ext0 n x (Fin.last n) = 0 := by simp [ext0]

@[simp] private theorem extend_zero_castSucc (n : ℕ) (x : Fin n → A) (j : Fin n) : ext0 n x j.castSucc = x j := by
  simp [ext0]

private theorem cont_mrep [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (M : G →* Matrix (Fin n) (Fin n) A) (h : ∀ i j, Continuous fun g => M g i j) : ContAction (mrep M) := by
  refine continuous_pi fun i => ?_
  simp only [mrep_apply]
  exact continuous_finset_sum _ fun j _ =>
    ((h i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)

private theorem tri_apply {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) (h : ∀ g i j, j < i → M g i j = 0)
    (g : G) (i : Fin n) (x : Fin n → A) (hx : ∀ j, i < j → x j = 0) :
    (∀ j, i < j → mrep M g x j = 0) ∧ mrep M g x i = M g i i * x i := by
  constructor
  · intro j hj
    rw [mrep_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · rw [hx k hk, mul_zero]
    · rw [h g j k (hk.trans_lt hj), zero_mul]
  · rw [mrep_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [h g i k hk, zero_mul]
    · rw [hx k hk, mul_zero]

end Mat

private theorem isCr_of_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]
  have h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    ext x
    simp only [Dcr, Submodule.mem_iInf]
    exact ⟨fun h g => h ⟨g, trivial⟩, fun h g => h g.1⟩
  unfold CrOn IsCr
  rw [h1, h2]

private theorem key (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {A : Type} [CommRing A]
    [Algebra E A] [Algebra ℚ_[l] A] [IsScalarTower ℚ_[l] E A] [Module.Finite E A] [Algebra ℤ_[l] A]
    [IsScalarTower ℤ_[l] ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A]
    [IsTopologicalRing A] (π : A →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (n : ℕ) :
    ∀ (M : G →* Matrix (Fin n) (Fin n) A), (∀ i j, Continuous fun g => M g i j) →
      ∀ (κ : Fin n → G →* Aˣ) (w : Fin n → ℤ), (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
      StrictAnti w → (∀ i g, φ g ∈ Iq l → κ i g = cycA l l A (φ g) ^ w i) →
      (∀ i j, i < j → ∃ g, π (κ i g : A) ≠ π (κ j g : A) * (cycA l l E (φ g) : E)) → IsCr φ (mrep M) := by
  induction n with
  | zero =>
    intro M hM κ w _ _ _ _ _
    exact crUnr φ hφ (mrep M) (cont_mrep M hM) 0 fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro M hM κ w htri hdiag hw hI hne
    haveI : ContinuousConstSMul E (Fin n → A) := ⟨fun c => IsModuleTopology.continuous_of_linearMap
      ((Algebra.lsmul ℚ_[l] ℚ_[l] (Fin n → A) : E →ₐ[ℚ_[l]] Module.End ℚ_[l] (Fin n → A)) c)⟩
    set M0 := topBlock M htri with hM0
    have hM0c : ∀ i j, Continuous fun g => M0 g i j := fun i j => hM _ _
    have htri0 : ∀ g i j, j < i → M0 g i j = 0 := fun g i j h => htri g _ _ (Fin.castSucc_lt_castSucc_iff.2 h)
    have h0 : IsCr φ (mrep M0) := ih M0 hM0c (fun i => κ i.castSucc) (fun i => w i.castSucc) htri0
      (fun g i => hdiag g _) (fun i j h => hw (Fin.castSucc_lt_castSucc_iff.2 h)) (fun i => hI _)
      (fun i j h => hne _ _ (Fin.castSucc_lt_castSucc_iff.2 h))
    set k := κ (Fin.last n) with hk
    have hkc : Continuous fun g => (k g : A) := by
      simp only [hk, ← hdiag]; exact hM _ _
    have hkc' : Continuous fun g => ((k⁻¹ g : Aˣ) : A) := by
      have : (fun g => ((k⁻¹ g : Aˣ) : A)) = (fun g => (k g : A)) ∘ fun g => g⁻¹ := by
        ext g; simp
      rw [this]; exact hkc.comp continuous_inv
    have hch : ∀ χ : G →* Aˣ, Continuous (fun g => (χ g : A)) → ContAction (chRep χ) := fun χ h =>
      (h.comp continuous_fst).mul continuous_snd
    have hkcr : IsCr φ (chRep k) := crUnr φ hφ _ (hch _ hkc) (w (Fin.last n)) fun g hg x => by
      rw [← hI _ g hg]; rfl
    have hkcr' : IsCr φ (chRep k⁻¹) := crUnr φ hφ _ (hch _ hkc') (-w (Fin.last n)) fun g hg x => by
      rw [zpow_neg, ← hI _ g hg]; rfl
    have htw : ContAction (twist k⁻¹ (mrep M0)) :=
      (hkc'.comp continuous_fst).smul (cont_mrep M0 hM0c)
    have htwcr : IsCr φ (twist k⁻¹ (mrep M0)) := by
      refine (admissible_of_bilinear_openSubgroup_galois φ hφ (chRep k⁻¹) (mrep M0) _ (hch _ hkc') (cont_mrep M0 hM0c) htw
        ((LinearMap.lsmul A (Fin n → A)).restrictScalars₁₂ ℚ_[l] ℚ_[l]) ?_ ?_).1 hkcr' h0
      · intro g x y
        simp [chRep, twist, smul_smul, mul_comm]
      · rw [eq_top_iff]
        intro x _
        exact Submodule.subset_span ⟨(1, x), by simp⟩
    have hπc : ∀ σ, π (cycA l l A σ : A) = (cycA l l E σ : E) := fun σ => by
      simp only [cycA, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A, IsScalarTower.algebraMap_apply ℚ_[l] E A,
        AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
      rfl
    let ψ : Fin n → G →* Eˣ := fun i => (Units.map (π : A →* E)).comp (k⁻¹ * κ i.castSucc)
    have hfil : ∀ S : Set (G →* Eˣ), (∀ i, ψ i ∈ S) → FiltBy (resCoef E (twist k⁻¹ (mrep M0))) S := by
      intro S hS
      refine filt_tri π hπ _ S (fun i g => ((k⁻¹ * κ i.castSucc) g : Aˣ)) (fun i => ⟨ψ i, hS i, fun g => rfl⟩) ?_
      intro g i x hx
      obtain ⟨a, b⟩ := tri_apply M0 htri0 g i x hx
      have e : ∀ j, resCoef E (twist k⁻¹ (mrep M0)) g x j = ((k⁻¹ g : Aˣ) : A) * mrep M0 g x j := fun j => rfl
      refine ⟨fun j hj => by rw [e, a j hj, mul_zero], ?_⟩
      have : M0 g i i = κ i.castSucc g := hdiag g _
      rw [e, b, this]
      simp [mul_assoc]
    have hpos : Positive φ (resCoef E (twist k⁻¹ (mrep M0))) := by
      refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ htw).1 htwcr, hfil _ fun i => ⟨w i.castSucc - w (Fin.last n), ?_, ⊤, isOpen_univ, ?_⟩⟩
      · have := hw (Fin.castSucc_lt_last i)
        omega
      · intro g _ hg
        have e : Units.map (π : A →* E) (cycA l l A (φ g)) = cycA l l E (φ g) := Units.ext (hπc _)
        simp only [ψ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hk, hI _ g hg]
        rw [map_mul, map_inv, map_zpow (Units.map (π : A →* E)), map_zpow (Units.map (π : A →* E)), e, zpow_sub]
        exact mul_comm _ _
    have hdual : H0dual ((cycA l l E).comp φ) (resCoef E (twist k⁻¹ (mrep M0))) = ⊥ := by
      refine h0dual_bot (hfil (Set.range ψ) fun i => ⟨i, rfl⟩) _ ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨g, hg⟩ := hne _ _ (Fin.castSucc_lt_last i)
      refine ⟨g, fun h => hg ?_⟩
      have h' : (ψ i g : E) = (cycA l l E (φ g) : E) := h
      rw [← h']
      change _ = π (k g : A) * π (((k⁻¹ * κ i.castSucc) g : Aˣ) : A)
      rw [← map_mul]
      simp
    have hF := prF hP φ hφ (resCoef E (twist k⁻¹ (mrep M0))) htw hpos hdual
    let c : G → Fin n → A := fun g i => ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n)
    have hc : c ∈ Z1 (resCoef E (twist k⁻¹ (mrep M0))) := by
      refine ⟨continuous_pi fun i => hkc'.mul (hM _ _), fun g h => funext fun i => ?_⟩
      change ((k⁻¹ (g * h) : Aˣ) : A) * M (g * h) i.castSucc (Fin.last n) =
        ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) + ((k⁻¹ g : Aˣ) : A) *
          ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n))
      have e : ((k⁻¹ h : Aˣ) : A) * (k h : A) = 1 := by simp
      have e2 : ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n)) =
          ((k⁻¹ h : Aˣ) : A) * ∑ j : Fin n, M g i.castSucc j.castSucc * M h j.castSucc (Fin.last n) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [map_mul, map_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, hdiag, ← hk, Units.val_mul, e2]
      linear_combination ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) * e
    rw [← hF] at hc
    have hc' : c ∈ UpperTheory.V.Loc.finiteCocycles φ (twist k⁻¹ (mrep M0)) := hc
    rw [← isCr_of_top] at h0 hkcr ⊢
    refine (crExt φ hφ (mrep M0) (mrep M) (cont_mrep M0 hM0c) (cont_mrep M hM) k (ext0 n)
      (LinearMap.proj (Fin.last n)) (Pi.single (Fin.last n) 1) c ?_ ?_ (by simp) ?_ ?_ ⊤ isOpen_univ h0 hkcr).2 hc'
    · intro x y h
      funext j
      simpa using congrFun h j.castSucc
    · intro y
      constructor
      · intro h
        refine ⟨fun j => y j.castSucc, funext fun j => ?_⟩
        induction j using Fin.lastCases with
        | last => rw [snocZeroLastCoordinate_last]; exact h.symm
        | cast j => simp
      · rintro ⟨x, rfl⟩
        simp
    · intro g x
      funext j
      induction j using Fin.lastCases with
      | last =>
        simp [mrep_apply, Fin.sum_univ_castSucc, fun j : Fin n => htri g _ _ (Fin.castSucc_lt_last j)]
      | cast j => simp [mrep_apply, Fin.sum_univ_castSucc, hM0, topBlock]
    · intro g
      funext j
      induction j using Fin.lastCases with
      | last => simp [mrep_apply, Pi.single_apply, hdiag, hk]
      | cast j => simp [mrep_apply, Pi.single_apply, c, (Fin.castSucc_lt_last j).ne]

end UpperTheory.V.Loc.DualInvariantFiltration

open UpperTheory.V.Loc.DualInvariantFiltration in
theorem UpperTheory.V.Loc.prC :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {A : Type} [CommRing A] [Algebra E A] [Algebra ℚ_[l] A] [IsScalarTower ℚ_[l] E A] [Module.Finite E A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] (π : A →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ {n : ℕ} (r : G →* GL (Fin n) A), (∀ i j, QCont l fun g => (r g : Matrix (Fin n) (Fin n) A) i j) → ∀ (κ : Fin n → G →* Aˣ) (w : Fin n → ℤ), UpperTri r κ → StrictAnti w → (∀ i g, φ g ∈ Iq l → κ i g = cycA l l A (φ g) ^ w i) → (∀ i j, i < j → ∃ g, π (κ i g : A) ≠ π (κ j g : A) * (cycA l l E (φ g) : E)) → IsCr φ (colRep r) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ A _ _ _ _ _ _ _ π hπ n r hr κ w htri hw hI hne
  letI : TopologicalSpace A := moduleTopology ℚ_[l] A
  haveI : IsModuleTopology ℚ_[l] A := ⟨rfl⟩
  haveI : Module.Finite ℚ_[l] A := Module.Finite.trans E A
  haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℚ_[l] A
  exact key hP φ hφ π hπ n ((Units.coeHom _).comp r) hr κ w (fun g => (htri g).1) (fun g => (htri g).2) hw hI hne
