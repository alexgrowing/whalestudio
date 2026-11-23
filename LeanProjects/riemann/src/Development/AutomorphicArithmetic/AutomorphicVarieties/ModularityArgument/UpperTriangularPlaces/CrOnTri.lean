import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Z.Keep.PotentialOfUnlocked

section Alg

variable {Γ E : Type} [Group Γ] [Field E]

private noncomputable def mrep {n : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) E) : Representation E Γ (Fin n → E) where
  toFun g := Matrix.toLin' (M g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

private theorem mrep_apply {n : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) E) (g : Γ) (x : Fin n → E) (i : Fin n) :
    mrep M g x i = ∑ j, M g i j * x j := rfl

private def topBlock {n : ℕ} (M : Γ →* Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (h : ∀ g i j, j < i → M g i j = 0) : Γ →* Matrix (Fin n) (Fin n) E where
  toFun g := (M g).submatrix Fin.castSucc Fin.castSucc
  map_one' := by rw [map_one, Matrix.submatrix_one _ (Fin.castSucc_injective n)]
  map_mul' g k := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, h k (Fin.last n) j.castSucc (Fin.castSucc_lt_last j)]

private def pad (n : ℕ) : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
  LinearMap.pi fun i => Fin.lastCases 0 (fun j => LinearMap.proj j) i

@[simp] private theorem pad_last (n : ℕ) (x : Fin n → E) : pad n x (Fin.last n) = 0 := by simp [pad]

@[simp] private theorem pad_cast (n : ℕ) (x : Fin n → E) (j : Fin n) : pad n x j.castSucc = x j := by
  simp [pad]

private theorem cont_mrep [TopologicalSpace Γ] [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}
    (M : Γ →* Matrix (Fin n) (Fin n) E) (h : ∀ i j, Continuous fun g => M g i j) : ContAction (mrep M) := by
  refine continuous_pi fun i => ?_
  simp only [mrep_apply]
  exact continuous_finset_sum _ fun j _ =>
    ((h i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)

private theorem tri_apply {n : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) E) (h : ∀ g i j, j < i → M g i j = 0)
    (g : Γ) (i : Fin n) (x : Fin n → E) (hx : ∀ j, i < j → x j = 0) :
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

private theorem filt_std {n : ℕ} (ρ : Representation E Γ (Fin n → E)) (S : Set (Γ →* Eˣ))
    (ψ : Fin n → Γ →* Eˣ) (hψ : ∀ i, ψ i ∈ S)
    (hρ : ∀ g (i : Fin n) (x : Fin n → E), (∀ j, i < j → x j = 0) →
      (∀ j, i < j → ρ g x j = 0) ∧ ρ g x i = ψ i g * x i) : FiltBy ρ S := by
  classical
  let U : ℕ → Submodule E (Fin n → E) := fun i =>
    { carrier := {x | ∀ j : Fin n, i ≤ j.val → x j = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      smul_mem' := fun c x hx j hj => by simp [hx j hj] }
  have hU : ∀ i x, x ∈ U i ↔ ∀ j : Fin n, i ≤ j.val → x j = 0 := fun _ _ => Iff.rfl
  refine ⟨n, U, ?_, ?_, fun i hi => ⟨fun x hx j hj => hx j (Nat.le_of_succ_le hj), ψ ⟨i, hi⟩, hψ _,
    Pi.single ⟨i, hi⟩ 1, ?_, fun g => ?_⟩⟩
  · rw [eq_bot_iff]
    intro x hx
    exact funext fun j => hx j (Nat.zero_le _)
  · rw [eq_top_iff]
    intro x _ j hj
    exact absurd j.2 (not_lt.2 hj)
  · refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx j hj => hx j (Nat.le_of_succ_le hj)) ?_)
    · have e : x = (x - x ⟨i, hi⟩ • Pi.single ⟨i, hi⟩ (1 : E)) + x ⟨i, hi⟩ • Pi.single ⟨i, hi⟩ (1 : E) := by simp
      rw [e]
      refine Submodule.add_mem_sup (fun j hj => ?_) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      rcases hj.lt_or_eq with h | h
      · have hne : j ≠ ⟨i, hi⟩ := fun e => by rw [e] at h; exact lt_irrefl _ h
        simp [hx j h, Pi.single_apply, hne]
      · have e2 : j = ⟨i, hi⟩ := Fin.ext h.symm
        subst e2
        simp
    · rw [Submodule.span_singleton_le_iff_mem]
      intro j hj
      have hne : j ≠ ⟨i, hi⟩ := fun e => by rw [e] at hj; exact absurd hj (by simp)
      simp [Pi.single_apply, hne]
  · have h0 : ∀ j : Fin n, (⟨i, hi⟩ : Fin n) < j → (Pi.single ⟨i, hi⟩ (1 : E) : Fin n → E) j = 0 := fun j hj =>
      Pi.single_eq_of_ne hj.ne' _
    obtain ⟨a, b⟩ := hρ g ⟨i, hi⟩ _ h0
    intro j hj
    rcases hj.lt_or_eq with h | h
    · have hij : (⟨i, hi⟩ : Fin n) < j := h
      simp [a j hij, h0 j hij, Units.smul_def]
    · have e2 : j = ⟨i, hi⟩ := Fin.ext h.symm
      subst e2
      simp [b]

private theorem h0dual_none {V : Type} [AddCommGroup V] [Module E V] {ρ : Representation E Γ V}
    {S : Set (Γ →* Eˣ)} (h : FiltBy ρ S) (χ : Γ →* Eˣ)
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

end Alg

private theorem res_cont {l : ℕ} {Γ E V : Type} [Group Γ] [TopologicalSpace Γ] [CommRing E] [AddCommGroup V]
    [Module E V] [TopologicalSpace V] (H : Subgroup Γ) (π : Representation E Γ V) (hπ : ContAction π) :
    ContAction (π.comp H.subtype : Representation E H V) :=
  hπ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

private theorem key (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (φ : Γ →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E]
    [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (H : Subgroup Γ) [H.Normal] (hH : IsOpen (H : Set Γ)) (n : ℕ) :
    ∀ (M : Γ →* Matrix (Fin n) (Fin n) E), (∀ i j, Continuous fun g => M g i j) →
      ∀ (κ : Fin n → Γ →* Eˣ) (w : Fin n → ℤ), (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
      StrictAnti w → (∀ i, ∀ g ∈ H, φ g ∈ Iq l → κ i g = cycA l l E (φ g) ^ w i) →
      (∀ i j, i < j → ∃ g, (κ i g : E) ≠ (κ j g : E) * (cycA l l E (φ g) : E)) → CrOn φ (mrep M) H := by
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  induction n with
  | zero =>
    intro M hM κ w _ _ _ _ _
    exact crUnr _ hφH _ (res_cont (l := l) H _ (cont_mrep M hM)) 0 fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro M hM κ w htri hdiag hw hI hne
    set M0 := topBlock M htri with hM0
    have hM0c : ∀ i j, Continuous fun g => M0 g i j := fun i j => hM _ _
    have htri0 : ∀ g i j, j < i → M0 g i j = 0 := fun g i j h => htri g _ _ (Fin.castSucc_lt_castSucc_iff.2 h)
    have h0 : CrOn φ (mrep M0) H := ih M0 hM0c (fun i => κ i.castSucc) (fun i => w i.castSucc) htri0
      (fun g i => hdiag g _) (fun i j h => hw (Fin.castSucc_lt_castSucc_iff.2 h)) (fun i => hI _)
      (fun i j h => hne _ _ (Fin.castSucc_lt_castSucc_iff.2 h))
    set k := κ (Fin.last n) with hk
    have hkc : Continuous fun g => (k g : E) := by
      simp only [hk, ← hdiag]; exact hM _ _
    have hkc' : Continuous fun g => ((k⁻¹ g : Eˣ) : E) := by
      have : (fun g => ((k⁻¹ g : Eˣ) : E)) = (fun g => (k g : E)) ∘ fun g => g⁻¹ := by
        ext g; simp
      rw [this]; exact hkc.comp continuous_inv
    have hch : ∀ χ : Γ →* Eˣ, Continuous (fun g => (χ g : E)) → ContAction (chRep χ) := fun χ h =>
      (h.comp continuous_fst).mul continuous_snd
    have hkcr : CrOn φ (chRep k) H :=
      crUnr _ hφH _ (res_cont (l := l) H _ (hch _ hkc)) (w (Fin.last n)) fun g hg x => by
        change (k g : E) • x = _
        rw [hk, hI _ g g.2 hg]
        rfl
    have hkcr' : CrOn φ (chRep k⁻¹) H :=
      crUnr _ hφH _ (res_cont (l := l) H _ (hch _ hkc')) (-w (Fin.last n)) fun g hg x => by
        change ((k⁻¹ g : Eˣ) : E) • x = _
        rw [MonoidHom.inv_apply, hk, hI _ g g.2 hg, zpow_neg]
        rfl
    have htw : ContAction (twist k⁻¹ (mrep M0)) :=
      (hkc'.comp continuous_fst).smul (cont_mrep M0 hM0c)
    have htwH := res_cont (l := l) H _ htw
    have htwcr : IsCr (φ.comp H.subtype) ((twist k⁻¹ (mrep M0)).comp H.subtype : Representation E H (Fin n → E)) := by
      refine (admissible_of_bilinear_openSubgroup_galois _ hφH ((chRep k⁻¹).comp H.subtype : Representation E H E)
        ((mrep M0).comp H.subtype : Representation E H (Fin n → E)) _ (res_cont (l := l) H _ (hch _ hkc'))
        (res_cont (l := l) H _ (cont_mrep M0 hM0c)) htwH
        ((LinearMap.lsmul E (Fin n → E)).restrictScalars₁₂ ℚ_[l] ℚ_[l]) ?_ ?_).1 hkcr' h0
      · intro g x y
        simp [chRep, twist, smul_smul, mul_comm]
      · rw [eq_top_iff]
        intro x _
        exact Submodule.subset_span ⟨(1, x), by simp⟩
    have hdr : IsDr φ (twist k⁻¹ (mrep M0)) :=
      ((isCrys_isDR_restrict_openSubgroup φ hφ _ htw).2 H hH).2.2 ((isCrys_isDR_restrict_openSubgroup _ hφH _ htwH).1 htwcr)
    let ψ : Fin n → Γ →* Eˣ := fun i => k⁻¹ * κ i.castSucc
    have hfil : ∀ S : Set (Γ →* Eˣ), (∀ i, ψ i ∈ S) → FiltBy (twist k⁻¹ (mrep M0)) S := by
      intro S hS
      refine filt_std _ S ψ hS ?_
      intro g i x hx
      obtain ⟨a, b⟩ := tri_apply M0 htri0 g i x hx
      have e : ∀ j, twist k⁻¹ (mrep M0) g x j = ((k⁻¹ g : Eˣ) : E) * mrep M0 g x j := fun j => rfl
      refine ⟨fun j hj => by rw [e, a j hj, mul_zero], ?_⟩
      have : M0 g i i = κ i.castSucc g := hdiag g _
      rw [e, b, this]
      simp [ψ, mul_assoc]
    have hpos : Positive φ (twist k⁻¹ (mrep M0)) := by
      refine ⟨hdr, hfil _ fun i => ⟨w i.castSucc - w (Fin.last n), ?_, H, hH, ?_⟩⟩
      · have := hw (Fin.castSucc_lt_last i)
        omega
      · intro g hgH hg
        simp only [ψ, MonoidHom.mul_apply, MonoidHom.inv_apply, hk, hI _ g hgH hg]
        rw [zpow_sub]
        exact mul_comm _ _
    have hdual : H0dual ((cycA l l E).comp φ) (twist k⁻¹ (mrep M0)) = ⊥ := by
      refine h0dual_none (hfil (Set.range ψ) fun i => ⟨i, rfl⟩) _ ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨g, hg⟩ := hne _ _ (Fin.castSucc_lt_last i)
      refine ⟨g, fun h => hg ?_⟩
      have h' : (ψ i g : E) = (cycA l l E (φ g) : E) := h
      rw [← h']
      simp [ψ, hk]
    have hF := prF hP φ hφ (twist k⁻¹ (mrep M0)) htw hpos hdual
    let c : Γ → Fin n → E := fun g i => ((k⁻¹ g : Eˣ) : E) * M g i.castSucc (Fin.last n)
    have hc : c ∈ Z1 (twist k⁻¹ (mrep M0)) := by
      refine ⟨continuous_pi fun i => hkc'.mul (hM _ _), fun g h => funext fun i => ?_⟩
      change ((k⁻¹ (g * h) : Eˣ) : E) * M (g * h) i.castSucc (Fin.last n) =
        ((k⁻¹ g : Eˣ) : E) * M g i.castSucc (Fin.last n) + ((k⁻¹ g : Eˣ) : E) *
          ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Eˣ) : E) * M h j.castSucc (Fin.last n))
      have e : ((k⁻¹ h : Eˣ) : E) * (k h : E) = 1 := by simp
      have e2 : ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Eˣ) : E) * M h j.castSucc (Fin.last n)) =
          ((k⁻¹ h : Eˣ) : E) * ∑ j : Fin n, M g i.castSucc j.castSucc * M h j.castSucc (Fin.last n) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [map_mul, map_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, hdiag, ← hk, Units.val_mul, e2]
      linear_combination ((k⁻¹ g : Eˣ) : E) * M g i.castSucc (Fin.last n) * e
    rw [← hF] at hc
    refine (crExt φ hφ (mrep M0) (mrep M) (cont_mrep M0 hM0c) (cont_mrep M hM) k (pad n)
      (LinearMap.proj (Fin.last n)) (Pi.single (Fin.last n) 1) c ?_ ?_ (by simp) ?_ ?_ H hH h0 hkcr).2 hc
    · intro x y h
      funext j
      simpa using congrFun h j.castSucc
    · intro y
      constructor
      · intro h
        refine ⟨fun j => y j.castSucc, funext fun j => ?_⟩
        induction j using Fin.lastCases with
        | last => rw [pad_last]; exact h.symm
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

end UpperTheory.V.Z.Keep.PotentialOfUnlocked

open UpperTheory.V.Z.Keep.PotentialOfUnlocked in

theorem UpperTheory.V.Z.Keep.crOnTri (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (φ : Γ →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E]
    [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (H : Subgroup Γ) [H.Normal] (hH : IsOpen (H : Set Γ)) {n : ℕ}
    (t : Γ →* GL (Fin n) E) (ht : ∀ i j, Continuous fun g => (t g : Matrix (Fin n) (Fin n) E) i j)
    (κ : Fin n → Γ →* Eˣ) (w : Fin n → ℤ) (htri : UpperTri t κ) (hw : StrictAnti w)
    (hI : ∀ i, ∀ g ∈ H, φ g ∈ Iq l → κ i g = cycA l l E (φ g) ^ w i)
    (hne : ∀ i j, i < j → ∃ g, (κ i g : E) ≠ (κ j g : E) * (cycA l l E (φ g) : E)) : CrOn φ (colRep t) H :=
  key hP φ hφ H hH n ((Units.coeHom _).comp t) ht κ w (fun g => (htri g).1) (fun g => (htri g).2) hw hI hne

namespace UpperTheory.V.Z.Keep.PotentialOfUnlocked

private theorem cr_descend (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (φ : Γ →* GQ l) (hφ : IsOpenEmbedding φ)
    (H : Subgroup Γ) [H.Normal] (hH : IsOpen (H : Set Γ)) {n : ℕ} (r₀ : Γ →* GL (Fin n) (Om l))
    (hr : Continuous fun g => (r₀ g : Matrix (Fin n) (Fin n) (Om l))) (P : GL (Fin n) (Om l))
    (κ : Fin n → Γ →* (Om l)ˣ) (w : Fin n → ℤ)
    (hfl : ∀ s, (∀ i j, j < i → (P * r₀ s * P⁻¹ : GL (Fin n) (Om l)) i j = 0) ∧
      ∀ i, (P * r₀ s * P⁻¹ : GL (Fin n) (Om l)) i i = (κ i s : Om l))
    (hw : StrictAnti w) (hI : ∀ i, ∀ g ∈ H, φ g ∈ Iq l → κ i g = cycA l l (Om l) (φ g) ^ w i)
    (hne : ∀ i j, κ i ≠ κ j * (cycA l l (Om l)).comp φ) :
    ∃ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1),
      (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) =
        (r₀ h : Matrix (Fin n) (Fin n) (Om l)) a b) ∧ IsCr (φ.comp H.subtype) (colRep r') := by
  classical
  let t : Set (Om l) := Set.range (fun p : Fin n × Fin n => (P : Matrix (Fin n) (Fin n) (Om l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((P⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) p.1 p.2)
  haveI : Finite t := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  let L₀ : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] t,
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral⟩
  obtain ⟨L, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ n r₀ hr L₀
  obtain ⟨s, hs⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem r₀ L.1 hent
  have := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  have hPm : ∀ a b, (P : Matrix (Fin n) (Fin n) (Om l)) a b ∈ L.1 := fun a b =>
    hL (IntermediateField.subset_adjoin _ _ (Or.inl ⟨(a, b), rfl⟩))
  have hPi : ∀ a b, ((P⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) a b ∈ L.1 := fun a b =>
    hL (IntermediateField.subset_adjoin _ _ (Or.inr ⟨(a, b), rfl⟩))
  let Pm : Matrix (Fin n) (Fin n) ↥L.1 := Matrix.of fun a b => ⟨_, hPm a b⟩
  let Pv : Matrix (Fin n) (Fin n) ↥L.1 := Matrix.of fun a b => ⟨_, hPi a b⟩
  have hPmm : Pm.map L.1.val = (P : Matrix (Fin n) (Fin n) (Om l)) := rfl
  have hPvm : Pv.map L.1.val = ((P⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) := rfl
  have hinj : Function.Injective fun X : Matrix (Fin n) (Fin n) ↥L.1 => X.map L.1.val :=
    Matrix.map_injective Subtype.val_injective
  have hone : (1 : Matrix (Fin n) (Fin n) ↥L.1).map L.1.val = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : Pm * Pv = 1 := hinj (by
    simp only []
    rw [Matrix.map_mul, hPmm, hPvm, hone, Units.mul_inv])
  have h2 : Pv * Pm = 1 := hinj (by
    simp only []
    rw [Matrix.map_mul, hPmm, hPvm, hone, Units.inv_mul])
  let Pe : GL (Fin n) ↥L.1 := ⟨Pm, Pv, h1, h2⟩
  let u : Γ →* GL (Fin n) ↥L.1 := conjGL Pe s
  have hsm : ∀ g, (s g : Matrix (Fin n) (Fin n) ↥L.1).map L.1.val = (r₀ g : Matrix (Fin n) (Fin n) (Om l)) :=
    fun g => Matrix.ext fun a b => hs g a b
  have hum : ∀ g, (u g : Matrix (Fin n) (Fin n) ↥L.1).map L.1.val =
      (P * r₀ g * P⁻¹ : GL (Fin n) (Om l)) := fun g => by
    change (Pm * (s g : Matrix (Fin n) (Fin n) ↥L.1) * Pv).map L.1.val = _
    rw [Matrix.map_mul, Matrix.map_mul, hsm, hPmm, hPvm]
    rfl
  have hu : ∀ g a b, (((u g : Matrix (Fin n) (Fin n) ↥L.1) a b : ↥L.1) : Om l) =
      (P * r₀ g * P⁻¹ : GL (Fin n) (Om l)) a b := fun g a b => congrFun (congrFun (hum g) a) b
  have hκE : ∀ i g, (κ i g : Om l) ∈ L.1 := fun i g => by
    rw [← (hfl g).2 i, ← hu]
    exact SetLike.coe_mem _
  let κ' : Fin n → Γ →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ i g, hκE i g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hPc : Continuous fun g => (P * r₀ g * P⁻¹ : GL (Fin n) (Om l)).val :=
    (continuous_const.matrix_mul hr).matrix_mul continuous_const
  have huc : ∀ i j, Continuous fun g => (u g : Matrix (Fin n) (Fin n) ↥L.1) i j := fun i j =>
    continuous_induced_rng.2 ((hPc.matrix_elem i j).congr fun g => (hu g i j).symm)
  have hcr : CrOn φ (colRep u) H := UpperTheory.V.Z.Keep.crOnTri hP φ hφ H hH u huc κ' w
    (fun g => ⟨fun a b hab => Subtype.ext ((hu g a b).trans ((hfl g).1 a b hab)),
      fun a => Subtype.ext ((hu g a a).trans ((hfl g).2 a))⟩) hw
    (fun i g hg hg' => Units.ext (Subtype.ext (by
      change (κ i g : Om l) = L.1.val _
      rw [hI i g hg hg', Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀]
      rfl)))
    (fun i j _ => by
      by_contra hcon
      push_neg at hcon
      exact hne i j (MonoidHom.ext fun g => Units.ext (congrArg Subtype.val (hcon g))))
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have hsc : Continuous fun g => (s g : Matrix (Fin n) (Fin n) ↥L.1) := continuous_matrix fun a b =>
    continuous_induced_rng.2 ((hr.matrix_elem a b).congr fun g => (hs g a b).symm)
  have cu : ContAction ((colRep u).comp H.subtype : Representation ↥L.1 H (Fin n → ↥L.1)) :=
    res_cont (l := l) H _ (((continuous_matrix huc).comp continuous_fst).matrix_mulVec continuous_snd)
  have cs : ContAction (colRep (s.comp H.subtype)) :=
    ((hsc.comp continuous_subtype_val).comp continuous_fst).matrix_mulVec continuous_snd
  let f : (Fin n → ↥L.1) →ₗ[ℚ_[l]] (Fin n → ↥L.1) := (Matrix.toLin' Pv).restrictScalars ℚ_[l]
  refine ⟨L, s.comp H.subtype, fun h a b => hs h a b, ?_⟩
  refine ((isCrys_isDR_sub_quot _ hφH _ _ cu cs f (fun g x => ?_)).2 fun y => ⟨Matrix.toLin' Pm y, ?_⟩).1 hcr
  · change Matrix.mulVec Pv (Matrix.mulVec (Pm * (s g : Matrix (Fin n) (Fin n) ↥L.1) * Pv) x) =
      Matrix.mulVec (s g : Matrix (Fin n) (Fin n) ↥L.1) (Matrix.mulVec Pv x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  · change Matrix.mulVec Pv (Matrix.mulVec Pm y) = y
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

end UpperTheory.V.Z.Keep.PotentialOfUnlocked

open UpperTheory.V.Z.Keep.PotentialOfUnlocked in

theorem UpperTheory.V.Z.Keep.crDescend (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (φ : Γ →* GQ l) (hφ : IsOpenEmbedding φ)
    (H : Subgroup Γ) [H.Normal] (hH : IsOpen (H : Set Γ)) {n : ℕ} (r₀ : Γ →* GL (Fin n) (Om l))
    (hr : Continuous fun g => (r₀ g : Matrix (Fin n) (Fin n) (Om l))) (P : GL (Fin n) (Om l))
    (κ : Fin n → Γ →* (Om l)ˣ) (w : Fin n → ℤ)
    (hfl : ∀ s, (∀ i j, j < i → (P * r₀ s * P⁻¹ : GL (Fin n) (Om l)) i j = 0) ∧
      ∀ i, (P * r₀ s * P⁻¹ : GL (Fin n) (Om l)) i i = (κ i s : Om l))
    (hw : StrictAnti w) (hI : ∀ i, ∀ g ∈ H, φ g ∈ Iq l → κ i g = cycA l l (Om l) (φ g) ^ w i)
    (hne : ∀ i j, κ i ≠ κ j * (cycA l l (Om l)).comp φ) :
    ∃ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1),
      (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) =
        (r₀ h : Matrix (Fin n) (Fin n) (Om l)) a b) ∧ IsCr (φ.comp H.subtype) (colRep r') :=
  cr_descend hP φ hφ H hH r₀ hr P κ w hfl hw hI hne
