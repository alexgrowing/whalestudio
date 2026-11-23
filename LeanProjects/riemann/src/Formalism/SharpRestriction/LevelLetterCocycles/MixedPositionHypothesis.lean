import Formalism.SharpRestriction.LevelLetterCocycles.LamPS

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def quotA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    ∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X

def normA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    (∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X) →
    ∃ (η₁ h' : ℕ) (b' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ), η₁ ≤ η ∧ h' ≤ h + S + 1 ∧
      HypN P K LL T₁ T₂ F S η₁ m h' up b'

end Local

def quotR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → quotA (D.loc l) K LL

def normR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → normA (D.loc l) K LL

def dvdR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → eK K ∣ l - 1

def p9R (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
    ∃ (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
      Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E

def splitR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ∀ κ ∈ latticeFiniteCocycles ((D.loc l).PD K) T.L,
      (l ^ (rhoA l (eK K) h' + sigA l (sK l K) h') : ℕ) • κ ∈
        (⨆ c, JZ ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c) ⊔ latticeCoboundaries T.L

def univR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ)
      (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b →
      ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ eK K * (eK K + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles ((D.loc l).PD K) T₂.L ∧
        ∀ x ∈ JZ ((HW l).W K 1 LL hG) T₂ π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c,
          (l ^ (sigA l (sK l K) h' + y2K l K h' S η) : ℕ) • x ∈
            F.ImF ((D.loc l).PD K) ⊔ Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V))

theorem YA_split (l e s h' S η : ℕ) :
    YA l e s h' S η = (rhoA l e h' + sigA l s h') + (sigA l s h' +
      (2 * sigA l s h' + kapA l e h' S + rhoA l e h' + max (2 * sigA l s h') (ycA l h' η))) := by
  unfold YA
  ring

theorem YA_mono (l e s h' S : ℕ) {η₁ η : ℕ} (h : η₁ ≤ η) : YA l e s h' S η₁ ≤ YA l e s h' S η := by
  rw [YA_split, YA_split]
  unfold ycA
  gcongr

theorem annihilation_of_scaled_spans {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq M]
    (J : ι → Submodule O M) (B Im : Submodule O M) (s : ι → Finset M) (hB : B ≤ Im) (a b : ℕ) (p : M)
    (hp : a • p ∈ (⨆ c, J c) ⊔ B) (hU : ∀ c, ∀ x ∈ J c, b • x ∈ Im ⊔ Submodule.span O (s c : Set M)) :
    b • a • p ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
  classical
  have key : (⨆ c, J c) ≤
      (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im).comap
        (b • LinearMap.id : M →ₗ[O] M) := by
    refine iSup_le fun c y hy => ?_
    have h1 := hU c y hy
    have hle : Im ⊔ Submodule.span O (s c : Set M) ≤
        Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
      refine sup_le le_sup_right (le_sup_of_le_left (Submodule.span_mono ?_))
      intro z hz
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)
    show b • y ∈ (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im)
    exact hle h1
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hp
  rw [← hxy, smul_add]
  have hx' : b • x ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := key hx
  exact Submodule.add_mem _ hx' (Submodule.mem_sup_right (nsmul_mem (hB hy) b))

set_option maxHeartbeats 2000000 in

theorem killR_of_steps (D : D7) (HW : HWOf D.loc) (hd : dvdR) (hq : quotR D) (hn : normR D)
    (h9 : p9R D HW) (hS : splitR D HW) (hU : univR D HW) : killR D := by
  classical
  unfold killR
  intro l _ hl K LL hG
  unfold killA
  intro T₁ T₂ F r S η m h up b hA
  have hjmp : ∀ τ (X : Set ℤ), JumpsInV ((D.loc l).PD K) T₁.ρ τ X → JumpsInV ((D.loc l).PD K) T₂.ρ τ X :=
    hq l hl K LL hG T₁ T₂ F hA.1 hA.2.1 hA.2.2.1
  obtain ⟨η₁, h', b', hη, hh', hN⟩ := hn l hl K LL hG T₁ T₂ F r S η m h up b hA hjmp
  have hc2 := hN.2.1
  have hj2 := hN.2.2.2.2.1
  have hηb := hN.2.2.2.2.2.1
  have hbS := hN.2.2.2.2.2.2.1
  have hh1 := hN.2.2.2.2.2.2.2.1
  obtain ⟨π', E, h9'⟩ := h9 l hl K LL hG T₂ hc2
  have hjmp2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hmem := hj2 τ a ha
    have h1 := hηb τ
    have h2 := hbS τ
    rcases hmem with hmem | hmem
    · unfold deep at hmem
      split_ifs at hmem
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
    · obtain ⟨x1, x2⟩ := hmem
      constructor <;> omega
  have hSp := hS l hl K LL hG π' E h9' T₂ h' hh1 hc2 hjmp2
  choose s₀ hs₀card hs₀sub hs₀J using fun c => hU l hl K LL hG π' E h9' T₁ T₂ F S η₁ m h' up b' hN c
  have hB : latticeCoboundaries T₂.L ≤ F.ImF ((D.loc l).PD K) := by
    unfold LatHom.ImF
    exact le_sup_right
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := by
    first
    | infer_instance
    | exact ⟨Module.finrank_pos.ne'⟩
    | exact ⟨(Formalism.MainNotions.N.Ln34.max_unramified_finrank_pos K).ne'⟩
    | exact ⟨(Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K).ne'⟩
    | (haveI := Formalism.MainNotions.WachCoordinates.Br.finiteDimensional_max_unramified K; exact ⟨Module.finrank_pos.ne'⟩)
    | (haveI := FiniteDimensional.left ℚ_[l] ↥(K0 K) ↥K.1; exact ⟨Module.finrank_pos.ne'⟩)
  refine ⟨sK l K, h', Nat.mul_div_cancel' (hd l hl K LL hG), hh1, hh', Finset.univ.biUnion s₀, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion s₀).card ≤ ∑ c, (s₀ c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c : ZMod (finrank ℚ_[l] ↥(K0 K)), eK K * (eK K + 1) * m :=
        Finset.sum_le_sum fun c _ => hs₀card c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        ring
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    exact hs₀sub c hc
  · intro p hp
    have hk := annihilation_of_scaled_spans _ _ _ s₀ hB _ _ p (hSp p hp) (fun c x hx => hs₀J c x hx)
    have hY : (l ^ YA l (eK K) (sK l K) h' S η₁ : ℕ) • p ∈
        Submodule.span ↥(OL LL) ((Finset.univ.biUnion s₀ : Finset _) : Set (↥(GK K) → T₂.V)) ⊔
          F.ImF ((D.loc l).PD K) := by
      rw [YA_split, pow_add, mul_comm, mul_smul]
      exact hk
    have e1 : YA l (eK K) (sK l K) h' S η =
        (YA l (eK K) (sK l K) h' S η - YA l (eK K) (sK l K) h' S η₁) + YA l (eK K) (sK l K) h' S η₁ :=
      (Nat.sub_add_cancel (YA_mono l (eK K) (sK l K) h' S hη)).symm
    rw [e1, pow_add, mul_smul]
    exact nsmul_mem hY _

end Formalism.MainNotions.N.Ln34

end
