import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremTwoFamilyOfVolume

noncomputable section

open MeasureTheory

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem measurableConstSMul_subgroup (Γ : Subgroup G) : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩

theorem smulInvariant_subgroup (Γ : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] :
    SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩

def stab (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}

def hit (Γ K : Subgroup G) (g x : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * x) ∈ K}

theorem hit_empty {Γ K : Subgroup G} {ι : Type*} (g : ι → G)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    {j : ι} (δ : Γ) (k : K) (i : ι) (hij : i ≠ j) : hit Γ K (g i) ((δ : G) * g j * k) = ∅ := by
  ext γ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have h' : (g i)⁻¹ * ((γ : G) * ((δ : G) * g j * k)) ∈ K := h
  apply hij
  refine hdisj i j 1 (γ * δ) ⟨_, h'⟩ k ?_
  simp [mul_assoc]

def hitEquiv {Γ K : Subgroup G} (gj : G) (δ : Γ) (k : K) :
    hit Γ K gj ((δ : G) * gj * k) ≃ stab Γ K gj where
  toFun γ := ⟨γ.1 * δ, by
    have h := K.mul_mem γ.2 (K.inv_mem k.2)
    simp only [stab, Set.mem_ofPred_eq, Subgroup.coe_mul]
    convert h using 1; group⟩
  invFun γ := ⟨γ.1 * δ⁻¹, by
    have h := K.mul_mem γ.2 k.2
    simp only [hit, Set.mem_ofPred_eq, Subgroup.coe_mul, Subgroup.coe_inv]
    convert h using 1; group⟩
  left_inv γ := by ext; simp
  right_inv γ := by ext; simp

open Classical in

theorem measure_fd_eq_sum {Γ K : Subgroup G} [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (stab Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    μ 𝓕 = ∑ i, μ K * ((Nat.card (stab Γ K (g i)) : ENNReal))⁻¹ := by
  have := measurableConstSMul_subgroup Γ
  have := smulInvariant_subgroup Γ μ

  let T : ι → Set G := fun i => (fun y => (g i)⁻¹ * y) ⁻¹' (K : Set G)
  have hT : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_mul _) hK
  let f : G → ENNReal := fun y => ∑ i, ((Nat.card (stab Γ K (g i)) : ENNReal))⁻¹ * (T i).indicator 1 y
  have hf : Measurable f := Finset.measurable_sum _ fun i _ =>
    (measurable_one.indicator (hT i)).const_mul _

  have hG : ∫⁻ y, f y ∂μ = ∑ i, μ K * ((Nat.card (stab Γ K (g i)) : ENNReal))⁻¹ := by
    rw [lintegral_finsetSum _ fun i _ => (measurable_one.indicator (hT i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator (hT i)), lintegral_indicator_one (hT i),
      measure_preimage_mul, mul_comm]

  have hpt : ∀ x, ∑' γ : Γ, f (γ • x) = 1 := by
    intro x
    obtain ⟨j, δ, k, rfl⟩ := hcov x
    have hsum : ∀ i, ∑' γ : Γ, (T i).indicator (1 : G → ENNReal) (γ • ((δ : G) * g j * k)) =
        Nat.card (hit Γ K (g i) ((δ : G) * g j * k)) := by
      intro i
      have hfin' : (hit Γ K (g i) ((δ : G) * g j * k)).Finite := by
        by_cases hij : i = j
        · rw [hij]
          have := (hfin j).to_subtype
          have : Finite (hit Γ K (g j) ((δ : G) * g j * k)) := Finite.of_equiv _ (hitEquiv (g j) δ k).symm
          exact Set.toFinite _
        · rw [hit_empty g hdisj δ k i hij]; exact Set.finite_empty
      have e : (fun γ : Γ => (T i).indicator (1 : G → ENNReal) (γ • ((δ : G) * g j * k))) =
          (hit Γ K (g i) ((δ : G) * g j * k)).indicator 1 := by
        funext γ
        simp only [Set.indicator, T, hit, Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.smul_def,
          smul_eq_mul, SetLike.mem_coe, Pi.one_apply]
        by_cases h : (g i)⁻¹ * ((γ : G) * ((δ : G) * g j * k)) ∈ K <;> simp [h]
      rw [e, ← tsum_subtype]
      haveI := hfin'.fintype
      rw [tsum_fintype]
      simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_eq_nat_card]
    have hswap : ∑' γ : Γ, f (γ • ((δ : G) * g j * k)) =
        ∑ i, ((Nat.card (stab Γ K (g i)) : ENNReal))⁻¹ *
          ∑' γ : Γ, (T i).indicator (1 : G → ENNReal) (γ • ((δ : G) * g j * k)) := by
      simp only [f]
      rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.tsum_mul_left]
    rw [hswap, Finset.sum_eq_single j]
    · rw [hsum j, Nat.card_congr (hitEquiv (g j) δ k)]
      have hne : (Nat.card (stab Γ K (g j)) : ENNReal) ≠ 0 := by
        have := (hfin j).to_subtype
        have hne : Nonempty (stab Γ K (g j)) := ⟨⟨1, by simp [stab]⟩⟩
        exact_mod_cast (Nat.card_pos (α := stab Γ K (g j))).ne'
      exact ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _)
    · intro i _ hij
      rw [hsum i, hit_empty g hdisj δ k i hij]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h

  have hmeas : ∀ γ : Γ, Measurable fun x => f (γ • x) := fun γ => hf.comp (measurable_const_smul γ)
  calc μ 𝓕 = ∫⁻ x in 𝓕, 1 ∂μ := (setLIntegral_one 𝓕).symm
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ • x) ∂μ := by simp only [hpt]
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, f (γ • x) ∂μ := lintegral_tsum fun γ => (hmeas γ).aemeasurable
    _ = ∫⁻ y, f y ∂μ := (h𝓕.lintegral_eq_tsum'' f).symm
    _ = _ := hG

theorem measure_fd_toReal {Γ K : Subgroup G} [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) {ι : Type*} [Fintype ι] (g : ι → G)
    (hcov : ∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j)
    (hfin : ∀ i, (stab Γ K (g i)).Finite)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal = ∑ i, ((Nat.card (stab Γ K (g i)) : ℝ))⁻¹ := by
  rw [measure_fd_eq_sum μ hK g hcov hdisj hfin h𝓕, hK1]
  simp only [one_mul]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    apply ENNReal.inv_ne_top.mpr
    have h1 : (1 : Γ) ∈ stab Γ K (g i) := by simp [stab]
    have hpos : 0 < Nat.card (stab Γ K (g i)) := by
      haveI := (hfin i).to_subtype
      exact Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    exact_mod_cast hpos.ne'

section Inst

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem isModTop : IsModuleTopology (AF F) (AF F ⊗[F] E) := by first | exact ⟨rfl⟩ | infer_instance

theorem isTopRing : IsTopologicalRing (AF F ⊗[F] E) := by
  haveI := isModTop (F := F) (E := E)
  first
    | exact IsModuleTopology.isTopologicalRing (AF F) _
    | exact IsModuleTopology.topologicalRing (AF F) _

theorem topGroupHA : IsTopologicalGroup (HA (AF F) σ J) := by
  haveI := isTopRing (F := F) (E := E)
  haveI h1 : IsTopologicalGroup (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ˣ := inferInstance
  haveI h2 : IsTopologicalGroup (GL (Fin M) (AF F ⊗[F] E)) := h1
  first
    | exact Subgroup.isTopologicalGroup _
    | exact @Subgroup.isTopologicalGroup _ _ _ h2 _
    | (unfold HA; infer_instance)
    | exact inferInstanceAs (IsTopologicalGroup ↥(HR (AF F) σ J))

theorem borelHA : BorelSpace (HA (AF F) σ J) := by first | exact ⟨rfl⟩ | infer_instance | (unfold HA; infer_instance)

theorem measurableMulHA : MeasurableMul (HA (AF F) σ J) := by
  haveI := topGroupHA σ J
  haveI := borelHA σ J
  first | infer_instance | (unfold HA; infer_instance)

theorem countableE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable

private theorem countable_subgroupOf_of_countable' {G' : Type*} [Group G'] (H K : Subgroup G') (hH : Countable H) :
    Countable (H.subgroupOf K) :=
  Function.Injective.countable (f := fun x : H.subgroupOf K => (⟨((x : K) : G'), x.2⟩ : H))
    (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : H => (w : G')) h)

private theorem countable_subgroup_map_of_countable {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A)
    (hH : Countable H) : Countable (H.map f) := by
  haveI := hH
  exact (f.subgroupMap_surjective H).countable

private theorem countable_GL_fin_of_countable {R : Type*} [CommRing R] [Countable R] (n : ℕ) : Countable (GL (Fin n) R) := by
  haveI : Countable (Fin n → Fin n → R) := inferInstance
  exact Function.Injective.countable (α := GL (Fin n) R) (β := Fin n → Fin n → R)
    (f := fun u => (u : Matrix (Fin n) (Fin n) R)) (fun a b h => Units.ext h)

theorem countableGamma : Countable (HFinIn (AF F) σ J) := by
  haveI := countableE (E := E)
  haveI := countable_GL_fin_of_countable (R := E) M
  unfold HFinIn HFin
  exact countable_subgroupOf_of_countable' _ _ (countable_subgroup_map_of_countable _ _ inferInstance)

end Inst

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mapAlg_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) A) : (X * Y).map φ = X.map φ * Y.map φ := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

theorem mapAlg_one {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} : (1 : Matrix (Fin n) (Fin n) A).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)

section Mats

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem HA_mat_mul (h h' : HA (AF F) σ J) : HA.mat (AF F) σ J (h * h') = HA.mat (AF F) σ J h * HA.mat (AF F) σ J h' :=
  rfl

theorem HA_mat_one : HA.mat (AF F) σ J 1 = 1 := rfl

theorem finMat_mul (h h' : HA (AF F) σ J) : finMat σ J (h * h') = finMat σ J h * finMat σ J h' := by
  first
    | simp [finMat, HA_mat_mul, Units.val_mul, mapAlg_mul, Matrix.map_mul]
    | (unfold finMat; rw [HA_mat_mul]; done)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  first
    | simp [finMat, HA_mat_one, mapAlg_one, Matrix.map_one]
    | (unfold finMat; rw [HA_mat_one]; done)

theorem infMat_mul (θ : Ainf F ⊗[F] E →+* ℂ) (h h' : HA (AF F) σ J) :
    infMat σ J θ (h * h') = infMat σ J θ h * infMat σ J θ h' := by
  first
    | simp [infMat, HA_mat_mul, Units.val_mul, mapAlg_mul, Matrix.map_mul]
    | (unfold infMat; rw [HA_mat_mul]; done)

theorem infMat_one (θ : Ainf F ⊗[F] E →+* ℂ) : infMat σ J θ (1 : HA (AF F) σ J) = 1 := by
  first
    | simp [infMat, HA_mat_one, mapAlg_one, Matrix.map_one]
    | (unfold infMat; rw [HA_mat_one]; done)

end Mats

theorem UpqT_mat_mul {P Q : ℕ} (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := rfl

theorem UpqT_mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

def KSet (D : D7) (W : HSpace D.host.E) (P Q : ℕ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram) :=
  {h | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D W) ↔
          (finMat D.sp.cm.sig W.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D W)) ∧
        ∀ ρ, ∃ b ∈ (Set.univ : Set (UpqT P Q)), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig W.gram (θ ρ) h}

def KSub (D : D7) (W : HSpace D.host.E) (P Q : ℕ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ) : Subgroup (HA (AF D.host.F) D.sp.cm.sig W.gram) where
  carrier := KSet D W P Q θ A
  mul_mem' := by
    intro h h' hh hh'
    refine ⟨fun y => ?_, fun ρ => ?_⟩
    · rw [finMat_mul, ← Matrix.mulVec_mulVec, hh'.1 y]
      exact hh.1 _
    · obtain ⟨b, -, hb⟩ := hh.2 ρ
      obtain ⟨b', -, hb'⟩ := hh'.2 ρ
      refine ⟨b * b', Set.mem_univ _, ?_⟩
      rw [UpqT_mat_mul, infMat_mul, Matrix.mul_assoc, hb', ← Matrix.mul_assoc, hb, Matrix.mul_assoc]
  one_mem' := by
    refine ⟨fun y => ?_, fun ρ => ⟨1, Set.mem_univ _, ?_⟩⟩
    · rw [finMat_one, Matrix.one_mulVec]
    · rw [UpqT_mat_one, infMat_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro h hh
    refine ⟨fun y => ?_, fun ρ => ?_⟩
    · have e : (finMat D.sp.cm.sig W.gram h).mulVec ((finMat D.sp.cm.sig W.gram h⁻¹).mulVec y) = y := by
        rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
      have := hh.1 ((finMat D.sp.cm.sig W.gram h⁻¹).mulVec y)
      rw [e] at this
      exact this.symm
    · obtain ⟨b, -, hb⟩ := hh.2 ρ
      refine ⟨b⁻¹, Set.mem_univ _, ?_⟩
      have e1 : infMat D.sp.cm.sig W.gram (θ ρ) h * infMat D.sp.cm.sig W.gram (θ ρ) h⁻¹ = 1 := by
        rw [← infMat_mul, mul_inv_cancel, infMat_one]
      have e2 : UpqT.mat b⁻¹ * UpqT.mat b = 1 := by
        rw [← UpqT_mat_mul, inv_mul_cancel, UpqT_mat_one]
      calc UpqT.mat b⁻¹ * A ρ
          = UpqT.mat b⁻¹ * (A ρ * (infMat D.sp.cm.sig W.gram (θ ρ) h * infMat D.sp.cm.sig W.gram (θ ρ) h⁻¹)) := by
            rw [e1, Matrix.mul_one]
        _ = (UpqT.mat b⁻¹ * UpqT.mat b) * A ρ * infMat D.sp.cm.sig W.gram (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc (A ρ), ← hb]; simp only [Matrix.mul_assoc]
        _ = A ρ * infMat D.sp.cm.sig W.gram (θ ρ) h⁻¹ := by rw [e2, Matrix.one_mul]

theorem measure_KSub (D : D7) (W : HSpace D.host.E) (P : ℕ)
    (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (hμ : IsVolMeas D W P 0 μ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq P 0 * A ρ = W.gram.map (embOf D ρ)) :
    μ (KSub D W P 0 θ A) = 1 := by
  have h := hμ.2.2 θ hθ |>.2 A hA (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hp : D.cd.cd P 0 Set.univ = 1 := by
    haveI := D.cd.prob P; exact measure_univ
  change μ (KSet D W P 0 θ A) = 1
  unfold KSet
  rw [h]
  simp [hp]

abbrev GamA (D : D7) (W : HSpace D.host.E) : Subgroup (HA (AF D.host.F) D.sp.cm.sig W.gram) :=
  HFinIn (AF D.host.F) D.sp.cm.sig W.gram

def DefClassDecomp (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
  ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) →
  ∀ A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq W.rank 0 * A ρ = W.gram.map (embOf D ρ)) →
    MeasurableSet (KSub D W W.rank 0 θ A : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) ∧
    ∃ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : KSub D W W.rank 0 θ A, x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) ∧
      (∀ i j (γ γ' : GamA D W) (k k' : KSub D W W.rank 0 θ A),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k = (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' →
          i = j) ∧
      (∀ i, (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) (g i)).Finite) ∧
      ∑ i, ((Nat.card (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) (g i)) : ℝ))⁻¹ = Formalism.HermitianLatticesTheory.mass W.hT W.L0

theorem mass_volume_identity_of_class_decomp (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (hC : DefClassDecomp D) : DefiniteVolumeEqMass D := by
  unfold DefiniteVolumeEqMass
  unfold VolTie at hT
  unfold AllSome at hT
  intro W hW hdef
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W W.rank 0 hW hdef
  obtain ⟨⟨𝓕, h𝓕⟩, hvol⟩ := hall μ hμ
  have hμ𝓕 := hvol 𝓕 h𝓕
  have hμ' := hμ
  unfold IsVolMeas AllSome at hμ'
  obtain ⟨hHaar, ⟨θ, hθ⟩, hθall⟩ := hμ'
  obtain ⟨⟨A, hA⟩, -⟩ := hθall θ hθ
  obtain ⟨hKm, n, g, hcov, hdisj, hfin, hsum⟩ := hC W hW hdef θ hθ A hA
  have hK1 := measure_KSub D W W.rank μ hμ θ hθ A hA
  haveI := hHaar
  haveI := Unfold.measurableMulHA D.sp.cm.sig W.gram
  haveI hcnt : Countable ↥(GamA D W) := Unfold.countableGamma D.sp.cm.sig W.gram
  have key := Unfold.measure_fd_toReal μ hKm hK1 g hcov hdisj hfin h𝓕
  have hpos : 0 < ∑ i, ((Nat.card (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) (g i)) : ℝ))⁻¹ := by
    obtain ⟨i0, -, -, -⟩ := hcov 1
    apply Finset.sum_pos
    · intro i _
      have h1 : (1 : GamA D W) ∈ Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) (g i) := by
        simp [Unfold.stab]
      haveI := (hfin i).to_subtype
      have hc : 0 < Nat.card (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) (g i)) :=
        Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
      exact inv_pos.mpr (by exact_mod_cast hc)
    · exact ⟨i0, Finset.mem_univ _⟩
  rw [hμ𝓕, ENNReal.toReal_ofReal'] at key
  have e2 := key.trans hsum
  have hmpos := lt_of_lt_of_eq hpos hsum
  have hvm : D.vol W = Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
    rcases le_total 0 (D.vol W) with h | h
    · rwa [max_eq_left h] at e2
    · rw [max_eq_right h] at e2
      linarith
  rw [hvm]
  first
    | exact hG W hW hdef
    | exact hG W hW
    | exact hG W
    | exact (hG W hW hdef).symm
    | (clear hT hall hvol hμ𝓕 hθall key e2 hpos hmpos; unfold GenusMassStd at hG; done)

theorem family_mass_volume_identity_of_class_decomp {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hR : TiedRealF Fm) (hH : HostInputsF Fm)
    (hC : ∀ x (i : Fm.Ix x), DefClassDecomp (Fm.D x i)) : ∀ x (i : Fm.Ix x), DefiniteVolumeEqMass (Fm.D x i) :=
  fun x i => mass_volume_identity_of_class_decomp _ (Formalism.L2.Theta.VolTieG.volTie (hR x i).vol) (hH x i).2.2 (hC x i)

theorem Link2_of_decomp (hC : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), DefClassDecomp (Fm.D x i)) :
    Link2 :=
  fun eps Fm hR _ hH hV => theorem_two_family_of_volume Fm hR hV (family_mass_volume_identity_of_class_decomp Fm hR hH (hC eps Fm))

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
