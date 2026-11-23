import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InfiniteOfConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToIdeleESymm

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

def lineGrp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l, Scales σ J x p l}
  one_mem' := ⟨1, by simp [Scales]⟩
  mul_mem' := fun {a b} ⟨l, e⟩ ⟨l', e'⟩ => ⟨l * l', by
    unfold Scales at *
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]⟩
  inv_mem' := fun {a} ⟨l, e⟩ => ⟨l⁻¹, by
    unfold Scales at *
    have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J a⁻¹).1 * Z)) e
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm⟩

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def IsReps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l, Scales σ J x (γ * t⁻¹ : ratPts σ J).1 l

structure IsFlow (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (a : ℝ → GAd σ J) : Prop where
  cont : Continuous a
  add : ∀ s t, a (s + t) = a s * a t
  onX : ∀ t, ∃ l, Scales σ J (col X) (a t) l ∧ (absE F E l : ℝ) = Real.exp t
  onY : ∀ t, ∃ l, Scales σ J (col Y) (a t) l ∧ (absE F E l : ℝ) = Real.exp (-t)
  mem : ∀ t, a t ∈ GlobalTheory.StdPar.levi σ J X Y {0}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {0}, a t * m = m * a t

example (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Scales σ J x 1 1 := by
  simp [Scales]

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

example {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHt K fun _ => 1 :=
  ⟨fun _ => one_pos, continuous_const, fun _ _ => rfl, fun _ => ⟨1, one_mem _, fun _ => (one_mul _).symm⟩⟩

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem exists_data (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    (hA : GlobalTheory.EisLine.IsAdapted σ J X Y L a) : ∃ h, Data σ J X Y L a h := by
  obtain ⟨h1, h, h2⟩ := GlobalTheory.IwLine.iwasawa_line F E σ hc hu n J hJ r X Y hW _ rfl L a hA
  exact ⟨h, hc, hu, hJ, hW, hA, h1, h2⟩

theorem data_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (L : Submodule (𝓞 E) (Fin 2 → E))
    (a : GL (Fin 2) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, hc, hu, hJ, hW, hA⟩ := GlobalTheory.EisLineModel.data_inhabited
  obtain ⟨h, H⟩ := exists_data hc hu hJ hW hA
  exact ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, h, H⟩

theorem exists_isReps (x : Matrix (Fin n) (Fin 1) E) : ∃ T, IsReps σ J x T := GlobalTheory.EisResLineModel.exists_reps x

omit [NumberField E] in

theorem scales_of_diag {C : Matrix (Fin n) (Fin (r + 1)) E} {p : GAd σ J} {l : Fin (r + 1) → (AF F ⊗[F] E)ˣ}
    (h : (matHom _ σ J p).1 * adMat F C = adMat F C * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))) :
    Scales σ J (ResLine.col C) p (l 0) := by
  ext i j
  have := congrFun (congrFun h i) 0
  rw [mul_diagonal] at this
  simpa [Matrix.mul_apply, ResLine.col, mul_comm] using this

theorem exists_isFlow (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : ∃ a, IsFlow σ J X Y a := by
  obtain ⟨t, htc, ht⟩ := GlobalTheory.IdTorus.exists_continuous_isIdTorusElt hc hJ hW
  have hd : (2 * (Module.finrank ℚ F : ℝ)) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := F); positivity
  let l : ℝ → Fin (r + 1) → (AF F ⊗[F] E)ˣ := fun s => Pi.mulSingle 0 (archUnit F E (s / (2 * Module.finrank ℚ F)))
  have l0 : ∀ s, (absE F E (l s 0) : ℝ) = Real.exp s := fun s => by
    simp only [l, Pi.mulSingle_eq_same]
    rw [GlobalTheory.HeckeAbsArch.absE_archUnit hc, mul_div_cancel₀ _ hd]
  have cl := fun s => GlobalTheory.IdTorusCent.centre_levi hc hJ hW (S := {0}) (by
      intro k hk i hi; rw [Finset.mem_singleton] at hk ⊢; subst hk; exact le_antisymm hi (Fin.zero_le _))
    (l := l s) (fun k hk => Pi.mulSingle_eq_of_ne (by simpa using hk) _) (ht (l s))
  refine ⟨fun s => t (l s), htc.comp ((continuous_mulSingle 0).comp
    (GlobalTheory.HeckeAbsArch.continuous_archUnit.comp (continuous_id.div_const _))), fun s s' => ?_,
    fun s => ⟨_, scales_of_diag (ht (l s)).1, l0 s⟩,
    fun s => ⟨_, scales_of_diag (l := fun k => (conjUnit σ (l s k))⁻¹) (ht (l s)).2.1, ?_⟩, fun s => (cl s).1, fun s => (cl s).2⟩
  · refine GlobalTheory.IdTorus.isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : l (s + s') = l s * l s' := by
      simp only [l]; rw [add_div, GlobalTheory.HeckeAbsArch.archUnit_add, Pi.mulSingle_mul]
    rw [this]; exact GlobalTheory.IdTorus.isIdTorusElt_mul (ht _) (ht _)
  · rw [map_inv, GlobalTheory.Doubling.absE_conjUnit, NNReal.coe_inv, l0, Real.exp_neg]

theorem ht_flow {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ}
    (H : Data σ J X Y L a h) {c : ℝ → GAd σ J} (hc : IsFlow σ J X Y c) (t : ℝ) : h (c t) = Real.exp t := by
  obtain ⟨l, h1, h2⟩ := hc.onX t
  simpa [h2] using H.ht _ l h1 1 (one_mem _)

theorem isHt_of_data {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ}
    (H : Data σ J X Y L a h) : IsHt (levelAll σ J L a) h := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  haveI := H.adapted.lat
  have hyx : cT (σ : E →+* E) (ResLine.col Y) * J * ResLine.col X = 1 := by
    ext i j
    have := congrFun (congrFun (GlobalTheory.StdPar.yx H.cm H.herm H.witt) 0) 0
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [cT, ResLine.col, Matrix.mul_apply] using this
  let φ : GAd σ J → AF F ⊗[F] E := fun p =>
    (adMat F (cT (σ : E →+* E) (ResLine.col Y) * J) * ((matHom _ σ J p).1 * adMat F (ResLine.col X))) 0 0
  have hφ : ∀ p l, Scales σ J (ResLine.col X) p l → φ p = l := fun p l e => by
    unfold Scales at e
    simp only [φ, e, Matrix.mul_smul, adMat, ← Matrix.map_mul, hyx]
    simp
  have cφ : Continuous φ := (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)).matrix_elem 0 0
  have hinv : ∀ p l, Scales σ J (ResLine.col X) p l → Scales σ J (ResLine.col X) p⁻¹ l⁻¹ := fun p l e => by
    unfold Scales at *
    rw [map_inv]; exact GlobalTheory.IwLine.inv_mul_eq_smul _ _ _ e
  have hmul : ∀ p l q m, Scales σ J (ResLine.col X) p l → Scales σ J (ResLine.col X) q m → Scales σ J (ResLine.col X) (p * q) (l * m) :=
    fun p l q m e e' => by
      unfold Scales at *
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]
  have eP : lineGrp σ J (ResLine.col X) = GlobalTheory.StdPar.frameStab σ J (ResLine.col X) ⊤ := by
    ext p
    refine ⟨fun ⟨l, e⟩ => ⟨Units.map (Matrix.scalar (Fin 1)).toMonoidHom l, trivial, e.trans ?_⟩, fun ⟨B, _, e⟩ =>
      ⟨Matrix.GeneralLinearGroup.det B, e.trans ?_⟩⟩
    · ext i j; simp [Matrix.mul_apply, mul_comm, Subsingleton.elim j 0]
    · ext i j; simp [Matrix.mul_apply, mul_comm, Subsingleton.elim j 0]
  have cP : IsClosed (lineGrp σ J (ResLine.col X) : Set (GAd σ J)) := by
    rw [eP]; exact GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  refine ⟨(GlobalTheory.EisLineModel.pos H.iwa H.ht).1, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [Scales]) k hk, fun g => ?_⟩
  · refine GlobalTheory.Doubling.continuous_of_prod cP (GlobalTheory.Doubling.isCompact_levelAll H.cm _ _ _)
      (fun g => let ⟨p, l, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, l, e⟩, k, hk, e'⟩) ?_
    let u : lineGrp σ J (ResLine.col X) → (AF F ⊗[F] E)ˣ := fun p => p.2.choose
    have hu : ∀ p : lineGrp σ J (ResLine.col X), Scales σ J (ResLine.col X) p (u p) := fun p => p.2.choose_spec
    have cu : Continuous u := Units.continuous_iff.2
      ⟨(cφ.comp continuous_subtype_val).congr fun p => hφ _ _ (hu p),
        (cφ.comp continuous_subtype_val.inv).congr fun p => hφ _ _ (hinv _ _ (hu p))⟩
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hu x.1) _ x.2.2).symm
  · obtain ⟨p, l, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    obtain ⟨q, m, e', k', hk', e''⟩ := H.iwa (k * x)
    rw [mul_assoc, e'', ← mul_assoc, H.ht _ _ (hmul _ _ _ _ e e') _ hk', H.ht _ _ e _ hk, H.ht _ _ e' _ hk', map_mul,
      NNReal.coe_mul]

theorem all_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (L : Submodule (𝓞 E) (Fin 2 → E))
    (a : GL (Fin 2) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (c : ℝ → GAd σ J) (T : Set (ratPts σ J)),
    Data σ J X Y L a h ∧ IsFlow σ J X Y c ∧ IsReps σ J (ResLine.col X) T ∧ IsHt (levelAll σ J L a) h ∧
      ∀ t, h (c t) = Real.exp t := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, h, H⟩ := data_inhabited
  obtain ⟨c, hc⟩ := exists_isFlow H.cm H.herm H.witt
  obtain ⟨T, hT⟩ := exists_isReps (σ := σ) (J := J) (ResLine.col X)
  exact ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, h, c, T, H, hc, hT, isHt_of_data H, ht_flow H hc⟩

example (H : Subgroup (GAd σ J)) : Countable (ratPts σ J ⊓ H : Subgroup (GAd σ J)) := inferInstance

theorem isHt_right {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {h : G → ℝ} (H : IsHt K h) (g : G) {k : G}
    (hk : k ∈ K) : h (g * k) = h g := by
  obtain ⟨k', hk', e⟩ := H.iw g
  rw [e, H.one _ (mul_mem hk' hk), mul_one]

abbrev Pl : Type := Multiplicative (Fin 2 → ℝ)

scoped instance measurableSpacePl : MeasurableSpace Pl := borel _

scoped instance borelSpacePl : BorelSpace Pl := ⟨rfl⟩

def axis (i : Fin 2) : Subgroup Pl where
  carrier := {g | ∀ j, j ≠ i → g.toAdd j = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  inv_mem' := fun ha j hj => by simp [ha j hj]

def intPts : Subgroup Pl where
  carrier := {g | ∀ j, ∃ m : ℤ, g.toAdd j = m}
  one_mem' := fun _ => ⟨0, by simp⟩
  mul_mem' := fun ha hb j => let ⟨m, e⟩ := ha j; let ⟨m', e'⟩ := hb j; ⟨m + m', by simp [e, e']⟩
  inv_mem' := fun ha j => let ⟨m, e⟩ := ha j; ⟨-m, by simp [e]⟩

theorem cont_coord (j : Fin 2) : Continuous fun g : Pl => g.toAdd j := (continuous_apply j).comp continuous_toAdd

theorem isClosed_axis (i : Fin 2) : IsClosed (axis i : Set Pl) := by
  have : (axis i : Set Pl) = ⋂ j, ⋂ (_ : j ≠ i), {g | g.toAdd j = 0} := by ext g; simp [axis]
  rw [this]
  exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (cont_coord j) continuous_const

scoped instance locallyCompactSpace_axis (i : Fin 2) : LocallyCompactSpace (axis i) := (isClosed_axis i).locallyCompactSpace

theorem single_mem (i : Fin 2) (c : ℝ) : Multiplicative.ofAdd (Pi.single i c) ∈ axis i := fun j hj => by simp [hj]

theorem single_int (i : Fin 2) (m : ℤ) : Multiplicative.ofAdd (Pi.single i (m : ℝ)) ∈ intPts := fun j => by
  by_cases h : j = i
  · exact ⟨m, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

def unitInt (i : Fin 2) : Set (axis i) := {u | u.1.toAdd i ∈ Set.Ico (0 : ℝ) 1}

theorem isFD (i : Fin 2) (μ : Measure (axis i)) : IsFundamentalDomain (intPts.subgroupOf (axis i)) (unitInt i) μ := by
  refine IsFundamentalDomain.mk' ?_ fun x => ?_
  · exact (((cont_coord i).comp continuous_subtype_val).measurable measurableSet_Ico).nullMeasurableSet
  · refine ⟨⟨⟨_, single_mem i ((-⌊x.1.toAdd i⌋ : ℤ) : ℝ)⟩, single_int i _⟩, ?_, fun g hg => ?_⟩
    · change (Pi.single i ((-⌊x.1.toAdd i⌋ : ℤ) : ℝ) + x.1.toAdd : Fin 2 → ℝ) i ∈ Set.Ico (0 : ℝ) 1
      simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_neg]
      exact ⟨by linarith [Int.floor_le (x.1.toAdd i)], by linarith [Int.lt_floor_add_one (x.1.toAdd i)]⟩
    · obtain ⟨m, e⟩ := g.2 i
      change g.1.1.toAdd i + x.1.toAdd i ∈ Set.Ico (0 : ℝ) 1 at hg
      have e' : g.1.1.toAdd i = m := e
      rw [e'] at hg
      have : ⌊x.1.toAdd i⌋ = -m := Int.floor_eq_iff.2 ⟨by push_cast; linarith [hg.1], by push_cast; linarith [hg.2]⟩
      refine Subtype.ext (Subtype.ext (Multiplicative.toAdd.injective (funext fun j => ?_)))
      by_cases h : j = i
      · subst h; simp [this, e']
      · simp [h, g.1.2 j h]

theorem fin_unitInt (i : Fin 2) (μ : Measure (axis i)) [μ.IsHaarMeasure] : μ (unitInt i) ≠ ⊤ := by
  have hc : IsCompact (Multiplicative.ofAdd '' (Set.Icc (0 : Fin 2 → ℝ) 1) : Set Pl) := isCompact_Icc.image continuous_ofAdd
  refine ne_top_of_le_ne_top ((isClosed_axis i).isClosedEmbedding_subtypeVal.isCompact_preimage hc).measure_ne_top
    (measure_mono fun u hu => ⟨u.1.toAdd, ⟨fun j => ?_, fun j => ?_⟩, rfl⟩)
  · by_cases h : j = i
    · subst h; exact hu.1
    · simp [u.2 j h]
  · by_cases h : j = i
    · subst h; exact hu.2.le
    · simp [u.2 j h]

theorem countable_intPts : Countable intPts :=
  Function.Injective.countable (f := fun (g : intPts) (j : Fin 2) => (g.2 j).choose) fun a b h =>
    Subtype.ext (Multiplicative.toAdd.injective (funext fun j => by
      rw [(a.2 j).choose_spec, (b.2 j).choose_spec]; exact congrArg _ (congrFun h j)))

theorem semiLat_plane : SemiLat (axis 0) (axis 1) intPts Measure.haar Measure.haar (unitInt 0) (unitInt 1) where
  closedN := isClosed_axis 0
  closedM := isClosed_axis 1
  norm := fun m _ u hu => by rwa [mul_comm m, mul_inv_cancel_right]
  disj := fun g h0 h1 => Multiplicative.toAdd.injective (funext fun j => by
    fin_cases j
    · exact h1 0 (by decide)
    · exact h0 1 (by decide))
  dec := fun γ hγ => by
    obtain ⟨m, e⟩ := hγ 0
    obtain ⟨m', e'⟩ := hγ 1
    refine ⟨_, single_mem 0 m, _, single_mem 1 m', single_int _ _, single_int _ _,
      Multiplicative.toAdd.injective (funext fun j => ?_)⟩
    fin_cases j <;> simp [e, e']
  haarN := inferInstance
  haarM := inferInstance
  domN := isFD 0 _
  domM := isFD 1 _
  finN := fin_unitInt 0 _
  finM := fin_unitInt 1 _
  count := countable_intPts
  topGrp := inferInstance
  borel := inferInstance

theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

example : IsHt (⊥ : Subgroup (Multiplicative ℝ)) fun g => Real.exp g.toAdd :=
  ⟨fun _ => Real.exp_pos _, Real.continuous_exp.comp continuous_toAdd,
    fun k hk => by rw [Subgroup.mem_bot.1 hk]; simp, fun g => ⟨1, one_mem _, fun x => by simp [Real.exp_add]⟩⟩

theorem fd_one {H : Type} [Group H] [MeasurableSpace H] [MeasurableSingletonClass H] (Λ : Subgroup H) (hΛ : ∀ g, g ∈ Λ)
    (μ : Measure H) : IsFundamentalDomain Λ ({1} : Set H) μ :=
  IsFundamentalDomain.mk' (measurableSet_singleton _).nullMeasurableSet fun x =>
    ⟨⟨x⁻¹, hΛ _⟩, inv_mul_cancel x, fun _ hy => Subtype.ext (eq_inv_of_mul_eq_one_left hy)⟩

theorem haar_count {H : Type} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [BorelSpace H] : (Measure.count : Measure H).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
    open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }

theorem semiLat_finite {G : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
    [BorelSpace G] (N M : Subgroup G) [hN : N.Normal] (hd : ∀ g ∈ N, g ∈ M → g = 1) (hs : ∀ g, ∃ u ∈ N, ∃ m ∈ M, g = u * m) :
    SemiLat N M ⊤ Measure.count Measure.count {1} {1} :=
  ⟨isClosed_discrete _, isClosed_discrete _, fun m _ u hu => hN.conj_mem u hu m, hd,
    fun γ _ => let ⟨u, hu, m, hm, e⟩ := hs γ; ⟨u, hu, m, hm, trivial, trivial, e⟩, haar_count, haar_count,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _, by simp, by simp,
    inferInstance, inferInstance, inferInstance⟩

example : letI : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥; letI : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
    SemiLat (alternatingGroup (Fin 3)) (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)) ⊤
      Measure.count Measure.count {1} {1} := by
  letI : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥
  letI : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
  haveI : DiscreteTopology (Equiv.Perm (Fin 3)) := ⟨rfl⟩
  haveI : BorelSpace (Equiv.Perm (Fin 3)) := ⟨borel_eq_top_of_discrete.symm⟩
  refine semiLat_finite _ _ ?_ ?_
  · simp only [Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; decide
  · simp only [Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; decide

end Inhab

end GlobalTheory.ResLine

end
