import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

theorem mul_one_by_one {R : Type} [CommRing R] (C : Matrix (Fin n) (Fin 1) R) (B : Matrix (Fin 1) (Fin 1) R) :
    C * B = B.det • C := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem absE_of_scales {x : Matrix (Fin n) (Fin 1) E} {L : Matrix (Fin 1) (Fin n) E} (hL : L * x = 1) {γ : GAd σ J}
    (hγ : γ ∈ ratPts σ J) {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x γ l) : absE F E l = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F x = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : E := (L * γ0.1.1 * x) 0 0 with hc
  have hl : l.1 = inclR (F := F) (AF F) c := by
    have := congrArg (adMat F L * ·) e
    simp only [Matrix.mul_smul] at this
    rw [hL', hmat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul] at this
    have := congrFun (congrFun this 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this.symm
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := l.mul_inv
      rw [hl, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim l 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = l from
      Units.ext (by simp [hl])] at this

theorem levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y →
    (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (ResLine.col X), m * u * m⁻¹ ∈ unipRad σ J (ResLine.col X)) ∧
    (∀ g ∈ unipRad σ J (ResLine.col X), g ∈ levi σ J X Y {0} → g = 1) ∧
    (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧
    (∀ u ∈ unipRad σ J (ResLine.col X), Scales σ J (ResLine.col X) u 1) ∧
    (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (ResLine.col X) m l ∧ absE F E l = 1) ∧
    ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (ResLine.col X) γ l → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hc : ResLine.col X = initCols X 0 := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hlev : ∀ m ∈ levi σ J X Y {0}, m ∈ frameStab σ J (initCols X 0) ⊤ ∧ m ∈ frameStab σ J (initCols Y 0) ⊤ :=
    fun m hm => by
      simp only [levi, Subgroup.mem_iInf] at hm
      exact hm 0 (Finset.mem_singleton_self _)
  have hT' : cT (σ : E →+* E) (initCols Y 0) * J * initCols X 0 = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE (0 : Fin (r + 1)).2)) (j.castLE (0 : Fin (r + 1)).2)).trans
      (by simp only [Matrix.one_apply, Fin.castLE_inj])
  have h6 : ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (initCols X 0) γ l → absE F E l = 1 := fun γ hγ l e =>
    absE_of_scales hT' hγ e
  rw [hc]
  refine ⟨fun m hm u hu => conj_mem hW 0 (hlev m hm).1 hu, fun g hg hm => eq_one h hJ hW 0 hg (hlev g hm).2,
    fun γ hγ hm => ⟨hm, ?_⟩, fun u hu => ?_, fun m hm => ?_, h6⟩
  · show γ ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker
    simp only [Subgroup.mem_iInf]
    intro k hk
    obtain rfl := Finset.mem_singleton.1 hk
    obtain ⟨B, -, e⟩ := (hlev γ hm).1
    exact ⟨B, h6 γ hγ (Matrix.GeneralLinearGroup.det B) (e.trans (mul_one_by_one _ _)), e⟩
  · exact (unipRad_fix hu).trans (one_smul _ _).symm
  · have h2 : m ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
    simp only [Subgroup.mem_iInf] at h2
    obtain ⟨B, hB, e⟩ := h2 0 (Finset.mem_singleton_self _)
    exact ⟨Matrix.GeneralLinearGroup.det B, e.trans (mul_one_by_one _ _), hB⟩

end GlobalTheory.ResLine.LeviFacts
