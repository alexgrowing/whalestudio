import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula

theorem relIndex_split {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (A B : AddSubgroup G) (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * A.relIndex (B ⊓ f.ker) := by
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ f.ker).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have h2 : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.mp hx
      obtain ⟨a, ha, k, hk, rfl⟩ := AddSubgroup.mem_sup.mp hx1
      refine AddSubgroup.mem_sup.mpr ⟨a, ha, k, AddSubgroup.mem_inf.mpr ⟨?_, hk⟩, rfl⟩
      have := B.sub_mem hx2 (hAB ha)
      simpa using this
    · refine sup_le (le_inf le_sup_left hAB) (le_inf ?_ inf_le_left)
      exact inf_le_right.trans le_sup_right
  have h3 : A.relIndex (A ⊔ (B ⊓ f.ker)) = A.relIndex (B ⊓ f.ker) :=
    AddSubgroup.relIndex_sup_left _ _
  have h4 := AddSubgroup.relIndex_mul_relIndex A ((A ⊔ f.ker) ⊓ B) B
    (le_inf le_sup_left hAB) inf_le_right
  rw [AddSubgroup.inf_relIndex_right, h2, h3] at h4
  rw [h1, ← h4, mul_comm]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_castSucc_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a b : Fin m) :
    blk σ c u d a.castSucc b.castSucc = c a b := by
  simp [blk]

theorem blk_castSucc_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a : Fin m) :
    blk σ c u d a.castSucc (Fin.last m) = u a := by
  simp [blk]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin (m + 1) → E) (i : Fin m) :
    (blk σ c u d).mulVec y i.castSucc
      = c.mulVec (fun j => y j.castSucc) i + y (Fin.last m) * u i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk_castSucc_castSucc,
    blk_castSucc_last]
  ring

variable [NumberField E]

def proj (E : Type) [Field E] [NumberField E] (m : ℕ) :
    (Fin (m + 1) → E) →ₗ[𝓞 E] (Fin m → E) :=
  LinearMap.funLeft (𝓞 E) E Fin.castSucc

@[simp] theorem proj_apply (m : ℕ) (v : Fin (m + 1) → E) (i : Fin m) :
    proj E m v i = v i.castSucc := rfl

theorem snoc_mem_intVec {m : ℕ} {y : Fin m → E} (hy : y ∈ intVec E m) (o : 𝓞 E) :
    (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E o) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨o, by simp⟩
  · obtain ⟨p, hp⟩ := hy j
    exact ⟨p, by simp [hp]⟩

theorem proj_mem_intVec {m : ℕ} {y : Fin (m + 1) → E} (hy : y ∈ intVec E (m + 1)) :
    proj E m y ∈ intVec E m := fun i => hy i.castSucc

theorem map_proj_intVec (m : ℕ) : (intVec E (m + 1)).map (proj E m) = intVec E m := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact proj_mem_intVec hy
  · intro y hy
    refine ⟨_, snoc_mem_intVec hy 0, ?_⟩
    funext i
    simp

theorem intVec_le_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : intVec E m ≤ lam c := le_sup_left

theorem mulVec_mem_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) {y : Fin m → E}
    (hy : y ∈ intVec E m) : c.mulVec y ∈ lam c :=
  Submodule.mem_sup_right ⟨y, hy, rfl⟩

theorem map_proj_lam {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) :
    (lam (blk σ c u d)).map (proj E m) = lam c ⊔ Submodule.span (𝓞 E) {u} := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, z, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨o, ho⟩ := hy (Fin.last m)
    have e : proj E m (x + (blk σ c u d).mulVecLin.restrictScalars (𝓞 E) y)
        = (proj E m x + c.mulVec (proj E m y)) + o • u := by
      funext i
      have := blk_mulVec_castSucc σ c u d y i
      simp only [proj_apply, Pi.add_apply, map_add, LinearMap.restrictScalars_apply,
        Matrix.mulVecLin_apply, Pi.smul_apply, Algebra.smul_def, ho]
      rw [this, add_assoc]
      rfl
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
    exact Submodule.add_mem _ (intVec_le_lam c (proj_mem_intVec hx))
      (mulVec_mem_lam c (proj_mem_intVec hy))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [← map_proj_intVec m]
      exact Submodule.map_mono (intVec_le_lam _)
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E 0)),
        mulVec_mem_lam _ (snoc_mem_intVec hy 0), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) 0 (algebraMap (𝓞 E) E 1)),
        mulVec_mem_lam _ (snoc_mem_intVec (Submodule.zero_mem _) 1), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp [show (fun _ : Fin m => (0 : E)) = 0 from rfl]

theorem relIndex_lam_sup {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) :
    (lam c).toAddSubgroup.relIndex (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = Ideal.absNorm (tor c u) := by
  let φ : 𝓞 E →+ (Fin m → E) := (LinearMap.toSpanSingleton (𝓞 E) _ u).toAddMonoidHom
  have hsup : (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = (lam c).toAddSubgroup ⊔ (⊤ : AddSubgroup (𝓞 E)).map φ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
      exact AddSubgroup.add_mem_sup ha ⟨t, trivial, rfl⟩
    · refine sup_le (fun x hx => Submodule.mem_sup_left hx) ?_
      rintro _ ⟨t, -, rfl⟩
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hcomap : (lam c).toAddSubgroup.comap φ = (tor c u).toAddSubgroup := by
    ext t
    change t • u ∈ lam c ↔ t ∈ tor c u
    rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  rw [hsup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.relIndex_comap, hcomap,
    AddSubgroup.relIndex_top_right]
  rfl

def lastInc (E : Type) [Field E] [NumberField E] (m : ℕ) : E →+ (Fin (m + 1) → E) :=
  (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m)).toAddMonoidHom

theorem comap_lastInc_intVec (m : ℕ) :
    (intVec E (m + 1)).toAddSubgroup.comap (lastInc E m)
      = (1 : Submodule (𝓞 E) E).toAddSubgroup := by
  ext x
  change (Pi.single (Fin.last m) x : Fin (m + 1) → E) ∈ intVec E (m + 1) ↔
    x ∈ (1 : Submodule (𝓞 E) E)
  rw [Submodule.mem_one]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h (Fin.last m)
    exact ⟨o, by simpa using ho⟩
  · rintro ⟨o, rfl⟩ i
    by_cases hi : i = Fin.last m
    · subst hi
      exact ⟨o, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hi]⟩

theorem map_lastInc_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).toAddSubgroup.map (lastInc E m)
      = (lam C).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [AddMonoidHom.mem_ker]
    funext i
    simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last]
  · intro hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hv
    rw [AddMonoidHom.mem_ker] at h2
    have hv' : lastInc E m (v (Fin.last m)) = v := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastInc]
      · have := congrFun h2 j
        simp only [LinearMap.toAddMonoidHom_coe, proj_apply, Pi.zero_apply] at this
        simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last, this]
    refine ⟨v (Fin.last m), ?_, hv'⟩
    change lastInc E m (v (Fin.last m)) ∈ lam C
    rw [hv']
    exact h1

theorem delta_blk (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  have hC := (GlobalTheory.T.delta_eq_lattice_index E (m + 1) (blk σ c u d)).2
  have hc := (GlobalTheory.T.delta_eq_lattice_index E m c).2
  have hsplit := relIndex_split (proj E m).toAddMonoidHom (intVec E (m + 1)).toAddSubgroup
    (lam (blk σ c u d)).toAddSubgroup (intVec_le_lam (blk σ c u d))
  have hA : (intVec E (m + 1)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (intVec E m).toAddSubgroup := by
    rw [← map_proj_intVec m]; rfl
  have hB : (lam (blk σ c u d)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup := by
    rw [← map_proj_lam σ c u d]; rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex (intVec E m).toAddSubgroup
    (lam c).toAddSubgroup (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
    (intVec_le_lam c) (fun x hx => Submodule.mem_sup_left hx)
  have hfib : (intVec E (m + 1)).toAddSubgroup.relIndex
      ((lam (blk σ c u d)).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker)
      = idx E (lastFib (blk σ c u d)) := by
    rw [← map_lastInc_lastFib, ← AddSubgroup.relIndex_comap, comap_lastInc_intVec]
    rfl
  rw [hC, hc, hsplit, hA, hB, hfib, ← hmul, relIndex_lam_sup]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula
