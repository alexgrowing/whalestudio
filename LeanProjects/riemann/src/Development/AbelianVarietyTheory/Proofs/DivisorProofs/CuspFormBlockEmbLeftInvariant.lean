import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockLeft

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem yx_eq_one {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E} (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  have h := congrArg (cT (σ : E →+* E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_one] at h
  have e1 : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j; simp [cT, sigma_sigma hcm]
  have e2 : cT (σ : E →+* E) J = J := by
    ext i j; simp [cT, hJ.1]
  rw [e1, e2, ← Matrix.mul_assoc] at h
  exact h

def selMat (l d k : ℕ) : Matrix (Fin d) (Fin (k + 1)) E := Matrix.of fun a i => if l + a.val = i.val then 1 else 0

section Frame

variable (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) {l d : ℕ} (h : l + d ≤ r) (k : Fin r)

theorem blk_init_one {Y X : Matrix (Fin n) (Fin r) E} (hM : cT (σ : E →+* E) Y * J * X = 1) :
    cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * GlobalTheory.StdPar.initCols X k = selMat l d k.val := by
  ext a i
  have := congrFun (congrFun hM ⟨l + a.val, by omega⟩) (Fin.castLE k.2 i)
  rw [Matrix.one_apply] at this
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp [selMat, Fin.ext_iff]

theorem blk_init_zero {Y X : Matrix (Fin n) (Fin r) E} (hM : cT (σ : E →+* E) Y * J * X = 0) :
    cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * GlobalTheory.StdPar.initCols X k = 0 := by
  ext a i
  have := congrFun (congrFun hM ⟨l + a.val, by omega⟩) (Fin.castLE k.2 i)
  exact this

theorem selMat_eq_zero (hk : k.val < l) : (selMat (E := E) l d k.val) = 0 := by
  ext a i
  have := i.2
  simp only [selMat, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by omega)]

theorem init_mul_selMat (hk : l + d ≤ k.val + 1) (Z : Matrix (Fin n) (Fin r) E) :
    GlobalTheory.StdPar.initCols Z k * (selMat (E := E) l d k.val)ᵀ = GlobalTheory.BlockForms.blkCols h Z := by
  ext c a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (⟨l + a.val, by omega⟩ : Fin (k.val + 1))]
  · rw [if_pos rfl]; rfl
  · intro i _ hi
    rw [if_neg]
    intro e
    exact hi (Fin.ext e.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem selMat_mul_transpose (hk : l + d ≤ k.val + 1) :
    (selMat (E := E) l d k.val) * (selMat (E := E) l d k.val)ᵀ = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single (⟨l + b.val, by omega⟩ : Fin (k.val + 1))]
  · simp only [if_true]
    by_cases hab : a = b
    · simp [hab]
    · rw [if_neg hab, if_neg]
      intro e; exact hab (Fin.ext (by simpa using e))
  · intro i _ hi
    rw [if_neg]
    intro e
    exact hi (Fin.ext e.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

end Frame

section Block

variable {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  (h : l + d ≤ r)

theorem cT_inclR {p q : Type} (M : Matrix p q E) :
    cT (sigR (AF F) σ) (M.map (inclR (F := F) (AF F))) = (cT (σ : E →+* E) M).map (inclR (F := F) (AF F)) := by
  ext i j
  simp [cT, sigR, inclR]

omit [NumberField E] in
theorem mul_adMat_expand {m : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (A A' : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))
    (hM : M = 1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (A' - 1) * adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J))
    (C : Matrix (Fin n) (Fin m) E) :
    M * adMat F C = adMat F C + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * C) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (A' - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J * C) := by
  subst hM
  simp only [GlobalTheory.SiegelSet.adMat, Matrix.map_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [NumberField E] in
theorem mem_frameStab_of {kk : ℕ} (g : GAd σ J) (C : Matrix (Fin n) (Fin kk) E) (Z : Matrix (Fin n) (Fin d) E)
    (Q : Matrix (Fin d) (Fin kk) E) (A A₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (hA : A * A₁ = 1)
    (hg : (matHom _ σ J g).1 * adMat F C = adMat F C + adMat F Z * (A - 1) * adMat F Q)
    (hQ : Q = 0 ∨ (C * Qᵀ = Z ∧ Q * Qᵀ = 1)) : g ∈ GlobalTheory.StdPar.frameStab σ J C ⊤ := by
  rcases hQ with hQ | ⟨hCQ, hQQ⟩
  · refine ⟨1, Subgroup.mem_top _, ?_⟩
    rw [hg, hQ]
    simp
  · set P := adMat F Qᵀ with hP
    have hQP : adMat F Q * P = 1 := by
      rw [hP, GlobalTheory.SiegelSet.adMat, GlobalTheory.SiegelSet.adMat, ← Matrix.map_mul, hQQ]
      simp
    have key : ∀ N N₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), N + N₁ + N * N₁ = 0 →
        (1 + P * N * adMat F Q) * (1 + P * N₁ * adMat F Q) = 1 := by
      intro N N₁ hN
      have e : P * N * adMat F Q * (P * N₁ * adMat F Q) = P * (N * N₁) * adMat F Q := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (adMat F Q) P, hQP, Matrix.one_mul]
      calc (1 + P * N * adMat F Q) * (1 + P * N₁ * adMat F Q) = 1 + P * (N + N₁ + N * N₁) * adMat F Q := by
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e,
              Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
            abel
        _ = 1 := by rw [hN, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    have hN : (A - 1) + (A₁ - 1) + (A - 1) * (A₁ - 1) = 0 := by
      have : (A - 1) + (A₁ - 1) + (A - 1) * (A₁ - 1) = A * A₁ - 1 := by noncomm_ring
      rw [this, hA, sub_self]
    have hB := key _ _ hN
    refine ⟨⟨_, _, hB, mul_eq_one_comm.mp hB⟩, Subgroup.mem_top _, ?_⟩
    show _ = adMat F C * (1 + P * (A - 1) * adMat F Q)
    rw [hg, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, GlobalTheory.SiegelSet.adMat,
      GlobalTheory.SiegelSet.adMat, ← Matrix.map_mul, hCQ]

theorem mem_levi_of (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y)
    (S : Finset (Fin r)) (hS : ∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) (g : GAd σ J)
    (A A₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (hA : A * A₁ = 1)
    (hg : (matHom _ σ J g).1 = 1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (cT (sigR (AF F) σ) A₁ - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J)) :
    g ∈ GlobalTheory.StdPar.levi σ J X Y S := by
  simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Subgroup.mem_inf]
  intro k hk
  have hcase : k.val < l ∨ l + d ≤ k.val + 1 := by
    by_contra hc
    push_neg at hc
    exact hS k hc.1 (by omega) hk
  have hYX := yx_eq_one hcm hJ hW
  constructor
  · refine mem_frameStab_of g _ (GlobalTheory.BlockForms.blkCols h X) (selMat l d k.val) A A₁ hA ?_ ?_
    · rw [mul_adMat_expand h _ _ _ hg, blk_init_one σ J h k hYX, blk_init_zero σ J h k hW.xx]
      simp
    · rcases hcase with hc | hc
      · exact Or.inl (selMat_eq_zero k hc)
      · exact Or.inr ⟨init_mul_selMat h k hc X, selMat_mul_transpose k hc⟩
  · refine mem_frameStab_of g _ (GlobalTheory.BlockForms.blkCols h Y) (selMat l d k.val) (cT (sigR (AF F) σ) A₁)
      (cT (sigR (AF F) σ) A) (by rw [← Formalism.UG.cT_mul, hA, Formalism.UG.cT_one]) ?_ ?_
    · rw [mul_adMat_expand h _ _ _ hg, blk_init_zero σ J h k hW.yy, blk_init_one σ J h k hW.xy]
      simp
    · rcases hcase with hc | hc
      · exact Or.inl (selMat_eq_zero k hc)
      · exact Or.inr ⟨init_mul_selMat h k hc Y, selMat_mul_transpose k hc⟩

theorem mem_ratPts_of (g : GAd σ J) (M : Matrix (Fin n) (Fin n) E)
    (hM : (matHom _ σ J g).1 = M.map (inclR (F := F) (AF F)))
    (hinj : Function.Injective (inclR (F := F) (E := E) (AF F))) : g ∈ ratPts σ J := by
  haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨inclR (F := F) (AF F) 0, inclR (F := F) (AF F) 1, fun e => zero_ne_one (hinj e)⟩⟩
  have hdet : M.det ≠ 0 := by
    intro h0
    have hu : IsUnit (M.map (inclR (F := F) (AF F))).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := (inclR (F := F) (E := E) (AF F)).map_det M
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) M * J * M = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  rw [hM, cT_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end Block

end GlobalTheory.CuspBlockLeft

namespace GlobalTheory.CuspBlockLeft

theorem cuspForm_blockEmb_left_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        ∀ (γ : GL (Fin d) E) (g : GlobalTheory.CuspRep.GA E d), ψ (ι (GlobalTheory.CuspRep.ratGL E d γ * g) * g₀) = ψ (ι g * g₀) := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW K _ S l d h ι hι _ hS _ _ ψ hψ g₀ _ γ g
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)

  have hlevi : ∀ g' : GlobalTheory.CuspRep.GA E d, ι g' ∈ GlobalTheory.StdPar.levi σ J Xf Yf S := fun g' =>
    GlobalTheory.CuspBlockLeft.mem_levi_of h hcm hJ hW S hS (ι g') (g'.1.map Φ.symm) ((g'⁻¹).1.map Φ.symm)
      (by rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; simp) (hmat g')
  have hratPt : ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
    refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
        (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
      GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
        (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
    rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
    simp [Matrix.map_add, Matrix.map_sub, Matrix.map_mul, Matrix.map_one]
  rw [map_mul, mul_assoc]
  exact hψ.1.leftM _ hratPt (hlevi _) _

end GlobalTheory.CuspBlockLeft
