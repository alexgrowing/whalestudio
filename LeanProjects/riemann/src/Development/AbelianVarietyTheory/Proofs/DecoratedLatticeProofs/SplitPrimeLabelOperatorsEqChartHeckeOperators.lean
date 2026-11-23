import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (opOf hyp)

noncomputable section

namespace GlobalTheory.ChainOnto.LabChart

variable {D : D7}

theorem opOf_eq_sum_rep {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) {a : GL (Fin V.rank) (w.adicCompletion D.host.E)} (ha : IsFrameAt w (frameLat V) a)
    {g : Gv V v} {d : Fin V.rank → ℤ} (hd : Antitone d) {u : Fin V.rank → w.adicCompletion D.host.E}
    (hu : ∀ i, Valued.v (u i) = WithZero.exp (-d i))
    (hg : (a⁻¹ * locMat D.sp.cm.sig V.gram h g * a).1 = Matrix.diagonal u)
    {R0 : Finset (Gv V v)} (r1 : ∀ γ ∈ R0, ∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, γ = k₁ * g * k₂)
    (r2 : ∀ x, (∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, x = k₁ * g * k₂) → ∃! γ, γ ∈ R0 ∧ γ⁻¹ * x ∈ Kv V v)
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (x : M)
    (hx : ∀ k ∈ Kv V v, π (embV V v k) x = x) :
    opOf π w (Finsupp.single (List.ofFn d) 1) x = ∑ γ ∈ R0, π (embV V v γ) x := by
  classical
  obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) w
  obtain ⟨ϖ, p1, p2⟩ : ∃ ϖ ∈ w.asIdeal, ϖ ∉ w.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  have hs := Supp.suppF_iff_of_isPrimeIdem V hef h
  have hK : ∀ y, y ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ ∃ k ∈ Kv V v, embV V v k = y := fun y => by
    constructor
    · rintro ⟨m1, m2⟩
      obtain ⟨k, rfl⟩ := (hs y).1 m2
      exact ⟨k, (Supp.emb_mem_KsphC V k).1 m1, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Supp.emb_mem_KsphC V k).2 hk, (hs _).2 ⟨k, rfl⟩⟩
  obtain ⟨s1, s2⟩ := rep_image (embV V v) (emb_injective _ _ v) hK r1 r2
  have hR : GlobalTheory.Hk3.SphOp V w (List.ofFn d) (R0.image (embV V v)) := by
    refine ⟨e, f, ϖ, embV V v g, ?_, hef, p1, p2, List.pairwise_ofFn.2 fun i j hij => hd hij.le, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, (hs _).2 ⟨g, rfl⟩, divAt_of_diagonal h hef p1 p2 ha hu (by rw [proj_emb_self, hg]),
      fun γ hγ => ?_, fun γ hγ => ⟨?_, s1 γ hγ⟩, s2⟩
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact (hs _).2 ⟨y, rfl⟩
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y)
  have hhyp : ∀ k ∈ hyp V w, π k x = x := by
    rintro k ⟨hk, e', f', hef', hsf⟩
    obtain ⟨y, rfl⟩ := (Supp.suppF_iff_of_isPrimeIdem V hef' h k).1 hsf
    exact hx y ((Supp.emb_mem_KsphC V y).1 hk)
  rw [← ((GlobalTheory.SphLabelOps.label_operators V w).1 _ _ hR).2 M π x hhyp, Finset.sum_image (emb_injective _ _ v).injOn]

end GlobalTheory.ChainOnto.LabChart

noncomputable section

namespace GlobalTheory.ChainOnto.LabChart

variable {D : D7}

theorem heckeVec_chart {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {h : w.under (𝓞 D.host.F) = v} {e : Gv V v ≃* GL (Fin V.rank) (w.adicCompletion D.host.E)}
    (he : IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) (t : GL (Fin V.rank) (w.adicCompletion D.host.E))
    {R0 : Finset (Gv V v)} (r1 : ∀ γ ∈ R0, ∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, γ = k₁ * e.symm t * k₂)
    (r2 : ∀ x, (∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, x = k₁ * e.symm t * k₂) → ∃! γ, γ ∈ R0 ∧ γ⁻¹ * x ∈ Kv V v)
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (x : M)
    (hx : ∀ k ∈ Kv V v, π (embV V v k) x = x) :
    heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (Formalism.UG.dosetInd ℂ (KGL w V.rank) t) x =
      ∑ γ ∈ R0, π (embV V v γ) x := by
  classical
  have hK : ∀ y, y ∈ (KGL w V.rank : Set (GL (Fin V.rank) (w.adicCompletion D.host.E))) ↔
      ∃ k ∈ Kv V v, e.toMonoidHom k = y := fun y =>
    ⟨fun hy => ⟨e.symm y, (he.2 _).2 (by simpa using hy), by simp⟩, by rintro ⟨k, hk, rfl⟩; exact (he.2 k).1 hk⟩
  obtain ⟨s1, s2⟩ := rep_image e.toMonoidHom e.injective hK r1 r2
  have ht : e.toMonoidHom (e.symm t) = t := by simp
  rw [ht] at s1 s2
  have hfix : x ∈ fixed ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) :=
    (mem_fixed_comp_symm e he.2).2 (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hx k hk)
  rw [heckeVec_dosetInd hfix (R := R0.image e.toMonoidHom) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (s1 γ hγ))
    fun y hy => s2 y (DoubleCoset.mem_doubleCoset.1 hy),
    Finset.sum_image (f := fun γ => (((π.comp (embV V v)).comp e.symm.toMonoidHom) γ) x) (show Function.Injective e.toMonoidHom from e.injective).injOn]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp

end GlobalTheory.ChainOnto.LabChart

noncomputable section

namespace GlobalTheory.ChainOnto.LabChart

variable {D : D7}

section Perm

variable {L : Type} [Field L] {n : ℕ}

def revM (L : Type) [Field L] (n : ℕ) : Matrix (Fin n) (Fin n) L := fun i j => if i.rev = j then 1 else 0

theorem revM_mul (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (revM L n * A) i j = A i.rev j := by
  simp [revM, Matrix.mul_apply]

theorem mul_revM (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * revM L n) i j = A i j.rev := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp [revM]
  · intro b _ hb
    have : b.rev ≠ j := fun e => hb (by rw [← e, Fin.rev_rev])
    simp [revM, this]
  · simp

theorem revM_mul_revM : revM L n * revM L n = 1 := by
  ext i j
  rw [revM_mul, revM, Matrix.one_apply, Fin.rev_rev]

def revGL (L : Type) [Field L] (n : ℕ) : GL (Fin n) L := ⟨revM L n, revM L n, revM_mul_revM, revM_mul_revM⟩

theorem revGL_mem (O : Subring L) : revGL L n ∈ Formalism.UG.GLint (Fin n) O := by
  refine Formalism.UG.P.cartan_mem_of_entries O _ (fun i j => ?_) (fun i j => ?_) <;>
  · change revM L n i j ∈ O
    unfold revM
    split_ifs
    · exact one_mem O
    · exact zero_mem O

theorem revGL_conj_diagonal (u : Fin n → L) (hu : ∀ i, u i ≠ 0) :
    ((revGL L n * Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal u)
      (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i) * revGL L n :
        GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => u i.rev) := by
  ext i j
  change (revM L n * Matrix.diagonal u * revM L n) i j = _
  rw [mul_revM, revM_mul]
  by_cases hij : i = j
  · subst hij; simp
  · have : i.rev ≠ j.rev := fun e => hij (Fin.rev_injective e)
    simp [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ this]

end Perm

end GlobalTheory.ChainOnto.LabChart

noncomputable section

namespace GlobalTheory.ChainOnto.LabChart

theorem split_label_ops : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ Kv V v, π (embV V v k) u = u) → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ V.rank, opOf π w (Finsupp.single (splitLab V.rank k) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (fun g => Tj ℂ V.rank (Ov D.host.E w) ϖ k g⁻¹) u ∧ opOf π w (Finsupp.single (dualLab (splitLab V.rank k)) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (Tj ℂ V.rank (Ov D.host.E w) ϖ k) u := by
  intro D V v w h _ e he M _ _ π x hx ϖ hϖ k hk
  classical
  obtain ⟨a, ha, hea⟩ := he.1
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have key : ∀ (d : Fin V.rank → ℤ) (t : GL (Fin V.rank) (w.adicCompletion D.host.E))
      (uu : Fin V.rank → w.adicCompletion D.host.E), Antitone d → (∀ i, Valued.v (uu i) = WithZero.exp (-d i)) →
      t.1 = Matrix.diagonal uu →
      opOf π w (Finsupp.single (List.ofFn d) 1) x =
        heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (Formalism.UG.dosetInd ℂ (KGL w V.rank) t) x := by
    intro d t uu hd hu ht
    obtain ⟨R0, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) (e.symm t)
    have hg : (a⁻¹ * locMat D.sp.cm.sig V.gram h (e.symm t) * a).1 = Matrix.diagonal uu := by
      rw [← hea, MulEquiv.apply_symm_apply, ht]
    rw [opOf_eq_sum_rep h ha hd hu hg r1 r2 π x hx, heckeVec_chart he t r1 r2 π x hx]
  set n := V.rank with hn
  set tJ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n ϖ k) (GlobalTheory.SatHecke.diagJ_det_ne hϖ k) with htJ
  have hTj : Tj ℂ n (Ov D.host.E w) ϖ k = Formalism.UG.dosetInd ℂ (KGL w n) tJ := GlobalTheory.SatHecke.Tj_eq_dosetInd hϖ k

  have hJ := key (fun i => if (i : ℕ) < k then 1 else 0) tJ (fun i => if (i : ℕ) < k then ϖ else 1)
    (fun i j hij => by
      have hij' : (i : ℕ) ≤ j := hij
      by_cases h1 : (i : ℕ) < k <;> by_cases h2 : (j : ℕ) < k <;> simp only [h1, h2, if_true, if_false] <;> omega)
    (fun i => by by_cases h1 : (i : ℕ) < k <;> simp [h1, hv])
    (by rw [htJ]; rfl)
  have hlJ : List.ofFn (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) = dualLab (splitLab n k) := by
    refine List.ext_getElem (by simp [dualLab, splitLab]; omega) fun i h1 h2 => ?_
    have := GlobalTheory.SphPar.dualLab_splitLab_getD n k i
    rw [List.getD_eq_getElem _ _ h2] at this
    simp [this]

  have huS : ∀ i : Fin n, (if n - k ≤ (i : ℕ) then ϖ⁻¹ else 1) ≠ 0 := fun i => by
    split_ifs
    · exact inv_ne_zero hϖ0
    · exact one_ne_zero
  set tS := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i : Fin n => if n - k ≤ (i : ℕ) then ϖ⁻¹ else 1)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => huS i) with htS
  have hS := key (fun i => if n - k ≤ (i : ℕ) then -1 else 0) tS (fun i => if n - k ≤ (i : ℕ) then ϖ⁻¹ else 1)
    (fun i j hij => by
      have hij' : (i : ℕ) ≤ j := hij
      by_cases h1 : n - k ≤ (i : ℕ) <;> by_cases h2 : n - k ≤ (j : ℕ) <;> simp only [h1, h2, if_true, if_false] <;> omega)
    (fun i => by by_cases h1 : n - k ≤ (i : ℕ) <;> simp [h1, hv])
    (by rw [htS]; rfl)
  have hlS : List.ofFn (fun i : Fin n => if n - k ≤ (i : ℕ) then (-1 : ℤ) else 0) = splitLab n k := by
    refine List.ext_getElem (by simp [splitLab]; omega) fun i h1 h2 => ?_
    simp only [List.getElem_ofFn, splitLab]
    by_cases hi : n - k ≤ i
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [hi]
    · rw [List.getElem_append_left (by simp; omega)]
      simp [hi]
  have hinv : tJ⁻¹ = revGL _ n * tS * revGL _ n := by
    refine (eq_inv_of_mul_eq_one_right (Units.ext ?_)).symm
    rw [Units.val_mul, htS, revGL_conj_diagonal _ huS, Units.val_one, htJ]
    change Formalism.UG.diagJ n ϖ k * _ = 1
    rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have e1 : (n - k ≤ (i.rev : ℕ)) ↔ (i : ℕ) < k := by rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < k
    · rw [if_pos h1, if_pos (e1.2 h1), mul_inv_cancel₀ hϖ0]
    · rw [if_neg h1, if_neg (mt e1.1 h1), mul_one]
  have hTinv : (fun g => Tj ℂ n (Ov D.host.E w) ϖ k g⁻¹) = Formalism.UG.dosetInd ℂ (KGL w n) tS := by
    rw [hTj, GlobalTheory.ChainOnto.dosetInd_comp_inv, hinv, dosetInd_mul (revGL_mem _) (revGL_mem _)]
  refine ⟨?_, ?_⟩
  · rw [← hlS, hS, hTinv]
  · rw [← hlJ, hJ, hTj]

end GlobalTheory.ChainOnto.LabChart
