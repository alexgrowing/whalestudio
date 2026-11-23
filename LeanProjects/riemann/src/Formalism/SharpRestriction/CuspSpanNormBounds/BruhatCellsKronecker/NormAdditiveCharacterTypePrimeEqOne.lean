import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ProductLValuesPolynomialBound
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
import Formalism.FlagUnipotentLattices.ValuationProductBound

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Schur

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem Kset_sub_UJset (k : ℕ) {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset (allPos k)) :
    g ∈ UJset (allPos k) := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show g.conjTranspose * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [Jm_allPos, Matrix.mul_one]
  exact h1

def htF {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ a : Fin k, -((a : ℕ) : ℝ) * x a

theorem htF_root {k : ℕ} (a b : Fin k) : htF (Formalism.REAL.root a b) = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
  unfold htF Formalism.REAL.root
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem htF_sum {k : ℕ} (c : Fin k → Fin k → ℕ) :
    htF (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) = ∑ a, ∑ b, (c a b : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  have hadd : ∀ x y : Fin k → ℝ, htF (x + y) = htF x + htF y := by
    intro x y; unfold htF; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by simp [mul_add])
  have hsm : ∀ (t : ℝ) (x : Fin k → ℝ), htF (t • x) = t * htF x := by
    intro t x; unfold htF; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by simp; ring)
  have h0 : htF (0 : Fin k → ℝ) = 0 := by unfold htF; simp
  let φ : (Fin k → ℝ) →+ ℝ := ⟨⟨htF, h0⟩, hadd⟩
  have e : ∀ x, htF x = φ x := fun _ => rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← e, hsm, htF_root]

theorem cdom_antisymm {k : ℕ} {ε : Fin k → Bool} {μ Λ : Fin k → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) : μ = Λ := by
  obtain ⟨c, hc, e1⟩ := h1
  obtain ⟨c', hc', e2⟩ := h2
  have hs : htF (Λ - μ) + htF (μ - Λ) = 0 := by
    unfold htF; rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero (fun i _ => by simp; ring)
  rw [e1, e2, htF_sum, htF_sum] at hs
  have nn : ∀ (d : Fin k → Fin k → ℕ), (∀ a b, d a b ≠ 0 → a < b ∧ ε a = ε b) →
      ∀ a b, 0 ≤ (d a b : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    intro d hd a b
    by_cases h : d a b = 0
    · simp [h]
    · have := (hd a b h).1
      have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have s1 : 0 ≤ ∑ a, ∑ b, (c a b : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => nn c hc a b))
  have s2 : 0 ≤ ∑ a, ∑ b, (c' a b : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => nn c' hc' a b))
  have z1 : ∑ a, ∑ b, (c a b : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = 0 := by linarith
  have z2 : ∀ a b, c a b = 0 := by
    intro a b
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => nn c hc a b))).1 z1 a
      (Finset.mem_univ a)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => nn c hc a b)).1 h3 b (Finset.mem_univ b)
    by_contra h
    have := (hc a b h).1
    have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact h (by exact_mod_cast h5)
    · linarith
  have : Λ - μ = 0 := by
    rw [e1]; exact Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by simp [z2 a b]))
  exact (sub_eq_zero.1 this).symm

theorem schur_lemma_unitary_distinct_params : NonGenericAndKTwoTheorems.adm7 := by
  intro k u u' H H' _ _ _ _ π ρ hπ hρ hne P hP
  obtain ⟨_, _, _, _, hπs, hπi, ⟨v, _, hv0, hvw⟩, hπd⟩ := hπ
  obtain ⟨_, _, _, _, hρs, hρi, ⟨v', _, hv'0, hv'w⟩, hρd⟩ := hρ
  by_contra hP0
  have comm : ∀ g ∈ Formalism.REAL.Kset (allPos k), ∀ x, P (ρ g x) = π g (P x) := by
    intro g hg x
    have := hP g (Kset_sub_UJset k hg)
    exact congrArg (fun T : H' →L[ℂ] H => T x) this

  have hker : LinearMap.ker (P : H' →ₗ[ℂ] H) = ⊥ := by
    rcases hρi (LinearMap.ker (P : H' →ₗ[ℂ] H)) le_top (by
      intro g hg x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hx' : P x = 0 := hx
      show P (ρ g x) = 0
      rw [comm g hg, hx', map_zero]) with h | h
    · exact h
    · exfalso
      apply hP0
      ext x
      have : x ∈ LinearMap.ker (P : H' →ₗ[ℂ] H) := by rw [h]; trivial
      exact this
  have hinj : Function.Injective P := by
    have := LinearMap.ker_eq_bot.1 hker
    exact this

  have hran : LinearMap.range (P : H' →ₗ[ℂ] H) = ⊤ := by
    rcases hπi (LinearMap.range (P : H' →ₗ[ℂ] H)) le_top (by
      rintro g hg _ ⟨x, rfl⟩
      exact ⟨ρ g x, comm g hg x⟩) with h | h
    · exfalso
      have : P v' ∈ LinearMap.range (P : H' →ₗ[ℂ] H) := ⟨v', rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hv'0 (hinj (by rw [this, map_zero]))
    · exact h

  have d1 : CDom (allPos k) (Formalism.QuantumDeterminants.lowK (allPos k) u') (Formalism.QuantumDeterminants.lowK (allPos k) u) := by
    refine hπd _ (P v') trivial (fun h => hv'0 (hinj (by rw [h, map_zero]))) ?_
    intro θ hθ
    rw [← comm _ hθ, hv'w θ hθ, map_smul]

  have d2 : CDom (allPos k) (Formalism.QuantumDeterminants.lowK (allPos k) u) (Formalism.QuantumDeterminants.lowK (allPos k) u') := by
    obtain ⟨w, hw⟩ : v ∈ LinearMap.range (P : H' →ₗ[ℂ] H) := by rw [hran]; trivial
    have hw' : P w = v := hw
    refine hρd _ w trivial (fun h => hv0 (by rw [← hw', h, map_zero])) ?_
    intro θ hθ
    apply hinj
    rw [comm _ hθ, hw', hvw θ hθ, map_smul, hw']
  have e := cdom_antisymm d1 d2
  apply hne
  unfold Formalism.QuantumDeterminants.lowK at e
  funext a
  have := congrFun e a
  simp only [Pi.add_apply, Pi.sub_apply] at this
  linarith

end Schur

section Mass

theorem stMassRatio_of_siegel (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : UnitaryVolumeMass.stMassRatio D :=
  fun j hj V V' _ _ _ _ _ _ _ _ hh hh' L L' s s' o o' =>
    h D.host.E D.sp.cm.cmUnram j hj V V' hh hh' L L' s s' o o'

theorem mass_ratio_ninth_of_siegel (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : NonGenericAndKTwoTheorems.IntegrationByPartsAlt D := stMassRatio_of_siegel h D

variable {eps : ℝ} (Fm : FamP eps)

theorem family_mass_ratio_of_siegel_bis (h : AdmissibleBoundsFromSource.FamilyTwelfthHypothesis) : NonGenericAndKTwoTheorems.FamilyMassFirstHypothesis Fm := fun _ _ => stMassRatio_of_siegel h _
theorem mass_one_bound_of_siegel_restricted (h : AdmissibleBoundsFromSource.FamilyTwelfthHypothesis) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun _ _ => stMassRatio_of_siegel h _
theorem family_mass_ratio_first_of_siegel (h : AdmissibleBoundsFromSource.FamilyTwelfthHypothesis) : AuxiliaryNormPrimes.SecondSizeStatement Fm := fun _ _ => stMassRatio_of_siegel h _

theorem mass_two_bound_restricted_of_family (h : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm) : LocalBesselAndTopKernel.BesselFormLine Fm := fun x i j hj => h x i j (by omega)
theorem family_mass_two_bound_of_mass_ratio (h : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm) : AuxiliaryNormPrimes.BesselFormLine Fm := fun x i => h x i
theorem family_mass_ratio_of_mass_two_bound (h : AuxiliaryNormPrimes.BesselFormLine Fm) : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm := fun x i => h x i

end Mass

section NG

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem R_eq_O (hs : M.split = none) : M.R = M.L.O := by
  unfold Model.R
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem theta_eq_one (hs : M.split = none) : theta M = 1 := by
  unfold theta
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem modK_unitO (hOK : M.OK) (hs : M.split = none) {x : E} (hx : IsUnitO M x) : M.modK x = 1 := by
  obtain ⟨hx, y, hy, hxy⟩ := hx
  have hR := R_eq_O hs
  have himg : (fun z => x * z) '' (M.R : Set E) = (M.R : Set E) := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact M.L.O.mul_mem hx hw
    · intro hz
      exact ⟨y * z, M.L.O.mul_mem hy hz, by show x * (y * z) = z; rw [← mul_assoc, hxy, one_mul]⟩
  unfold Model.modK
  rw [himg, hOK.haar.volR]
  rfl

theorem isUnitO_one : IsUnitO M (1 : E) := ⟨M.L.O.one_mem, 1, M.L.O.one_mem, one_mul 1⟩

theorem isUnitO_mul {x y : E} (hx : IsUnitO M x) (hy : IsUnitO M y) : IsUnitO M (x * y) := by
  obtain ⟨hx, x', hx', e⟩ := hx
  obtain ⟨hy, y', hy', e'⟩ := hy
  exact ⟨M.L.O.mul_mem hx hy, x' * y', M.L.O.mul_mem hx' hy', by
    calc x * y * (x' * y') = (x * x') * (y * y') := by ring
      _ = 1 := by rw [e, e', one_mul]⟩

theorem isUnitO_neg_one_pow (n : ℕ) : IsUnitO M ((-1 : E) ^ n) :=
  ⟨M.L.O.pow_mem (M.L.O.neg_mem M.L.O.one_mem) n, (-1) ^ n, M.L.O.pow_mem (M.L.O.neg_mem M.L.O.one_mem) n, by
    rw [← mul_pow]; simp⟩

theorem isUnitO_cj {x : E} (hx : IsUnitO M x) : IsUnitO M (M.L.cj x) := by
  obtain ⟨hx, y, hy, e⟩ := hx
  exact ⟨Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L x hx, M.L.cj y, Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L y hy, by
    rw [← map_mul, e, map_one]⟩

variable {H : HermSp M V} {r : ℕ}

theorem MMgen_eq (P : FPair H r) (hs : M.split = none) : P.MMgen = Sum.elim P.A.f P.B.f := by
  unfold FPair.MMgen HermSp.MMfam
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem gram_det_eq (P : FPair H r) (hs : M.split = none) :
    (H.gram P.MMgen).det = (-1) ^ (r + 1) * P.Gv := by
  set c : E →+* E := (M.L.cj : E ≃ₐ[F] E).toAlgHom.toRingHom with hc
  have hcx : ∀ x, c x = M.L.cj x := fun _ => rfl
  set Zh := H.Zhat P.A.f P.B.f with hZh
  have hG : H.gram (Sum.elim P.A.f P.B.f) =
      Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.A.T) else 0) Zh
        (Zh.transpose.map c) (Matrix.diagonal fun i => if i = Fin.last r then -(algebraMap F E P.B.T) else 0) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.A.h_zz]
        · simp [ha, P.A.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.A.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.A.h_iso b a (Or.inr ha)
    · simp [HermSp.gram, hZh, HermSp.Zhat]
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Matrix.map_apply,
        Matrix.transpose_apply, hZh, HermSp.Zhat, hcx]
      exact H.h_herm _ _
    · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = Fin.last r
        · subst ha; simp [P.B.h_zz]
        · simp [ha, P.B.h_iso a a (Or.inl ha)]
      · rw [if_neg hab]
        by_cases ha : a = Fin.last r
        · exact P.B.h_iso b a (Or.inl (fun h => hab (by rw [ha, h])))
        · exact P.B.h_iso b a (Or.inr ha)
  rw [MMgen_eq P hs, hG, Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramDetGen E r (Zh.transpose.map c) Zh]
  have d1 : (Zh.transpose.map c).det = M.L.cj Zh.det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have d2 : ((Zh.transpose.map c).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [← hcx, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  have e1 : P.Dm (r + 1) = Zh.det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos le_rfl]
    rfl
  have e2 : P.Dm r = (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
    rfl
  rw [d1, d2]
  unfold FPair.Gv HermSp.Gdet HermSp.normE
  change _ = (-1) ^ (r + 1) * (P.Dm (r + 1) * M.L.cj (P.Dm (r + 1)) - algebraMap F E (P.A.T * P.B.T) * (P.Dm r * M.L.cj (P.Dm r)))
  rw [e1, e2, map_mul]
  ring

theorem NG_Hp_one (hOK : M.OK) (P : FPair H r) (hP : P.PrimeTo) : P.Hp = 1 := by
  obtain ⟨hs, hG, hD⟩ := hP
  unfold FPair.Hp
  have h1 : M.modK (algebraMap F E (theta M)) = 1 := by
    rw [theta_eq_one hs, map_one]; exact modK_unitO hOK hs isUnitO_one
  have h2 : M.modK (H.gram P.MMgen).det = 1 := by
    rw [gram_det_eq P hs]; exact modK_unitO hOK hs (isUnitO_mul (isUnitO_neg_one_pow _) hG)
  have h3 : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = 1 :=
    Finset.prod_eq_one (fun l hl => modK_unitO hOK hs (isUnitO_mul (hD l hl) (isUnitO_cj (hD l hl))))
  rw [h1, h2, h3]
  simp

end NG

section K2

open Formalism.MainNotions.S.Cnt

theorem k_parameter_bound_of_hypotheses (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hH : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hk : Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) : NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT := by
  obtain ⟨_, _, _, _, hlf, _, _, _, _, _, hrd, hg1, hg1', hg2, hg2', _, _, _, _, _, _, hgap, hT, hClm, hCl⟩ := hH.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hTg⟩ := hH.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  refine ⟨hk, Fin.forall_fin_two.2 ⟨⟨hg1, hg1'⟩, ⟨hg2, hg2'⟩⟩, ?_, ?_, ?_, ?_, D.sp.cm.cmUnram⟩
  · intro τ a c hac
    have hG : 0 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    have h1 := abs_gap_of_consec (lamS D.R (D.hc τ)) _ hG (hgap τ) a c hac
    refine lt_of_le_of_lt ?_ h1
    have h3 : (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
    have h4 : Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 0 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  · rw [le_div_iff₀ hCl] at hrd
    linarith
  · have hf2 : (2 : ℝ) ≤ D.R.f := by
      have : 2 ≤ D.R.f := by
        unfold Ranks.f Ranks.n
        have := D.R.ord_pos
        omega
      exact_mod_cast this
    have hlf0 : 0 < Real.log (D.R.f : ℝ) := Real.log_pos (by linarith)
    rcases Nat.eq_zero_or_pos D.R.rS with h0 | h0
    · exfalso
      rw [h0] at hlf
      simp at hlf
      linarith
    · have hr1 : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast h0
      refine le_trans hlf (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
      have : ((D.R.rS : ℝ) ^ 2) ^ 2 = (D.R.rS : ℝ) ^ 4 := by ring
      rw [this]
      exact le_self_pow₀ hr1 (by norm_num)
  · intro u
    refine ⟨(hT u).2, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime 0)).2 (hTg u).1
    · exact (Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime 1)).2 (hTg u).2

variable {eps : ℝ} (Fm : FamP eps)

theorem eventually_hypotheses_K2_of_scale (Cg cb Cu cT CT C0 : ℝ) :
    OwnEv Fm fun C' Cl x i => Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      NonGenericAndKTwoTheorems.KTwoHypotheses (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
  have he := eps_pos Fm
  obtain ⟨x0, _, hx0⟩ := ev_rpow (show 0 < eps / 100 by positivity) (sCl Fm)
  refine ownEv_intro Fm x0 (fun x hx hx1 i hH => ⟨hH, k_parameter_bound_of_hypotheses _ _ _ _ _ _ _ _ _ _ hH ?_⟩)
  have hs := (Fm.sizes x hx1 i).2.2.2.1.2.2.2.2.2.2.1
  unfold szTh at hs
  rw [Fm.L_x x i hx1, Fm.L_eps] at hs
  refine le_trans ?_ hs
  have hL : 0 ≤ (Fm.L x i).sc.L := by unfold Scale.L; exact Real.rpow_nonneg (le_of_lt (lt_trans one_pos (Fm.L x i).sc.one_lt_alt)) _
  have := hx0 x hx
  gcongr

theorem kernel_square_bound_under_hypotheses (h : NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummability Fm) (Cg cb Cu cT CT C0 : ℝ) :
    OwnEv Fm fun C' Cl x i => Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      (∀ u : (Fm.D x i).what₂.Word,
        Summable (fun t : NonGenericAndKTwoTheorems.TermsPP (Fm.D x i) u u => (Fm.D x i).s.aTerm u u t.1) ∧
        hsNormSq (NonGenericAndKTwoTheorems.Kpp (Fm.D x i) u u) ≤ ((Fm.D x i).duS u : ℝ) *
          Real.exp (-(((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.f * Real.log (Fm.D x i).R.k))) ∧
      ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' →
        ∀ t : (Fm.D x i).s.Term u u', (Fm.D x i).s.Gterm t = 0 → (Fm.D x i).s.aTerm u u' t = 0 :=
  OwnEv.mono (fun _ _ _ _ hh hH => ⟨hh.1.1 (hh.2 hH), hh.1.2 (hh.2 hH)⟩)
    (((h.1 Cg cb Cu cT CT C0).and (h.2 Cg cb Cu cT CT C0)).and (eventually_hypotheses_K2_of_scale Fm Cg cb Cu cT CT C0))

def TheoremK2PairBound (D : D7) (u : D.what₂.Word) : Prop :=
  Summable (fun p : pairsIn D.s (NonGenericAndKTwoTheorems.TermsPP D u u) => ‖D.s.pval p.1‖) ∧
    (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D *
        (∑' p : pairsIn D.s (NonGenericAndKTwoTheorems.TermsPP D u u), D.s.pval p.1).re ≤
      (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def RelevantZeroTermsVanish (D : D7) : Prop :=
  ∀ u u' : D.what₂.Word, u ≠ u' → ∀ t : D.s.Term u u', D.s.relevant t → D.s.Gterm t = 0 → D.s.aTerm u u' t = 0

theorem kernel_second_part_of_pair_bound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (h1 : NonGenericAndKTwoTheorems.adm1 D large₂ C' Cl Cg cb Cu cT CT C0) (h2 : NonGenericAndKTwoTheorems.adm2 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hB : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, TheoremK2PairBound D u) :
    NonGenericAndKTwoTheorems.Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH u
  have := FiniteDimensional.complete ℂ (D.s.Cu u)
  refine ⟨?_, le_trans (h1 hH.1 u u (NonGenericAndKTwoTheorems.TermsPP D u u) (Or.inr (Or.inr (Or.inl rfl))) (hB hH u).1) (hB hH u).2⟩
  have hs : Summable (fun t : D.s.Term u u => ‖D.s.aTerm u u t‖) := (h2 hH.1 u u).2
  exact (hs.subtype (NonGenericAndKTwoTheorems.TermsPP D u u)).of_norm

theorem kernel_third_part_of_relevant_case (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (h4 : NonGenericAndKTwoTheorems.ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0)
    (hR : NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → RelevantZeroTermsVanish D) :
    NonGenericAndKTwoTheorems.PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH u u' hne t ht
  by_cases hr : D.s.relevant t
  · exact hR hH u u' hne t hr ht
  · exact h4 hH.1 u u' t hr

theorem theorem_K2_of_pair_bounds (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)
    (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM : ℝ)
    (hB : NonGenericAndKTwoTheorems.admitted D large₂ X Gv C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM →
      NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → (∀ u, TheoremK2PairBound D u) ∧ RelevantZeroTermsVanish D) :
    NonGenericAndKTwoTheorems.NonIdentityTermSummabilityOfAdmissible D large₂ X Gv C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM := fun hA =>
  ⟨kernel_second_part_of_pair_bound D large₂ _ _ _ _ _ _ _ _ hA.1 hA.2.1 (fun hH => (hB hA hH).1),
    kernel_third_part_of_relevant_case D large₂ _ _ _ _ _ _ _ _ hA.2.2.2.1 (fun hH => (hB hA hH).2)⟩

theorem theorem_K2_family_of_pair_bounds (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))
    (hB : NonGenericAndKTwoTheorems.AdmF Fm At Gv → ∀ Cg cb Cu cT CT C0 : ℝ, OwnEv Fm fun C' Cl x i =>
      NonGenericAndKTwoTheorems.KTwoHypotheses (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
        (∀ u, TheoremK2PairBound (Fm.D x i) u) ∧ RelevantZeroTermsVanish (Fm.D x i)) :
    NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummabilityOfAdmissible Fm At Gv := fun hA =>
  ⟨fun Cg cb Cu cT CT C0 => OwnEv.mono
      (fun _ _ _ _ hh => kernel_second_part_of_pair_bound _ _ _ _ _ _ _ _ _ _ hh.1.1 hh.1.2 (fun hH => (hh.2 hH).1))
      (((hA.1 Cg cb Cu cT CT C0).and (hA.2.1 Cg cb Cu cT CT C0)).and (hB hA Cg cb Cu cT CT C0)),
    fun Cg cb Cu cT CT C0 => OwnEv.mono
      (fun _ _ _ _ hh => kernel_third_part_of_relevant_case _ _ _ _ _ _ _ _ _ _ hh.1 (fun hH => (hh.2 hH).2))
      ((hA.2.2.2.1 Cg cb Cu cT CT C0).and (hB hA Cg cb Cu cT CT C0))⟩

end K2

section Copies

theorem k_parameter_bound_unfolded_of_hyps (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hk : Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) : UnitaryVolumeMass.KTwoParameterConditions D large₂ Cl Cg CT :=
  k_parameter_bound_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 hH hk

theorem schur_lemma_statement : UnitaryVolumeMass.stSchurLem := schur_lemma_unitary_distinct_params

theorem minkM_term (N p j : ℕ) (hp : 2 ≤ p) : N / (p ^ j * (p - 1)) ≤ 2 * N / p ^ (j + 1) := by
  have h1 : N / (p ^ j * (p - 1)) = 2 * N / (2 * (p ^ j * (p - 1))) := by
    rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
  rw [h1]
  apply Nat.div_le_div_left
  · have : p ≤ 2 * (p - 1) := by omega
    calc p ^ (j + 1) = p ^ j * p := pow_succ _ _
      _ ≤ p ^ j * (2 * (p - 1)) := Nat.mul_le_mul_left _ this
      _ = 2 * (p ^ j * (p - 1)) := by ring
  · positivity

theorem minkM_dvd (N : ℕ) : NonGenericAndKTwoTheorems.minkM N ∣ (2 * N).factorial := by
  unfold NonGenericAndKTwoTheorems.minkM
  rw [← Int.natCast_dvd_natCast]
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hne
    have hp' := (Finset.mem_filter.1 hp).2
    have hq' := (Finset.mem_filter.1 hq).2
    exact IsCoprime.pow (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp' hq').2 hne))
  · intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    have key : p ^ (∑ j ∈ Finset.range (N + 1), N / (p ^ j * (p - 1))) ∣ (2 * N).factorial := by
      rw [hp'.pow_dvd_factorial_iff (b := 2 * N + 2) (lt_of_le_of_lt (Nat.log_le_self _ _) (by omega))]
      calc ∑ j ∈ Finset.range (N + 1), N / (p ^ j * (p - 1))
          ≤ ∑ j ∈ Finset.range (N + 1), 2 * N / p ^ (1 + j) :=
            Finset.sum_le_sum (fun j _ => by rw [add_comm 1 j]; exact minkM_term N p j hp'.two_le)
        _ = ∑ i ∈ Finset.Ico 1 (N + 2), 2 * N / p ^ i := by
            rw [Finset.sum_Ico_eq_sum_range]; rfl
        _ ≤ ∑ i ∈ Finset.Ico 1 (2 * N + 2), 2 * N / p ^ i :=
            Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl (by omega))
    exact_mod_cast key

theorem minkowski_weak_of_exact (h : NonGenericAndKTwoTheorems.adm11) : UnitaryVolumeMass.stBRmink := fun N G hG => (h N G hG).trans (minkM_dvd N)

theorem minkowski_weak_hyp_of_exact_hyp (h : NonGenericAndKTwoTheorems.adm11) : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder := minkowski_weak_of_exact h

end Copies

section Vol

def gvTriv (D : D7) : Cnt.GaugeVol D := ⟨fun _ => 0, fun _ => 0, fun _ _ _ _ _ => rfl⟩

theorem trivial_gauge_condition_holds (D : D7) : NonGenericAndKTwoTheorems.DefiniteComplementMassVolumes D (gvTriv D) := fun _ _ _ _ _ _ _ _ => rfl

variable {eps : ℝ} (Fm : FamP eps)

theorem MassVolF_triv : PX.MassVolF Fm (fun _ _ _ => gvTriv _) := fun _ _ _ => trivial_gauge_condition_holds _

theorem kernel_family_of_trivial_gauge (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Cnt.GaugeVol (Fm.D x i))
    (h : NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummabilityOfAdmissible Fm At (fun _ _ _ => gvTriv _)) : NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummabilityOfAdmissible Fm At Gv := by
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, a14, a15⟩
  exact h ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, MassVolF_triv Fm, a13, a14, a15⟩

end Vol

section NGEq

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel ComplexConjugate

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem psi_eq_psi_zero_of_not_split (hs : M.split = none) : M.psiR = M.L.psi0 := by
  unfold Model.psiR
  split
  · rfl
  · rename_i g hg
    rw [hs] at hg
    cases hg

theorem norm_additiveCharacter_typePrime_eq_one (hOK : M.OK) (hs : M.split = none) (x : E) : ‖M.L.psi0 x‖ = 1 := by
  have h := Formalism.MainNotions.LocalModelPeriodLattices.unitary_of M hOK (Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK).1 (Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK).2.1
    (Formalism.MainNotions.LocalModelPeriodLattices.R_top M hOK).2.2 x
  rw [psi_eq_psi_zero_of_not_split hs] at h
  have h1 : M.L.psi0 x * M.L.psi0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [← h, Complex.mul_conj] at h1
  have h2 : Complex.normSq (M.L.psi0 x) = 1 := by exact_mod_cast h1
  rw [Complex.normSq_eq_norm_sq] at h2
  have h3 : 0 ≤ ‖M.L.psi0 x‖ := norm_nonneg _
  nlinarith

variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem norm_om (hOK : M.OK) (hs : M.split = none) (t : Term V M r) : ‖om P t‖ = 1 := by
  unfold om FrameD.psiOf
  rw [norm_mul, norm_inv, norm_additiveCharacter_typePrime_eq_one hOK hs, norm_additiveCharacter_typePrime_eq_one hOK hs]
  simp

def NGEqStep (P : FPair H r) (R : Reps P) : Prop :=
  ∀ d : Datum P, (R.RT d).Subsingleton ∧ ∀ t ∈ R.RT d, mu P t = 1 ∧ ¬ BBne (H := H) t

theorem amp_sq_eq (hOK : M.OK) (hs : M.split = none) (R : Reps P) (d : Datum P) (hd : (R.RT d).Subsingleton)
    (hμ : ∀ t ∈ R.RT d, mu P t = 1) (S : Term V M r → Prop) (hS : ∀ t ∈ R.RT d, S t) :
    ((‖amp R d S‖₊ : ENNReal)) ^ 2 = ∑' t : R.RT d, ENNReal.ofReal (mu P t.1) := by
  rcases (R.RT d).eq_empty_or_nonempty with he | ⟨t0, ht0⟩
  · have e1 : IsEmpty {t // t ∈ R.RT d ∧ S t} := ⟨fun t => (Set.ext_iff.1 he t.1).1 t.2.1⟩
    have e2 : IsEmpty (R.RT d) := ⟨fun t => (Set.ext_iff.1 he t.1).1 t.2⟩
    unfold amp
    rw [tsum_empty, tsum_empty]
    simp
  · unfold amp
    rw [tsum_eq_single (⟨t0, ht0, hS t0 ht0⟩ : {t // t ∈ R.RT d ∧ S t})
      (fun b hb => absurd (Subtype.ext (hd b.2.1 ht0)) hb),
      tsum_eq_single (⟨t0, ht0⟩ : R.RT d) (fun b hb => absurd (Subtype.ext (hd b.2 ht0)) hb)]
    have h1 : ‖((mu P t0 : ℝ) : ℂ) * om P t0‖₊ = 1 := by
      apply NNReal.eq
      simp [hμ t0 ht0, norm_om hOK hs t0]
    rw [h1, hμ t0 ht0]
    simp

theorem NG_equality_of (hOK : M.OK) (hP : P.PrimeTo) (R : Reps P) (h : NGEqStep P R) (d0 : Datum P) :
    P.Hp = 1 ∧ sumSq R d0 (fun t => ¬ BBne (H := H) t) = nn R d0 ∧ sumSq R d0 (fun _ => True) = nn R d0 := by
  refine ⟨NG_Hp_one hOK P hP, ?_, ?_⟩
  · unfold sumSq nn
    refine tsum_congr (fun d => ?_)
    rw [amp_sq_eq hOK hP.1 R d.1 (h d.1).1 (fun t ht => ((h d.1).2 t ht).1) _ (fun t ht => ((h d.1).2 t ht).2)]
  · unfold sumSq nn
    refine tsum_congr (fun d => ?_)
    rw [amp_sq_eq hOK hP.1 R d.1 (h d.1).1 (fun t ht => ((h d.1).2 t ht).1) _ (fun _ _ => trivial)]

def NGIneq (k : ℕ) (P : FPair H r) (C : ℝ) : Prop :=
  ∀ (R : Reps P) (d0 : Datum P),
    sumSq R d0 (BBne (H := H)) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2) *
        (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5))) * nn R d0 ∧
    sumSq R d0 (fun t => ¬ BBne (H := H) t) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2)) * nn R d0 ∧
    sumSq R d0 (fun _ => True) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2)) * nn R d0

theorem NGAt_of (hOK : M.OK) (k : ℕ) (C : ℝ) (h3 : NGIneq k P C) (hE : P.PrimeTo → ∀ R : Reps P, NGEqStep P R) :
    NGAt k P C := fun R d0 =>
  ⟨(h3 R d0).1, (h3 R d0).2.1, (h3 R d0).2.2, fun hP => NG_equality_of hOK hP R (hE hP R) d0⟩

theorem NGAt_of_primeTo (hOK : M.OK) (k : ℕ) (C : ℝ) (hP : P.PrimeTo) (hE : ∀ R : Reps P, NGEqStep P R) :
    NGAt k P C := by
  intro R d0
  obtain ⟨h1, h2, h3⟩ := NG_equality_of hOK hP R (hE R) d0
  have hz : sumSq R d0 (BBne (H := H)) = 0 := by
    unfold sumSq
    rw [ENNReal.tsum_eq_zero]
    intro d
    have e1 : IsEmpty {t // t ∈ R.RT d.1 ∧ BBne (H := H) t} := ⟨fun t => ((hE R d.1).2 t.1 t.2.1).2 t.2.2⟩
    unfold amp
    rw [tsum_empty]
    simp
  refine ⟨by rw [hz]; exact bot_le, ?_, ?_, fun _ => ⟨h1, h2, h3⟩⟩
  · rw [h2, h1]; simp
  · rw [h3, h1]; simp

end NGEq

section BB

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem h_sum_left {ι : Type} (s : Finset ι) (c : ι → E) (m : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • m i) y = ∑ i ∈ s, c i * H.h (m i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem sat_of_unit_gram {ι : Type} [Fintype ι] [DecidableEq ι] (abelian₂ : Submodule M.L.O V) (m : ι → V)
    (hmem : ∀ j, m j ∈ abelian₂) (hint : ∀ v ∈ abelian₂, ∀ j, H.h v (m j) ∈ M.L.O) (hu : IsUnitO M (H.gram m).det)
    (v : V) (hv : v ∈ abelian₂) (hsp : v ∈ Submodule.span E (Set.range m)) :
    v ∈ Submodule.span M.L.O (Set.range m) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hsp
  set G := H.gram m with hG
  let G₀ : Matrix ι ι M.L.O := fun a b => ⟨G a b, hint (m b) (hmem b) a⟩
  have hG₀ : G = G₀.map M.L.O.subtype := by ext a b; rfl
  have hadj : ∀ a b, G.adjugate a b ∈ M.L.O := by
    intro a b
    rw [hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (G₀.adjugate a b).2
  have hGc : ∀ j, (G.mulVec c) j ∈ M.L.O := by
    intro j
    have : (G.mulVec c) j = H.h (∑ i, c i • m i) (m j) := by
      rw [h_sum_left]
      simp only [Matrix.mulVec, dotProduct, hG, HermSp.gram, Matrix.of_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [this]
    exact hint _ hv j
  have hdc : ∀ i, G.det * c i ∈ M.L.O := by
    intro i
    have e : G.adjugate.mulVec (G.mulVec c) = G.det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    simp only [Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    simp only [Matrix.mulVec, dotProduct]
    exact M.L.O.sum_mem (fun j _ => M.L.O.mul_mem (hadj i j) (hGc j))
  obtain ⟨_, y, hy, hdy⟩ := hu
  have hc : ∀ i, c i ∈ M.L.O := by
    intro i
    have : c i = y * (G.det * c i) := by rw [← mul_assoc, mul_comm y, hdy, one_mul]
    rw [this]
    exact M.L.O.mul_mem hy (hdc i)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have : c i • m i = (⟨c i, hc i⟩ : M.L.O) • m i := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem not_BBne_of {t : Term V M r} (hmem : ∀ j, H.MMfam t j ∈ t.abelian₂)
    (hint : ∀ v ∈ t.abelian₂, ∀ j, H.h v (H.MMfam t j) ∈ M.L.O) (hu : IsUnitO M (H.gram (H.MMfam t)).det) :
    ¬ BBne (H := H) t := by
  rintro ⟨v, hv, hsp, hn⟩
  exact hn (sat_of_unit_gram t.abelian₂ _ hmem hint hu v hv hsp)

end BB

section Frames

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem h_sum_right {ι : Type} (s : Finset ι) (c : ι → E) (m : ι → V) (y : V) :
    H.h y (∑ i ∈ s, c i • m i) = ∑ i ∈ s, M.L.cj (c i) * H.h y (m i) := by
  rw [H.h_herm _ y, h_sum_left, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, ← H.h_herm (m i) y]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  have := H.h_add_left (x - x') x' y
  rw [sub_add_cancel] at this
  rw [this]; ring

variable (Fr : FrameD H r)

theorem Fj_mono {i j : ℕ} (hij : i ≤ j) : Fr.Fj i ≤ Fr.Fj j :=
  Submodule.span_mono (Set.image_mono (fun a (ha : a.val < i) => lt_of_lt_of_le ha hij))

theorem Fj_r : Fr.Fj r = H.X Fr.f := by
  unfold FrameD.Fj HermSp.X
  congr 1
  ext v
  constructor
  · rintro ⟨a, _, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩

theorem Fj_zero : Fr.Fj 0 = ⊥ := by
  unfold FrameD.Fj
  have : {a : Fin r | a.val < 0} = ∅ := by ext a; simp
  rw [this]; simp

theorem e_mem_Fj (a : Fin r) : Fr.e a ∈ Fr.Fj (a.val + 1) :=
  Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem h_X_f {x : V} (hx : x ∈ H.X Fr.f) (b : Fin (r + 1)) : H.h x (Fr.f b) = 0 := by
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem h_f_X {x : V} (hx : x ∈ H.X Fr.f) (b : Fin (r + 1)) : H.h (Fr.f b) x = 0 := by
  rw [H.h_herm x (Fr.f b), h_X_f Fr hx, map_zero]

theorem h_X_X {x y : V} (hx : x ∈ H.X Fr.f) (hy : y ∈ H.X Fr.f) : H.h x y = 0 := by
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h_f_X Fr hy _
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := fun _ hx _ hy => h_X_X Fr hx hy

theorem z_mem_perp : Fr.z ∈ H.perp (H.X Fr.f) := fun _ hx => h_f_X Fr hx _

theorem NSet_apply_Fj {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) {j : ℕ} (hj : j ≤ r) {v : V} (hv : v ∈ Fr.Fj j) :
    g v ∈ Fr.Fj j := by
  have := Fj_mono Fr (Nat.sub_le j 1) (hg.2.1 j hj v hv)
  have e : g v = (g v - v) + v := by abel
  rw [e]
  exact Submodule.add_mem _ this hv

theorem NSet_one : (1 : V ≃ₗ[E] V) ∈ Fr.NSet :=
  ⟨fun _ _ => rfl, fun j _ v _ => by simp, fun v _ => by simp⟩

theorem NSet_mul {g g' : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) (hg' : g' ∈ Fr.NSet) : g * g' ∈ Fr.NSet := by
  refine ⟨fun x y => ?_, fun j hj v hv => ?_, fun v hv => ?_⟩
  · show H.h (g (g' x)) (g (g' y)) = _
    rw [hg.1, hg'.1]
  · show g (g' v) - v ∈ _
    have e : g (g' v) - v = (g (g' v) - g' v) + (g' v - v) := by abel
    rw [e]
    exact Submodule.add_mem _ (hg.2.1 j hj _ (NSet_apply_Fj Fr hg' hj hv)) (hg'.2.1 j hj v hv)
  · show g (g' v) - v ∈ _
    have h1 := hg'.2.2 v hv
    have h2 : g' v ∈ H.perp (H.X Fr.f) := by
      have e : g' v = (g' v - v) + v := by abel
      rw [e]
      exact Submodule.add_mem _ (X_le_perp Fr h1) hv
    have e : g (g' v) - v = (g (g' v) - g' v) + (g' v - v) := by abel
    rw [e]
    exact Submodule.add_mem _ (hg.2.2 _ h2) h1

theorem NSet_inv_Fj {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) :
    ∀ j, j ≤ r → ∀ v ∈ Fr.Fj j, g.symm v - v ∈ Fr.Fj (j - 1) := by
  intro j
  induction j with
  | zero =>
    intro _ v hv
    rw [Fj_zero, Submodule.mem_bot] at hv
    subst hv
    simp
  | succ j ih =>
    intro hj v hv
    have hu := hg.2.1 (j + 1) hj v hv
    simp only [Nat.add_sub_cancel] at hu ⊢
    have h1 := ih (by omega) _ hu
    have h2 : g.symm (g v - v) ∈ Fr.Fj j := by
      have e : g.symm (g v - v) = (g.symm (g v - v) - (g v - v)) + (g v - v) := by abel
      rw [e]
      exact Submodule.add_mem _ (Fj_mono Fr (Nat.sub_le j 1) h1) hu
    have e : g.symm v - v = -(g.symm (g v - v)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ h2

theorem NSet_inv {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) : g⁻¹ ∈ Fr.NSet := by
  refine ⟨fun x y => ?_, NSet_inv_Fj Fr hg, fun v hv => ?_⟩
  · show H.h (g.symm x) (g.symm y) = _
    rw [← hg.1 (g.symm x) (g.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · show g.symm v - v ∈ _
    have hu := hg.2.2 v hv
    have h1 := NSet_inv_Fj Fr hg r le_rfl (g v - v) (by rw [Fj_r]; exact hu)
    have h2 : g.symm (g v - v) ∈ H.X Fr.f := by
      have e : g.symm (g v - v) = (g.symm (g v - v) - (g v - v)) + (g v - v) := by abel
      rw [e]
      refine Submodule.add_mem _ ?_ hu
      rw [← Fj_r]
      exact Fj_mono Fr (Nat.sub_le r 1) h1
    have e : g.symm v - v = -(g.symm (g v - v)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ h2

theorem mem_NSet_of_mem_N {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : g ∈ Fr.NSet := by
  unfold FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact NSet_one Fr
  | mul x y _ _ hx hy => exact NSet_mul Fr hx hy
  | inv x _ hx => exact NSet_inv Fr hx

variable {Fr} {L : Submodule M.L.O (H.Wb Fr.f)}

theorem prF_e (a : Fin r) : Fr.prF (Fr.e a) = 0 := by
  classical
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.e a) (Fr.es c) • Fr.e c = Fr.e a := by
    rw [Finset.sum_eq_single a]
    · have := Fr.h_es a a
      simp only [if_true] at this
      show H.h (Fr.f a.castSucc) (Fr.es a) • Fr.e a = _
      rw [this, one_smul]
    · intro c _ hc
      have := Fr.h_es a c
      rw [if_neg (Ne.symm hc)] at this
      show H.h (Fr.f a.castSucc) (Fr.es c) • Fr.e c = _
      rw [this, zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ c, H.h (Fr.e a) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
  rw [h1, h2]; simp

theorem h_z_es (c : Fin r) : H.h Fr.z (Fr.es c) = 0 := by
  show H.h (Fr.f (Fin.last r)) (Fr.es c) = 0
  rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero]

theorem frame_projection_last_eq_self : Fr.prF Fr.z = Fr.z := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h Fr.z (Fr.es c) • Fr.e c = 0 :=
    Finset.sum_eq_zero (fun c _ => by rw [h_z_es, zero_smul])
  have h2 : ∑ c, H.h Fr.z (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne), zero_smul])
  rw [h1, h2]; simp

theorem f_mem_LamStd (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  rcases Fin.eq_castSucc_or_eq_last b with ⟨a, rfl⟩ | rfl
  · refine ⟨fun c => ?_, fun c => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [Fr.h_es]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)]; exact M.L.O.zero_mem
    · exact (prF_e a).symm
    · rw [map_zero]; exact L.zero_mem
  · obtain ⟨xz, hxz, hxL, _⟩ := hL.2.2
    refine ⟨fun c => ?_, fun c => ?_, ⟨xz, ?_, hxL⟩⟩
    · rw [show Fr.f (Fin.last r) = Fr.z from rfl, h_z_es]; exact M.L.O.zero_mem
    · show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne)]; exact M.L.O.zero_mem
    · rw [hxz]; exact frame_projection_last_eq_self.symm

theorem h_LamStd_f (hL : Fr.IsInner L) {v : V} (hv : v ∈ Fr.LamStd L) (b : Fin (r + 1)) :
    H.h v (Fr.f b) ∈ M.L.O := by
  unfold FrameD.LamStd at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨_, h2, w, hw, hwL⟩ := hv
    rcases Fin.eq_castSucc_or_eq_last b with ⟨a, rfl⟩ | rfl
    · exact h2 a
    · obtain ⟨xz, hxz, hxL, _⟩ := hL.2.2
      have h3 := (hL.2.1 w).1 hwL xz hxL
      rw [hw, hxz] at h3
      have e : H.h (Fr.prF v) Fr.z = H.h v Fr.z := by
        unfold FrameD.prF
        rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
        have z1 : ∑ i, H.h v (Fr.es i) * H.h (Fr.e i) Fr.z = 0 :=
          Finset.sum_eq_zero (fun i _ => by
            rw [show H.h (Fr.e i) Fr.z = 0 from Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last i).ne), mul_zero])
        have z2 : ∑ i, H.h v (Fr.e i) * H.h (Fr.es i) Fr.z = 0 :=
          Finset.sum_eq_zero (fun i _ => by rw [show H.h (Fr.es i) Fr.z = 0 from Fr.h_sz i, mul_zero])
        rw [z1, z2]; ring
      rw [e] at h3
      exact h3
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) (Fr.f b) = (c : E) * H.h x (Fr.f b) := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end Frames

section GramInv

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem gram_det_change {ι : Type} [Fintype ι] [DecidableEq ι] (m m' : ι → V) (A : Matrix ι ι E)
    (h : ∀ j, m' j = ∑ i, A j i • m i) :
    (H.gram m').det = M.L.cj A.det * (H.gram m).det * A.det := by
  set c : E →+* E := (M.L.cj : E ≃ₐ[F] E).toAlgHom.toRingHom with hc
  have hcx : ∀ x, c x = M.L.cj x := fun _ => rfl
  have e : H.gram m' = A.map c * H.gram m * A.transpose := by
    ext a b
    simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [h a, h b, h_sum_left]
    simp only [h_sum_right, hcx]
    exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hcx, RingHom.map_det]
  rfl

variable (Fr : FrameD H r)

theorem coef_Fj {j : ℕ} {v : V} (hv : v ∈ Fr.Fj j) :
    ∃ c : Fin r → E, (∀ a : Fin r, j ≤ a.val → c a = 0) ∧ v = ∑ a, c a • Fr.e a := by
  classical
  unfold FrameD.Fj at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
    · have : b ≠ a := fun h => by subst h; exact absurd ha (not_lt.2 hb)
      simp [this]
    · rw [Finset.sum_eq_single a] <;> simp [Pi.single_apply]
      intro b hb; simp [hb]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h1, h2⟩ := hx
    obtain ⟨c', h1', h2'⟩ := hy
    exact ⟨c + c', fun a ha => by simp [h1 a ha, h1' a ha], by
      rw [h2, h2', ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => by simp [add_smul])⟩
  | smul t x _ hx =>
    obtain ⟨c, h1, h2⟩ := hx
    exact ⟨t • c, fun a ha => by simp [h1 a ha], by
      rw [h2, Finset.smul_sum]; exact Finset.sum_congr rfl (fun a _ => by simp [mul_smul])⟩

theorem N_row {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) (a : Fin (r + 1)) :
    ∃ row : Fin (r + 1) → E, (∀ b, a < b → row b = 0) ∧ row a = 1 ∧ g (Fr.f a) = ∑ b, row b • Fr.f b := by
  classical
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
  · have h1 := hg.2.1 (a'.val + 1) a'.2 _ (e_mem_Fj Fr a')
    simp only [Nat.add_sub_cancel] at h1
    obtain ⟨c, hc0, hc⟩ := coef_Fj Fr h1
    refine ⟨Fin.lastCases 0 (fun b' => c b' + if b' = a' then 1 else 0), fun b hb => ?_, ?_, ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · have hlt : a' < b' := by simpa using hb
        beta_reduce
        rw [Fin.lastCases_castSucc, hc0 b' (le_of_lt hlt), if_neg (ne_of_gt hlt), add_zero]
      · beta_reduce
        rw [Fin.lastCases_last]
    · beta_reduce
      rw [Fin.lastCases_castSucc, hc0 a' le_rfl, if_pos rfl, zero_add]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, zero_smul, add_zero, add_smul, Finset.sum_add_distrib]
      have e1 : ∑ x : Fin r, (if x = a' then (1 : E) else 0) • Fr.f x.castSucc = Fr.f a'.castSucc := by
        rw [Finset.sum_eq_single a'] <;> simp
        intro b hb; simp [hb]
      rw [e1]
      have e2 : g (Fr.f a'.castSucc) = (g (Fr.e a') - Fr.e a') + Fr.f a'.castSucc := by
        show _ = (g (Fr.f a'.castSucc) - Fr.f a'.castSucc) + _
        abel
      rw [e2, hc]
      rfl
  · have h1 := hg.2.2 _ (z_mem_perp Fr)
    rw [← Fj_r] at h1
    obtain ⟨c, _, hc⟩ := coef_Fj Fr h1
    refine ⟨Fin.lastCases 1 (fun b' => c b'), fun b hb => absurd hb (not_lt.2 (Fin.le_last b)), ?_, ?_⟩
    · beta_reduce
      rw [Fin.lastCases_last]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_smul]
      have e2 : g (Fr.f (Fin.last r)) = (g Fr.z - Fr.z) + Fr.f (Fin.last r) := by
        show _ = (g (Fr.f (Fin.last r)) - Fr.f (Fin.last r)) + _
        abel
      rw [e2, hc]
      rfl

theorem N_matrix {g : V ≃ₗ[E] V} (hg : g ∈ Fr.NSet) :
    ∃ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, A.det = 1 ∧ ∀ a, g (Fr.f a) = ∑ b, A a b • Fr.f b := by
  choose A h1 h2 h3 using N_row Fr hg
  refine ⟨Matrix.of A, ?_, h3⟩
  have hT : (Matrix.of A).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h' : i < j := hij
    exact h1 i j h'
  rw [Matrix.det_of_isLowerTriangular _ hT]
  exact Finset.prod_eq_one (fun i _ => h2 i)

variable {P : FPair H r}

theorem gram_det_term (hs : M.split = none) {t : Term V M r} {n n' : V ≃ₗ[E] V} (hn : n ∈ P.A.N) (hn' : n' ∈ P.B.N)
    (hf : t.f = fun b => n (P.A.f b)) (hf' : t.f' = fun b => n' (P.B.f b)) :
    (H.gram (H.MMfam t)).det = (H.gram P.MMgen).det := by
  obtain ⟨A, hA, hA'⟩ := N_matrix P.A (mem_NSet_of_mem_N P.A hn)
  obtain ⟨B, hB, hB'⟩ := N_matrix P.B (mem_NSet_of_mem_N P.B hn')
  have hm : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam
    split
    · rfl
    · rename_i g hg
      rw [hs] at hg
      cases hg
  rw [hm, MMgen_eq P hs, gram_det_change (Sum.elim P.A.f P.B.f) (Sum.elim t.f t.f') (Matrix.fromBlocks A 0 0 B)]
  · rw [Matrix.det_fromBlocks_zero₂₁, hA, hB]; simp
  · rintro (a | a)
    · simp [Fintype.sum_sum_type, hf, hA' a]
    · simp [Fintype.sum_sum_type, hf', hB' a]

theorem not_BBne_term (hP : P.PrimeTo) (d : Datum P) {t : Term V M r} (ht : IsTermOver P d t) :
    ¬ BBne (H := H) t := by
  obtain ⟨hs, hG, _⟩ := hP
  obtain ⟨_, _, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, _⟩ := ht
  have hnU := (mem_NSet_of_mem_N P.A hn).1
  have hnU' := (mem_NSet_of_mem_N P.B hn').1
  have hm : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam
    split
    · rfl
    · rename_i g hg
      rw [hs] at hg
      cases hg
  apply not_BBne_of
  · rw [hm]
    rintro (b | b)
    · simp only [Sum.elim_inl]
      rw [hf, hL]
      exact ⟨P.A.f b, f_mem_LamStd d.hL b, rfl⟩
    · simp only [Sum.elim_inr]
      rw [hf', hL']
      exact ⟨P.B.f b, f_mem_LamStd d.hL' b, rfl⟩
  · intro v hv
    rw [hm]
    rintro (b | b)
    · simp only [Sum.elim_inl]
      rw [hL] at hv
      obtain ⟨v0, hv0, rfl⟩ := hv
      rw [hf]
      show H.h (n v0) (n (P.A.f b)) ∈ _
      rw [hnU]
      exact h_LamStd_f d.hL hv0 b
    · simp only [Sum.elim_inr]
      rw [hL'] at hv
      obtain ⟨v0, hv0, rfl⟩ := hv
      rw [hf']
      show H.h (n' v0) (n' (P.B.f b)) ∈ _
      rw [hnU']
      exact h_LamStd_f d.hL' hv0 b
  · rw [gram_det_term hs hn hn' hf hf', gram_det_eq P hs]
    exact isUnitO_mul (isUnitO_neg_one_pow _) hG

def NGEqStep' (P : FPair H r) (R : Reps P) : Prop :=
  ∀ d : Datum P, (R.RT d).Subsingleton ∧ ∀ t ∈ R.RT d, mu P t = 1

theorem NGEqStep_of (hP : P.PrimeTo) (R : Reps P) (h : NGEqStep' P R) : NGEqStep P R := fun d =>
  ⟨(h d).1, fun t ht => ⟨(h d).2 t ht, not_BBne_term hP d ((R.hRT d).1 ht)⟩⟩

theorem NGAt_of_primeTo' (hOK : M.OK) (k : ℕ) (C : ℝ) (hP : P.PrimeTo) (hE : ∀ R : Reps P, NGEqStep' P R) :
    NGAt k P C := NGAt_of_primeTo hOK k C hP (fun R => NGEqStep_of hP R (hE R))

end GramInv

section NGAsm

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

def massS (R : Reps P) (d : Datum P) (S : Term V M r → Prop) : ℝ :=
  ∑' t : {t // t ∈ R.RT d ∧ S t}, mu P t.1

theorem mu_nonneg (t : Term V M r) : 0 ≤ mu P t := by unfold mu volRel; positivity

theorem wt_nonneg (d0 d : Datum P) : 0 ≤ Datum.wt d0 d := by unfold Datum.wt volRel; positivity

theorem summable_sub (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1)) (S : Term V M r → Prop) :
    Summable (fun t : {t // t ∈ R.RT d ∧ S t} => mu P t.1) :=
  hs.comp_injective (i := fun t : {t // t ∈ R.RT d ∧ S t} => (⟨t.1, t.2.1⟩ : R.RT d))
    (fun _ _ h => Subtype.ext (congrArg (fun x : R.RT d => x.1) h))

theorem massS_nonneg (R : Reps P) (d : Datum P) (S : Term V M r → Prop) : 0 ≤ massS R d S :=
  tsum_nonneg (fun _ => mu_nonneg _)

theorem norm_term (hω : ∀ t : Term V M r, ‖om P t‖ = 1) (t : Term V M r) : ‖((mu P t : ℝ) : ℂ) * om P t‖ = mu P t := by
  rw [norm_mul, hω, mul_one, Complex.norm_real, Real.norm_of_nonneg (mu_nonneg t)]

theorem norm_amp_le (hω : ∀ t : Term V M r, ‖om P t‖ = 1) (R : Reps P) (d : Datum P)
    (hs : Summable (fun t : R.RT d => mu P t.1)) (S : Term V M r → Prop) : ‖amp R d S‖ ≤ massS R d S := by
  unfold amp massS
  have h1 : Summable (fun t : {t // t ∈ R.RT d ∧ S t} => ‖((mu P t.1 : ℝ) : ℂ) * om P t.1‖) := by
    simp only [norm_term hω]; exact summable_sub R d hs S
  refine le_trans (norm_tsum_le_tsum_norm h1) (le_of_eq ?_)
  simp only [norm_term hω]

theorem amp_split (hω : ∀ t : Term V M r, ‖om P t‖ = 1) (R : Reps P) (d : Datum P)
    (hs : Summable (fun t : R.RT d => mu P t.1)) (S : Term V M r → Prop) {Ty : Type} [Fintype Ty]
    (typ : Term V M r → Ty) : amp R d S = ∑ τ, amp R d (fun t => S t ∧ typ t = τ) := by
  classical
  set f : Term V M r → ℂ := fun t => ((mu P t : ℝ) : ℂ) * om P t with hf
  have e : ∀ S' : Term V M r → Prop, amp R d S' = ∑' t, ({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f t :=
    fun S' => tsum_subtype ({t | t ∈ R.RT d ∧ S' t} : Set _) f
  have hsum : ∀ S' : Term V M r → Prop, Summable (({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f) := by
    intro S'
    rw [← summable_subtype_iff_indicator]
    refine Summable.of_norm ?_
    have : (fun t : ({t | t ∈ R.RT d ∧ S' t} : Set _) => ‖(f ∘ Subtype.val) t‖) = fun t => mu P t.1 := by
      funext t; exact norm_term hω t.1
    rw [this]
    exact summable_sub R d hs S'
  rw [e S]
  simp only [e]
  rw [← Summable.tsum_finsetSum (fun τ _ => hsum _)]
  refine tsum_congr (fun t => ?_)
  by_cases ht : t ∈ R.RT d ∧ S t
  · rw [Set.indicator_of_mem (show t ∈ {t | t ∈ R.RT d ∧ S t} from ht),
      Finset.sum_eq_single (typ t)]
    · rw [Set.indicator_of_mem (show t ∈ {t' | t' ∈ R.RT d ∧ S t' ∧ typ t' = typ t} from ⟨ht.1, ht.2, rfl⟩)]
    · intro τ _ hτ
      exact Set.indicator_of_notMem (s := {t' | t' ∈ R.RT d ∧ S t' ∧ typ t' = τ}) (f := f)
        (fun h => hτ (show t ∈ R.RT d ∧ S t ∧ typ t = τ from h).2.2.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Set.indicator_of_notMem (show t ∉ {t | t ∈ R.RT d ∧ S t} from ht)]
    exact (Finset.sum_eq_zero (fun τ _ =>
      Set.indicator_of_notMem (s := {t' | t' ∈ R.RT d ∧ S t' ∧ typ t' = τ}) (f := f)
        (fun h => ht ⟨(show t ∈ R.RT d ∧ S t ∧ typ t = τ from h).1,
          (show t ∈ R.RT d ∧ S t ∧ typ t = τ from h).2.1⟩))).symm

theorem amp_of_empty (R : Reps P) (d : Datum P) (he : R.RT d = ∅) (S : Term V M r → Prop) : amp R d S = 0 := by
  have e1 : IsEmpty {t // t ∈ R.RT d ∧ S t} := ⟨fun t => (Set.ext_iff.1 he t.1).1 t.2.1⟩
  unfold amp
  rw [tsum_empty]

theorem sumSq_eq (R : Reps P) (d0 : Datum P) (Ds : Finset R.RD) (off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅)
    (S : Term V M r → Prop) :
    sumSq R d0 S = ENNReal.ofReal (∑ d : Ds, Datum.wt d0 d.1.1 * ‖amp R d.1.1 S‖ ^ 2) := by
  unfold sumSq
  rw [tsum_eq_sum (s := Ds) (fun d hd => by rw [amp_of_empty R d.1 (off d hd)]; simp),
    Finset.sum_coe_sort Ds (fun d : R.RD => Datum.wt d0 d.1 * ‖amp R d.1 S‖ ^ 2),
    ENNReal.ofReal_sum_of_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (by positivity))]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [ENNReal.ofReal_mul (wt_nonneg _ _), ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

theorem nn_eq (R : Reps P) (d0 : Datum P) (Ds : Finset R.RD) (off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅)
    (hs : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1)) :
    nn R d0 = ENNReal.ofReal (∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1) := by
  unfold nn
  rw [tsum_eq_sum (s := Ds) (fun d hd => by
      have e2 : IsEmpty (R.RT d.1) := ⟨fun t => (Set.ext_iff.1 (off d hd) t.1).1 t.2⟩
      rw [tsum_empty]; simp),
    Finset.sum_coe_sort Ds (fun d : R.RD => Datum.wt d0 d.1 * ∑' t : R.RT d.1, mu P t.1),
    ENNReal.ofReal_sum_of_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [ENNReal.ofReal_mul (wt_nonneg _ _), ENNReal.ofReal_tsum_of_nonneg (fun _ => mu_nonneg _) (hs d)]

structure NGSteps2 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (S : Term V M r → Prop) where
  Ds : Finset R.RD
  off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅
  summ : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1)
  om1 : ∀ t : Term V M r, ‖om P t‖ = 1
  Ty : Type
  fin : Fintype Ty
  typ : Term V M r → Ty
  be : Ty → ℝ
  I : Ty → ℝ
  H1 : 1 ≤ P.Hp
  card : (Fintype.card Ty : ℝ) ≤ P.Hp ^ (c * (r + 1) ^ 2)
  be1 : ∀ τ, 1 ≤ be τ
  I0 : ∀ τ, 0 ≤ I τ
  Ibe : ∀ τ, I τ ≤ be τ
  c2 : ∀ (τ : Ty) (d : Ds), massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤ P.Hp ^ (c * (r + 1) ^ 2) * I τ ^ (k - 1)
  c1 : ∀ τ : Ty, ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤
    P.Hp ^ (c * (r + 1) ^ 2) * (be τ ^ (k - 1))⁻¹ * ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1

def nongenericConstantNoGain (c : ℕ) : ℕ := (Formalism.HermitianLatticeCounting.Final.S4.assemblyNG2 c).choose

def gainBoundConstant (c : ℕ) (C₀ : ℝ) : ℕ := (Formalism.HermitianLatticeCounting.Final.S4.assemblyNG c C₀).choose

theorem rpow_exp (x : ℝ) (C : ℕ) : x ^ ((C : ℝ) * ((r : ℝ) + 1) ^ 2) = x ^ (C * (r + 1) ^ 2) := by
  have h : ((C * (r + 1) ^ 2 : ℕ) : ℝ) = (C : ℝ) * ((r : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [← h, Real.rpow_natCast]

theorem NG_second_of_steps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {S : Term V M r → Prop}
    (X : NGSteps2 k R d0 c S) :
    sumSq R d0 S ≤ ENNReal.ofReal (P.Hp ^ ((nongenericConstantNoGain c : ℝ) * ((r : ℝ) + 1) ^ 2)) * nn R d0 := by
  let _ := X.fin
  have hnn : 0 ≤ ∑ d : X.Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))
  have key := (Formalism.HermitianLatticeCounting.Final.S4.assemblyNG2 c).choose_spec k ((r + 1) ^ 2) P.Hp _ X.Ds X.Ty
    (fun d => Datum.wt d0 d.1.1) (fun τ d => amp R d.1.1 (fun t => S t ∧ X.typ t = τ))
    (fun τ d => massS R d.1.1 (fun t => S t ∧ X.typ t = τ)) X.be X.I X.H1 hnn (fun d => wt_nonneg _ _) X.card X.be1 X.I0
    X.Ibe (fun τ d => massS_nonneg _ _ _) X.c2 X.c1 (fun τ d => norm_amp_le X.om1 R _ (X.summ d.1) _)
  rw [sumSq_eq R d0 X.Ds X.off, nn_eq R d0 X.Ds X.off X.summ, ← ENNReal.ofReal_mul (by have := X.H1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_exp]
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl (fun d _ => by rw [amp_split X.om1 R d.1.1 (X.summ d.1) S X.typ])

structure NGSteps1 (k : ℕ) (R : Reps P) (d0 : Datum P) (c : ℕ) (C₀ : ℝ) extends
    NGSteps2 k R d0 c (BBne (H := H)) where
  hk : 4 * r + 7 ≤ k
  q2 : 2 ≤ qF F
  qH : (∃ d : R.RD, ∃ t ∈ R.RT d.1, BBne (H := H) t) → (qF F : ℝ) ≤ P.Hp
  isBe : Ty → Prop
  Ial : ∀ τ, ¬ isBe τ → I τ ≤ be τ / (qF F : ℝ)
  e : ∀ (τ : Ty) (d : Ds), isBe τ → ‖amp R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)‖ ≤
    C₀ * (qF F : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)

theorem NG_first_of_steps {k : ℕ} {R : Reps P} {d0 : Datum P} {c : ℕ} {C₀ : ℝ} (X : NGSteps1 k R d0 c C₀) :
    sumSq R d0 (BBne (H := H)) ≤ ENNReal.ofReal (P.Hp ^ ((gainBoundConstant c C₀ : ℝ) * ((r : ℝ) + 1) ^ 2) *
      (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5))) * nn R d0 := by
  let _ := X.fin
  by_cases hex : ∃ d : R.RD, ∃ t ∈ R.RT d.1, BBne (H := H) t
  swap
  · have hz : sumSq R d0 (BBne (H := H)) = 0 := by
      unfold sumSq
      rw [ENNReal.tsum_eq_zero]
      intro d
      have e1 : IsEmpty {t // t ∈ R.RT d.1 ∧ BBne (H := H) t} := ⟨fun t => hex ⟨d, t.1, t.2.1, t.2.2⟩⟩
      unfold amp
      rw [tsum_empty]
      simp
    rw [hz]; exact bot_le
  have hnn : 0 ≤ ∑ d : X.Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))
  have key := (Formalism.HermitianLatticeCounting.Final.S4.assemblyNG c C₀).choose_spec k r (qF F) ((r + 1) ^ 2) P.Hp _ X.Ds X.Ty
    (fun d => Datum.wt d0 d.1.1) (fun τ d => amp R d.1.1 (fun t => BBne (H := H) t ∧ X.typ t = τ))
    (fun τ d => massS R d.1.1 (fun t => BBne (H := H) t ∧ X.typ t = τ)) X.be X.I X.isBe
    (Nat.one_le_pow _ _ (Nat.succ_pos r)) X.hk X.q2 X.H1 (fun _ => X.qH hex) hnn (fun d => wt_nonneg _ _) X.card X.be1 X.I0
    X.Ibe X.Ial (fun τ d => massS_nonneg _ _ _) X.c2 X.c1 (fun τ d => norm_amp_le X.om1 R _ (X.summ d.1) _) X.e
  have hq : (0 : ℝ) < qF F := by have := X.q2; exact_mod_cast (by omega : 0 < qF F)
  rw [sumSq_eq R d0 X.Ds X.off, nn_eq R d0 X.Ds X.off X.summ,
    ← ENNReal.ofReal_mul (by have := X.H1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_exp]
  have hz : (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5)) = (qF F : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) := by
    have h : ((-((k : ℤ) - 2 * r - 5) : ℤ) : ℝ) = -((k : ℝ) - 2 * r - 5) := by push_cast; ring
    rw [← h, Real.rpow_intCast]
  rw [hz]
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl (fun d _ => by rw [amp_split X.om1 R d.1.1 (X.summ d.1) _ X.typ])

theorem NGAt_of_steps (hOK : M.OK) (k c : ℕ) (C₀ C : ℝ) (hH : 1 ≤ P.Hp) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C) (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (X1 : ∀ (R : Reps P) (d0 : Datum P), NGSteps1 k R d0 c C₀)
    (X2 : ∀ (R : Reps P) (d0 : Datum P), NGSteps2 k R d0 c (fun t => ¬ BBne (H := H) t))
    (X3 : ∀ (R : Reps P) (d0 : Datum P), NGSteps2 k R d0 c (fun _ => True))
    (hE : P.PrimeTo → ∀ R : Reps P, NGEqStep' P R) : NGAt k P C := by
  have mono : ∀ C' : ℝ, C' ≤ C → P.Hp ^ (C' * ((r : ℝ) + 1) ^ 2) ≤ P.Hp ^ (C * ((r : ℝ) + 1) ^ 2) := fun C' h =>
    Real.rpow_le_rpow_of_exponent_le hH (mul_le_mul_of_nonneg_right h (by positivity))
  refine NGAt_of hOK k C (fun R d0 => ⟨?_, ?_, ?_⟩) (fun hP R => NGEqStep_of hP R (hE hP R))
  · refine le_trans (NG_first_of_steps (X1 R d0)) (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact mul_le_mul_of_nonneg_right (mono _ hC1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_trans (NG_second_of_steps (X2 R d0)) (mul_le_mul_left (ENNReal.ofReal_le_ofReal (mono _ hC2)) _)
  · exact le_trans (NG_second_of_steps (X3 R d0)) (mul_le_mul_left (ENNReal.ofReal_le_ofReal (mono _ hC2)) _)

end NGAsm

section NGAll

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section One

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem NGAt_of_noTerms (hOK : M.OK) (k : ℕ) (C : ℝ) (h : ∀ (R : Reps P) (d : Datum P), R.RT d = ∅) : NGAt k P C := by
  intro R d0
  have hz : ∀ S : Term V M r → Prop, sumSq R d0 S = 0 := by
    intro S
    unfold sumSq
    rw [ENNReal.tsum_eq_zero]
    intro d
    rw [amp_of_empty R d.1 (h R d.1)]
    simp
  have hn : nn R d0 = 0 := by
    unfold nn
    rw [ENNReal.tsum_eq_zero]
    intro d
    have e2 : IsEmpty (R.RT d.1) := ⟨fun t => (Set.ext_iff.1 (h R d.1) t.1).1 t.2⟩
    rw [tsum_empty]
    simp
  simp only [hz, hn, mul_zero, le_refl, true_and, and_true]
  exact fun hP => NG_Hp_one hOK P hP

end One

def NGStepsAll (k r c : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) →
        (∀ (R : Reps P) (d : Datum P), R.RT d = ∅) ∨
        (1 ≤ P.Hp ∧
          (∀ (R : Reps P) (d0 : Datum P), Nonempty (NGSteps1 k R d0 c C₀) ∧
            Nonempty (NGSteps2 k R d0 c (fun t => ¬ BBne (H := H) t)) ∧ Nonempty (NGSteps2 k R d0 c (fun _ => True))) ∧
          (P.PrimeTo → ∀ R : Reps P, NGEqStep' P R))

theorem nongeneric_local_bound_of_estimates (k r c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C) (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : NGStepsAll k r c C₀) : NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk P hP
  rcases h F E M hOK V H hrk P hP with h0 | ⟨hH, hS, hE⟩
  · exact NGAt_of_noTerms hOK k C h0
  · exact NGAt_of_steps hOK k c C₀ C hH hC1 hC2 (fun R d0 => (hS R d0).1.some) (fun R d0 => (hS R d0).2.1.some)
      (fun R d0 => (hS R d0).2.2.some) hE

theorem nongeneric_family_bound_of_estimates {eps : ℝ} (Fm : FamP eps) (c : ℕ) (C₀ C : ℝ) (hC1 : (gainBoundConstant c C₀ : ℝ) ≤ C)
    (hC2 : (nongenericConstantNoGain c : ℝ) ≤ C)
    (h : ∀ x (i : Fm.Ix x), 4 * (Fm.D x i).R.rS + 7 ≤ (Fm.D x i).R.k → NGStepsAll (Fm.D x i).R.k (Fm.D x i).R.rS c C₀) :
    NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C := fun x i hk => nongeneric_local_bound_of_estimates _ _ c C₀ C hC1 hC2 (h x i hk)

end NGAll

end Formalism.MainNotions.BridgeLemma

end
