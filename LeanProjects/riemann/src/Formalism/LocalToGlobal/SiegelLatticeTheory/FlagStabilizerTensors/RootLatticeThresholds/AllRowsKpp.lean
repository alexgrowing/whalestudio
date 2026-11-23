import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsKpp

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsRhoX
  Formalism.L2.SG.Pf.AllRowsFin

def JPred (kk s : ℕ) {N g : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : Prop :=
  IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0

variable {D : D7}

abbrev cjM (P γ : G0g D.nd) (kv : Σ k : Fin 2, D.nd.PlG k) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) :=
  (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

def KppShape (X : HidaSetting D) : Prop :=
  ∃ (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), (∀ kv, ψ kv ≠ 1) ∧
    ∀ x : KSub X.B.I,
      ((x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)) ∧
      ((x : X.B.I.Gf) ∈ X.K2 → X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)))

def KppFwd (X : HidaSetting D) : Prop :=
  ∃ (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), (∀ kv, ψ kv ≠ 1) ∧
    ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      (∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)) ∧
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))

theorem blk_mono (rS k : ℕ) {i j : ℕ} (h : i ≤ j) : Formalism.MainNotions.StandardLattice.blk rS k i ≤ Formalism.MainNotions.StandardLattice.blk rS k j := by
  unfold Formalism.MainNotions.StandardLattice.blk
  split_ifs <;> omega

theorem jPred_iff (kk s : ℕ) {N g : ℕ} (hN : N = kk + 2 * s + 1) (M : Matrix (Fin N) (Fin N) (ZMod g)) :
    JPred kk s M ↔ Formalism.MainNotions.StandardLattice.IsRowLev kk s M := by
  subst hN
  constructor
  · rintro ⟨hU, hz⟩
    refine ⟨fun i j hij => ?_, fun i => (hU i i).2 rfl, fun i j _ hji => (hU i j).1 hji,
      fun i j hj hij hbi => ?_⟩
    · have hji : j < i := by
        by_contra h
        push_neg at h
        have := blk_mono s kk (Fin.le_def.1 h)
        omega
      exact (hU i j).1 hji
    · have hne : i.val ≠ s + kk := fun h => hij (Fin.ext (h.trans hj.symm))
      have hi1 : s ≤ i.val ∧ i.val < s + kk := by
        unfold Formalism.MainNotions.StandardLattice.blk at hbi
        split_ifs at hbi with h1 h2 <;> omega
      have h5 := hz i.val hi1.1 hi1.2
      unfold entN at h5
      rw [dif_pos ⟨i.isLt, by omega⟩] at h5
      have hj' : j = ⟨s + kk, by omega⟩ := Fin.ext hj
      rw [hj']
      exact h5
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun a b => ⟨fun hba => ?_, fun hab => by subst hab; exact h2 a⟩, fun a ha1 ha2 => ?_⟩
    · have hle := blk_mono s kk (Fin.le_def.1 hba.le)
      rcases lt_or_eq_of_le hle with h | h
      · exact h1 a b h
      · exact h3 a b h.symm hba
    · unfold entN
      rw [dif_pos ⟨by omega, by omega⟩]
      refine h4 _ _ rfl ?_ ?_
      · intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · show Formalism.MainNotions.StandardLattice.blk s kk a = s
        unfold Formalism.MainNotions.StandardLattice.blk
        split_ifs <;> omega

theorem r_eq (D : D7) : D.R.r = D.R.k + 2 * (D.R.m / 2 - 1) + 1 := by
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨t, ht⟩ := h1
  show D.R.k + D.R.m - 1 = _
  omega

open Classical in

def JJ (P : G0g D.nd) : Finset (G0g D.nd) :=
  Finset.univ.filter fun γ => ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P γ kv)

def cJ (D : D7) (g : ℕ) : ℕ :=
  Nat.card {A : GL (Fin D.R.r) (ZMod g) // Formalism.MainNotions.StandardLattice.IsRowLev D.R.k (D.R.m / 2 - 1)
    (A : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g))}

theorem card_conj (kv : Σ k : Fin 2, D.nd.PlG k) (Q : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Nat.card {M : GL (Fin D.R.r) (ZMod (D.host.g kv.1)) //
      JPred D.R.k (D.R.m / 2 - 1) ((Q⁻¹ * M * Q : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))} = cJ D (D.host.g kv.1) := by
  unfold cJ
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj Q⁻¹).toEquiv ?_
  intro M
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  exact jPred_iff _ _ (r_eq D) _

theorem prod_sigma_const (c : Fin 2 → ℕ) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), c kv.1 = c 0 ^ D.R.f * c 1 ^ D.R.f := by
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]

theorem card_JJ (P : G0g D.nd) : (JJ P).card = cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f := by
  classical
  rw [← prod_sigma_const (fun k => cJ D (D.host.g k))]
  unfold JJ
  rw [← Fintype.card_subtype]
  calc Fintype.card {x : G0g D.nd // ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P x kv)}
      = Fintype.card (∀ kv : (Σ k : Fin 2, D.nd.PlG k), {M : GL (Fin D.R.r) (ZMod (D.host.g kv.1)) //
          JPred D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * M * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))}) :=
        Fintype.card_congr (@Equiv.subtypePiEquivPi (Σ k : Fin 2, D.nd.PlG k)
          (fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
          (fun kv M => JPred D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * M * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))
    _ = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), cJ D (D.host.g kv.1) := by
      rw [Fintype.card_pi]
      refine Finset.prod_congr rfl fun kv _ => ?_
      rw [← Nat.card_eq_fintype_card]
      exact card_conj kv (P kv)

theorem jPred_one (kk s : ℕ) {N g : ℕ} : JPred kk s (1 : Matrix (Fin N) (Fin N) (ZMod g)) := by
  refine ⟨fun a b => ⟨fun hba => ?_, fun hab => ?_⟩, fun a _ ha => ?_⟩
  · exact Matrix.one_apply_ne (ne_of_gt hba)
  · subst hab
    exact Matrix.one_apply_eq a
  · unfold entN
    split_ifs with h
    · exact Matrix.one_apply_ne (by intro h'; have := congrArg Fin.val h'; simp at this; omega)
    · rfl

theorem cJ_pos (D : D7) (k : Fin 2) : 0 < cJ D (D.host.g k) := by
  unfold cJ
  have : Nonempty {A : GL (Fin D.R.r) (ZMod (D.host.g k)) // Formalism.MainNotions.StandardLattice.IsRowLev D.R.k (D.R.m / 2 - 1)
      (A : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))} :=
    ⟨⟨1, (jPred_iff _ _ (r_eq D) _).1 (by rw [Units.val_one]; exact jPred_one _ _)⟩⟩
  exact Nat.card_pos

section Count

open PI.MassDataKppVolLemmas

variable (X : HidaSetting D)

def KgSub : Subgroup X.B.I.Gf where
  carrier := X.B.I.Kg X.B.g
  mul_mem' := fun hx hy => Kg_mul' X.B.I X.B.g hx hy
  one_mem' := one_mem_Kg' X.B.I X.B.g
  inv_mem' := fun hx => Kg_inv' X.B.I X.B.g hx

abbrev concreteLevelAdelicSubset : Subgroup X.B.I.Gf := levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X)

theorem le1 : KgSub X ≤ KSub X.B.I := fun _ hx => hx.1
theorem le2 : KgSub X ≤ concreteLevelAdelicSubset X := fun x hx => ((Formalism.L2.SG.Closed.level_subgroup_properties X).1 x hx).1
theorem le3 : concreteLevelAdelicSubset X ≤ KSub X.B.I := fun x hx => Formalism.L2.SG.Count.level_set_le_compact X hx

def rho2 : concreteLevelAdelicSubset X →* G0g D.nd := (rhoX X).comp (Subgroup.inclusion (le3 X))

theorem ker1 : (KgSub X).subgroupOf (KSub X.B.I) = (rhoX X).ker := by
  ext x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, rhoX_eq_one_iff]
  rfl

theorem ker2 : (KgSub X).subgroupOf (concreteLevelAdelicSubset X) = (rho2 X).ker := by
  ext x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, rho2, MonoidHom.comp_apply, rhoX_eq_one_iff]
  rfl

variable {X}

theorem idx1 (hS : Function.Surjective (rhoX X)) :
    (KgSub X).relIndex (KSub X.B.I) = Fintype.card (G0g D.nd) := by
  rw [Subgroup.relIndex, ker1, Subgroup.index_ker, MonoidHom.range_eq_top.2 hS, Subgroup.card_top,
    Nat.card_eq_fintype_card]

theorem idx2 : (KgSub X).relIndex (concreteLevelAdelicSubset X) = Nat.card (rho2 X).range := by
  rw [Subgroup.relIndex, ker2, Subgroup.index_ker]

theorem natCard_codeWordStages_finiteGroup_eq : Fintype.card (G0g D.nd) =
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 0))) ^ D.R.f * Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 1))) ^ D.R.f := by
  classical
  rw [← prod_sigma_const (fun k => Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))), Fintype.card_pi]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [Nat.card_eq_fintype_card]

theorem levelSubgroup_relIndex_eq (hS : Function.Surjective (rhoX X)) :
    (KgSub X).relIndex (concreteLevelAdelicSubset X) = cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hopen : IsOpen ((KgSub X : Set X.B.I.Gf)) := X.B.I.topf_open X.B.g (g_pos X)
  have hc1 := idx1 hS
  have hpos1 : (KgSub X).relIndex (KSub X.B.I) ≠ 0 := by rw [hc1]; exact Fintype.card_ne_zero
  have hmul := Subgroup.relIndex_mul_relIndex (KgSub X) (concreteLevelAdelicSubset X) (KSub X.B.I) (le2 X) (le3 X)
  have hpos2 : (KgSub X).relIndex (concreteLevelAdelicSubset X) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hpos1 hmul.symm
  have hμ1 := Glob_measure_eq_relIndex_mul X.B.μf (KSub X.B.I) (KgSub X) (le1 X) hopen hpos1
  have hμ2 := Glob_measure_eq_relIndex_mul X.B.μf (concreteLevelAdelicSubset X) (KgSub X) (le2 X) hopen hpos2
  have hD := Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X
  unfold Formalism.L2.SG.Pf.RowDictPf.DstarIdx at hD
  have e1 : (X.B.μf X.B.I.Kset).toReal = (Fintype.card (G0g D.nd) : ℝ) * V X := by
    have : X.B.μf X.B.I.Kset = X.B.μf (KSub X.B.I : Set X.B.I.Gf) := rfl
    rw [this, hμ1, ENNReal.toReal_mul, hc1, ENNReal.toReal_natCast]
    rfl
  have e2 : X.volK2 = ((KgSub X).relIndex (concreteLevelAdelicSubset X) : ℝ) * V X := by
    unfold HidaSetting.volK2
    have : X.B.μf X.K2 = X.B.μf (concreteLevelAdelicSubset X : Set X.B.I.Gf) := rfl
    rw [this, hμ2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rfl
  rw [e1, e2] at hD
  unfold Formalism.MainNotions.StandardLattice.idxSig Formalism.MainNotions.StandardLattice.idxRowLoc Formalism.MainNotions.StandardLattice.idxLoc at hD
  rw [natCard_codeWordStages_finiteGroup_eq] at hD
  have hV := V_pos X
  have hJ0 := cJ_pos D 0
  have hJ1 := cJ_pos D 1
  have hG0 : 0 < Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 0))) := Nat.card_pos
  have hG1 : 0 < Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 1))) := Nat.card_pos
  have hD' : (((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 0))) ^ D.R.f *
      Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 1))) ^ D.R.f : ℕ) : ℝ) * V X) /
      (((KgSub X).relIndex (concreteLevelAdelicSubset X) : ℝ) * V X) =
      ((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 0))) : ℝ) / (cJ D (D.host.g 0) : ℝ)) ^ D.R.f *
      ((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 1))) : ℝ) / (cJ D (D.host.g 1) : ℝ)) ^ D.R.f := hD
  have hc2 : (0 : ℝ) < ((KgSub X).relIndex (concreteLevelAdelicSubset X) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hpos2
  rw [mul_div_mul_right _ _ hV.ne', div_pow, div_pow, div_mul_div_comm,
    div_eq_div_iff hc2.ne' (by positivity)] at hD'
  push_cast at hD'
  have hne : ((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f) ≠ 0 := by positivity
  have key := mul_left_cancel₀ hne hD'
  exact_mod_cast key.symm

theorem kppShape_of_fwd (hS : Function.Surjective (rhoX X)) (hF : KppFwd X) : KppShape X := by
  classical
  obtain ⟨P, ψ, hψ, hF⟩ := hF
  refine ⟨P, ψ, hψ, fun x => ⟨⟨fun hx => (hF x hx).1, fun hJ => ?_⟩, fun hx => (hF x hx).2⟩⟩
  set R : Finset (G0g D.nd) := Finset.univ.filter fun γ => γ ∈ (rho2 X).range with hR
  have hRsub : R ⊆ JJ P := by
    intro γ hγ
    rw [hR, Finset.mem_filter] at hγ
    obtain ⟨y, rfl⟩ := hγ.2
    unfold JJ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hF (Subgroup.inclusion (le3 X) y) y.2).1⟩
  have hRcard : R.card = (JJ P).card := by
    rw [card_JJ, ← levelSubgroup_relIndex_eq hS, idx2, hR, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hEq : R = JJ P := Finset.eq_of_subset_of_card_le hRsub hRcard.ge
  have hmem : rhoX X x ∈ R := by
    rw [hEq]; unfold JJ; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hJ⟩
  rw [hR, Finset.mem_filter] at hmem
  obtain ⟨y, hy⟩ := hmem.2
  have h1 : rhoX X ((Subgroup.inclusion (le3 X) y)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, ← hy]
    show (rhoX X (Subgroup.inclusion (le3 X) y))⁻¹ * rhoX X (Subgroup.inclusion (le3 X) y) = 1
    exact inv_mul_cancel _
  have h2 := (rhoX_eq_one_iff X _).1 h1
  have h3 : ((Subgroup.inclusion (le3 X) y)⁻¹ * x : KSub X.B.I).1 ∈ concreteLevelAdelicSubset X := le2 X h2
  have h4 : (y : X.B.I.Gf) * ((Subgroup.inclusion (le3 X) y)⁻¹ * x : KSub X.B.I).1 ∈ concreteLevelAdelicSubset X := (concreteLevelAdelicSubset X).mul_mem y.2 h3
  have e : (y : X.B.I.Gf) * ((Subgroup.inclusion (le3 X) y)⁻¹ * x : KSub X.B.I).1 = x := by
    show (y : X.B.I.Gf) * ((y : X.B.I.Gf)⁻¹ * (x : X.B.I.Gf)) = x
    group
  rw [e] at h4
  exact h4

end Count

end Formalism.L2.SG.Pf.AllRowsKpp
