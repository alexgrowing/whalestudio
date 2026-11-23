import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

variable (D : D7) {Dall Dgood : ℕ}

def CountCylAt (A : AllRowsAt D Dall Dgood) (c₃ : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    |(A.dimT (cyl D k S) : ℝ) -
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))

def CylinderCountUniformAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) : Prop :=
  CountCylAt D A c₃ ∧ lawL D A.eVec CL ∧ LabelCountSpace A ∧ TieCountAt A n₀ Alev C₃ cb ∧ TieAdmG D

theorem badAt_leC (D : D7) {Dall Dgood : ℕ} (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) (hc : 0 < c₃)
    (h : CylinderCountUniformAt D A n₀ Alev C₃ c₃ cb CL) :
    ∃ (S0 : Finset (Tup D 0)) (S1 : Finset (Tup D 1)), (∀ t ∈ S0, ¬ goodAt D 0 t) ∧ (∀ t ∈ S1, ¬ goodAt D 1 t) ∧
      (Dall : ℝ) - (Dgood : ℝ) ≤ kF c₃ * (locShare D A.eVec 0 S0 + locShare D A.eVec 1 S1) * (Dall : ℝ) := by
  classical
  obtain ⟨hcount, hL, ⟨hT3a, hinj, hgood⟩, ⟨b, hh, hSC, hgap, hC, hf, hb, hpos⟩, -⟩ := h
  set dS := A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e with hdS
  set ε := Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) with hε

  have hDS : ∀ (k : Fin 2) (S : Finset (Tup D k)),
      A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k (S : Set (Tup D k)))) =
        dS * locShare D A.eVec k S := by
    intro k S
    simp only [hdS, Formalism.MainNotions.S.AutInst.Dstar, locShare]
    rw [A.eT_one k S]
    ring

  have hn : (6 : ℝ) ≤ (A.B.I.n : ℝ) := by
    rw [A.n_eq]; exact_mod_cast Formalism.MainNotions.N.CuspidalLatticeIdempotents.r_ge_six D
  have hf1 : (1 : ℝ) ≤ (A.B.I.f : ℝ) := by
    rw [A.f_eq]
    have : 1 ≤ D.R.f := by
      show 1 ≤ 2 * D.R.ord
      have := (show 1 ≤ D.R.ord from D.R.ord_pos)
      omega
    exact_mod_cast this
  have hlog6 : Real.log 6 ≤ Real.log (A.B.I.n : ℝ) := Real.log_le_log (by norm_num) hn
  have hlog6p : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hεle : ε ≤ Real.exp (-(c₃ * Real.log 6)) := by
    rw [hε]
    apply Real.exp_le_exp.mpr
    have hnf : (1 : ℝ) ≤ (A.B.I.n : ℝ) * (A.B.I.f : ℝ) := by nlinarith
    have : Real.log 6 ≤ (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) := by nlinarith
    nlinarith
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hε1 : ε < 1 := lt_of_le_of_lt hεle (exp_neg_log_six_lt_one hc)

  have hdimU : A.dimT (cyl D 0 Set.univ) = Dall := by
    rw [hT3a]
    have hall : ∀ τ : Fin Dall, (fun k => A.labAll k τ) ∈ cyl D 0 Set.univ := fun τ => by simp [cyl]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card, Fintype.card_fin]
  have hU := hcount 0 Set.univ
  rw [hdimU, cyl_univ, A.eT_univ] at hU
  have hDall : (1 - ε) * dS ≤ (Dall : ℝ) := by
    have := (abs_le.mp hU).1
    nlinarith
  have hDallpos : 0 < (Dall : ℝ) := lt_of_lt_of_le (mul_pos (by linarith) hpos) hDall

  let Sk : (k : Fin 2) → Finset (Tup D k) := fun k =>
    (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D k (A.labAll k τ)).image fun τ => A.labAll k τ
  have hSk : ∀ k, ∀ t ∈ Sk k, ¬ goodAt D k t := by
    intro k t ht
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hτ).2
  have hmem : ∀ (k : Fin 2) (τ : Fin Dall),
      (fun k => A.labAll k τ) ∈ cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k)) ↔ ¬ goodAt D k (A.labAll k τ) := by
    intro k τ
    constructor
    · intro hτ; exact hSk k _ hτ
    · intro hτ
      show A.labAll k τ ∈ ((Sk k : Finset (Tup D k)) : Set (Tup D k))
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩, rfl⟩)
  have hdimK : ∀ k, A.dimT (cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k))) =
      (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D k (A.labAll k τ)).card := by
    intro k
    rw [hT3a, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun τ => by rw [hmem k τ]; simp))

  have hDrows : (Finset.univ.filter fun τ : Fin Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)).card =
      Dgood := by
    have : (Finset.univ.filter fun τ : Fin Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) =
        Finset.univ.image A.inc := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      rw [hgood τ]
      simp [Set.mem_range]
    rw [this, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hbad : Dall - Dgood ≤
      (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card +
      (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card := by
    have hsub : (Finset.univ : Finset (Fin Dall)) ⊆
        ((Finset.univ.filter fun τ : Fin Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) ∪
          (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 0 (A.labAll 0 τ))) ∪
        (Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 1 (A.labAll 1 τ)) := by
      intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hg : D.ntypes.goodTuple (fun k => A.labAll k τ)
      · exact Or.inl (Or.inl hg)
      · by_contra hc
        push_neg at hc
        apply hg
        intro k
        fin_cases k
        · exact hc.1.2
        · exact hc.2
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    rw [Finset.card_univ, Fintype.card_fin, hDrows] at this
    omega

  have hK : ∀ k, ((Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D k (A.labAll k τ)).card : ℝ) ≤
      (1 + ε) * (dS * locShare D A.eVec k (Sk k)) := by
    intro k
    have h := hcount k ((Sk k : Finset (Tup D k)) : Set (Tup D k))
    rw [hdimK k, hDS k (Sk k)] at h
    have := (abs_le.mp h).2
    nlinarith
  refine ⟨Sk 0, Sk 1, hSk 0, hSk 1, ?_⟩
  have hl0 := locShare_nonneg D A.eVec CL hL 0 (Sk 0)
  have hl1 := locShare_nonneg D A.eVec CL hL 1 (Sk 1)
  set L := locShare D A.eVec 0 (Sk 0) + locShare D A.eVec 1 (Sk 1) with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hDle : Dgood ≤ Dall := by
    rw [← hDrows]; exact (Finset.card_filter_le _ _).trans (by simp)
  have hbadR : (Dall : ℝ) - (Dgood : ℝ) ≤ (1 + ε) * dS * L := by
    have hcast : ((Dall - Dgood : ℕ) : ℝ) = (Dall : ℝ) - (Dgood : ℝ) := by
      push_cast [hDle]; ring
    have hb : ((Dall - Dgood : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card : ℝ) +
        ((Finset.univ.filter fun τ : Fin Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℝ) := by
      exact_mod_cast hbad
    rw [hcast] at hb
    have := hK 0
    have := hK 1
    rw [hLdef]; nlinarith

  have hkf := kF_mul hc
  have hkf0 := kF_nonneg hc
  have hstep : (1 + ε) * dS * L ≤ kF c₃ * L * (Dall : ℝ) := by
    have h1' : (1 + ε) ≤ kF c₃ * (1 - ε) := by nlinarith
    have h2' : kF c₃ * L * ((1 - ε) * dS) ≤ kF c₃ * L * (Dall : ℝ) :=
      mul_le_mul_of_nonneg_left hDall (mul_nonneg hkf0 hL0)
    have h3 := mul_le_mul_of_nonneg_right h1' (mul_nonneg hpos.le hL0)
    calc (1 + ε) * dS * L = (1 + ε) * (dS * L) := by ring
      _ ≤ kF c₃ * (1 - ε) * (dS * L) := h3
      _ = kF c₃ * L * ((1 - ε) * dS) := by ring
      _ ≤ kF c₃ * L * (Dall : ℝ) := h2'
  have hfin : (Dall : ℝ) - (Dgood : ℝ) ≤ kF c₃ * L * (Dall : ℝ) := by linarith
  exact hfin

def FamilyDeficitBoundOfUniformAdmissibility {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ), 0 < c₃ →
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), CylinderCountUniformAt (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL) → ParO Fm →
      FamilyDeficitBracketBound Fm J Dall Dgood ∧ (ParX Fm → FamilyExpDeficitBound Fm J Dall Dgood)

theorem family_count_of_uniform_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) (hL : LocU Fm J A) :
    FamilyDeficitBoundOfUniformAdmissibility Fm J Dall Dgood A := by
  intro n₀ Alev C₃ c₃ cb CL x₂ hc hA hO
  obtain ⟨C, c, hc0, o, ho, x0, hloc⟩ :=
    hL CL x₂ (fun x hx i ι => ⟨(hA x hx i ι).2.1, (hA x hx i ι).2.2.2.2⟩) hO
  have key : ∀ x ≥ max x0 x₂, ∀ (i : Fm.Ix x) (ι : J x i),
      DeficitBracketBound (Fm.D x i) (Dall x i ι) (Dgood x i ι) (2 * kF c₃ * C) c (o x) := by
    intro x hx i ι
    obtain ⟨S0, S1, h0, h1, hd⟩ :=
      badAt_leC (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL hc (hA x (le_trans (le_max_right _ _) hx) i ι)
    have hl := hloc x (le_trans (le_max_left _ _) hx) i ι
    have e0 := hl 0 S0 h0
    have e1 := hl 1 S1 h1
    have hK := kF_nonneg hc
    have hD0 : (0 : ℝ) ≤ (Dall x i ι : ℝ) := Nat.cast_nonneg _
    unfold DeficitBracketBound
    calc ((Dall x i ι : ℕ) : ℝ) - (Dgood x i ι : ℝ)
        ≤ kF c₃ * (locShare _ _ 0 S0 + locShare _ _ 1 S1) * (Dall x i ι : ℝ) := hd
      _ ≤ kF c₃ * (C * br2 (Fm.D x i) c (o x) + C * br2 (Fm.D x i) c (o x)) * (Dall x i ι : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add e0 e1) hK) hD0
      _ = (2 * kF c₃ * C) * br2 (Fm.D x i) c (o x) * (Dall x i ι : ℝ) := by ring
  refine ⟨⟨2 * kF c₃ * C, c, hc0, o, ho, max x0 x₂, fun x hx i ι => key x hx i ι⟩, fun hX => ?_⟩
  obtain ⟨x1, hx1⟩ := hX (2 * kF c₃ * C) c o hc0 ho
  refine ⟨max x1 (max x0 x₂), fun x hx i ι => ?_⟩
  have h1 := key x (le_trans (le_max_right _ _) hx) i ι
  have h2 := hx1 x (le_trans (le_max_left _ _) hx) i
  have hD0 : (0 : ℝ) ≤ (Dall x i ι : ℝ) := Nat.cast_nonneg _
  unfold DeficitBracketBound at h1
  unfold ExpDeficitBound'
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hD0)

theorem family_count_of_weight_property {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι))
    (x₃ : ℝ) (hW : ∀ x ≥ x₃, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocalShareBounds.PropW (Fm.D x i)) : FamilyDeficitBoundOfUniformAdmissibility Fm J Dall Dgood A :=
  family_count_of_uniform_local Fm J Dall Dgood A (Formalism.MainNotions.N.CylinderCountFamily.locU_of_propW Fm J A x₃ hW)

theorem family_count_all {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : FamilyDeficitBoundOfUniformAdmissibility Fm J Dall Dgood A :=
  family_count_of_weight_property Fm J Dall Dgood A 0 fun x _ i =>
    Formalism.MainNotions.N.LocalShareBounds.propW_of_counts (Formalism.MainNotions.N.LocalShareBounds.counts_closed (Fm.D x i))

end Formalism.MainNotions.N.CylinderCountFamily
