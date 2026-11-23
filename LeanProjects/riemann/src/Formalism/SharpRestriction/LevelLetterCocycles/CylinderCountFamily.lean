import Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal
import Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.SqfCounts

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def LabelCountSpace (A : AllRowsAt D Dall Dgood) : Prop :=
  (∀ S : Set (Tup2 D), A.dimT S = Nat.card {τ : Fin Dall // (fun k => A.labAll k τ) ∈ S}) ∧
    Function.Injective A.inc ∧
    ∀ τ : Fin Dall, D.ntypes.goodTuple (fun k => A.labAll k τ) ↔ τ ∈ Set.range A.inc

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def Adm2At (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) : Prop :=
  adm1 D n₀ Alev C₃ c₃ cb ∧ lawL D A.eVec CL ∧ LabelCountSpace A ∧ TieCountAt A n₀ Alev C₃ cb ∧ TieAdmG D

def DeficitBracketBound (Dall Dgood : ℕ) (C c o : ℝ) : Prop :=
  (Dall : ℝ) - (Dgood : ℝ) ≤ C * br2 D c o * (Dall : ℝ)

def ExpDeficitBound' (Dall Dgood : ℕ) (x eps : ℝ) : Prop :=
  (Dall : ℝ) - (Dgood : ℝ) ≤ Real.exp (-(x ^ (eps / 7))) * (Dall : ℝ)

def FamilyDeficitBracketBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), DeficitBracketBound (Fm.D x i) (Dall x i ι) (Dgood x i ι) C c (o x)

def FamilyExpDeficitBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), ExpDeficitBound' (Dall x i ι) (Dgood x i ι) x Fm.ez

def FamilyDeficitTheorem {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ), 0 < c₃ →
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), Adm2At (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL) → ParO Fm →
      FamilyDeficitBracketBound Fm J Dall Dgood ∧ (ParX Fm → FamilyExpDeficitBound Fm J Dall Dgood)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one

theorem labelCountSpace_toAt_of_labelCountGoodInjective {D : D7} (A : AllRows D) (h : LabelCountGoodInjective A) : LabelCountSpace A.toAt := ⟨h.1, h.2.1, h.2.2.2⟩

theorem admissibleDeficitAt_toAt_of_adm2 {D : D7} (A : AllRows D) {n₀ : ℕ} {Alev C₃ c₃ cb CL : ℝ} (h : Adm2 D A n₀ Alev C₃ c₃ cb CL) :
    Adm2At D A.toAt n₀ Alev C₃ c₃ cb CL := ⟨h.1, h.2.1, labelCountSpace_toAt_of_labelCountGoodInjective A h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

theorem badAt_le (D : D7) {Dall Dgood : ℕ} (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) (hc : 0 < c₃)
    (h : Adm2At D A n₀ Alev C₃ c₃ cb CL) :
    ∃ (S0 : Finset (Tup D 0)) (S1 : Finset (Tup D 1)), (∀ t ∈ S0, ¬ goodAt D 0 t) ∧ (∀ t ∈ S1, ¬ goodAt D 1 t) ∧
      (Dall : ℝ) - (Dgood : ℝ) ≤ kF c₃ * (locShare D A.eVec 0 S0 + locShare D A.eVec 1 S1) * (Dall : ℝ) := by
  classical
  obtain ⟨h1, hL, ⟨hT3a, hinj, hgood⟩, ⟨b, hh, hSC, hgap, hC, hf, hb, hpos⟩, -⟩ := h

  have hcount : ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) -
          A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
        Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
          A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S)) := fun k S =>
    h1 A.B.I b A.B.lam A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) A.B.H A.B.σ A.B.w A.B.Hs A.B.σs A.B.tens A.B.μf
      A.B.fund A.B.R (A.ReT (cyl D k S)) hh (hSC k S).1 (hSC k S).2 hgap hC hf hb
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
      have := D.R.ord_pos
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

def LocU {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) {Dall Dgood : ∀ x i, J x i → ℕ}
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ CL x₂ : ℝ,
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), lawL (Fm.D x i) (A x i ι).eVec CL ∧ TieAdmG (Fm.D x i)) → ParO Fm →
      ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
        ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (ι : J x i), LocalShareBound (Fm.D x i) (A x i ι).eVec C c (o x)

theorem family_bound_of_uniform_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) (hL : LocU Fm J A) :
    FamilyDeficitTheorem Fm J Dall Dgood A := by
  unfold FamilyDeficitTheorem
  intro n₀ Alev C₃ c₃ cb CL x₂ hc hAdm hO
  obtain ⟨C, c, hc0, o, ho, x0, hx0⟩ :=
    hL CL x₂ (fun x hx i ι => ⟨(hAdm x hx i ι).2.1, (hAdm x hx i ι).2.2.2.2⟩) hO
  have hk := Formalism.MainNotions.FamilyNumericLemmas.kF_nonneg hc
  have key : ∀ x ≥ max x0 x₂, ∀ (i : Fm.Ix x) (ι : J x i),
      (Dall x i ι : ℝ) - Dgood x i ι ≤ (kF c₃ * (2 * C)) * br2 (Fm.D x i) c (o x) * Dall x i ι := by
    intro x hx i ι
    obtain ⟨S0, S1, h0, h1, hle⟩ := badAt_le (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL hc
      (hAdm x (le_trans (le_max_right _ _) hx) i ι)
    have hp := hx0 x (le_trans (le_max_left _ _) hx) i ι
    have e0 := hp 0 S0 h0
    have e1 := hp 1 S1 h1
    have hD : (0 : ℝ) ≤ Dall x i ι := Nat.cast_nonneg _
    calc (Dall x i ι : ℝ) - Dgood x i ι
        ≤ kF c₃ * (locShare (Fm.D x i) (A x i ι).eVec 0 S0 + locShare (Fm.D x i) (A x i ι).eVec 1 S1) *
          Dall x i ι := hle
      _ ≤ kF c₃ * (2 * C * br2 (Fm.D x i) c (o x)) * Dall x i ι := by
        apply mul_le_mul_of_nonneg_right _ hD
        apply mul_le_mul_of_nonneg_left _ hk
        linarith
      _ = (kF c₃ * (2 * C)) * br2 (Fm.D x i) c (o x) * Dall x i ι := by ring
  constructor
  · unfold FamilyDeficitBracketBound
    exact ⟨kF c₃ * (2 * C), c, hc0, o, ho, max x0 x₂, key⟩
  · intro hX
    unfold Formalism.MainNotions.ArithmeticCylinders.ParX at hX
    obtain ⟨x1, hx1⟩ := hX (kF c₃ * (2 * C)) c o hc0 ho
    unfold FamilyExpDeficitBound
    refine ⟨max x1 (max x0 x₂), fun x hx i ι => ?_⟩
    unfold ExpDeficitBound'
    exact le_trans (key x (le_trans (le_max_right _ _) hx) i ι)
      (mul_le_mul_of_nonneg_right (hx1 x (le_trans (le_max_left _ _) hx) i) (Nat.cast_nonneg _))

private theorem lawL_mono' {D : D7} {eV : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))}
    {CL CL' : ℝ} (h : CL ≤ CL') (hL : lawL D eV CL) : lawL D eV CL' := by
  intro k v
  obtain ⟨h1, h2, h3⟩ := hL k v
  refine ⟨h1, fun f hf hsq => ⟨(h2 f hf hsq).1, (h2 f hf hsq).2.trans ?_⟩, h3⟩
  gcongr

theorem locU_of_propW {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) {Dall Dgood : ∀ x i, J x i → ℕ}
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι))
    (x₃ : ℝ) (hW : ∀ x ≥ x₃, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocalShareBounds.PropW (Fm.D x i)) : LocU Fm J A := by
  unfold LocU
  intro CL x₂ hLT hO
  have hCL' : 0 ≤ max CL 0 := le_max_right _ _
  have hpos : 0 < 1 / ((max CL 0 + 1) * 2 ^ 12) :=
    div_pos one_pos (mul_pos (by linarith) (by norm_num))
  unfold Formalism.MainNotions.ArithmeticCylinders.ParO at hO
  obtain ⟨x₁, hx₁⟩ := hO _ hpos
  refine ⟨10 ^ 10, 1 / 5, by norm_num, fun _ => 0, tendsto_const_nhds, max x₁ (max x₂ x₃),
    fun x hx i ι => ?_⟩
  have hx1 : x ≥ x₁ := le_trans (le_max_left _ _) hx
  have hx2 : x ≥ x₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x ≥ x₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hL, hA⟩ := hLT x hx2 i ι
  exact Formalism.MainNotions.N.LocalShareBounds.provedLocal_of_law (hW x hx3 i) hCL' (lawL_mono' (le_max_left CL 0) hL) hA
    (fun k => hx₁ x hx1 i k)

theorem family_bound_of_weight_property {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι))
    (x₃ : ℝ) (hW : ∀ x ≥ x₃, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocalShareBounds.PropW (Fm.D x i)) : FamilyDeficitTheorem Fm J Dall Dgood A := family_bound_of_uniform_local Fm J Dall Dgood A (locU_of_propW Fm J A x₃ hW)

theorem family_bound_all {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : FamilyDeficitTheorem Fm J Dall Dgood A := family_bound_of_weight_property Fm J Dall Dgood A 0 fun x _ i =>
    Formalism.MainNotions.N.LocalShareBounds.propW_of_counts (Formalism.MainNotions.N.LocalShareBounds.counts_closed _)

end Formalism.MainNotions.N.CylinderCountFamily
