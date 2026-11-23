import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfUnramifiedLifting

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module

variable {l : ℕ} [Fact l.Prime]

theorem fd_mu (m : ℕ) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}) := by
  classical
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have hfin : Set.Finite {x : Om l | x ^ (l ^ m) = 1} := by
    have : {x : Om l | x ^ (l ^ m) = 1} ⊆
        ((Polynomial.nthRoots (l ^ m) (1 : Om l)).toFinset : Set (Om l)) := by
      intro x hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hl).2 hx
    exact (Finset.finite_toSet _).subset this
  have := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

def richLL (K LL : FinExt l) (m : ℕ) : FinExt l :=
  ⟨(bigLL K LL).1 ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}, by
    have := (bigLL K LL).2
    have := fd_mu (l := l) m
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_richLL (K LL : FinExt l) (m : ℕ) : LL.1 ≤ (richLL K LL m).1 := (le_bigLL K LL).trans le_sup_left

theorem caseA_richLL (K LL : FinExt l) (m : ℕ) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) :
    CaseA K (richLL K LL m) :=
  ⟨hK, h2, le_rfl, fun h => absurd h h2, (le_inf le_rfl hK).trans le_sup_left, fun τ x =>
    (le_sup_left : (bigLL K LL).1 ≤ (richLL K LL m).1)
      ((le_sup_right : _ ≤ (bigLL K LL).1) (τ.fieldRange_le_normalClosure ⟨x, rfl⟩))⟩

theorem exists_prim_Om (m : ℕ) : ∃ x : Om l, IsPrimitiveRoot x (l ^ m) := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ m) (Om l))
    (Polynomial.degree_cyclotomic_pos (l ^ m) (Om l) hpos).ne'
  exact ⟨x, (Polynomial.isRoot_cyclotomic_iff).mp hx⟩

theorem prim_richLL (K LL : FinExt l) (m : ℕ) :
    ∃ ζ : ↥(richLL K LL m).1, IsPrimitiveRoot ζ (l ^ m) := by
  obtain ⟨x, hx⟩ := exists_prim_Om (l := l) m
  have hmem : x ∈ (richLL K LL m).1 :=
    (le_sup_right : _ ≤ (richLL K LL m).1) (IntermediateField.subset_adjoin _ _ hx.pow_eq_one)
  exact ⟨⟨x, hmem⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hx⟩

theorem lift_of_caseA_rich (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
      (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)),
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) n emb ((Th l).v LL) := by
  intro l _ K LL n _ emb
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  intro hL h5
  have hn := hL.2.2.1
  subst hn
  have h5' : 5 ≤ l := by rwa [(Th l).PD_p K] at h5
  have hK : K.1 ≤ MaximalUnramifiedExtension l := by
    intro x hx
    obtain ⟨y, hy⟩ := hL.1.2 ⟨x, hx⟩
    have : (y : Om l) = x := congrArg Subtype.val hy
    rw [← this]
    exact y.2.2
  set m := N (finrank ℚ_[l] ↥(K0 K))
  have hA := caseA_richLL K LL m hK (by omega)
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥(richLL K LL m).1) := Fintype.ofFinite _
  have H' : ThmELiftAt ((Th l).PD K) (O := ↥(OL (richLL K LL m))) (finrank ℚ_[l] ↥(K0 K))
      (fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      ((Th l).v (richLL K LL m)) := by
    intro hL'
    obtain ⟨a, ha⟩ := exists_rot (PD := (Th l).PD K)
      (emb := fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      (Wf l K (richLL K LL m) hA).emb_bij.2
      hL'.2.2.2.2.1 (Wf l K (richLL K LL m) hA).emb_σ
    have := thmELiftAt_rot (Wf l K (richLL K LL m) hA).emb a
      (hLift l K (richLL K LL m) hA h5' (prim_richLL K LL m))
    rw [← ha] at this
    exact this hL'
  exact thmELiftAt_bc (IntermediateField.inclusion (le_richLL K LL m)) ((Th l).v (richLL K LL m))
    emb (richLL K LL m).2 (by rw [(Th l).PD_p K]; exact (Th l).v_l _)
    ⟨inferInstance, Formalism.BasicNotions.Examples₂.LB.OL_dvr _, Formalism.BasicNotions.Examples₂.LB.OL_frac _⟩
    (hBC l K LL (richLL K LL m) (le_richLL K LL m)) H' hL h5

theorem local_theorem_of_cyclotomic_lift (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) : LiftingTheoremLocalTheory Th 800 :=
  ⟨lift_of_caseA_rich Th N Wf hLift hBC, thmEBound_holds⟩

end Formalism.MainNotions.N.Ln03
