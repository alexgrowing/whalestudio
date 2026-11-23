import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Mass

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}

instance pointUnique (D : D7) (d : ℕ) : Unique (VC D 0 d) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

theorem hf_zero (D : D7) (T : Tor D) {d : ℕ} (z w : VC D 0 d) : Hf D T z w = 0 := by simp [Hf]

theorem iop_id (D : D7) (T : Tor D) {d : ℕ} (A B : AddSubgroup (VC D 0 d)) (G : VC D 0 d → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  have : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  have : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hf_zero]
  simp
  congr 1
  exact Subsingleton.elim _ _

theorem hecke_real {d : ℕ} (χ : HeckeU D d) (g : GA D 0) (x : (AE D)ˣ)
    (hx : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1))
    (e : x = Matrix.GeneralLinearGroup.det (g : GL (Fin 0) (AE D)) * sgU D x) : χ.f x = 1 := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.SplitCharacter.exists_split_character D d χ 0
  rw [← hc g x hx e, Subsingleton.elim g 1, map_one]

def weilPoint (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {d : ℕ} (χ : HeckeU D d) : WeilO D cc δ 0 d (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := RankZero.triv D
  chV' := χ
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intro g g' x x' L₁ L₁' _ _ hx e _ _ _
    rw [iop_id, hecke_real χ g x (fun q hq hi => (hx q hq hi).1) e]
    simp [RankZero.triv]

theorem taylor_const (D : D7) {d : ℕ} (α : Mono D 0 d) (c : ℂ) : taylor D (fun _ => c) α = c := by
  have : α = 0 := by ext k; exact k.2.2.elim0
  subst this
  have h : ∀ (k : ℕ) (v : Fin k → VC D 0 d), k = 0 → iteratedFDeriv ℂ k (fun _ : VC D 0 d => c) 0 v = c := by
    intro k v hk; subst hk; simp
  unfold taylor
  rw [h _ _ (by simp)]
  simp

theorem normSq_one (D : D7) (T : Tor D) {d : ℕ} (A : AddSubgroup (VC D 0 d)) : normSq D T A (fun _ => 1) = 1 := by
  have hex : ∃ Fd : Set (VC D 0 d), MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume := by
    refine ⟨Set.univ, MeasureTheory.IsAddFundamentalDomain.mk' (by simp) fun x => ⟨0, by simp, fun y _ => Subsingleton.elim _ _⟩⟩
  have hs := Classical.epsilon_spec hex
  unfold normSq
  simp only [hf_zero]
  set Fd := Classical.epsilon (fun Fd : Set (VC D 0 d) => MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (VC D 0 d)) Set.univ = 1 := by
    simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  have hF : Fd = Set.univ := by
    have hc := hs.ae_covers
    by_contra hne
    have he : Fd = ∅ := by
      rcases Set.eq_empty_or_nonempty Fd with h | ⟨x, hx⟩
      · exact h
      · exact absurd (Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y x]; exact hx) hne
    rw [he] at hc
    simp only [Set.mem_empty_iff_false, exists_false, Filter.eventually_false_iff_eq_bot,
      MeasureTheory.ae_eq_bot] at hc
    rw [hc] at hv; simp at hv
  rw [hF]
  simp [MeasureTheory.average_eq, MeasureTheory.Measure.real, hv]

theorem vac_one (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (d : ℕ) : oddE0 D cc δ t0 0 d (fun _ => 1) := by
  have : IsEmpty (Fin (fF D * 0 * d)) := ⟨fun i => by have := i.2; simp at this⟩
  have hon : OnB D (fun _ : Fin (fF D * 0 * d) => (0 : Matrix (Fin d) (Fin 0) D.host.E)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  refine ⟨⟨differentiable_const _, fun x _ z => ?_⟩, fun α => ?_, ?_, ⟨fun _ => 0, 1, hon, ⟨one_mem _, fun σ => ?_⟩, ?_⟩, ?_⟩
  · simp [al, U, hf_zero]
  · rw [taylor_const]; exact one_mem _
  · rw [La0, normSq_one]; simp
  · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
    rw [this]; simp
  · rw [iop_id]; funext z; simp [pullB]
  · intro p _ lam _
    refine ⟨fun _ => 0, 1, hon, ⟨linearIndependent_empty_type, fun i => isEmptyElim i,
      fun y _ => ⟨1, by simp, fun i => isEmptyElim i, Subsingleton.elim _ _⟩⟩, one_mem _, ?_, ?_, ?_⟩
    · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
      simp [lamC, this]
    · have hi : ((LaB D (tor0 D cc δ) (fun _ : Fin (fF D * 0 * d) => (0 : Matrix (Fin d) (Fin 0) D.host.E))).addSubgroupOf
          (La0 D (tor0 D cc δ) 0 d)).index = 1 := by
        rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
      rw [hi]; simp
    · rw [iop_id]; funext z; simp [pullB]

def pairPoint (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (k m : ℕ) (χ : HeckeU D (2 * k))
    (hχ : ∀ τ, χ.n τ = 2 * ((k : ℤ) + m)) : Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 (Nat.zero_le _) (even_two_mul k) (vac_one D cc δ t0 (2 * k)) (weilPoint D cc δ χ) (fun _ => m)
    (fun τ => by simp only [weilPoint, hχ]; push_cast; ring) (fun _ _ => rfl) (fun _ _ => ⟨1, by simp, by simp [weilPoint]⟩)

def mass (D : D7) (d : ℕ) : ℚ := ∑ᶠ h : Cls D d (intG D d), ((gam D (intG D d) h.out : ℚ))⁻¹

theorem mass_pos (D : D7) (d : ℕ) : 0 < mass D d := by
  have := (cls_finite_card_le D d).1
  have := Fintype.ofFinite (Cls D d (intG D d))
  have : Nonempty (Cls D d (intG D d)) := ⟨Quotient.mk'' 1⟩
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun h _ => ?_) Finset.univ_nonempty
  have := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D d _ le_rfl h.out).1
  positivity

theorem coord_pairPoint (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (k m : ℕ) (χ : HeckeU D (2 * k)) (hχ)
    (h) (T) : (pairPoint crv pt0 k m χ hχ).coord h T = 1 := by
  have ht : ∀ x h T, (pairPoint crv pt0 k m χ hχ).term x h T = 1 := by
    intro x h T
    have hm : minorPol D T = 1 := by
      unfold minorPol
      exact Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => Matrix.det_fin_zero
    show GL3Theta.applyAt0 D (minorPol D T) (fun _ => 1) = 1
    rw [hm]
    have := taylor_const D (d := 2 * k) 0 1
    simp [GL3Theta.applyAt0, MvPolynomial.support_one]
    exact this
  unfold Pair.coord
  simp only [ht]
  show ∑ᶠ x : Cls D 0 (intG D 0), ((gam D (intG D 0) x.out : ℂ))⁻¹ * 1 = 1
  rw [finsum_unique, RankZero.gam0]; simp

theorem norm_pairPoint (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (k m : ℕ) (χ : HeckeU D (2 * k)) (hχ) :
    (pairPoint crv pt0 k m χ hχ).norm = (mass D (2 * k) : ℝ) := by
  have hq : ∀ h, (pairPoint crv pt0 k m χ hχ).sq h = 1 := by
    intro h
    unfold Pair.sq
    simp only [coord_pairPoint]
    have : Unique (Tup D 0 (2 * k) (fun _ => m)) :=
      ⟨⟨fun τ j => ⟨Fin.elim0, fun i => i.elim0⟩⟩, fun T => funext fun τ => funext fun j =>
        Subtype.ext (funext fun i => i.elim0)⟩
    show ∑ _T : Tup D 0 (2 * k) (fun _ => m), ‖(1 : ℂ)‖ ^ 2 = 1
    simp
  unfold Pair.norm mass
  simp only [hq]
  have := (Rat.castHom ℝ).toAddMonoidHom.map_finsum_of_preimage_zero
    (fun x hx => by simpa using hx) (fun h : Cls D (2 * k) (intG D (2 * k)) => ((gam D (intG D (2 * k)) h.out : ℚ))⁻¹)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_inv, Rat.cast_natCast] at this
  rw [this]
  simp only [mul_one]
  rfl

theorem two_dvd_gam (D : D7) {d : ℕ} (hd : 0 < d) : 2 ∣ gam D (intG D d) 1 := by
  have hmem : (-1 : GL (Fin d) (AE D)) ∈ GA D d := by
    have h := (GA D d).one_mem
    have e : Formalism.UG.cT (sgA D) (-1 : Matrix (Fin d) (Fin d) (AE D)) = -Formalism.UG.cT (sgA D) 1 := by
      ext i j
      simp [Formalism.UG.cT, Matrix.one_apply, apply_ite (sgA D), eq_comm]
    unfold sgA at e
    change _ = _ at h ⊢
    simpa [e] using h
  let u : GA D d := ⟨-1, hmem⟩
  have hr : u ∈ ratG D d := (mem_ratG u).2 ⟨-1, by
    unfold IsRat
    ext i j
    simp [u, Matrix.one_apply, apply_ite (inc D)]⟩
  have h1 := (mem_intG (1 : GA D d)).1 (one_mem _)
  have hi : u ∈ intG D d := (mem_intG u).2 fun i j => by
    have := h1 i j
    constructor
    · simpa [u] using neg_mem this.1
    · simpa [u] using neg_mem this.2
  have hc : gam D (intG D d) 1 = Nat.card (ratG D d ⊓ intG D d : Subgroup (GA D d)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun γ => by simp [Subgroup.mem_inf])
  let v : (ratG D d ⊓ intG D d : Subgroup (GA D d)) := ⟨u, hr, hi⟩
  have hv : orderOf v = 2 := by
    refine orderOf_eq_prime (by ext i j; simp [v, u]) fun h => ?_
    have h2 : (-1 : AE D) = 1 := by
      have := congrArg (fun w : (ratG D d ⊓ intG D d : Subgroup (GA D d)) =>
        ((w.1.1 : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) ⟨0, hd⟩ ⟨0, hd⟩) h
      simpa [v, u] using this
    have h3 : (-1 : D.host.E) = 1 := inc_inj D (by simpa using h2)
    norm_num at h3
  rw [hc, ← hv]
  exact orderOf_dvd_natCard v

theorem exists_pairPoint (D : D7) (k m : ℕ) :
    ∃ (δ t0 : ℂ) (P : Pair D ⊤ δ t0 1), P.a = 0 ∧ P.d = 2 * k ∧ (∀ τ, P.n τ = m) ∧ P.J = intG D P.d ∧
      (∀ h T, P.coord h T = 1) ∧ Nonempty (Tup D P.a P.d P.n) ∧ P.norm = (mass D (2 * k) : ℝ) := by
  obtain ⟨δ, hδ⟩ := exists_crv_top D
  obtain ⟨t0, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D ⊤ δ hδ).1
  obtain ⟨χ, hχ, -⟩ := exists_unramified_heckeU D (2 * k) ((k : ℤ) + m) (even_two_mul k)
  exact ⟨δ, t0, pairPoint hδ ht k m χ hχ, rfl, rfl, fun _ => rfl, rfl, coord_pairPoint hδ ht k m χ hχ,
    ⟨fun τ j => ⟨Fin.elim0, fun i => i.elim0⟩⟩, norm_pairPoint hδ ht k m χ hχ⟩

end GlobalTheory.NormSum.Mass
