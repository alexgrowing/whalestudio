import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InTypeIsoSortedPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdAllAway

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3.FamModel

open Formalism.L2.Col

theorem nb_congr {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {P : Ideal (𝓞 E)} {s y : List ℕ}
    (f : inType P s ≃ₗ[𝓞 E] inType P y) (d : DecoSet E n ST SG) : d.inertSet P s = d.inertSet P y := by
  ext d'
  simp only [DecoSet.inertSet, Set.mem_ofPred_eq, IsInertNbr]
  constructor
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f⟩, ⟨e₂.trans f⟩⟩, hf, hb⟩
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f.symm⟩, ⟨e₂.trans f.symm⟩⟩, hf, hb⟩

theorem op_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : Col.GSD K} (c : Col.DecoPts S E n ST SG)
    (P : HeightOneSpectrum (𝓞 E)) (s : List ℕ) :
    (Col.heckeI c P.asIdeal s).op = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
  obtain ⟨y, hy₁, hy₂, ⟨f⟩⟩ := GlobalTheory.InertTypeIso.inType_iso_sorted_pos P.asIdeal s
  have hnb : ∀ d, c.nbI P.asIdeal s d = c.nbI P.asIdeal y d := by
    intro d
    rw [DecoPts.nbI, DecoPts.nbI, DecoSet.inertNb, DecoSet.inertNb, nb_congr f]
  have hop : (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply, heckeI_op_apply, hnb]
  by_cases hlen : 2 * y.length ≤ n
  · exact Or.inr ⟨y, ⟨hy₁, hy₂, hlen⟩, hop⟩
  · left
    rw [hop]
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply]
    have hempty : c.nbI P.asIdeal y d = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => hlen ?_
      rw [DecoPts.mem_nbI, DecoSet.inertNb] at he
      split_ifs at he with hfin
      · exact GlobalTheory.InertRank.two_mul_length_le P y (c.pts d) (c.pts e) hy₂ (hfin.mem_toFinset.mp he)
      · simp at he
    simp [hempty]

theorem csd_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (Q : offSubI ST SG SG' S0) (s : List ℕ) :
    heckeCSDI S h c SG S0 (Q, s) = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ heckeCSDI S h c SG S0 (Q, s) = heckeCSDI S h c SG S0 (Q, y) := by
  rcases op_zero_or c (offSubI.lev Q).1 s with h0 | ⟨y, hy, hyeq⟩
  · left
    simp only [heckeCSDI, Col.heckeFamI]
    rw [h0, map_zero]
  · right
    refine ⟨y, hy, ?_⟩
    simp only [heckeCSDI, Col.heckeFamI]
    rw [hyeq]

theorem rank_rows (R : Ranks) : R.N R.m - 1 = R.r + R.m * R.t := by
  have hm := R.two_le_m
  simp only [Ranks.N, Ranks.r, Nat.mul_succ]
  generalize R.m * R.t = x
  omega

theorem inertJunk_col {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) where
  R t Q s := by
    rcases csd_zero_or (Col.mtildeKGSD W Ch sel t.1) (Col.mtildeKOk W Ch sel t.1 hX) (formPts _ _) Pr.vGs S0 Q s with
      h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · refine Or.inr ⟨y, ?_, hyeq⟩
      show Col.InertTypeOk (R.r + R.m * R.t) y
      rw [← rank_rows R]
      exact hy
  L j t Q s := by
    rcases csd_zero_or (Col.mtKGSD W Ch sel t.1 (j.1 + 1)) (Col.mtKOk W Ch sel t.1 hX (j.1 + 1)) (formPts _ _) Pr.vGs S0
        Q s with h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hyeq⟩

theorem not_inertJunk {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn K G Pl0 T m) (t : T) [Nontrivial (A.MtildeCSD t).Forms] :
    ¬ InertJunk (⟨A, fun _ => Set.univ, fun _ k => if k.2 = [0] then (2 : K) • 1 else 1, fun _ _ _ => 1, fun _ e => e⟩ :
      FamIn3 K G Pl0 Unit (List ℕ) T m) := by
  intro hJ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rcases hJ.R t ⟨(), Set.mem_univ _⟩ [0] with h | ⟨s', ⟨_, hpos, _⟩, heq⟩
  · dsimp only at h
    rw [if_pos rfl, smul_eq_zero] at h
    rcases h with h | h
    · exact h2 h
    · exact one_ne_zero h
  · have hs : s' ≠ [0] := by
      rintro rfl
      exact lt_irrefl 0 (hpos 0 (List.mem_singleton_self 0))
    dsimp only at heq
    rw [if_pos rfl, if_neg hs, two_smul] at heq
    exact one_ne_zero (add_eq_left.mp heq)

theorem goodGeneric_linear {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (ψ : G →* Kˣ) (P : Subgroup G) :
    GoodGeneric {fun g => (ψ g : K)} P (ψ.comp P.subtype) := by
  classical
  intro χ hχ
  rw [Finset.mem_singleton] at hχ
  subst hχ
  intro h0
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key := congrArg (MonoidAlgebra.lift K K G ((Units.coeHom K).comp ψ)) h0
  rw [map_mul, map_zero, chiIdem, lvlIdem, map_sum, map_sum] at key
  simp only [MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype,
    map_inv, map_one, Units.val_one, smul_eq_mul, mul_assoc, Units.inv_mul, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at key
  rw [← Nat.card_eq_fintype_card (α := P), mul_inv_cancel₀ hP, mul_one, one_div, mul_inv_cancel₀ hG] at key
  exact one_ne_zero key

private lemma chiIdem_mul_single {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (χ : G → K)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) (h : G) (c : K) :
    chiIdem χ * MonoidAlgebra.single h c = (c * χ h) • chiIdem χ := by
  have h1 : χ 1 * χ 1 = χ 1 := by rw [← hχ, one_mul]
  have hh : χ h * χ h⁻¹ = χ 1 := by rw [← hχ, mul_inv_cancel]
  simp only [chiIdem, Finset.sum_mul, MonoidAlgebra.single_mul_single, Finset.smul_sum,
    MonoidAlgebra.smul_single, smul_eq_mul]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun u => ?_
  rw [Equiv.coe_mulRight, mul_inv_rev, hχ h⁻¹ u⁻¹]
  congr 1
  linear_combination (-(c * χ u⁻¹ / (Fintype.card G : K))) * h1 + (-(c * χ u⁻¹ * χ 1 / (Fintype.card G : K))) * hh

private lemma chiIdem_mul_lvlIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (χ : G → K)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) :
    chiIdem χ * lvlIdem P ψ = (∑ h : P, (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K) * χ h) • chiIdem χ := by
  simp only [lvlIdem, Finset.mul_sum, Finset.sum_smul, chiIdem_mul_single χ hχ]
  congr 1
  exact congrArg (@Finset.univ (↥P)) (Subsingleton.elim _ _)

private lemma sum_char_subgroup_eq_zero_of_eq_neg_one {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (χ : G → K)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) (P : Subgroup G) [Fintype P] (a : P) (ha : χ a = -1) :
    ∑ h : P, χ h = 0 := by
  have e := Fintype.sum_equiv (Equiv.mulLeft a) (fun h : P => χ ((a * h : P) : G)) (fun h : P => χ h) fun _ => rfl
  simp only [Subgroup.coe_mul, hχ, ha, neg_one_mul, Finset.sum_neg_distrib] at e
  have h2 : (2 : K) * ∑ h : P, χ h = 0 := by linear_combination -e
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

theorem not_goodGeneric_sign : ¬ GoodGeneric (K := ℚ) (G := ℤˣ) {fun g : ℤˣ => ((g.val : ℤ) : ℚ)} ⊤ 1 := by
  classical
  intro hG
  have hχ : ∀ a b : ℤˣ, (((a * b).val : ℤ) : ℚ) = ((a.val : ℤ) : ℚ) * ((b.val : ℤ) : ℚ) := fun a b => by simp
  apply hG _ (Finset.mem_singleton_self _)
  have hs := sum_char_subgroup_eq_zero_of_eq_neg_one (fun g : ℤˣ => ((g.val : ℤ) : ℚ)) hχ ⊤ ⟨-1, Subgroup.mem_top _⟩ (by simp)
  rw [chiIdem_mul_lvlIdem _ hχ]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, ← Finset.mul_sum, hs, mul_zero, zero_smul]

section Real

open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

theorem trISepWith_self : TrISepWith A3 A3.trI ↔ A3.fam3.TrISep := by
  rfl

theorem trISepWith_id : TrISepWith A3 fun _ e => e := by
  intro j p _ p' _ h
  exact h

theorem labW_single (j : Fin D.R.m) {I : Type} (pl : I → Pl D.host.E) (d : I → List ℤ) (c : Pl D.host.E → List ℤ → ℂ) (i : I)
    (h : IsLab (Wc D j) (pl i) (d i)) : labW j pl (fun i => Finsupp.single (d i) 1) c i = c (pl i) (d i) := by
  rw [labW, evC, Finsupp.sum_single_index (by simp)]
  simp [h]

variable {A3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftDict_eigen {R : RealDat3 D A3 Ks} {j : Fin D.R.m} {t : T} {pl cV cW} (H : LiftDict R j t pl cV cW) (h)
    (hh : IsOpsV R.toRealDat j t h) (x) (s : (A3.liftI j t).OpIx → D.what₂.LL) (hx : ∀ i, (A3.liftI j t).opAll i x = s i • x) (i) :
    h (pl i) (cV i) (R.jV j t x) = D.what₂.embLL (s i) • R.jV j t x := by
  exact (H.op h hh i x).symm.trans ((congrArg (R.jV j t) (hx i)).trans (map_smulₛₗ (R.jV j t) (s i) x))

theorem rowDict_eigen {R : RealDat3 D A3 Ks} {t : T} {pl cX c0} (H : RowDict R t pl cX c0) (h)
    (hh : IsOpsX R.toRealDat t h) (x) (s : (A3.rowI t).OpIx → D.what₂.LL) (hx : ∀ i, (A3.rowI t).opAll i x = s i • x) (i) :
    h (pl i) (cX i) (R.jX t x) = D.what₂.embLL (s i) • R.jX t x := by
  exact (H.op h hh i x).symm.trans ((congrArg (R.jX t) (hx i)).trans (map_smulₛₗ (R.jX t) (s i) x))

end Real

end GlobalTheory.Hk3.FamModel

end
