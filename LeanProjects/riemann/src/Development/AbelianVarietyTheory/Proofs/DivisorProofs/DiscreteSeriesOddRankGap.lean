import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section
namespace GlobalTheory.ParamMatch

theorem lamAt_anti_fin {Rk : Ranks} (h : HCParam Rk) {n : ℕ} (hn : n ≤ Rk.r) :
    StrictAnti fun a : Fin n => Formalism.L2.NTheta.lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have h1 := Formalism.L2.NTheta.lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at h1
  have h2 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ (b : ℕ) - a)
  show Formalism.L2.NTheta.lamAt h b < Formalism.L2.NTheta.lamAt h a
  linarith

theorem enum_fst {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum S lam ε)
    (f : Fin n → ℚ) (hf : StrictAnti f) (hS : S.image Prod.fst = Finset.univ.image f) (a : Fin n) :
    lam a = f a := by
  obtain ⟨h1, q, hq, rfl⟩ := he
  have h3 : StrictAnti q := fun a b hab => by
    have := h1 hab
    rw [hq, hq] at this
    exact_mod_cast this
  have h4 : Finset.univ.image q = Finset.univ.image f := by
    rw [← hS, Finset.image_image]; rfl
  have h5 : q = f := by
    refine (h3.range_inj hf).1 ?_
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) h4
    simpa [Finset.coe_image] using this
  rw [hq, h5]

theorem lamAt_b' {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + j) = -h.b j := by
  have hc : ∀ (x y : ℕ) (hx : x < Rk.m) (hy : y < Rk.m), x = y → h.b ⟨x, hx⟩ = h.b ⟨y, hy⟩ := by
    rintro x _ _ _ rfl; rfl
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  rw [hc _ _ _ j.2 (by omega)]

theorem lamAt_v' {Rk : Ranks} (h : HCParam Rk) (j : Fin (Rk.k - 1)) :
    Formalism.L2.NTheta.lamAt h j = h.v j := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_pos j.2]

theorem parA_fst (D : D7) (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parA (Ptw D) 0 ρ).image Prod.fst = Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  have hk := D.R.m_add_three_le_k
  have hv : (Ptw D).v ρ = (D.hc ρ).v := rfl
  have hb : (Ptw D).b ρ = (D.hc ρ).b := rfl
  ext x
  simp [parA, TPar.Dpar]
  rw [hv, hb]
  constructor
  · rintro (⟨a, rfl, -⟩ | ⟨a, rfl⟩ | ⟨a, rfl, -⟩)
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
    · exact ⟨⟨a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_v' _ a⟩
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    unfold Ranks.r at ha
    by_cases h1 : (a : ℕ) < D.R.k - 1
    · exact Or.inr (Or.inl ⟨⟨a, h1⟩, (lamAt_v' _ ⟨a, h1⟩).symm⟩)
    · let c : Fin D.R.m := ⟨a - (D.R.k - 1), by omega⟩
      have hc : Formalism.L2.NTheta.lamAt (D.hc ρ) a = -(D.hc ρ).b c := by
        rw [← lamAt_b' _ c]; congr 1; simp only [c]; omega
      rw [hc]
      by_cases h2 : (c : ℕ) = 0 ∨ Even (c : ℕ)
      · exact Or.inr (Or.inr ⟨c, rfl, h2⟩)
      · push_neg at h2
        exact Or.inl ⟨c, rfl, h2.1, Nat.not_even_iff_odd.mp h2.2⟩

theorem tauE_inj {D : D7} {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

open Formalism.FrobeniusOrbits in
theorem tauE_ne_conj' {D : D7} (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

theorem lab_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ρ : D.what₂.Tau) :
    lab (sg0 D A) ρ = ρ ∧ labE (sg0 D A) ρ = tauE D ρ := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hb : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => Formalism.IndefR.Conj.labE_base τ
  rw [hs]
  refine ⟨?_, hb ρ⟩
  have hex : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hb ρ)⟩
  unfold lab
  rw [dif_pos hex]
  rcases hex.choose_spec with h | h
  · rw [hb] at h; exact tauE_inj h
  · rw [hb] at h; exact absurd h (tauE_ne_conj' _ _)

theorem parAt_fst {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parAt (Wc D i) (sg0 D A) ρ).image Prod.fst =
      Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  obtain ⟨h1, h2⟩ := lab_base R ρ
  have hpq : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    have hk := D.R.m_add_three_le_k
    have hi := i.2
    rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2]
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [parAt, if_pos (by rw [h1]; exact h2), kapAt, h1]
  generalize ((Wc D i).sig (tauE D ρ)).1 = p at hpq ⊢
  generalize ((Wc D i).sig (tauE D ρ)).2 = q at hpq ⊢
  have ho : Odd (p + q) := hpq ▸ Formalism.L2.NTheta.odd_r D.R
  ext x
  simp only [Formalism.L2.NTheta.holPar, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_def, Formalism.L2.NTheta.holEnt_kapW _ _ _ ho]
  constructor
  · rintro ⟨(a | c), rfl⟩
    · exact ⟨⟨a, by omega⟩, rfl⟩
    · exact ⟨⟨p + c, by omega⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    by_cases hap : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hap⟩, rfl⟩
    · refine ⟨Sum.inr ⟨a - p, by omega⟩, ?_⟩
      simp only [Sum.elim_inr]
      congr 1
      omega

theorem params_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)), ∃ (hr : (Wc D i).rank = (Yc D 0).rank) (lam : D.what₂.Tau → Fin (Yc D 0).rank → ℤ), Odd (Yc D 0).rank ∧ (∀ ρ, Gap (lam ρ)) ∧ (∀ ρ a, M₀.lam ρ a = lam ρ a) ∧ ∀ ρ a, (R.MW i (sg0 D A)).lam ρ a = lam ρ (a.cast hr) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG i M₀
  have hY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
    simp [Ranks.rankY]
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℚ)) = Formalism.L2.NTheta.lamAt (D.hc ρ) n := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast]
  have keyR : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℝ)) = ((Formalism.L2.NTheta.lamAt (D.hc ρ) n : ℚ) : ℝ) := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast, Rat.cast_intCast]
  refine ⟨hW.trans hY.symm, fun ρ a => ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋, hY ▸ Formalism.L2.NTheta.odd_r D.R, ?_, ?_, ?_⟩
  · intro ρ a b hab
    have hb : (b : ℕ) < D.R.r := lt_of_lt_of_eq b.2 hY
    have h1 := hG.gapR ρ a (by omega)
    rw [← hab] at h1
    have hr1 : ((Yc D 0).rank : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by
      rw [hY]
      have : D.R.r ≤ 100 * D.R.r ^ 4 := by
        have := Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) D.R.r
        omega
      exact_mod_cast this
    have : ((Yc D 0).rank : ℚ) ≤ ((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋ - ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (b : ℕ)⌋ : ℤ) : ℚ) := by
      push_cast
      rw [key, key]
      linarith
    exact_mod_cast this
  · intro ρ a
    rw [enum_fst (M₀.enum ρ) (fun a : Fin (Yc D 0).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hY.le) (parA_fst D ρ hY) a, keyR]
  · intro ρ a
    rw [enum_fst ((R.MW i (sg0 D A)).enum ρ) (fun a : Fin (Wc D i).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hW.le) (parAt_fst R i ρ hW) a]
    exact (keyR ρ (a : ℕ)).symm

end GlobalTheory.ParamMatch
