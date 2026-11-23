import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
namespace GlobalTheory.Survey.LevelVectorSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

theorem four_le_of_sizes (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) : 4 ≤ b := by
  have h1 := (h.1 τ).2.2.2 i
  have h2 := (D.hc τ).gap_be i
  have h3 : (5 : ℚ) ≤ D.R.t := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 5 ≤ D.R.t)
  have h4 : (4 : ℚ) ≤ (D.hc τ).e i - (D.hc τ).b i := by linarith
  have h5 : (4 : ℝ) ≤ (((D.hc τ).e i : ℚ) : ℝ) - (((D.hc τ).b i : ℚ) : ℝ) := by exact_mod_cast h4
  have := (abs_le.1 h1).1
  linarith

theorem hookProd_pos (μ : YoungDiagram) : 0 < Formalism.LatticeIndexTer.hookProd μ := by
  unfold Formalism.LatticeIndexTer.hookProd
  refine Finset.prod_pos fun x hx => ?_
  have hx' : (x.1, x.2) ∈ μ := hx
  have a := YoungDiagram.mem_iff_lt_rowLen.1 hx'
  have b := YoungDiagram.mem_iff_lt_colLen.1 hx'
  omega

theorem locK_eq_one {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt P) (a : 𝓞 E) (k : Eˣ) (hk : (k : E) = a) (ha : a ∉ P.asIdeal) : χ.locK P k = 1 := by
  refine h _ ?_
  show Valued.v (((k : E)) : P.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
  have := (P.valuation_eq_one_iff_notMem (K := E) (r := a)).2 ha
  exact this

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem {F : Face D A} (h : R.Char F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2

open Classical in

theorem isConjChars_base {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu

theorem isLocal_triv : IsLocalLevel (D := D) R.triv := by
  refine ⟨fun _ => ⊥, fun _ => 1, ?_⟩
  have key : ∀ (H : Subgroup (G0 R.Pg D.R.r)) (c : H →* ℂˣ), H = ⊥ → R.triv = ⟨H, c⟩ := by
    rintro H c rfl
    have : c = 1 := by ext x; rw [Subsingleton.elim x 1]; simp
    subst this; rfl
  exact key _ _ (Subgroup.pi_bot)

theorem lev_triv (i : Fin D.R.m) (t : T) (m) : lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) R.triv m) =
    lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := rfl

theorem grp_triv (i : Fin D.R.m) (t : T) (m) :
    grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv m) = (levEnv _ (R.βV i) (R.datVt i t)).J := rfl

theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (e : n = r) (g : GL (Fin n) κ) (h : upperLeftBlock hr g = 1) : g = 1 := by
  subst e
  have hg : g ∈ blockTri (κ := κ) (n := n) (blk2 n) := by
    intro a b hab
    simp [blk2] at hab
  unfold upperLeftBlock at h
  rw [extendOne_of_mem _ hg] at h
  have h2 := congrArg (fun x : GL (Fin n) κ => (x : Matrix (Fin n) (Fin n) κ)) h
  ext a b
  exact congrFun (congrFun h2 a) b

theorem omegaG_triv (i : Fin D.R.m) (m) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    Datum.omegaG (R.datWp i R.triv) m y = Datum.omegaK R.Pg y := by
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ g : ∀ PP : ↥R.Pg, GL (Fin (Wc D i).rank) (kP PP.1),
      (fun PP => upperLeftBlock (r_le_rank_Wc i) (g PP)) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) → ∀ PP, g PP = 1 := fun g hg PP =>
    eq_one_of_full_upper_block_eq_one _ hrk _ (congrFun (Subgroup.mem_bot.1 hg) PP)
  unfold Datum.omegaG Datum.omegaK
  split_ifs with h1 h2 h2
  · have hg := key _ h1.2.choose_spec.2.2
    have e1 : (R.datWp i R.triv).s = 0 := rfl
    have e2 : ∀ x, (R.datWp i R.triv).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e1, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, Units.val_one, one_mul]
    refine Finset.prod_eq_one fun PP _ => ?_
    rw [hg PP]; simp
  · exfalso
    refine h2 fun PP hP => ⟨h1.1 PP hP, ?_⟩
    obtain ⟨g, g1, -, g3⟩ := h1.2
    exact (g1 ⟨PP, hP⟩).symm.trans (congrArg Units.val (key g g3 ⟨PP, hP⟩))
  · exfalso
    refine h1 ⟨fun PP hP => (h2 PP hP).1, fun _ => 1, fun PP => (h2 PP.1 PP.2).2.symm, fun _ => Subgroup.one_mem _, ?_⟩
    have : (fun PP : ↥R.Pg => upperLeftBlock (r_le_rank_Wc i) (1 : GL (Fin (Wc D i).rank) (kP PP.1))) = 1 := by
      funext PP; exact blockDiagonalExtendByOnePrimeField_one _ _
    exact this ▸ Subgroup.one_mem _
  · rfl

open Classical in

theorem isLevelVec_base {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1

theorem levFn_congr {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (cg cg' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (xq xq' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (h1 : ∀ c, ∀ PP ∈ Pg, cg c PP = cg' c PP) (h2 : ∀ PP ∈ Q, xq PP = xq' PP) (x) :
    levFn β ⟨r, hr, t, s, Pg, Q, P, cg, xq⟩ x = levFn β ⟨r, hr, t, s, Pg, Q, P, cg', xq'⟩ x := by
  unfold levFn
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => by dsimp only; rw [h1 _ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => by dsimp only; rw [h2 PP hP]

open Classical in

theorem chr_base {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

include R in
theorem delta_base (i : Fin D.R.m) : deltaAtEmb D i (sg0 D A) = RealDat.Delta i := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold deltaAtEmb RealDat.Delta
  congr 1 <;> funext ρ
  · unfold aPlAt; rw [hl]
  · unfold aMiAt; rw [hl]

theorem apply_base {F : Face D A} (hA : AdelicLiftScalar R F) (h : R.Char F) (i : Fin D.R.m) (b : ℝ) (hb : Sizes D i b) (t : T)
    (ht : PrimeToHost R t) :
    ∃ th, IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th ∧
      ∀ ev, typePart R i (sg0 D A) t R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i (sg0 D A) t R.triv ev, th (adjLev R.triv th x) = (l : ℂ) • x) ∧
          mainTerm D i (sg0 D A) - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  have key := hA h i b hb t ht _ _ hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_base R h i t) (R.ωP i t) (h.thP.ωP i t)
    (onb (R.MW i (sg0 D A))) (fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ)) _ _ (isLevelVec_base R h i t)
    (h.thP.pt_theta i t) (R.cV i) (h.models.cV i) (R.ioP i) (by rw [delta_base R]; exact h.thP.ioP i t)
    (R.νV i t) (R.fdV i t) (h.models.νV i t) _ (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t)
    (by rw [chr_base R h]; exact h.models.HV i t)
  obtain ⟨⟨th, hth⟩, h2⟩ := key
  exact ⟨th, hth, h2 th hth⟩

end GlobalTheory.Survey.LevelVectorSizeBounds

end
