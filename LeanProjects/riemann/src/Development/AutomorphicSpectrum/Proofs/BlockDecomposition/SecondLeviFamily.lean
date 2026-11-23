import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteLeviBoundaryAndLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarOnWeightSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionUnipotentRadicalRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SuccAboveCastSuccCastSucc

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CapClsProof

open Formalism.REAL (GlRel qdet qminor)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)
open GlobalTheory.SmGL (stdBlocks)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def inj (s : Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => (1 / 2 : ℂ) •
    (if s then FreeAlgebra.ι ℂ (false, p) + FreeAlgebra.ι ℂ (true, p)
      else FreeAlgebra.ι ℂ (false, p) - FreeAlgebra.ι ℂ (true, p))

section Eval

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evalCartan_inclusion (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evKP E1 E2 (inj s z) = CompanionTheory.D.LK.ev (if s then E1 else E2) z := by
  have e : (evKP E1 E2).comp (inj s) = CompanionTheory.D.LK.ev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s
    · simp [evKP, inj, CompanionTheory.D.LK.ev, kA, pA]
      module
    · simp [evKP, inj, CompanionTheory.D.LK.ev, kA, pA]
      module
  exact DFunLike.congr_fun e z

theorem evLv_inj (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evLv lev E1 E2 (inj s z) = CompanionTheory.RgExh.U.evL lev (if s then E1 else E2) z := by
  have e : (evLv lev E1 E2).comp (inj s) = CompanionTheory.RgExh.U.evL lev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    by_cases hp : lev p.1 = lev p.2
    · cases s
      · simp [evLv, inj, CompanionTheory.RgExh.U.evL, kA, pA, hp]
        module
      · simp [evLv, inj, CompanionTheory.RgExh.U.evL, kA, pA, hp]
        module
    · cases s <;> simp [evLv, inj, CompanionTheory.RgExh.U.evL, hp]
  exact DFunLike.congr_fun e z

theorem evLc_inj (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evLc lev E1 E2 (inj s z) = CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) z := by
  have e : (evLc lev E1 E2).comp (inj s) = CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    by_cases hp : lev p.1 = lev p.2
    · cases s <;> simp [inj, CompanionTheory.RgExh.U.evL, hp, firstLeviFamily, secondLeviFamily]
    · cases s <;> simp [inj, evLc, CompanionTheory.RgExh.U.evL, hp]
  exact DFunLike.congr_fun e z

def wL (s : Bool) (w : Pos n → V) (l : Lt n) : V :=
  (1 / 2 : ℂ) • (if l.1 && !s then -w l.2 else w l.2)

theorem sum_letters (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (w : Pos n → V) :
    (∑ i : Pos n, if CompanionTheory.RgExh.U.inU lev i then (if s then E1 else E2) i.1.1 i.1.2 (w i) else 0) =
      ∑ l : Lt n, if inUU lev l then xL E1 E2 l (wL s w l) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · cases s <;> simp [hi, xL, kA, pA, wL, CompanionTheory.RgExh.U.inU] <;> module
  · simp [hi, CompanionTheory.RgExh.U.inU]

end Eval

theorem central (s : Bool) (Y : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hP : IsPairA E1 E2) (c d : Fin n) : Commute (kA E1 E2 c d) (evKP E1 E2 (inj s (fa n Y))) := by
  rw [evalCartan_inclusion]
  have hG : GlRel (if s then E1 else E2) := by
    cases s
    · simpa using hP.2.1
    · simpa using hP.1
  have hc : ∀ p q, Commute ((if s then E1 else E2) p q) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := fun p q => by
    rw [GlobalTheory.CompanionTheory.RgCOBlock.ev_fa]
    exact (Formalism.REAL.qDetCentral (Module.End ℂ V) n _ hG _ p q).symm
  have h1 : Commute (E1 c d) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
    cases s
    · exact GlobalTheory.CompanionTheory.PairMult.CapProdProof.commute_ev _ _ (fun p q => hP.2.2 _ _ p q) _
    · simpa using hc c d
  have h2 : Commute (E2 c d) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
    cases s
    · simpa using hc c d
    · exact GlobalTheory.CompanionTheory.PairMult.CapProdProof.commute_ev _ _ (fun p q => (hP.2.2 p q _ _).symm) _
  exact h1.add_left h2

theorem co_class (hAct : ActUU) (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (hM : ∀ a, lev a < M) (s : Bool) (Y r : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (hP : IsPairA E1 E2)
    (hq : qdet (if s then E1 else E2) (Y + ((n : ℂ) - 1) / 2) = r • (1 : Module.End ℂ V)) (v : V)
    (hv : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0) :
    r • (Pi.single (omU lev) v : Cq n V) -
      CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) (fb (sz lev M) h Y) (Pi.single (omU lev) v) ∈
      bdSub lev E1 E2 := by
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  obtain ⟨w, w1, w2, w3⟩ := hAct n lev hm (inj s (fa n Y)) (inj s (fb (sz lev M) h Y))
    (fun V _ _ E1 E2 hP c d => central s Y V E1 E2 hP c d)
    (fun V _ _ E1 E2 hP x => by
      have hG : GlRel (if s then E1 else E2) := by
        cases s
        · simpa using hP.2.1
        · simpa using hP.1
      obtain ⟨w, hw⟩ := (GlobalTheory.CompanionTheory.RgCOBlock.co_hyp n M lev (sz lev M) h Y hm hlev V _ hG).2 x
      refine ⟨wL s w, ?_⟩
      rw [← sum_letters, evalCartan_inclusion, evLv_inj]
      exact hw) V E1 E2 hP v hv
  refine ⟨w, ⟨w1, w2⟩, ?_⟩
  show bdL (inUU lev) E1 E2 w = _
  rw [← w3, evalCartan_inclusion, evLc_inj, GlobalTheory.CompanionTheory.RgCOBlock.ev_fa, hq]
  congr 1
  funext A
  by_cases hA : A = omU lev
  · subst hA
    simp
  · simp [Pi.single_eq_of_ne hA]

def sg (lev : Fin n → ℕ) (j : ℕ) : ℂ :=
  (((univ.filter fun b => j < lev b).card : ℂ) - ((univ.filter fun b => lev b < j).card : ℂ)) / 2

theorem sum_sz (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) (P : ℕ → Prop) [DecidablePred P] :
    ∑ b ∈ univ.filter (fun b : Fin M => P (b : ℕ)), sz lev M b = (univ.filter fun a => P (lev a)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (⟨lev a, hM a⟩ : Fin M))
    (t := univ.filter fun b : Fin M => P (b : ℕ))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : P (b : ℕ) := (Finset.mem_filter.1 hb).2
    unfold sz
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, Fin.ext_iff]
    constructor
    · intro h
      exact ⟨h ▸ hb', h⟩
    · exact fun h => h.2
  · intro a ha
    simpa using ha

theorem modExp_sz (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) (i : Fin M) :
    ((GlobalTheory.SmGL.modExp (fun i => Fin (sz lev M i)) i : ℤ) : ℂ) / 2 = sg lev i := by
  have h1 := sum_sz M lev hM (fun b => (i : ℕ) < b)
  have h2 := sum_sz M lev hM (fun b => b < (i : ℕ))
  have e1 : (univ.filter fun b : Fin M => i < b) = univ.filter fun b : Fin M => (i : ℕ) < b := rfl
  have e2 : (univ.filter fun b : Fin M => b < i) = univ.filter fun b : Fin M => (b : ℕ) < i := rfl
  simp only [GlobalTheory.SmGL.modExp, Fintype.card_fin, sg]
  rw [e1, e2]
  push_cast
  rw [← Nat.cast_sum, ← Nat.cast_sum, h1, h2]

theorem std_eq_blkE (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev) (i : Fin M) :
    (fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩) = blkE lev (i : ℕ) := by
  have hs : StrictMono fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩ := fun p q hpq => by
    rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
    have : (p : ℕ) < q := hpq
    omega
  have hf : ∀ p : Fin (sz lev M i), stdBlocks (sz lev M) h ⟨i, p⟩ ∈ blk lev (i : ℕ) := fun p => by
    simpa [blk] using GlobalTheory.CompanionTheory.RgCOBlock.lev_stdBlocks lev h hm i p
  exact Finset.orderEmbOfFin_unique (s := blk lev (i : ℕ)) rfl hf hs

theorem capS_empty {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (lev : Fin n → ℕ)
    (j : ℕ) (u : ℂ) (hj : j ∉ univ.image lev) : capS F lev j u = 1 := by
  have e : ∀ (t : ℕ) (a b : Fin t → Fin n) (x : ℂ), t = 0 → qminor F a b x = 1 := by
    rintro t a b x rfl
    simp [qminor]
  refine e _ _ _ _ ?_
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a _ ha => hj ?_)
  exact Finset.mem_image.2 ⟨a, mem_univ _, ha⟩

theorem prod_filter {A : Type} [Monoid A] (g : ℕ → A) (p : ℕ → Prop) [DecidablePred p] (hg : ∀ j, ¬p j → g j = 1) (l : List ℕ) :
    ((l.filter fun j => decide (p j)).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x
    · simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, hx, ih, hg x hx]

theorem levs_eq (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) :
    levs lev = (List.range M).filter fun j => decide (j ∈ univ.image lev) := by
  have hp : (univ.image lev).sort (· ≤ ·) |>.Perm ((List.range M).filter fun j => decide (j ∈ univ.image lev)) := by
    refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ((List.nodup_range).filter _)).2 fun j => ?_
    simp only [Finset.mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hj
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
      exact ⟨hM a, Finset.mem_image.2 ⟨a, mem_univ _, rfl⟩⟩
    · exact fun hj => hj.2
  exact hp.eq_of_pairwise' (Finset.pairwise_sort _ _) ((List.pairwise_lt_range.imp le_of_lt).filter _)

theorem evL_fb_capProd (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev) (hM : ∀ a, lev a < M)
    {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (Y : ℂ) :
    CompanionTheory.RgExh.U.evL lev F (fb (sz lev M) h Y) = capProd F lev (sg lev) Y := by
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  rw [GlobalTheory.CompanionTheory.RgCOBlock.evL_fb lev (sz lev M) h hlev]
  have hblk : ∀ i : Fin M, qdet (fun p q : Fin (sz lev M i) => F (stdBlocks (sz lev M) h ⟨i, p⟩) (stdBlocks (sz lev M) h ⟨i, q⟩))
      (Y + ((sz lev M i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (sz lev M i)) i : ℂ) / 2) =
      capS F lev (i : ℕ) (Y - sg lev i) := fun i => by
    have hinj : Function.Injective fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩ := fun p q hpq => by
      have := (stdBlocks (sz lev M) h).injective hpq
      simpa using this
    unfold qdet capS
    rw [GlobalTheory.CompanionTheory.RgHeSM.qminor_restrict F _ hinj, modExp_sz M lev hM i]
    simp only [Function.comp_id]
    rw [std_eq_blkE M lev h hm i]
    congr 1
    show _ = Y - sg lev i + (((sz lev M i : ℕ) : ℂ) - 1) / 2
    ring
  have hg : (List.ofFn fun i : Fin M => capS F lev (i : ℕ) (Y - sg lev i)) =
      (List.range M).map fun j => capS F lev j (Y - sg lev j) := by
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  simp only [hblk]
  rw [hg, capProd, levs_eq M lev hM, prod_filter _ _ (fun j hj => capS_empty F lev j _ hj)]

theorem shift_real (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (j : ℕ) :
    (∑ a ∈ blk lev j, (muQ lam lev a + 2 * rhoU lev a)) - ((blk lev j).card : ℝ) *
      (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ)) =
      2 * ∑ a ∈ blk lev j, Lr lam a := by
  have hcard : (((univ.filter fun b => j < lev b).card : ℝ) + ((univ.filter fun b => lev b < j).card : ℝ) +
      ((blk lev j).card : ℝ)) = n := by
    have e : (univ.filter fun b => j < lev b).card + (univ.filter fun b => lev b < j).card + (blk lev j).card = n := by
      unfold blk
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      have : ∀ a : Fin n, ((if j < lev a then 1 else 0) + (if lev a < j then 1 else 0) + (if lev a = j then 1 else 0) : ℕ) = 1 := by
        intro a
        split_ifs <;> omega
      simp [this]
    exact_mod_cast e
  have hs := GlobalTheory.CompanionTheory.PairMult.Asm.level_sum lev hm j
  have hr : ∀ a ∈ blk lev j, rhoU lev a =
      (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ)) / 2 := fun a ha => by
    have : lev a = j := (Finset.mem_filter.1 ha).2
    simp only [rhoU, this]
  have e1 : ∑ a ∈ blk lev j, (muQ lam lev a + 2 * rhoU lev a) = 2 * ∑ a ∈ blk lev j, (lam a : ℝ) +
      ((blk lev j).card : ℝ) * (2 * (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ))) := by
    rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [muQ, hr a ha]
    ring
  have e2 : ∑ a ∈ blk lev j, Lr lam a = ∑ a ∈ blk lev j, (lam a : ℝ) + ((blk lev j).card : ℝ) * (((n : ℝ) - 1) / 2) -
      ∑ a ∈ blk lev j, ((a : ℕ) : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rfl
  change 2 * ∑ a ∈ blk lev j, ((a : ℕ) : ℝ) = 2 * ((blk lev j).card : ℝ) * ((univ.filter fun a => lev a < j).card : ℝ) +
    ((blk lev j).card : ℝ) * (((blk lev j).card : ℝ) - 1) at hs
  rw [e1, e2]
  linear_combination ((blk lev j).card : ℝ) * hcard + hs

theorem shift_id (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (j : ℕ) :
    (∑ a ∈ blk lev j, ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ)) - ((blk lev j).card : ℂ) * (sg lev j + sg lev j) =
      2 * ∑ a ∈ blk lev j, (Lr lam a : ℂ) := by
  have e := congrArg (fun x : ℝ => (x : ℂ)) (shift_real lam lev hm j)
  simp only [sg]
  push_cast at e ⊢
  rw [← e]
  ring

theorem capCls_of (hAct : ActUU) (hC : GlobalTheory.CompanionTheory.PairMult.CapOne) (hD : GlobalTheory.CompanionTheory.PairMult.DualCap) : CapCls := by
  intro n lam _ lev hlev
  refine ⟨sg lev, sg lev, shift_id lam lev hlev.1, ?_⟩
  intro V _ _ E1 E2 hA v hv u
  obtain ⟨M, hM⟩ : ∃ M, ∀ a, lev a < M :=
    ⟨univ.sup lev + 1, fun a => Nat.lt_succ_of_le (Finset.le_sup (f := lev) (mem_univ a))⟩
  have h : ∑ i, sz lev M i = n := by
    simpa using sum_sz M lev hM (fun _ => True)
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hLχ : (fun a => ((Lr lam a : ℝ) : ℂ)) = infOf lam true := by
    funext a
    simp [Lr, infOf]
  have hneg : (fun a => -infOf lam true a) = infOf lam false := by
    funext a
    simp [infOf]
  have hcap : Formalism.QuantumDeterminants.capP (infOf lam true) u = ∏ a, (u + (Lr lam a : ℂ)) := by
    rw [← hLχ]
    rfl
  have hq1 : qdet E1 (u + ((n : ℂ) - 1) / 2) = (∏ a, (u + (Lr lam a : ℂ))) • (1 : Module.End ℂ V) := by
    rw [← hcap]
    exact hC n V E1 (infOf lam true) hA.gl1 hA.ch1 u
  have hq2 : qdet E2 (u + ((n : ℂ) - 1) / 2) = (∏ a, (u + (Lr lam a : ℂ))) • (1 : Module.End ℂ V) := by
    rw [← hcap]
    exact hD n V E2 (infOf lam true) hA.gl2 (by rw [hneg]; exact hA.ch2) u
  have hk : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0 := by
    rintro ⟨s, i⟩ rfl -
    exact hv.2 i.1.1 i.1.2 i.2 rfl
  have c1 := co_class hAct M lev h hlev.1 hM true u _ V E1 E2 hP hq1 v hk
  have c2 := co_class hAct M lev h hlev.1 hM false u _ V E1 E2 hP hq2 v hk
  rw [evL_fb_capProd M lev h hlev.1 hM] at c1 c2
  constructor
  · simpa using (bdSub lev E1 E2).neg_mem c1
  · simpa using (bdSub lev E1 E2).neg_mem c2

end GlobalTheory.CompanionTheory.CapClsProof
