import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegRightMulLetterShiftApply

noncomputable section

open Finset Formalism.REAL
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.PairMult.CenScal (UD Ds eb mi eu xl xl_apply xs_same levRel_xl leftMulLetter negRightMulLetterShift central_letters evB_intertwine
  mem_of_eb center_UD_le glHom glHom_comm glHom_single qdet_map)

namespace GlobalTheory.CompanionTheory.BlockCapelliWords

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

variable {n : ℕ}

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (X : Fin n → Fin n → A) (f : Fin t → Fin n)
    (hf : Function.Injective f) (u : ℂ) : qminor X f f u = qdet (fun i k => X (f i) (f k)) u := by
  unfold qdet qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp [Tm, hf.eq_iff]

theorem qminor_of_size_zero {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (ht : t = 0) (X : Fin n → Fin n → A)
    (f : Fin t → Fin n) (u : ℂ) : qminor X f f u = 1 := by
  subst ht
  simp [qminor]

theorem blkE_injective (lev : Fin n → ℕ) (j : ℕ) : Function.Injective (blkE lev j) :=
  ((blk lev j).orderEmbOfFin rfl).injective

theorem lev_blkE (lev : Fin n → ℕ) (j : ℕ) (i : Fin (blk lev j).card) : lev (blkE lev j i) = j := by
  have h : blkE lev j i ∈ blk lev j := (blk lev j).orderEmbOfFin_mem rfl i
  exact (Finset.mem_filter.1 h).2

theorem exists_blkE (lev : Fin n → ℕ) (a : Fin n) : ∃ i, blkE lev (lev a) i = a := by
  refine ⟨((blk lev (lev a)).orderIsoOfFin rfl).symm ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩, ?_⟩
  exact congrArg Subtype.val (((blk lev (lev a)).orderIsoOfFin rfl).apply_symm_apply
    ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩)

abbrev numLev (lev : Fin n → ℕ) : ℕ := univ.sup lev + 1

abbrev bd (lev : Fin n → ℕ) : Fin (numLev lev) → ℕ := fun i => (blk lev i).card

def blkEquiv (lev : Fin n → ℕ) : (Σ i, Fin (bd lev i)) ≃ Fin n :=
  Equiv.ofBijective (fun p => blkE lev p.1 p.2) (by
    constructor
    · rintro ⟨i, p⟩ ⟨k, q⟩ h
      have h' : blkE lev i p = blkE lev k q := h
      have hik : i = k := Fin.ext ((lev_blkE lev i p).symm.trans ((congrArg lev h').trans (lev_blkE lev k q)))
      subst hik
      rw [blkE_injective lev i h']
    · intro a
      obtain ⟨i, hi⟩ := exists_blkE lev a
      exact ⟨⟨⟨lev a, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))⟩, i⟩, hi⟩)

def kpWord : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if p.1 then FreeAlgebra.ι ℂ (true, p.2) - FreeAlgebra.ι ℂ (false, p.2)
    else FreeAlgebra.ι ℂ (true, p.2) + FreeAlgebra.ι ℂ (false, p.2)

theorem evLv_eq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (F1 F2 : Fin n → Fin n → Module.End ℂ V)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    evLv lev F1 F2 b = GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2 (kpWord b) := by
  have h : evLv lev F1 F2 = (GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2).comp kpWord := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨s, p, q⟩ := x
    by_cases hpq : lev p = lev q
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq, pA, kA]
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq]
  rw [h]
  rfl

theorem isLevPairA_of_lRel {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2) : IsLevPairA lev F1 F2 :=
  fun a b c d h1 h2 => ⟨h.1 a b c d h1 h2, h.2.1 a b c d h1 h2, (h.2.2 a b c d h1 h2).eq⟩

theorem lRel_of_isLevPairA {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : IsLevPairA lev F1 F2) : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2 :=
  ⟨fun a b c d h1 h2 => (h a b c d h1 h2).1, fun a b c d h1 h2 => (h a b c d h1 h2).2.1,
    fun a b c d h1 h2 => (h a b c d h1 h2).2.2⟩

theorem invLev_kpWord {lev : Fin n → ℕ} {b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hb : InvLv lev b) :
    GlobalTheory.CompanionTheory.PairMult.InvLev lev (kpWord b) := by
  intro W _ _ X1 X2 hL p q hpq
  have h := hb W X1 X2 (isLevPairA_of_lRel hL) p q hpq
  rw [evLv_eq] at h
  exact h

theorem exists_rho {M : ℕ} {d : Fin M → ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) {lev : Fin n → ℕ}
    (he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ)) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hL : GlobalTheory.CompanionTheory.PairMult.LRel lev X1 X2) :
    ∃ ρ : UD d →ₐ[ℂ] Module.End ℂ W, ∀ i p q, ρ (eb d i p q) = X1 (e ⟨i, p⟩) (e ⟨i, q⟩) := by
  have hl : ∀ i (p q : Fin (d i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  have hG : ∀ i, GlRel (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) := fun i a c f g => by
    have := hL.1 (e ⟨i, a⟩) (e ⟨i, c⟩) (e ⟨i, f⟩) (e ⟨i, g⟩) (hl _ _ _) (hl _ _ _)
    simpa only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] using this
  have hC : ∀ i k, i ≠ k → ∀ (p q : Fin (d i)) (r v : Fin (d k)),
      Commute (X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (X1 (e ⟨k, r⟩) (e ⟨k, v⟩)) := fun i k hik p q r v => by
    have := hL.1 (e ⟨i, p⟩) (e ⟨i, q⟩) (e ⟨k, r⟩) (e ⟨k, v⟩) (hl _ _ _) (hl _ _ _)
    have n1 : e ⟨i, q⟩ ≠ e ⟨k, r⟩ := fun h => hik (congrArg Sigma.fst (e.injective h))
    have n2 : e ⟨k, v⟩ ≠ e ⟨i, p⟩ := fun h => hik (congrArg Sigma.fst (e.injective h)).symm
    rw [if_neg n1, if_neg n2, sub_zero] at this
    exact sub_eq_zero.1 this
  refine ⟨lift ℂ (DirectSum.toLieAlgebra _
    (fun i => glHom (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (hG i))
    (fun i k hik Z Z' => glHom_comm _ _ (hC i k hik) Z Z')), fun i p q => ?_⟩
  simp only [eb, eu, GlobalTheory.CompanionTheory.PairMult.CenScal.mi_ι, lift_ι_apply]
  refine (GlobalTheory.EnvCentre.toLieAlgebra_of (fun i => GlobalTheory.CompanionTheory.PairMult.CenScal.Gl (d i)) _ _ i _).trans ?_
  exact glHom_single _ (hG i) p q

def capLetter (lev : Fin n → ℕ) (p : ℕ × ℂ) : UD (bd lev) :=
  if h : p.1 < numLev lev then
    mi (bd lev) ⟨p.1, h⟩ (qdet (eu (bd lev ⟨p.1, h⟩)) (p.2 + ((bd lev ⟨p.1, h⟩ : ℂ) - 1) / 2))
  else 1

def capWord (lev : Fin n → ℕ) : FreeAlgebra ℂ (ℕ × ℂ) →ₐ[ℂ] UD (bd lev) := FreeAlgebra.lift ℂ (capLetter lev)

theorem rho_capWord {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W)
    (ρ : UD (bd lev) →ₐ[ℂ] Module.End ℂ W)
    (hρ : ∀ i p q, ρ (eb (bd lev) i p q) = F (blkE lev i p) (blkE lev i q)) (z : FreeAlgebra ℂ (ℕ × ℂ)) :
    ρ (capWord lev z) = evCap lev F z := by
  have h : ρ.comp (capWord lev) = evCap lev F := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨j, u⟩ := x
    simp only [Function.comp_apply, AlgHom.comp_apply, capWord, evCap, FreeAlgebra.lift_ι_apply, capLetter]
    by_cases hj : j < numLev lev
    · rw [dif_pos hj]
      simp only [capS]
      rw [qminor_reindex _ _ (blkE_injective lev j), ← AlgHom.comp_apply, qdet_map]
      congr 1
      funext p q
      exact hρ ⟨j, hj⟩ p q
    · rw [dif_neg hj, map_one]
      have hc : (blk lev j).card = 0 := by
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a _ ha => hj ?_)
        rw [← ha]
        exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
      exact (qminor_of_size_zero hc _ _ _).symm
  rw [← h]
  rfl

theorem mem_range_capWord (lev : Fin n → ℕ) {y : UD (bd lev)}
    (hy : y ∈ Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u))) :
    ∃ z, capWord lev z = y := by
  have hle : Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u)) ≤
      (capWord lev).range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.1 hx
    refine ⟨FreeAlgebra.ι ℂ ((i : ℕ), u - ((bd lev i : ℂ) - 1) / 2), ?_⟩
    change capWord lev (FreeAlgebra.ι ℂ _) = _
    simp only [capWord, FreeAlgebra.lift_ι_apply, capLetter]
    rw [dif_pos i.2]
    simp
  obtain ⟨z, hz⟩ := hle hy
  exact ⟨z, hz⟩

theorem commutant_block_capelli_words : LeviCommutantWordReduction := by
  intro n lev _ b hb ν hν
  let e := blkEquiv lev
  have he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ) := fun i p => lev_blkE lev i p
  let τ : Fin n → ℂ := fun a => (ν a : ℂ)
  have hτ : ∀ a c, lev a = lev c → τ a = τ c := fun a c h => by simp only [τ, hν a c h]
  have hb' := invLev_kpWord hb
  have hl : ∀ i (p q : Fin (bd lev i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  set y := GlobalTheory.CompanionTheory.PairMult.evB lev (leftMulLetter (xl e)) (negRightMulLetterShift (xl e) τ) (kpWord b) 1 with hy
  have hcen : y ∈ Subalgebra.center ℂ (UD (bd lev)) := by
    rw [Subalgebra.mem_center_iff]
    intro g
    have hg : g ∈ Subalgebra.centralizer ℂ {y} := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      have := central_letters (levRel_xl e he) hτ hb' _ _ (hl i r v)
      rw [xl_apply, xs_same] at this
      exact this.symm) g
    rw [Subalgebra.mem_centralizer_iff] at hg
    exact (hg _ rfl).symm
  obtain ⟨z, hz⟩ := mem_range_capWord lev (center_UD_le (bd lev) hcen)
  refine ⟨z, fun H _ _ F1 F2 hL h hh => ?_⟩
  have hL' := lRel_of_isLevPairA hL
  obtain ⟨ρ, hρ⟩ := exists_rho e he hL'
  have hρx : ∀ p q, lev p = lev q → ρ (xl e p q) = F1 p q := by
    intro p q hpq
    obtain ⟨⟨i, p⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨k, q⟩, rfl⟩ := e.surjective q
    rw [he, he] at hpq
    obtain rfl : i = k := Fin.ext hpq
    rw [xl_apply, xs_same, hρ]
  have hcomm : ∀ p q, lev p = lev q → ∀ u, Commute (ρ u) (F2 p q) := fun p q hpq u => by
    have hu : u ∈ (Subalgebra.centralizer ℂ {F2 p q}).comap ρ := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rw [hρ]
      exact (hL'.2.2 _ _ _ _ (hl _ _ _) hpq).eq.symm) u
    rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff] at hu
    exact (hu _ rfl).symm
  have e1 := evB_intertwine (x := xl e) (τ := τ) ρ F1 F2 h hρx hcomm hh (kpWord b) 1
  rw [map_one, Module.End.one_apply] at e1
  rw [evLv_eq, e1, ← hy, ← hz, rho_capWord F1 ρ hρ]

end GlobalTheory.CompanionTheory.BlockCapelliWords
