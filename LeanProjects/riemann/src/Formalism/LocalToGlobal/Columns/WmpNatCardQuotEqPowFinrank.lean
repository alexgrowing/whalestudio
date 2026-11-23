import Formalism.LocalToGlobal.Columns.WmLemmas
import Formalism.FlagUnipotentLattices.IdealCountLeWAsm
import Lemmata.GeneralBFactRightMore.Imports

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section WmPSym
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem conjugatePrime_conjugatePrime (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem wmp_dual_toAddSubgroup (L : Submodule (𝓞 E) (Sp E n)) :
    (dual (hStd E n) L).toAddSubgroup =
      Formalism.HermitianLatticeCounting.S6.hdual (hStd E n).flip (algebraMap (𝓞 E) E).range L.toAddSubgroup := by
  ext x
  rw [Submodule.mem_toAddSubgroup, dualBasic_mem_dual]
  change _ ↔ ∀ y ∈ L, (hStd E n).flip x y ∈ (algebraMap (𝓞 E) E).range
  simp only [LinearMap.flip_apply, Submodule.mem_one, RingHom.mem_range]

theorem wmp_hStd_nondeg (x : Sp E n) (h : ∀ y, (hStd E n).flip x y = 0) : x = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [LinearMap.flip_apply, hStd_apply] at this
  simp only [Pi.single_apply, apply_ite (star : E → E), star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

theorem wmp_relIndex_dual {L M : Submodule (𝓞 E) (Sp E n)} (hLM : L ≤ M) (hM : M.FG)
    (hL : Submodule.span E (L : Set (Sp E n)) = ⊤) :
    (dual (hStd E n) M).toAddSubgroup.relIndex (dual (hStd E n) L).toAddSubgroup =
      L.toAddSubgroup.relIndex M.toAddSubgroup := by
  rw [wmp_dual_toAddSubgroup, wmp_dual_toAddSubgroup]
  exact Formalism.HermitianLatticeCounting.Final.S6.dualIndex E (Sp E n) (hStd E n).flip M L wmp_hStd_nondeg hLM hM hL

theorem wmp_card_quot (B N : Submodule (𝓞 E) (Sp E n)) :
    Nat.card (N ⧸ B.comap N.subtype) = B.toAddSubgroup.relIndex N.toAddSubgroup := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
  rfl

theorem wmp_relIndex_inf_eq {N N₁ : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hN₁ : Submodule.IsLattice E N₁) (hu : IsUnimodular (hStd E n) N) (hu₁ : IsUnimodular (hStd E n) N₁)
    (hB : Submodule.IsLattice E (N ⊓ N₁)) :
    (N ⊓ N₁).toAddSubgroup.relIndex N.toAddSubgroup = (N ⊓ N₁).toAddSubgroup.relIndex N₁.toAddSubgroup := by
  have key : ∀ M : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E M → IsUnimodular (hStd E n) M → N ⊓ N₁ ≤ M →
      (N ⊓ N₁).toAddSubgroup.relIndex (dual (hStd E n) (N ⊓ N₁)).toAddSubgroup =
        ((N ⊓ N₁).toAddSubgroup.relIndex M.toAddSubgroup) ^ 2 := by
    intro M hM huM hBM
    have hMD : M ≤ dual (hStd E n) (N ⊓ N₁) := by
      have := dual_anti hBM
      rwa [huM] at this
    rw [← AddSubgroup.relIndex_mul_relIndex _ M.toAddSubgroup _ hBM hMD, sq]
    congr 1
    have e := wmp_relIndex_dual hBM hM.fg hB.span_eq_top
    rw [huM] at e
    exact e
  have e1 := key N hN hu inf_le_left
  have e2 := key N₁ hN₁ hu₁ inf_le_right
  rw [e1] at e2
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) e2

theorem wmp_quot_equiv_of_card (Q : HeightOneSpectrum (𝓞 E)) (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    (hM : ∀ p ∈ Q.asIdeal, ∀ x : M, p • x = 0) {i : ℕ}
    (hc : Nat.card M = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ i) :
    Nonempty (M ≃ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ Q.asIdeal)) := by
  have := Q.isMaximal
  let _ : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  have hfinQ : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  have hq : 1 < Nat.card (𝓞 E ⧸ Q.asIdeal) := Finite.one_lt_card
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have ht : Module.IsTorsionBySet (𝓞 E) M (Q.asIdeal : Set (𝓞 E)) := fun x p => hM p.1 p.2 x
  let _ : Module (𝓞 E ⧸ Q.asIdeal) M := ht.module
  have : IsScalarTower (𝓞 E) (𝓞 E ⧸ Q.asIdeal) M := ht.isScalarTower
  have : FiniteDimensional (𝓞 E ⧸ Q.asIdeal) M := Module.Finite.of_finite
  let _ : Fintype M := Fintype.ofFinite M
  let _ : Fintype (𝓞 E ⧸ Q.asIdeal) := Fintype.ofFinite _
  have h1 := Module.card_eq_pow_finrank (K := 𝓞 E ⧸ Q.asIdeal) (V := M)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc] at h1
  have hd : finrank (𝓞 E ⧸ Q.asIdeal) M = i := (Nat.pow_right_injective hq h1).symm
  exact ⟨(LinearEquiv.ofFinrankEq M (Fin i → 𝓞 E ⧸ Q.asIdeal) (by rw [hd, finrank_fin_fun])).restrictScalars (𝓞 E)⟩

theorem wmp_isHeckeNbr_symm {P : HeightOneSpectrum (𝓞 E)} {i : ℕ} {N N₁ : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (hN₁ : Submodule.IsLattice E N₁) (hu : IsUnimodular (hStd E n) N)
    (hu₁ : IsUnimodular (hStd E n) N₁) (h : IsHeckeNbr P.asIdeal i N N₁) :
    IsHeckeNbr (conjPrime₂ P).asIdeal i N₁ N := by
  rw [isHeckeNbr_iff] at h ⊢
  obtain ⟨h1, h2, ⟨e⟩⟩ := h
  rw [conjugatePrime_conjugatePrime]
  refine ⟨h2, h1, ?_⟩
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (conjPrime₂ P).ne_bot
  have hB : Submodule.IsLattice E (N ⊓ N₁) :=
    lattice_of_smul hN hN inf_le_left hp0 fun x hx => ⟨Submodule.smul_mem _ _ hx, h2 (Submodule.smul_mem_smul hp hx)⟩
  apply wmp_quot_equiv_of_card P
  · intro a ha x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨h1 (Submodule.smul_mem_smul ha y.2), Submodule.smul_mem _ _ y.2⟩
  · rw [wmp_card_quot, ← wmp_relIndex_inf_eq hN hN₁ hu hu₁ hB, ← wmp_card_quot, inf_comm,
      Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin i), Fintype.card_fin, card_quot_conjP]

def WmpInt (Q : HeightOneSpectrum (𝓞 E)) (y : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * y = algebraMap (𝓞 E) E r

theorem wmp_hStd_osmul_right (u z : Sp E n) (s : 𝓞 E) :
    hStd E n u (s • z) = algebraMap (𝓞 E) E s * hStd E n u z := by
  rw [← algebraMap_smul E s z, map_smul, smul_eq_mul]

theorem wmp_hStd_osmul_left (u z : Sp E n) (s : 𝓞 E) :
    hStd E n (s • u) z = algebraMap (𝓞 E) E (cO E s) * hStd E n u z := by
  rw [← algebraMap_smul E s u, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, algebraMap_cO]
  rfl

theorem localization_le_of_le_localization₃ {Q : HeightOneSpectrum (𝓞 E)} {M L : Submodule (𝓞 E) (Sp E n)} (h : M ≤ localization₂ Q.asIdeal L) :
    localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP Q M x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_locP Q L _).1 (h hsx)
  exact (mem_locP Q L x).2 ⟨t * s, fun hm => (Q.isPrime.mem_or_mem hm).elim ht hs, by rw [mul_smul]; exact htx⟩

theorem wmp_exists_unif (P : HeightOneSpectrum (𝓞 E)) :
    ∃ a ∈ P.asIdeal, ∃ c : 𝓞 E, c ∉ P.asIdeal ∧ ∀ p ∈ P.asIdeal, ∃ t : 𝓞 E, c * p = a * t := by
  first | exact Bl.general_b_fact_right_more.goal1 .. | (apply Bl.general_b_fact_right_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_more.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_more.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_more.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_more.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_more.goal1 E ‹_› ‹_› ‹_› P | exact @Bl.general_b_fact_right_more.goal1 E ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_right_more.goal1 E ‹_› ‹_› | exact @Bl.general_b_fact_right_more.goal1 E ‹_› | exact @Bl.general_b_fact_right_more.goal1 E

end WmPSym

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section WmPUp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

def wmpC (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) (N N₁ : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  Ideal.span {a} • N₁ ⊔ P.asIdeal • N

end WmPUp

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section WmPK
variable {E : Type} [Field E] [NumberField E] [StarRing E]

def wmpToK (P : HeightOneSpectrum (𝓞 E)) {V : Type} [AddCommGroup V] [Module (𝓞 E) V] [Module (𝓞 E ⧸ P.asIdeal) V]
    [IsScalarTower (𝓞 E) (𝓞 E ⧸ P.asIdeal) V] (p : Submodule (𝓞 E) V) : Submodule (𝓞 E ⧸ P.asIdeal) V where
  carrier := p
  add_mem' := p.add_mem
  zero_mem' := p.zero_mem
  smul_mem' := fun c x hx => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    exact p.smul_mem r hx

variable {P : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module (𝓞 E) V] [Module (𝓞 E ⧸ P.asIdeal) V]
    [IsScalarTower (𝓞 E) (𝓞 E ⧸ P.asIdeal) V]

theorem card_wmpToK (p : Submodule (𝓞 E) V) : Nat.card (wmpToK P p) = Nat.card p :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end WmPK

section WmPSub
variable {k V : Type} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Finite V]

end WmPSub

section WmPCountUp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

end WmPCountUp

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section WmPCountDown
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

end WmPCountDown

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section WmPMain
variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

end WmPMain

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section LemU

variable {κ K : Type} [CommRing κ] [Field K]

def wmpkTop {r n : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin n) κ) (hg : g ∈ blockUT n κ r bl) : GL (Fin r) κ where
  val := restr h g
  inv := restr h (g⁻¹ : GL (Fin n) κ)
  val_inv := by
    rw [← restr_mul h bl _ (Subgroup.inv_mem _ hg), ← Units.val_mul, mul_inv_cancel, Units.val_one, restr_one]
  inv_val := by
    rw [← restr_mul h bl _ hg, ← Units.val_mul, inv_mul_cancel, Units.val_one, restr_one]

end LemU

section Det

variable {κ : Type} [CommRing κ]

end Det

section Red

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
  {SG : Finset (HeightOneSpectrum (𝓞 E))}

end Red

section Main

variable {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S)

end Main

section Final

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Final

end Formalism.L2.Col
