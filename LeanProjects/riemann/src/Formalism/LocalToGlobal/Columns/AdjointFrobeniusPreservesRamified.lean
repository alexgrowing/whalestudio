import Mathlib
import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LogVandermondeBounds.LogVandermondeProofs.RamifiedLatticeOperatorIdentity
import Formalism.LogVandermondeBounds.LogVandermondeProofs.FourierIsometryOnNormKernel

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.LogVandermondeBounds

section CoordLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
  {N : Submodule (𝓞 E) (Sp E n)}

theorem FunAt.zero {f : Sp E n → 𝓞 E ⧸ P.asIdeal} (h : FunAt P N f) : f 0 = 0 := by
  have := h.smul 0 0 (Submodule.zero_mem _)
  simpa using this

theorem FunAt.sum {f : Sp E n → 𝓞 E ⧸ P.asIdeal} (h : FunAt P N f) {ι : Type} (s : Finset ι) (v : ι → Sp E n)
    (hv : ∀ i ∈ s, v i ∈ localization₂ P.asIdeal N) : f (∑ i ∈ s, v i) = ∑ i ∈ s, f (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      h.add _ (hv a (Finset.mem_insert_self _ _)) _
        (Submodule.sum_mem _ fun i hi => hv i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hv i (Finset.mem_insert_of_mem hi)]

theorem FunAt.of_smul_mem {f : Sp E n → 𝓞 E ⧸ P.asIdeal} (h : FunAt P N f) {z : Sp E n}
    (hz : z ∈ P.asIdeal • N) : f z = 0 := by
  have key : z ∈ N ∧ f z = 0 := by
    refine Submodule.smul_induction_on hz (fun p hp y hy => ?_) (fun y y' hy hy' => ?_)
    · refine ⟨N.smul_mem p hy, ?_⟩
      rw [h.smul p y (le_locP _ _ hy), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
    · refine ⟨N.add_mem hy.1 hy'.1, ?_⟩
      rw [h.add y (le_locP _ _ hy.1) y' (le_locP _ _ hy'.1), hy.2, hy'.2, add_zero]
  exact key.2

theorem FunAt.ext_on {f g : Sp E n → 𝓞 E ⧸ P.asIdeal} (hf : FunAt P N f) (hg : FunAt P N g)
    (h : ∀ z ∈ N, f z = g z) : f = g := by
  funext y
  by_cases hy : y ∈ localization₂ P.asIdeal N
  · obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 hy
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [← hf.smul s y hy, ← hg.smul s y hy, h _ hsy]
  · rw [hf.off y hy, hg.off y hy]

variable {co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)}

theorem CoordAt.comp (h : CoordAt P N co) (i : Fin n) : FunAt P N fun y => co y i where
  add x hx y hy := by rw [h.add x hx y hy]; rfl
  smul a x hx := by rw [h.smul a x hx]; rfl
  off x hx := by rw [h.off x hx]; rfl

theorem CoordAt.zero (h : CoordAt P N co) : co 0 = 0 := funext fun i => (h.comp i).zero

theorem CoordAt.of_smul_mem (h : CoordAt P N co) {z : Sp E n} (hz : z ∈ P.asIdeal • N) : co z = 0 :=
  funext fun i => (h.comp i).of_smul_mem hz

theorem CoordAt.sub (h : CoordAt P N co) {x y : Sp E n} (hx : x ∈ localization₂ P.asIdeal N)
    (hy : y ∈ localization₂ P.asIdeal N) : co (x - y) = co x - co y := by
  have h1 : x - y = x + (-1 : 𝓞 E) • y := by rw [neg_smul, one_smul, sub_eq_add_neg]
  rw [h1, h.add x hx _ (Submodule.smul_mem _ _ hy), h.smul _ y hy, map_neg, map_one, neg_smul, one_smul,
    sub_eq_add_neg]

theorem CoordAt.sub_mem (h : CoordAt P N co) {x y : Sp E n} (hx : x ∈ N) (hy : y ∈ N) (e : co x = co y) :
    x - y ∈ P.asIdeal • N :=
  h.ker _ (N.sub_mem hx hy) (by rw [h.sub (le_locP _ _ hx) (le_locP _ _ hy), e, sub_self])

end CoordLemmas

section FibLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {d : DecoSet E n ST SG} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibLemmas

section FibModel

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {d : DecoSet E n ST SG} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibModel

section Exists

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem intAt_algebraMap_ow (P : HeightOneSpectrum (𝓞 E)) (r : Ow P) : IntAt P (algebraMap (Ow P) E r) := by
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl r
  refine ⟨a, t, t.2, ?_⟩
  rw [IsScalarTower.algebraMap_apply (𝓞 E) (Ow P) E, ← map_mul, mul_comm, IsLocalization.mk'_spec,
    ← IsScalarTower.algebraMap_apply]

theorem exists_locBasis (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) :
    ∃ β : Module.Basis (Fin n) E (Sp E n), (∀ i, β i ∈ localization₂ P.asIdeal N) ∧
      ∀ y ∈ localization₂ P.asIdeal N, ∀ i, IntAt P (β.repr y i) := by
  classical
  obtain ⟨ι, _, b, bK, hb⟩ := exists_basis_atW P hN.fg hN.span_eq_top
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨bK.reindex e, fun i => ?_, fun y hy i => ?_⟩
  · rw [Module.Basis.reindex_apply, hb]
    exact (mem_locP _ _ _).2 (mem_atW_iff.1 (b (e.symm i)).2)
  · have hy' : y ∈ atW P N := mem_atW_iff.2 ((mem_locP _ _ _).1 hy)
    have h1 : (∑ j, b.repr ⟨y, hy'⟩ j • b j) = (⟨y, hy'⟩ : atW P N) := b.sum_repr _
    have h2 : y = ∑ j, algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ j) • bK j := by
      have h3 := congrArg (fun z : atW P N => (z : Sp E n)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans ?_
      exact Finset.sum_congr rfl fun j _ => by rw [hb, ow_smul_def]
    have h4 : bK.repr y (e.symm i) = algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ (e.symm i)) := by
      have h5 := congrArg (fun z => bK.repr z (e.symm i)) h2
      simp only [Module.Basis.repr_sum_self] at h5
      exact h5
    rw [Module.Basis.repr_reindex_apply, h4]
    exact intAt_algebraMap_ow P _

theorem exists_coordAt (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) : ∃ co, CoordAt P N co := by
  classical
  obtain ⟨β, hβ, hint⟩ := exists_locBasis P hN
  let co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal) := fun y =>
    if y ∈ localization₂ P.asIdeal N then fun i => redP P (β.repr y i) else 0
  have hpos : ∀ y, y ∈ localization₂ P.asIdeal N → co y = fun i => redP P (β.repr y i) := fun y hy => if_pos hy
  have hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x := by
    intro a x hx
    rw [hpos _ (Submodule.smul_mem _ a hx), hpos _ hx]
    funext i
    rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def,
      redP_osmul a (hint x hx i)]
    rfl
  refine ⟨co, ⟨?_, hsm, fun x hx => if_neg hx, ?_, ?_⟩⟩
  · intro x hx y hy
    rw [hpos _ (Submodule.add_mem _ hx hy), hpos _ hx, hpos _ hy]
    funext i
    rw [map_add, Finsupp.add_apply, reduction_add (hint x hx i) (hint y hy i)]
    rfl
  · intro c
    choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
    have hy0 : ∑ i, r i • β i ∈ localization₂ P.asIdeal N := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hβ i)
    have hc0 : co (∑ i, r i • β i) = c := by
      rw [hpos _ hy0]
      funext i
      have : (∑ i, r i • β i) = ∑ i, algebraMap (𝓞 E) E (r i) • β i :=
        Finset.sum_congr rfl fun i _ => (algebraMap_smul E _ _).symm
      rw [this, Module.Basis.repr_sum_self, reduction_coe, hr]
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 hy0
    have := P.isMaximal
    obtain ⟨t', ht'⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
    refine ⟨t • s • ∑ i, r i • β i, N.smul_mem t hsy, ?_⟩
    rw [hsm t _ (Submodule.smul_mem _ s hy0), hsm s _ hy0, hc0, smul_smul, mul_comm, ht', one_smul]
  · intro x hx h0
    have hxl := le_locP P N hx
    rw [hpos _ hxl] at h0
    have hterm : ∀ i, β.repr x i • β i ∈ localization₂ P.asIdeal (P.asIdeal • N) := by
      intro i
      obtain ⟨r, s, hs, hrs⟩ := hint x hxl i
      have hr : r ∈ P.asIdeal := by
        have h1 := reduction_spec P hs hrs
        rw [congrFun h0 i] at h1
        simp only [Pi.zero_apply, mul_zero] at h1
        exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
      obtain ⟨s', hs', hb⟩ := (mem_locP _ _ _).1 (hβ i)
      refine (mem_locP _ _ _).2 ⟨s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
      have e : (s * s') • (β.repr x i • β i) = r • (s' • β i) := by
        rw [mul_smul, smul_comm s' (β.repr x i) (β i), ← algebraMap_smul E s, smul_smul, hrs, algebraMap_smul]
      rw [e]
      exact Submodule.smul_mem_smul hr hb
    have hsum : x ∈ localization₂ P.asIdeal (P.asIdeal • N) := by
      rw [← β.sum_repr x]
      exact Submodule.sum_mem _ fun i _ => hterm i
    obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hsum
    exact mem_smul_of_loc hx hs hsx

end Exists

section Apply

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Apply

section Dict

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  {C : CoefPk X n (DecoSet X.E n ST SG)} {Λ : LevFam X.E X.K n SG}

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E} {d : DecoSet X.E n ST SG} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Dict

section T1

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section Lin

variable {C Λ} {d : DecoSet X.E n ST SG} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Lin

end T1

section T7

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section DictC

variable {C Λ} {d : DecoSet X.E n ST SG} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)} {σ : X.K →+* ℂ}

end DictC

end T7

section ColsT1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable (Ps : CharT X Pr)

end ColsT1

section AdjA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end AdjA

section AdjB
variable {X : Fields}

end AdjB

section AdjC
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjC

section AdjD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end AdjD

section AdjF
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjF

section RamStable

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end RamStable

end Formalism.L2.Col
