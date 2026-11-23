import Formalism.LocalToGlobal.Columns.HeckeInertSq
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem isInertNbr_par {γ δ : 𝓞 E} (hgd : γ + δ = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel γ X X') (hYY' : HiRel γ Y Y') (hXY : HiRel δ X Y) (hX'Y' : HiRel δ X' Y')
    {P : Ideal (𝓞 E)} {s : List ℕ} (h : IsInertNbr P s X Y) : IsInertNbr P s X' Y' := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  obtain ⟨q1⟩ := hi_quot hgd hXX' hYY' hXY hX'Y'
  obtain ⟨q2⟩ := hi_quot hgd hYY' hXX' hXY.symm hX'Y'.symm
  exact ⟨⟨q1.symm.trans e1⟩, ⟨q2.symm.trans e2⟩⟩

theorem isHeckeNbr_par {γ δ : 𝓞 E} (hgd : γ + δ = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel γ X X') (hYY' : HiRel γ Y Y') (hXY : HiRel δ X Y) (hX'Y' : HiRel δ X' Y')
    {P : Ideal (𝓞 E)} {i : ℕ} (h : IsHeckeNbr P i X Y) : IsHeckeNbr P i X' Y' := by
  obtain ⟨h1, h2, ⟨e⟩⟩ := h
  obtain ⟨q⟩ := hi_quot hgd hXX' hYY' hXY hX'Y'
  exact ⟨hi_transport hgd hYY' hXX' hX'Y'.2 h1, hi_transport hgd hXX' hYY' hX'Y'.1 h2, ⟨q.symm.trans e⟩⟩

theorem IsHeckeNbr.mul_smul_le {P : HeightOneSpectrum (𝓞 E)} {i : ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsHeckeNbr P.asIdeal i N N') :
    (P.asIdeal * (conjPrime₂ P).asIdeal) • N ≤ N' ∧ (P.asIdeal * (conjPrime₂ P).asIdeal) • N' ≤ N := by
  obtain ⟨h1, h2, -⟩ := h
  have hc : (conjPrime₂ P).asIdeal ≤ conjIdeal (K := E) P.asIdeal := by
    intro a ha
    refine Ideal.subset_span ⟨cO E a, ha, ?_⟩
    show algebraMap (𝓞 E) E a = algebraMap (𝓞 E) E (cO E (cO E a))
    rw [cO_cO]
  constructor
  · rw [mul_comm, Submodule.mul_smul]
    exact (Submodule.smul_mono le_rfl Submodule.smul_le_right).trans
      ((Submodule.smul_mono hc le_rfl).trans h2)
  · rw [Submodule.mul_smul]
    exact (Submodule.smul_mono le_rfl Submodule.smul_le_right).trans h1

def HiConj (I : Ideal (𝓞 E)) : Prop := ∀ a ∈ I, cO E a ∈ I

theorem hiConj_mul {I J : Ideal (𝓞 E)} (hI : HiConj I) (hJ : HiConj J) : HiConj (I * J) := by
  intro a ha
  refine Submodule.mul_induction_on (C := fun r => cO E r ∈ I * J) ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]
    exact Ideal.mul_mem_mul (hI x hx) (hJ y hy)
  · rw [map_add]
    exact Ideal.add_mem _ hx hy

theorem hiConj_pow {I : Ideal (𝓞 E)} (hI : HiConj I) (k : ℕ) : HiConj (I ^ k) := by
  induction k with
  | zero =>
    intro a _
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ k ih =>
    rw [pow_succ]
    exact hiConj_mul ih hI

theorem hiConj_of_conjP {P : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P = P) : HiConj P.asIdeal := by
  intro a ha
  have h' : a ∈ (conjPrime₂ P).asIdeal := by rw [hP]; exact ha
  exact Ideal.mem_comap.1 h'

theorem hiConj_split (P : HeightOneSpectrum (𝓞 E)) : HiConj (P.asIdeal * (conjPrime₂ P).asIdeal) := by
  intro a ha
  refine Submodule.mul_induction_on (C := fun r => cO E r ∈ P.asIdeal * (conjPrime₂ P).asIdeal) ha
    (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]
    have hy' : cO E y ∈ P.asIdeal := hy
    have hx' : cO E x ∈ (conjPrime₂ P).asIdeal := by
      show cO E (cO E x) ∈ P.asIdeal
      rw [cO_cO]
      exact hx
    exact Ideal.mul_mem_mul_rev hy' hx'
  · rw [map_add]
    exact Ideal.add_mem _ hx hy

theorem hi_isCoprime {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) : IsCoprime P.asIdeal Q.asIdeal := Ideal.isCoprime_iff_sup_eq.2
    (Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal fun e => h (HeightOneSpectrum.ext e))

theorem hi_sup_inert_split {P Q : HeightOneSpectrum (𝓞 E)} (h1 : P ≠ Q) (h2 : P ≠ conjPrime₂ Q) (k : ℕ) :
    P.asIdeal ^ k ⊔ Q.asIdeal * (conjPrime₂ Q).asIdeal = ⊤ := Ideal.isCoprime_iff_sup_eq.1 ((hi_isCoprime h1).mul_right (hi_isCoprime h2)).pow_left

theorem hi_sup_split_inert {P Q : HeightOneSpectrum (𝓞 E)} (h1 : P ≠ Q) (h2 : P ≠ conjPrime₂ Q) (k : ℕ) :
    Q.asIdeal * (conjPrime₂ Q).asIdeal ⊔ P.asIdeal ^ k = ⊤ := by
  rw [sup_comm]
  exact hi_sup_inert_split h1 h2 k

theorem hi_sup_inert_inert {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) (k l : ℕ) :
    P.asIdeal ^ k ⊔ Q.asIdeal ^ l = ⊤ := Ideal.isCoprime_iff_sup_eq.1 (hi_isCoprime h).pow

theorem hi_exists_not_mem {I : Ideal (𝓞 E)} {R : HeightOneSpectrum (𝓞 E)} (h : ¬ I ≤ R.asIdeal) :
    ∃ b ∈ I, b ∉ R.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h fun b hb => hc b hb

theorem hi_sameAt_inert {P R : HeightOneSpectrum (𝓞 E)} (hRP : R ≠ P) {s : List ℕ}
    {N N' : Submodule (𝓞 E) (Sp E n)} (h : IsInertNbr P.asIdeal s N N') : SameAt R N N' := by
  obtain ⟨h1, h2⟩ := h.smul_le
  have hnle : ¬ P.asIdeal ^ s.sum ≤ R.asIdeal := by
    intro hle
    have hPR : P.asIdeal ≤ R.asIdeal := Ideal.IsPrime.le_of_pow_le hle
    exact hRP (HeightOneSpectrum.ext ((P.isMaximal.eq_of_le R.isPrime.ne_top hPR).symm))
  obtain ⟨b, hb, hbR⟩ := hi_exists_not_mem hnle
  exact ⟨b, hbR, b, hbR, fun x hx => h2 (Submodule.smul_mem_smul hb hx),
    fun x hx => h1 (Submodule.smul_mem_smul hb hx)⟩

theorem hi_sameAt_split {P R : HeightOneSpectrum (𝓞 E)} (hRP : R ≠ P) (hRP' : R ≠ conjPrime₂ P) {i : ℕ}
    {N N' : Submodule (𝓞 E) (Sp E n)} (h : IsHeckeNbr P.asIdeal i N N') : SameAt R N N' := by
  obtain ⟨h1, h2⟩ := IsHeckeNbr.mul_smul_le h
  have hnle : ¬ P.asIdeal * (conjPrime₂ P).asIdeal ≤ R.asIdeal := by
    intro hle
    rcases (R.isPrime.mul_le).1 hle with hPR | hPR
    · exact hRP (HeightOneSpectrum.ext ((P.isMaximal.eq_of_le R.isPrime.ne_top hPR).symm))
    · exact hRP' (HeightOneSpectrum.ext (((conjPrime₂ P).isMaximal.eq_of_le R.isPrime.ne_top hPR).symm))
  obtain ⟨b, hb, hbR⟩ := hi_exists_not_mem hnle
  exact ⟨b, hbR, b, hbR, fun x hx => h2 (Submodule.smul_mem_smul hb hx),
    fun x hx => h1 (Submodule.smul_mem_smul hb hx)⟩

end Moves

section Exch

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def HiPar (R : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n) → Prop) : Prop :=
  ∀ (γ δ : 𝓞 E) (X X' Y Y' : Submodule (𝓞 E) (Sp E n)), γ + δ = 1 → HiRel γ X X' → HiRel γ Y Y' → HiRel δ X Y →
    HiRel δ X' Y' → R X Y → R X' Y'

def HiBd (I : Ideal (𝓞 E)) (R : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n) → Prop) : Prop :=
  ∀ N N', R N N' → I • N ≤ N' ∧ I • N' ≤ N

theorem hi_middle_unique {I J : Ideal (𝓞 E)} (hIJ : I ⊔ J = ⊤) {Rx Ry : Submodule (𝓞 E) (Sp E n) →
    Submodule (𝓞 E) (Sp E n) → Prop} (hx : HiBd I Rx) (hy : HiBd J Ry) {d e₁ e₂ f : DecoSet E n ST SG}
    (h1 : Rx d.1.N e₁.1.N) (h1' : Ry e₁.1.N f.1.N) (h2 : Rx d.1.N e₂.1.N) (h2' : Ry e₂.1.N f.1.N)
    (hf1 : e₁.1.f = d.1.f) (hb1 : e₁.1.be = d.1.be) (hf2 : e₂.1.f = d.1.f) (hb2 : e₂.1.be = d.1.be) :
    e₁ = e₂ := by
  obtain ⟨α, hα, β, hβ, hab⟩ : ∃ α ∈ I, ∃ β ∈ J, α + β = 1 := by
    obtain ⟨a, ha, b, hb, h⟩ :=
      Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ I ⊔ J by rw [hIJ]; exact Submodule.mem_top)
    exact ⟨a, ha, b, hb, h⟩
  have r1 : HiRel α e₁.1.N d.1.N := HiRel.of_ideal (hx _ _ h1).2 (hx _ _ h1).1 hα
  have s1 : HiRel β e₁.1.N f.1.N := HiRel.of_ideal (hy _ _ h1').1 (hy _ _ h1').2 hβ
  have r2 : HiRel α e₂.1.N d.1.N := HiRel.of_ideal (hx _ _ h2).2 (hx _ _ h2).1 hα
  have s2 : HiRel β e₂.1.N f.1.N := HiRel.of_ideal (hy _ _ h2').1 (hy _ _ h2').2 hβ
  have hN : e₁.1.N = e₂.1.N := hi_eq hab r1 s1 r2 s2
  exact Subtype.ext (Deco.ext hN (hf1.trans hf2.symm) (hb1.trans hb2.symm))

theorem hi_exchange {I J : Ideal (𝓞 E)} (hIJ : I ⊔ J = ⊤) (hJc : HiConj J) (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    {Rx Ry : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n) → Prop} (hx : HiBd I Rx) (hy : HiBd J Ry)
    (px : HiPar Rx) (py : HiPar Ry)
    (sT : ∀ N N', Ry N N' → ∀ R : ST, SameAt R.1 N N') (sG : ∀ N N', Ry N N' → ∀ w : SG, SameAt w.1 N N')
    {d e f : DecoSet E n ST SG} (h1 : Rx d.1.N e.1.N) (h2 : Ry e.1.N f.1.N) :
    ∃ e' : DecoSet E n ST SG, Ry d.1.N e'.1.N ∧ Rx e'.1.N f.1.N ∧ e'.1.f = d.1.f ∧ e'.1.be = d.1.be := by
  obtain ⟨α, hα, β, hβ, hab, hαc, hβc⟩ := hi_exists_conj hJc hIJ
  have rNe : HiRel α d.1.N e.1.N := HiRel.of_ideal (hx _ _ h1).1 (hx _ _ h1).2 hα
  have reM : HiRel β e.1.N f.1.N := HiRel.of_ideal (hy _ _ h2).1 (hy _ _ h2).2 hβ
  obtain ⟨rN, rM⟩ := hiCorner_rel rNe reM
  set C := hiCorner α β f.1.N d.1.N with hC
  obtain ⟨i, hi, hi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
  have hl : Submodule.IsLattice E C :=
    hiCorner_lattice hab d.2.lat f.2.lat hi0 hj0 (fun x hx' => (hx _ _ h1).1 (Submodule.smul_mem_smul hi hx'))
      (fun y hy' => (hy _ _ h2).1 (Submodule.smul_mem_smul hj hy'))
  have hu : IsUnimodular (hStd E n) C := hiCorner_unimodular hab hαc hβc d.2.uni f.2.uni rNe reM
  have hba : β + α = 1 := by rw [add_comm]; exact hab
  have hyC : Ry d.1.N C := py α β e.1.N d.1.N f.1.N C hab rNe.symm rM.symm reM rN h2
  have hxC : Rx C f.1.N := px β α d.1.N C e.1.N f.1.N hba rN reM rNe rM h1
  refine ⟨⟨{ N := C, f := d.1.f, be := d.1.be },
    d.2.replN hl hu (fun R => sT _ _ hyC R) (fun w => sG _ _ hyC w)⟩, hyC, hxC, rfl, rfl⟩

end Exch

section Count

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

theorem hi_count_eq {I J : Ideal (𝓞 E)} (hIJ : I ⊔ J = ⊤) (hIc : HiConj I) (hJc : HiConj J) (hI0 : I ≠ ⊥)
    (hJ0 : J ≠ ⊥) {Rx Ry : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n) → Prop} (hx : HiBd I Rx)
    (hy : HiBd J Ry) (px : HiPar Rx) (py : HiPar Ry)
    (sTx : ∀ N N', Rx N N' → ∀ R : ST, SameAt R.1 N N') (sGx : ∀ N N', Rx N N' → ∀ w : SG, SameAt w.1 N N')
    (sTy : ∀ N N', Ry N N' → ∀ R : ST, SameAt R.1 N N') (sGy : ∀ N N', Ry N N' → ∀ w : SG, SameAt w.1 N N')
    (A B : DecoSet E n ST SG → Finset (DecoSet E n ST SG))
    (hA : ∀ d e, e ∈ A d ↔ Rx d.1.N e.1.N ∧ e.1.f = d.1.f ∧ e.1.be = d.1.be)
    (hB : ∀ d e, e ∈ B d ↔ Ry d.1.N e.1.N ∧ e.1.f = d.1.f ∧ e.1.be = d.1.be) (d f : DecoSet E n ST SG) :
    ((A d).filter fun e => f ∈ B e).card = ((B d).filter fun e => f ∈ A e).card := by
  have hJI : J ⊔ I = ⊤ := by rw [sup_comm]; exact hIJ
  have hL : ((A d).filter fun e => f ∈ B e).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro e₁ he₁ e₂ he₂
    rw [Finset.mem_filter, hA, hB] at he₁ he₂
    exact hi_middle_unique hIJ hx hy he₁.1.1 he₁.2.1 he₂.1.1 he₂.2.1 he₁.1.2.1 he₁.1.2.2 he₂.1.2.1 he₂.1.2.2
  have hR : ((B d).filter fun e => f ∈ A e).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro e₁ he₁ e₂ he₂
    rw [Finset.mem_filter, hB, hA] at he₁ he₂
    exact hi_middle_unique hJI hy hx he₁.1.1 he₁.2.1 he₂.1.1 he₂.2.1 he₁.1.2.1 he₁.1.2.2 he₂.1.2.1 he₂.1.2.2
  have hiff : 0 < ((A d).filter fun e => f ∈ B e).card ↔ 0 < ((B d).filter fun e => f ∈ A e).card := by
    rw [Finset.card_pos, Finset.card_pos]
    constructor
    · rintro ⟨e, he⟩
      rw [Finset.mem_filter, hA, hB] at he
      obtain ⟨⟨h1, hf1, hb1⟩, h2, hf2, hb2⟩ := he
      obtain ⟨e', g1, g2, gf, gb⟩ := hi_exchange hIJ hJc hI0 hJ0 hx hy px py sTy sGy h1 h2
      refine ⟨e', ?_⟩
      rw [Finset.mem_filter, hB, hA]
      exact ⟨⟨g1, gf, gb⟩, g2, hf2.trans (hf1.trans gf.symm), hb2.trans (hb1.trans gb.symm)⟩
    · rintro ⟨e, he⟩
      rw [Finset.mem_filter, hB, hA] at he
      obtain ⟨⟨h1, hf1, hb1⟩, h2, hf2, hb2⟩ := he
      obtain ⟨e', g1, g2, gf, gb⟩ := hi_exchange hJI hIc hJ0 hI0 hy hx py px sTx sGx h1 h2
      refine ⟨e', ?_⟩
      rw [Finset.mem_filter, hA, hB]
      exact ⟨⟨g1, gf, gb⟩, g2, hf2.trans (hf1.trans gf.symm), hb2.trans (hb1.trans gb.symm)⟩
  rcases Nat.eq_zero_or_pos ((A d).filter fun e => f ∈ B e).card with h0 | hp
  · have hn : ¬ 0 < ((B d).filter fun e => f ∈ A e).card := fun hp => by
      have := hiff.2 hp
      omega
    omega
  · have := hiff.1 hp
    omega

end Count

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

open Classical in

theorem hi_commute (c : DecoPts S E n ST SG) (A B : LocOp S S)
    (a b : DecoSet E n ST SG → Finset (DecoSet E n ST SG))
    (hA : ∀ (φ : S.EqFun) (d : S.D), ((A.op φ : S.EqFun) : S.D → S.V) d =
      ∑ e ∈ (a (c.pts d)).map c.pts.symm.toEmbedding, (φ : S.D → S.V) e)
    (hB : ∀ (φ : S.EqFun) (d : S.D), ((B.op φ : S.EqFun) : S.D → S.V) d =
      ∑ e ∈ (b (c.pts d)).map c.pts.symm.toEmbedding, (φ : S.D → S.V) e)
    (h : ∀ d f, ((a d).filter fun e => f ∈ b e).card = ((b d).filter fun e => f ∈ a e).card) :
    Commute A.op B.op := by
  classical
  have key : ∀ (D : DecoSet E n ST SG) (ψ : DecoSet E n ST SG → S.V)
      (p q : DecoSet E n ST SG → Finset (DecoSet E n ST SG)) (U : Finset (DecoSet E n ST SG)),
      (∀ e ∈ p D, q e ⊆ U) →
      ∑ x ∈ p D, ∑ y ∈ q x, ψ y = ∑ y ∈ U, ((p D).filter fun e => y ∈ q e).card • ψ y := by
    intro D ψ p q U hU
    rw [Finset.sum_comm' (t' := U) (s' := fun y => (p D).filter fun e => y ∈ q e)]
    · simp only [Finset.sum_const]
    · intro x y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨⟨hx, hy⟩, hU x hx hy⟩
      · rintro ⟨⟨hx, hy⟩, -⟩
        exact ⟨hx, hy⟩
  show A.op * B.op = B.op * A.op
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [hA, hB, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  let U := ((a (c.pts d)).biUnion b) ∪ ((b (c.pts d)).biUnion a)
  have e1 := key (c.pts d) (fun y => (φ : S.D → S.V) (c.pts.symm y)) a b U
    (fun e he y hy => Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨e, he, hy⟩))
  have e2 := key (c.pts d) (fun y => (φ : S.D → S.V) (c.pts.symm y)) b a U
    (fun e he y hy => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, hy⟩))
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact Finset.sum_congr rfl fun y _ => by rw [h (c.pts d) y]

theorem heckeD_op_apply' (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeD c P i).op φ : S.EqFun) : S.D → S.V) d =
      ∑ e ∈ ((c.pts d).heckeNb P i).map c.pts.symm.toEmbedding, (φ : S.D → S.V) e := by
  simp only [heckeD, LocOp.ofNbr_op_apply, LinearMap.id_apply] <;> rfl

theorem heckeI_op_apply' (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeI c P s).op φ : S.EqFun) : S.D → S.V) d =
      ∑ e ∈ ((c.pts d).inertNb P s).map c.pts.symm.toEmbedding, (φ : S.D → S.V) e := by
  rw [heckeI_op_apply]
  rfl

theorem heckeI_comm_heckeD (c : DecoPts S E n ST SG) {P Q : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P = P)
    (hPQ : P ≠ Q) (hPQ' : P ≠ conjPrime₂ Q) (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P)
    (hSTQ : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) (hSGQ : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) (s : List ℕ) (i : ℕ) :
    Commute (heckeI c P.asIdeal s).op (heckeD c Q.asIdeal i).op := by
  classical
  have hP0 : P.asIdeal ^ s.sum ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact P.ne_bot)
  have hQ0 : Q.asIdeal * (conjPrime₂ Q).asIdeal ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact Q.ne_bot)
      (by rw [Ideal.zero_eq_bot]; exact (conjPrime₂ Q).ne_bot)
  have hQc : conjIdeal (K := E) Q.asIdeal ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    have hmem : cO E x ∈ conjIdeal (K := E) Q.asIdeal := Ideal.subset_span ⟨x, hx, rfl⟩
    rw [h, Ideal.mem_bot] at hmem
    apply hx0
    rw [← cO_cO x, hmem, map_zero]
  refine hi_commute c _ _ (fun d => d.inertNb P.asIdeal s) (fun d => d.heckeNb Q.asIdeal i)
    (heckeI_op_apply' c P.asIdeal s) (heckeD_op_apply' c Q.asIdeal i) ?_
  intro d f
  exact hi_count_eq (Rx := IsInertNbr P.asIdeal s) (Ry := IsHeckeNbr Q.asIdeal i)
    (hi_sup_inert_split hPQ hPQ' _) (hiConj_pow (hiConj_of_conjP hP) _) (hiConj_split Q)
    hP0 hQ0 (fun N N' h => h.smul_le) (fun N N' h => IsHeckeNbr.mul_smul_le h)
    (fun γ δ X X' Y Y' hgd h1 h2 h3 h4 h => isInertNbr_par hgd h1 h2 h3 h4 h)
    (fun γ δ X X' Y Y' hgd h1 h2 h3 h4 h => isHeckeNbr_par hgd h1 h2 h3 h4 h)
    (fun N N' h R => hi_sameAt_inert (hST R) h) (fun N N' h w => hi_sameAt_inert (hSG w) h)
    (fun N N' h R => hi_sameAt_split (hSTQ R).1 (hSTQ R).2 h)
    (fun N N' h w => hi_sameAt_split (hSGQ w).1 (hSGQ w).2 h)
    _ _ (fun d e => DecoSet.mem_inertNb P.ne_bot s d e) (fun d e => DecoSet.mem_heckeNb Q.ne_bot hQc i d e) d f

theorem heckeI_comm_heckeI_ne (c : DecoPts S E n ST SG) {P Q : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P = P)
    (hQ : conjPrime₂ Q = Q) (hPQ : P ≠ Q) (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P)
    (hSTQ : ∀ R : ST, R.1 ≠ Q) (hSGQ : ∀ w : SG, w.1 ≠ Q) (s t : List ℕ) :
    Commute (heckeI c P.asIdeal s).op (heckeI c Q.asIdeal t).op := by
  classical
  have hP0 : ∀ k : ℕ, P.asIdeal ^ k ≠ ⊥ := fun k => by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact P.ne_bot)
  have hQ0 : ∀ k : ℕ, Q.asIdeal ^ k ≠ ⊥ := fun k => by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact Q.ne_bot)
  refine hi_commute c _ _ (fun d => d.inertNb P.asIdeal s) (fun d => d.inertNb Q.asIdeal t)
    (heckeI_op_apply' c P.asIdeal s) (heckeI_op_apply' c Q.asIdeal t) ?_
  intro d f
  exact hi_count_eq (Rx := IsInertNbr P.asIdeal s) (Ry := IsInertNbr Q.asIdeal t)
    (hi_sup_inert_inert hPQ _ _) (hiConj_pow (hiConj_of_conjP hP) _) (hiConj_pow (hiConj_of_conjP hQ) _)
    (hP0 _) (hQ0 _) (fun N N' h => h.smul_le) (fun N N' h => h.smul_le)
    (fun γ δ X X' Y Y' hgd h1 h2 h3 h4 h => isInertNbr_par hgd h1 h2 h3 h4 h)
    (fun γ δ X X' Y Y' hgd h1 h2 h3 h4 h => isInertNbr_par hgd h1 h2 h3 h4 h)
    (fun N N' h R => hi_sameAt_inert (hST R) h) (fun N N' h w => hi_sameAt_inert (hSG w) h)
    (fun N N' h R => hi_sameAt_inert (hSTQ R) h) (fun N N' h w => hi_sameAt_inert (hSGQ w) h)
    _ _ (fun d e => DecoSet.mem_inertNb P.ne_bot s d e) (fun d e => DecoSet.mem_inertNb Q.ne_bot t d e) d f

end Ops

section All

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem InertOff.ne_of_mem {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : InertOff S0) {R : HeightOneSpectrum (𝓞 E)}
    (h : R ∈ S0) : R ≠ P.1 := fun e => P.2.2.2 (e ▸ h)

theorem InertOff.ne_split {S0 S1 : Set (HeightOneSpectrum (𝓞 E))} (P : InertOff S0) (Q : SplitOff S1) :
    P.1 ≠ Q.1 ∧ P.1 ≠ conjPrime₂ Q.1 := by
  have hcc : ∀ R : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ R) = R := fun R => by
    apply HeightOneSpectrum.ext
    ext x
    show cO E (cO E x) ∈ R.asIdeal ↔ x ∈ R.asIdeal
    rw [cO_cO]
  have hceq : ∀ R : HeightOneSpectrum (𝓞 E), conjIdeal (K := E) R.asIdeal = (conjPrime₂ R).asIdeal := by
    intro R
    apply le_antisymm
    · refine (Ideal.span_le).2 ?_
      rintro r ⟨s, hs, hrs⟩
      have hr : r = cO E s := by
        apply IsFractionRing.injective (𝓞 E) E
        rw [hrs]
        rfl
      show cO E r ∈ R.asIdeal
      rw [hr, cO_cO]
      exact hs
    · intro a ha
      refine Ideal.subset_span ⟨cO E a, ha, ?_⟩
      show algebraMap (𝓞 E) E a = algebraMap (𝓞 E) E (cO E (cO E a))
      rw [cO_cO]
  have hQ : conjPrime₂ Q.1 ≠ Q.1 := fun h => Q.2.1 (by rw [hceq, h])
  constructor
  · intro e
    apply hQ
    rw [← e]
    exact P.2.1
  · intro e
    apply hQ
    calc conjPrime₂ Q.1 = P.1 := e.symm
      _ = conjPrime₂ P.1 := P.2.1.symm
      _ = conjPrime₂ (conjPrime₂ Q.1) := by rw [← e]
      _ = Q.1 := hcc _

theorem heckeCommAll_of_same (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E)))
    (hsame : ∀ (P : LevOffI ST SG S0) (s t : List ℕ), Commute (heckeFamI c S0 (P, s)) (heckeFamI c S0 (P, t))) :
    HeckeCommAll c S0 := by
  have mixed : ∀ (x : LevOffI ST SG S0 × List ℕ) (y : LevOff ST SG S0 × ℕ),
      Commute (heckeFamI c S0 x) (heckeFam c S0 y) := by
    intro x y
    obtain ⟨h1, h2⟩ := InertOff.ne_split x.1 y.1
    exact heckeI_comm_heckeD c x.1.2.1 h1 h2 (fun R => x.1.ne_of_mem (Or.inl (Or.inr R.2)))
      (fun w => x.1.ne_of_mem (Or.inr w.2)) (fun R => SplitOff.ne_of_mem y.1 (Or.inl (Or.inr R.2)))
      (fun w => SplitOff.ne_of_mem y.1 (Or.inr w.2)) x.2 y.2
  rintro (x | x) (y | y)
  · exact heckeOperators_commute c S0 x y
  · exact (mixed y x).symm
  · exact mixed x y
  · by_cases h : x.1.1 = y.1.1
    · obtain ⟨P, s⟩ := x
      obtain ⟨Q, t⟩ := y
      have e : P = Q := Subtype.ext h
      subst e
      exact hsame P s t
    · exact heckeI_comm_heckeI_ne c x.1.2.1 y.1.2.1 h (fun R => x.1.ne_of_mem (Or.inl (Or.inr R.2)))
        (fun w => x.1.ne_of_mem (Or.inr w.2)) (fun R => y.1.ne_of_mem (Or.inl (Or.inr R.2)))
        (fun w => y.1.ne_of_mem (Or.inr w.2)) x.2 y.2

def InertTypeOk (n : ℕ) (s : List ℕ) : Prop :=
  s.Pairwise (· ≥ ·) ∧ (∀ a ∈ s, 0 < a) ∧ 2 * s.length ≤ n

end All

end Formalism.L2.Col
