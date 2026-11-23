import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQOfCongE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Split

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S Q : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

def compVal (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) (p : HeightOneSpectrum (𝓞 E)) : Kˣ :=
  if h : p ∈ S then (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩
  else if h' : p ∈ Q then (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ else 1

theorem compVal_left (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∈ S) :
    compVal Λ Θ k1 k2 p = (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_pos h]

theorem compVal_right (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∉ S)
    (h' : p ∈ Q) : compVal Λ Θ k1 k2 p = (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_neg h, dif_pos h']

open Classical in

theorem prod_compVal (hd : Disjoint S Q) (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) :
    ∏ p ∈ S ∪ Q, compVal Λ Θ k1 k2 p = Λ.chr k1 * Θ.chr k2 := by
  have e1 : Λ.chr k1 = _ := piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) k1
  have e2 : Θ.chr k2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) k2
  rw [e1, e2, Finset.prod_union hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Q]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
  · exact dif_pos w.2
  · exact (dif_neg (Finset.disjoint_right.1 hd w.2)).trans (dif_pos w.2)

end Split
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

section Cong

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_mul_one {P : HeightOneSpectrum (𝓞 E)} {c : ℕ} {k g g' : Sp E n ≃ₗ[E] Sp E n}
    (hk : k ∈ GLint E n P) (hkg : k * g' = 1) (h : CongE P c g g') : CongE P c (k * g) 1 := by
  intro x hx
  have e1 : (k * g) x - (1 : Sp E n ≃ₗ[E] Sp E n) x = k (g x - g' x) := by
    rw [map_sub, ← LinearEquiv.mul_apply k g', hkg]
    rfl
  rw [e1, ← map_smul]
  exact (hk _).2 (h x hx)

end Cong
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_type (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (al : (I.idx a).β i) (P : SBof I a)
    (hP : P.1 ∈ (B.primes X).vGs) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κw : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal)) (hκw : κw ∈ (((I.idx a).levG i al) ⟨P.1, hP⟩).H)
    (hred' : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g'P x) = (κw⁻¹).1.mulVec (redV P.1 x))
    (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨κw, hκw⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hD : (I.cst a).D P = 1 := hL.depthG P hP
  have hred : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (gP x) = (κw⁻¹).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [← hred' x hx]
    have h1 := (mem_localization_standardLattice _ _).1 (hcong x hx)
    rw [hD, pow_one] at h1
    have hq0 : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    funext l
    have e1 : gP x l = g'P x l + (qOf P.1 : B.fields.E) * (((qOf P.1 : ℕ) : B.fields.E)⁻¹ • (gP x - g'P x)) l := by
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      ring
    show redP P.1 (gP x l) = redP P.1 (g'P x l)
    rw [e1]
    exact GlobalTheory.LastSteps.redP_add_q (h1 l)
  have hc := hL.chrG i al ⟨P.1, hP⟩ (⟨κw, hκw⟩)⁻¹ gP r hr hrx hred
  exact hc.symm.trans ((congrArg Units.val (map_inv (((I.idx a).levG i al) ⟨P.1, hP⟩).lam _)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_twist (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i) (P : SBof I a)
    (hQ : P.1 ∈ I.Q a) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κQ : ↥(GLint B.fields.E (B.R.N i) P.1)) (hκQ : κQ ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H)
    (hg' : g'P = (κQ⁻¹).1) (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hg : gP ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp i P.1 ((I.idx a).h i al P) := ⟨r, hr, hrx⟩
  let gI : ↥(GLint B.fields.E (B.R.N i) P.1) := ⟨gP, hL.int i al P hg⟩
  have hH : gI ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H := by
    rw [hL.grpQ i al ⟨P.1, hQ⟩]
    exact Subgroup.mem_subgroupOf.2 hg
  have hc := hL.chrQ i al ⟨P.1, hQ⟩ ⟨gI, hH⟩ r hr hrx
  have hkg : κQ.1 * g'P = 1 := by
    rw [hg']
    exact congrArg Subtype.val (mul_inv_cancel κQ)
  have hcd : CongE P.1 ((I.cst a).D P) (κQ * gI).1 1 := congE_mul_one (g := gP) κQ.2 hkg hcong
  obtain ⟨hdH, hdl⟩ := levQ_deep I hOk a i hi al P hQ (κQ * gI) hcd
  have e2 : (⟨gI, hH⟩ : ↥(((I.idx a).levQ i al) ⟨P.1, hQ⟩).H) = (⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩ :=
    Subtype.ext (by show gI = κQ⁻¹ * (κQ * gI); group)
  have h4 : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ((⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩) = ((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩)⁻¹ :=
    ((map_mul (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _ _).trans ((congrArg _ hdl).trans (mul_one _))).trans (map_inv (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _)
  exact hc.symm.trans ((congrArg Units.val ((congrArg (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam e2).trans h4)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open Classical in

theorem chr_mul_prod_midAt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi hi).symm⟩
  let k1 : ↥((I.idx a).levG i al).grp := κ.2.1
  let k2 : ↥((I.idx a).levQ i al).grp := κ.2.2
  have e : (((I.stp u a i).chr (Idx.of al hi) κ : B.fields.Kˣ) : B.fields.K) =
      ((((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 : B.fields.Kˣ) : B.fields.K) := rfl
  rw [e]
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_right.2 fun {P} hP => GlobalTheory.Mem.Col2.TC.Q_notMem_of_ok hOk a P hP
  have hprod : ∏ P : SBof I a, compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 =
      ((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 := by
    rw [Finset.prod_coe_sort (SBof I a) (compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2)]
    exact prod_compVal hd _ _ k1 k2
  have hz : ∀ P : SBof I a, z P = ((compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 : B.fields.Kˣ) : B.fields.K)⁻¹ := by
    intro P
    obtain ⟨⟨r, hr, hrx, hzr⟩, hlift, hcong⟩ := H P
    rw [hzr]
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · refine (chiInv_at_type I hOk a i al P hP (g P) (g' P) r hr hrx (k1.1 ⟨P.1, hP⟩) (k1.2 _ (Set.mem_univ _))
        (hlift.2.1 hP) hcong).trans ?_
      rw [compVal_left _ _ k1 k2 hP]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      refine (chiInv_at_twist I hOk a i hi al P hQ (g P) (g' P) r hr hrx (k2.1 ⟨P.1, hQ⟩) (k2.2 _ (Set.mem_univ _))
        (hlift.2.2 hQ) hcong).trans ?_
      exact congrArg (fun x : B.fields.Kˣ => (x : B.fields.K)⁻¹) (compVal_right _ _ k1 k2 hP hQ).symm
  rw [← hprod, Finset.prod_congr rfl fun P _ => hz P, Units.coe_prod, Finset.prod_inv_distrib]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun P _ => Units.ne_zero _)

end GlobalTheory.Mem.Col2.AdT

end
