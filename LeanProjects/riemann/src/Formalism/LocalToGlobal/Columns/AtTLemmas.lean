import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section DiaMoves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem upA_smul {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {x : Sp E n} (hx : x ∈ N)
    {r : 𝓞 E} (hr : r ∉ P.asIdeal) : upA P.asIdeal N (r • x) = upA P.asIdeal N x := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have e : a • (r • x) = (r • a) • x := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    rw [SetLike.mem_coe, e]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨r • a, Submodule.smul_mem _ r ha, rfl⟩)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨s, p, hp, e⟩ := P.isMaximal.exists_inv hr
    have e2 : a • x = a • (p • x) + (s • a) • (r • x) := by
      have e3 : (s • a) • (r • x) = a • ((s * r) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
        ring
      rw [e3, ← smul_add, ← add_smul, add_comm, e, one_smul]
    rw [SetLike.mem_coe, e2]
    exact Submodule.add_mem_sup (inv_smul_mem ha (Submodule.smul_mem_smul hp hx))
      (Submodule.subset_span ⟨s • a, Submodule.smul_mem _ s ha, rfl⟩)

theorem exists_lift_unit (P : HeightOneSpectrum (𝓞 E)) (c : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ r : 𝓞 E, Ideal.Quotient.mk P.asIdeal r = c.1 ∧ r ∉ P.asIdeal := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c.1
  refine ⟨r, hr, fun h0 => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, hr] at h0
  exact c.ne_zero h0

theorem Deco.IsUp.dia {P : ST} {q : 𝓞 E} {d d' : Deco E n ST SG} (hd : d.Ok) (h : Deco.IsUp P q d d')
    (c : DiaG E ST) : Deco.IsUp P q (d.dia c) (d'.dia c) := by
  classical
  obtain ⟨x, hx, hfx, rfl⟩ := h
  obtain ⟨r, hr, hrP⟩ := exists_lift_unit P.1 (c P)⁻¹
  have hN : upN P.1.asIdeal d.N (r • x) = upN P.1.asIdeal d.N x := by
    unfold upN
    rw [upA_smul hx hrP]
  refine ⟨r • x, Submodule.smul_mem _ r hx, ?_, ?_⟩
  · show (c P).1 * d.f P (r • x) = 1
    rw [hd.f_smul P r x (le_locP _ _ hx), hr, hfx, mul_one, Units.mul_inv]
  · ext1
    · exact hN.symm
    · funext Q y
      simp only [Deco.dia, Deco.up]
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self, Function.update_self]
        have hiff : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N (r • x)) ↔
            y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x) := by rw [hN]
        by_cases hy : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)
        · rw [if_pos hy]
          exact (if_pos (hiff.2 hy)).symm
        · rw [if_neg hy, mul_zero]
          exact (if_neg (fun h' => hy (hiff.1 h'))).symm
      · rw [Function.update_of_ne hQ, Function.update_of_ne hQ]
    · rfl

theorem Deco.kerAt_dia (d : Deco E n ST SG) (c : DiaG E ST) (P : ST) : (d.dia c).kerAt P = d.kerAt P := by
  unfold Deco.kerAt
  congr 1
  ext x
  show (x ∈ d.N ∧ (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ d.f P x = 0)
  rw [Units.mul_right_eq_zero]

theorem Deco.IsDnA.dia {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG} (hd : d.Ok)
    (hd' : d'.Ok) (h : Deco.IsDnA P q a d d') (c : DiaG E ST) : Deco.IsDnA P q a (d.dia c) (d'.dia c) := by
  classical
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · ext1
    · show d'.N = (d.dia c).dnN P
      unfold Deco.dnN
      rw [Deco.kerAt_dia]
      exact congrArg Deco.N h1
    · funext Q y
      have h3 : d'.f Q = (d.dn P (d'.f P)).f Q := by rw [← h1]
      simp only [Deco.dia, Deco.dn] at h3 ⊢
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self]
      · rw [Function.update_of_ne hQ]
        rw [Function.update_of_ne hQ] at h3
        rw [h3]
    · have h6 := congrArg Deco.be h1
      exact h6
  · intro e he hfe
    obtain ⟨r, hr, hrP⟩ := exists_lift_unit P.1 (c P)
    have hfe' : (c P).1 * d.f P e = 1 := hfe
    have h4 : d.f P (r • e) = 1 := by rw [hd.f_smul P r e (le_locP _ _ he), hr, hfe']
    have h5 := h2 (r • e) (Submodule.smul_mem _ r he) h4
    show (c P).1 * d'.f P (q • e) = a
    rw [smul_comm] at h5
    by_cases hy : q • e ∈ d'.at P.1
    · rw [← h5, hd'.f_smul P r _ hy, hr]
    · have hy' : r • q • e ∉ d'.at P.1 := by
        intro hm
        apply hy
        obtain ⟨s, hs, hm'⟩ := (mem_locP P.1 _ _).1 hm
        refine (mem_locP P.1 _ _).2 ⟨s * r, fun hsr => ?_, by rw [mul_smul]; exact hm'⟩
        rcases P.1.isPrime.mem_or_mem hsr with h' | h'
        · exact hs h'
        · exact hrP h'
      rw [← h5, hd'.f_off P _ hy, hd'.f_off P _ hy', mul_zero]

instance diaAction : MulAction (DiaG E ST) (DecoSet E n ST SG) where
  smul c d := d.dia c
  one_smul := DecoSet.dia_one
  mul_smul c c' d := DecoSet.dia_mul c c' d

theorem DecoSet.dia_smul_def (c : DiaG E ST) (d : DecoSet E n ST SG) : c • d = d.dia c := rfl

instance diaComm : SMulCommClass (DiaG E ST) (UF E n × GLG E n SG) (DecoSet E n ST SG) :=
  ⟨fun c a d => (DecoSet.dia_smul c a d)⟩

theorem DecoSet.dia_inv_dia (c : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c).dia c⁻¹ = d :=
  inv_smul_smul c d

theorem DecoSet.dia_mem_upSet (c : DiaG E ST) (P : ST) (q : 𝓞 E) (d d' : DecoSet E n ST SG) :
    d'.dia c ∈ (d.dia c).upSet P q ↔ d' ∈ d.upSet P q := by
  constructor
  · intro h
    have h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).upSet P q := Deco.IsUp.dia (d.dia c).2 h c⁻¹
    rwa [DecoSet.dia_inv_dia, DecoSet.dia_inv_dia] at h1
  · intro h
    exact Deco.IsUp.dia d.2 h c

theorem DecoSet.dia_mem_dnSetA (c : DiaG E ST) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal)
    (d d' : DecoSet E n ST SG) : d'.dia c ∈ (d.dia c).dnSetA P q a ↔ d' ∈ d.dnSetA P q a := by
  constructor
  · intro h
    have h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).dnSetA P q a :=
      Deco.IsDnA.dia (d.dia c).2 (d'.dia c).2 h c⁻¹
    rwa [DecoSet.dia_inv_dia, DecoSet.dia_inv_dia] at h1
  · intro h
    exact Deco.IsDnA.dia d.2 d'.2 h c

theorem DecoSet.sum_dia {M : Type*} [AddCommMonoid M] (nb : DecoSet E n ST SG → Finset (DecoSet E n ST SG))
    (c : DiaG E ST) (h : ∀ d d', d'.dia c ∈ nb (d.dia c) ↔ d' ∈ nb d) (F : DecoSet E n ST SG → M)
    (d : DecoSet E n ST SG) : ∑ d' ∈ nb d, F (d'.dia c) = ∑ d' ∈ nb (d.dia c), F d' :=
  Finset.sum_equiv (MulAction.toPerm c) (fun d' => (h d d').symm) (fun _ _ => rfl)

end DiaMoves

section OpsL

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

theorem diaG_apply (c : DiaG X.E ST) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((diaG C Λ c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia c) := by
  unfold diaG
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

theorem diamond_action_apply (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((diamondOperatorOnForms' C Λ P c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia1 P c) := by
  unfold diamondOperatorOnForms'
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

open Classical in
theorem diamond_single_eq (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : diamondOperatorOnForms' C Λ P c = diaG C Λ (Pi.mulSingle P c) := rfl

theorem UG_apply (P : ST) (q : 𝓞 X.E) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((UG C Λ P q φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      ∑ d' ∈ (DecoSet.upSet_finite d P q).toFinset, (φ : (formGSD C Λ).D → (formGSD C Λ).V) d' := by
  unfold UG
  exact LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

theorem DaG_apply (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) (φ : (formGSD C Λ).EqFun)
    (d : DecoSet X.E n ST SG) :
    ((DaG C Λ P q a φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      ∑ d' ∈ (DecoSet.dnSetA_finite d P q a).toFinset, (φ : (formGSD C Λ).D → (formGSD C Λ).V) d' := by
  unfold DaG
  exact LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

theorem NmG_eq (P : ST) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ] : NmG C Λ P = ∑ c, diamondOperatorOnForms' C Λ P c := by
  unfold NmG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem GsG_eq (P : ST) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ] :
    GsG C Λ P ψ = ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, ψ (c : 𝓞 X.E ⧸ P.1.asIdeal) • diamondOperatorOnForms' C Λ P c := by
  unfold GsG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem FFG_eq (P : ST) (q : 𝓞 X.E) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)] :
    FFG C Λ P q ψ = ∑ a : 𝓞 X.E ⧸ P.1.asIdeal, ψ a • DaG C Λ P q a := by
  unfold FFG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem diaG_one : diaG C Λ 1 = 1 := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [diaG_apply, DecoSet.dia_one]
  rfl

theorem diaG_mul (c c' : DiaG X.E ST) : diaG C Λ (c * c') = diaG C Λ c * diaG C Λ c' := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, diaG_apply, diaG_apply, diaG_apply, mul_comm, DecoSet.dia_mul]

def diaHom : DiaG X.E ST →* Module.End X.K (formGSD C Λ).EqFun where
  toFun := diaG C Λ
  map_one' := diaG_one C Λ
  map_mul' := diaG_mul C Λ

theorem diaG_eq_dia (c : DiaG X.E ST) :
    haveI : SMulCommClass (DiaG X.E ST) (formGSD C Λ).G (formGSD C Λ).D :=
      ⟨fun c a d => DecoSet.dia_smul c (FormG.incl Λ a) d⟩
    diaG C Λ c = (GSD.Slice.dia (formGSD C Λ) c).op := rfl

theorem UG_diaG (P : ST) (q : 𝓞 X.E) (c : DiaG X.E ST) :
    UG C Λ P q * diaG C Λ c = diaG C Λ c * UG C Λ P q := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, Module.End.mul_apply, UG_apply, diaG_apply, UG_apply]
  refine (Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_
  exact DecoSet.sum_dia (fun d => (DecoSet.upSet_finite d P q).toFinset) c
    (fun d d' => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.dia_mem_upSet c P q d d')
    (fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d

theorem DaG_diaG (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) (c : DiaG X.E ST) :
    DaG C Λ P q a * diaG C Λ c = diaG C Λ c * DaG C Λ P q a := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, Module.End.mul_apply, DaG_apply, diaG_apply, DaG_apply]
  refine (Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_
  exact DecoSet.sum_dia (fun d => (DecoSet.dnSetA_finite d P q a).toFinset) c
    (fun d d' => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.dia_mem_dnSetA c P q a d d')
    (fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d

theorem comm_NmG {A : Module.End X.K (formGSD C Λ).EqFun} (hA : ∀ c, A * diaG C Λ c = diaG C Λ c * A) (P : ST) :
    A * NmG C Λ P = NmG C Λ P * A := by
  unfold NmG
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => hA _

theorem diaG_comm (c c' : DiaG X.E ST) : diaG C Λ c * diaG C Λ c' = diaG C Λ c' * diaG C Λ c := by
  rw [← diaG_mul, ← diaG_mul, mul_comm]

end OpsL

section ColsL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem mem_ColRamV (u : Pr.Word) (j : ℕ) (φ : ColV W Ch u j) :
    φ ∈ ColRamV W Ch u j ↔ ∀ P, NmOp W Ch u j P φ = 0 := by
  simp only [ColRamV, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_ColRamV_of_comm (u : Pr.Word) (j : ℕ) {A : Module.End X.K (ColV W Ch u j)}
    (hA : ∀ c, A * diaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) c =
      diaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) c * A)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : A φ ∈ ColRamV W Ch u j := by
  rw [mem_ColRamV] at hφ ⊢
  intro P
  have h1 : NmOp W Ch u j P * A = A * NmOp W Ch u j P := (comm_NmG _ _ hA P).symm
  rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hφ P, map_zero]

theorem UOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : UOp W Ch u j P φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (UG_diaG _ _ P _) hφ

theorem DaOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (a : 𝓞 X.E ⧸ P.1.asIdeal)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : DaOp W Ch u j P a φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (DaG_diaG _ _ P _ a) hφ

theorem DOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : DOp W Ch u j P φ ∈ ColRamV W Ch u j :=
  DaOp_mem_ColRamV W Ch u j P 1 hφ

theorem diaOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : diaOp W Ch u j P c φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (A := diaOp W Ch u j P c) (fun c' => diaG_comm _ _ _ c') hφ

theorem list_prod_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (l : List (Module.End X.K M)) (h : ∀ A ∈ l, ∀ φ ∈ p, A φ ∈ p) : ∀ φ ∈ p, l.prod φ ∈ p := by
  induction l with
  | nil => intro φ hφ; simpa using hφ
  | cons A l ih =>
    intro φ hφ
    rw [List.prod_cons, Module.End.mul_apply]
    exact h A (List.mem_cons_self) _ (ih (fun B hB => h B (List.mem_cons_of_mem _ hB)) φ hφ)

theorem pow_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (A : Module.End X.K M) (h : ∀ φ ∈ p, A φ ∈ p) (k : ℕ) : ∀ φ ∈ p, (A ^ k) φ ∈ p := by
  induction k with
  | zero => intro φ hφ; simpa using hφ
  | succ k ih =>
    intro φ hφ
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h φ hφ)

theorem UprodC_mem_ColRamV (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : UprodC W Ch u j w φ ∈ ColRamV W Ch u j := by
  refine list_prod_mem (ColRamV W Ch u j) _ ?_ φ hφ
  intro A hA ψ hψ
  obtain ⟨P, -, rfl⟩ := List.mem_map.1 hA
  exact UOp_mem_ColRamV W Ch u j P hψ

theorem TUmC_mem_MramV (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) {φ : MfV W Ch u}
    (hφ : φ ∈ MramV W Ch u) : TUmC W Ch u w φ ∈ MramV W Ch u := by
  unfold TUmC
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _
    (pow_mem (MramV W Ch u) _ (fun ψ hψ => UprodC_mem_ColRamV W Ch u 0 w hψ) R.m φ hφ)

theorem mem_ramified_sublattice_iff (u : Pr.Word) (φ : MfV W Ch u) :
    φ ∈ ramifiedSublattice W Ch u ↔ φ ∈ MfL W Ch u ∧ φ ∈ MramV W Ch u := Iff.rfl

theorem mem_MramL (u : Pr.Word) (φ : MramV W Ch u) : φ ∈ MramL W Ch u ↔ ramIncl W Ch u φ ∈ MfL W Ch u := Iff.rfl

theorem ramIncl_injective (u : Pr.Word) : Function.Injective (ramIncl W Ch u) := Subtype.val_injective

theorem range_ramIncl (u : Pr.Word) : LinearMap.range (ramIncl W Ch u) = MramV W Ch u :=
  Submodule.range_subtype _

theorem MramL_eq_comap (u : Pr.Word) :
    MramL W Ch u = (MfL W Ch u).comap ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) := rfl

theorem MramL_map (u : Pr.Word) :
    (MramL W Ch u).map ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) = ramifiedSublattice W Ch u := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨hψ, ψ.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨φ, h2⟩, h1, rfl⟩

theorem ramified_sublattice_le_integral (u : Pr.Word) : ramifiedSublattice W Ch u ≤ MfL W Ch u := inf_le_left

theorem ramified_sublattice_saturated (u : Pr.Word) {a : 𝓞 X.K} (ha : a ≠ 0) {φ : MfV W Ch u} (hφ : φ ∈ MfL W Ch u)
    (h : a • φ ∈ ramifiedSublattice W Ch u) : φ ∈ ramifiedSublattice W Ch u := by
  refine ⟨hφ, ?_⟩
  have h1 : (algebraMap (𝓞 X.K) X.K a) • φ ∈ MramV W Ch u := by
    rw [algebraMap_smul]
    exact h.2
  have h2 : algebraMap (𝓞 X.K) X.K a ≠ 0 := by
    intro h0
    exact ha (RingOfIntegers.coe_injective (by simpa using h0))
  exact ((MramV W Ch u).smul_mem_iff h2).1 h1

theorem scaled_ramified_le_span (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    scaledRamifiedLattice W Ch u w ≤ (MramV W Ch u).restrictScalars (𝓞 X.K) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact TUmC_mem_MramV W Ch u w hφ.2

theorem NlamG_map (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    (NlamG W Ch u w).map ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) = scaledRamifiedLattice W Ch u w := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact hψ
  · intro h
    exact ⟨⟨φ, scaled_ramified_le_span W Ch u w h⟩, h, rfl⟩

def TUmR (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MramV W Ch u) :=
  (TUmC W Ch u w).restrict fun _ h => TUmC_mem_MramV W Ch u w h

theorem NlamG_eq_map (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    NlamG W Ch u w = (MramL W Ch u).map ((TUmR W Ch u w).restrictScalars (𝓞 X.K)) := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, e⟩
    exact ⟨⟨ψ, hψ.2⟩, hψ.1, Subtype.ext e⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨ψ.1, ⟨hψ, ψ.2⟩, rfl⟩

end ColsL

section SeenL

variable {X : Fields} {Pr : Primes X}

theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (x : 𝓞 X.E) :
    x ∈ (pullW τ w).asIdeal ↔ X.embO τ x ∈ w.asIdeal := Iff.rfl

theorem coe_embO (τ : X.Tau) (x : 𝓞 X.E) : ((X.embO τ x : 𝓞 X.K) : X.K) = X.emb τ (x : X.E) := rfl

theorem pullW_mem_vT (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    pullW τ w ∈ Pr.vT u ↔ X.embO τ (Pr.piT u) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

theorem embO_of_Kq {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (τ τ' : X.Tau) : X.embO τ x = X.embO τ' x :=
  RingOfIntegers.ext (hx τ τ')

theorem conjO_mem_Kq (hX : X.Ok) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) : ((X.conjO x : 𝓞 X.E) : X.E) ∈ X.Kq := by
  intro τ τ'
  show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))
  rw [hX.emb_star, hX.emb_star, hx τ τ']

theorem seenC_iff (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    seenC Pr u w ↔ ∀ τ, pullW τ w ∈ Pr.vT u :=
  forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm

theorem seenC_or_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : seenC Pr u w ∨ seenBarC Pr u w := by
  by_cases hne : Nonempty X.Tau
  · obtain ⟨τ₀⟩ := hne
    have h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
      rw [← map_mul, hPr.piT_norm u, map_natCast]
      exact hw
    rcases w.isPrime.mem_or_mem h1 with h | h
    · left
      intro τ
      rw [embO_of_Kq (hPr.piT_Kq u) τ τ₀]
      exact h
    · right
      intro τ
      rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]
      exact h
  · left
    intro τ
    exact absurd ⟨τ⟩ hne

theorem not_seen_both (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau)
    (h1 : X.embO τ (Pr.piT u) ∈ w.asIdeal) (h2 : X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : False := by
  obtain ⟨a, b, e⟩ := hPr.piT_cop u
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e' := congrArg (X.embO τ) e
  rw [map_add, map_mul, map_mul, map_one] at e'
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

variable {R : Ranks} (W : Wts X Pr.Word R)

theorem topsP_of_seenC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenC Pr u w) :
    topsP W u w = W.tops := by
  classical
  unfold topsP
  exact Finset.filter_true_of_mem fun τ _ => (pullW_mem_vT hPr u τ w).2 (h τ)

theorem topsP_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    topsP W u w = ∅ := by
  classical
  unfold topsP
  exact Finset.filter_false_of_mem fun τ _ h1 => not_seen_both hPr u w τ ((pullW_mem_vT hPr u τ w).1 h1) (h τ)

theorem mem_VVTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) :
    P ∈ VVTc W u w ↔ ∃ τ ∈ topsP W u w, pullW τ w = P.1 := by
  classical
  unfold VVTc topsP SeesP
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, hτ, e⟩
    exact ⟨τ, ⟨hτ, by rw [e]; exact P.2⟩, e⟩
  · rintro ⟨τ, ⟨hτ, -⟩, e⟩
    exact ⟨τ, hτ, e⟩

theorem VVTc_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    VVTc W u w = ∅ := by
  classical
  ext P
  rw [mem_VVTc, topsP_of_seenBarC W hPr u w h]
  simp

end SeenL

end Formalism.L2.Col
