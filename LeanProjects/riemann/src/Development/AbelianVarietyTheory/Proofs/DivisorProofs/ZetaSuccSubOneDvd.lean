import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSubOneMemJacobson

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.FrobQuot

variable {p : ℕ} [Fact p.Prime] (S : CycPerfd p)

theorem theta_frobenius (a : Ainf p S.R) :
    ∃ t : S.R, fontaineTheta S.R p (frobenius a) = fontaineTheta S.R p a ^ p + p * t := by
  have h := CycElem.theta_phiInv_pow S (frobenius a)
  rw [Dieudonne.phiInv_frobenius, ← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨-t, by linear_combination ht⟩

theorem zeta_sub_one_dvd_p (n : ℕ) : zeta S.ε (n + 1) - 1 ∣ (p : S.R) :=
  (zeta_sub_one_dvd S n).trans (zeta_one_sub_one_dvd S)

theorem zeta_succ_sub_one_dvd (n : ℕ) : zeta S.ε (n + 1) - 1 ∣ zeta S.ε n - 1 := by
  have h := sub_one_dvd_pow_sub_one (zeta S.ε (n + 1)) p
  rwa [zeta_succ_pow] at h

theorem zeta_sub_one_dvd_two (r : ℕ) : zeta S.ε (r + 2) - 1 ∣ zeta S.ε 2 - 1 := by
  induction r with
  | zero => exact dvd_rfl
  | succ r ih => exact (zeta_succ_sub_one_dvd S (r + 2)).trans ih

theorem mem_base_iff {h : ℕ} (x : Fin h → S.R) : x ∈ base S h ↔ ∀ j, ∃ v, x j = (zeta S.ε 1 - 1) * v := by
  rw [mem_base]
  constructor
  · rintro ⟨y, rfl⟩ j
    exact ⟨y j, rfl⟩
  · intro h
    choose v hv using h
    exact ⟨v, funext fun j => (hv j).symm⟩

theorem step_base (r : ℕ) (a : Ainf p S.R) (x y w : S.R)
    (hx : (zeta S.ε 1 - 1) * fontaineTheta S.R p a = (zeta S.ε (r + 2) - 1) * x)
    (hy : (zeta S.ε 1 - 1) * fontaineTheta S.R p (frobenius a) = (zeta S.ε (r + 1) - 1) * y)
    (hw : x = (zeta S.ε 1 - 1) * w) : ∃ v, y = (zeta S.ε 1 - 1) * v := by
  have hπ : IsSMulRegular S.R (zeta S.ε 1 - 1) := isSMulRegular_zeta_sub_one S 0
  have h1 : fontaineTheta S.R p a = (zeta S.ε (r + 2) - 1) * w := hπ (by
    simp only [smul_eq_mul]
    rw [hx, hw]
    ring)
  obtain ⟨t, ht⟩ := theta_frobenius S a
  obtain ⟨s, hs⟩ := CycElem.exists_zeta_sub_one S (r + 1)
  obtain ⟨q, hq⟩ := zeta_sub_one_dvd_p S r
  set m := (zeta S.ε (r + 1 + 1) - 1) * ((zeta S.ε (r + 1 + 1) - 1) * s + 1)
  have h2 : fontaineTheta S.R p (frobenius a) = (zeta S.ε (r + 1) - 1) * (w ^ p + q * (t - m * w ^ p)) := by
    rw [ht, h1, mul_pow]
    have hs' : zeta S.ε (r + 1) - 1 = (zeta S.ε (r + 2) - 1) ^ p + p * m := by rw [hs]; ring
    linear_combination (t - m * w ^ p) * hq - w ^ p * hs'
  refine ⟨w ^ p + q * (t - m * w ^ p), isSMulRegular_zeta_sub_one S r ?_⟩
  simp only [smul_eq_mul]
  rw [← hy, h2]
  ring

theorem step_inj (r : ℕ) (a : Ainf p S.R) (x y w : S.R)
    (hx : (zeta S.ε 1 - 1) * fontaineTheta S.R p a = (zeta S.ε (r + 2) - 1) * x)
    (hy : (zeta S.ε 1 - 1) * fontaineTheta S.R p (frobenius a) = (zeta S.ε (r + 1) - 1) * y)
    (hw : y = (zeta S.ε 1 - 1) * w) : ∃ v, x = (zeta S.ε 1 - 1) * v := by
  have hπ : IsSMulRegular S.R (zeta S.ε 1 - 1) := isSMulRegular_zeta_sub_one S 0
  have h1 : fontaineTheta S.R p (frobenius a) = (zeta S.ε (r + 1) - 1) * w := hπ (by
    simp only [smul_eq_mul]
    rw [hy, hw]
    ring)
  obtain ⟨w', rfl⟩ := S.surj w
  have h2 : frobenius a - muN S (r + 1) * w' ∈ RingHom.ker (fontaineTheta S.R p) := by
    rw [RingHom.mem_ker, map_sub, map_mul, theta_muN, h1, sub_self]
  rw [S.ker_eq, Ideal.mem_span_singleton'] at h2
  obtain ⟨b, hb⟩ := h2
  have hx0 : phiInv p S.R (xi S.ε) = xiN S 1 := phiInv_xiN S 0
  have h3 : a = muN S (r + 2) * phiInv p S.R w' + xiN S 1 * phiInv p S.R b := by
    have h4 := congrArg (phiInv p S.R) hb
    rw [map_mul, map_sub, map_mul, Dieudonne.phiInv_frobenius, phiInv_muN, hx0] at h4
    linear_combination -h4
  have h5 : zeta S.ε (r + 2) - 1 ∣ fontaineTheta S.R p (xiN S 1) :=
    (zeta_sub_one_dvd_two S r).trans ((dvd_pow_self _ (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)).trans
      (CycElem.associated_theta_xiN S 0).symm.dvd)
  obtain ⟨v0, hv0⟩ := h5
  refine ⟨fontaineTheta S.R p (phiInv p S.R w') + v0 * fontaineTheta S.R p (phiInv p S.R b),
    isSMulRegular_zeta_sub_one S (r + 1) ?_⟩
  simp only [smul_eq_mul]
  rw [← hx, h3, map_add, map_mul, map_mul, theta_muN, hv0]
  ring

end GlobalTheory.PerfdLat.FrobQuot

namespace GlobalTheory.PerfdLat.FrobQuot

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

def Rel (r : ℕ) {n : ℕ} (k : Fin n → Ainf p S.R) (x y : Fin n → S.R) : Prop :=
  (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ k = (zeta S.ε (r + 2) - 1) • x ∧
    (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) = (zeta S.ε (r + 1) - 1) • y

variable {D c}

theorem Rel.sub {r n : ℕ} {k k' : Fin n → Ainf p S.R} {x x' y y' : Fin n → S.R} (h : Rel r k x y)
    (h' : Rel r k' x' y') : Rel r (k - k') (x - x') (y - y') :=
  ⟨by rw [map_sub, smul_sub, smul_sub, h.1, h'.1], by rw [map_sub, map_sub, smul_sub, smul_sub, h.2, h'.2]⟩

theorem Rel.add {r n : ℕ} {k k' : Fin n → Ainf p S.R} {x x' y y' : Fin n → S.R} (h : Rel r k x y)
    (h' : Rel r k' x' y') : Rel r (k + k') (x + x') (y + y') :=
  ⟨by rw [map_add, smul_add, smul_add, h.1, h'.1], by rw [map_add, map_add, smul_add, smul_add, h.2, h'.2]⟩

theorem Rel.zero (r n : ℕ) : Rel (S := S) r (0 : Fin n → Ainf p S.R) 0 0 :=
  ⟨by simp, by simp⟩

theorem Rel.smul {r n : ℕ} {k : Fin n → Ainf p S.R} {x y : Fin n → S.R} (h : Rel r k x y) (a : Ainf p S.R) :
    Rel r (a • k) (fontaineTheta S.R p a • x) (fontaineTheta S.R p (frobenius a) • y) :=
  ⟨by rw [map_smulₛₗ, smul_comm, h.1, smul_comm], by rw [map_smulₛₗ, map_smulₛₗ, smul_comm, h.2, smul_comm]⟩

theorem Rel.base {r n : ℕ} {k : Fin n → Ainf p S.R} {x y : Fin n → S.R} (h : Rel r k x y) :
    x ∈ GlobalTheory.PerfdLat.base S n → y ∈ GlobalTheory.PerfdLat.base S n := by
  rw [mem_base_iff, mem_base_iff]
  intro hx j
  obtain ⟨w, hw⟩ := hx j
  exact step_base S r (k j) (x j) (y j) w (congrFun h.1 j) (congrFun h.2 j) hw

theorem Rel.base_inv {r n : ℕ} {k : Fin n → Ainf p S.R} {x y : Fin n → S.R} (h : Rel r k x y) :
    y ∈ GlobalTheory.PerfdLat.base S n → x ∈ GlobalTheory.PerfdLat.base S n := by
  rw [mem_base_iff, mem_base_iff]
  intro hy j
  obtain ⟨w, hw⟩ := hy j
  exact step_inj S r (k j) (x j) (y j) w (congrFun h.1 j) (congrFun h.2 j) hw

variable (D c)

theorem exists_rel (r : ℕ) (x : H D c (r + 1)) : ∃ y : H D c r, ∃ k, Rel r k (x : Fin G.height → S.R) y := by
  obtain ⟨k, hk, hx⟩ := (mem_H D c (r + 1) x).1 x.2
  obtain ⟨d, hd⟩ := zeta_sub_one_dvd S r
  have hy : d • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) ∈ H D c r :=
    (mem_H D c r _).2 ⟨_, (mem_K_succ D c (r + 1) k).1 hk, by rw [smul_smul, ← hd]⟩
  exact ⟨⟨_, hy⟩, k, hx, by rw [smul_smul, ← hd]⟩

theorem p_smul_mem_base (r : ℕ) (y : Fin G.height → S.R) (hy : y ∈ H D c r) : (p : S.R) • y ∈ GlobalTheory.PerfdLat.base S G.height := by
  obtain ⟨k, -, hk⟩ := (mem_H D c r y).1 hy
  obtain ⟨q, hq⟩ := zeta_sub_one_dvd_p S r
  refine (mem_base S _).2 ⟨q • piMap (fontaineTheta S.R p) _ k, ?_⟩
  rw [smul_comm, hk, hq, mul_comm, mul_smul]

abbrev cls (r : ℕ) (y : H D c r) : QQ D c r := Submodule.Quotient.mk y

theorem cls_eq_iff (r : ℕ) (y y' : H D c r) :
    cls D c r y = cls D c r y' ↔ (y : Fin G.height → S.R) - y' ∈ GlobalTheory.PerfdLat.base S G.height := by
  rw [cls, cls, Submodule.Quotient.eq]
  rfl

theorem p_smul_QQ (r : ℕ) (q : QQ D c r) : (p : S.R) • q = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact p_smul_mem_base D c r _ y.2

variable {D c}

theorem cls_eq_of_rel {r : ℕ} {x x' : H D c (r + 1)} {y y' : H D c r} {k k' : Fin G.height → Ainf p S.R}
    (h : Rel r k (x : Fin G.height → S.R) y) (h' : Rel r k' (x' : Fin G.height → S.R) y')
    (hx : cls D c (r + 1) x = cls D c (r + 1) x') : cls D c r y = cls D c r y' := by
  rw [cls_eq_iff] at hx ⊢
  exact (h.sub h').base hx

variable (D c)

def rep (r : ℕ) (q : QQ D c r) : H D c r := Function.surjInv (Submodule.Quotient.mk_surjective _) q

theorem cls_rep (r : ℕ) (q : QQ D c r) : cls D c r (rep D c r q) = q :=
  Function.surjInv_eq (Submodule.Quotient.mk_surjective _) q

def val (r : ℕ) (x : H D c (r + 1)) : H D c r := (exists_rel D c r x).choose

theorem rel_val (r : ℕ) (x : H D c (r + 1)) : ∃ k, Rel r k (x : Fin G.height → S.R) (val D c r x) :=
  (exists_rel D c r x).choose_spec

def psi (r : ℕ) : QQ D c (r + 1) →+ QQ D c r where
  toFun q := cls D c r (val D c r (rep D c (r + 1) q))
  map_zero' := by
    obtain ⟨k, hk⟩ := rel_val D c r (rep D c (r + 1) 0)
    have h := cls_eq_of_rel (x' := 0) (y' := 0) hk (Rel.zero r _) (by rw [cls_rep] <;> rfl)
    rw [h]
    rfl
  map_add' q q' := by
    obtain ⟨k, hk⟩ := rel_val D c r (rep D c (r + 1) (q + q'))
    obtain ⟨k1, hk1⟩ := rel_val D c r (rep D c (r + 1) q)
    obtain ⟨k2, hk2⟩ := rel_val D c r (rep D c (r + 1) q')
    have h := cls_eq_of_rel (x' := rep D c (r + 1) q + rep D c (r + 1) q')
      (y' := val D c r (rep D c (r + 1) q) + val D c r (rep D c (r + 1) q')) hk (hk1.add hk2)
      (by rw [cls_rep]; simp only [cls, Submodule.Quotient.mk_add]; rw [← cls, ← cls, cls_rep, cls_rep])
    rw [h]
    rfl

theorem psi_cls {r : ℕ} {x : H D c (r + 1)} {y : H D c r} {k : Fin G.height → Ainf p S.R}
    (h : Rel r k (x : Fin G.height → S.R) y) : psi D c r (cls D c (r + 1) x) = cls D c r y := by
  obtain ⟨k0, hk0⟩ := rel_val D c r (rep D c (r + 1) (cls D c (r + 1) x))
  exact cls_eq_of_rel hk0 h (cls_rep D c (r + 1) _)

end GlobalTheory.PerfdLat.FrobQuot

namespace GlobalTheory.PerfdLat.FrobQuot

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

theorem psi_smul (r : ℕ) (a : S.R) (q : QQ D c (r + 1)) : psi D c r (a • q) = a ^ p • psi D c r q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨k, hk⟩ := rel_val D c r x
  obtain ⟨a', rfl⟩ := S.surj a
  have h := hk.smul a'
  obtain ⟨t, ht⟩ := theta_frobenius S a'
  have h1 : psi D c r (cls D c (r + 1) (fontaineTheta S.R p a' • x)) =
      cls D c r (fontaineTheta S.R p (frobenius a') • val D c r x) := psi_cls D c h
  rw [← Submodule.Quotient.mk_smul]
  change psi D c r (cls D c (r + 1) _) = _
  rw [h1, psi_cls D c hk, ht, add_smul]
  simp only [cls, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
  rw [mul_comm, mul_smul, p_smul_QQ, smul_zero, add_zero]

theorem psi_injective (r : ℕ) : Function.Injective (psi D c r) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨k, hk⟩ := rel_val D c r x
  have h0 : psi D c r (cls D c (r + 1) x) = cls D c r (val D c r x) := psi_cls D c hk
  have h1 : cls D c r (val D c r x) = cls D c r 0 := by rw [← h0]; exact hq
  rw [cls_eq_iff] at h1
  have h2 := hk.base_inv (by simpa using h1)
  rw [Submodule.Quotient.mk_eq_zero]
  exact h2

theorem psi_surjective (r : ℕ) : Function.Surjective (psi D c r) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨k', hk', hy⟩ := (mem_H D c r y).1 y.2
  obtain ⟨d, hd⟩ := zeta_sub_one_dvd S (r + 1)
  set k := piMap (phiInv p S.R) (Fin G.height) k'
  have hk : piMap frobenius _ k = k' := funext fun j => Dieudonne.frobenius_phiInv _
  have hkK : k ∈ K D c (r + 2) := (mem_K_succ D c (r + 1) k).2 (hk ▸ hk')
  have hx : d • piMap (fontaineTheta S.R p) _ k ∈ H D c (r + 1) :=
    (mem_H D c (r + 1) _).2 ⟨k, hkK, by rw [smul_smul, ← hd]⟩
  refine ⟨cls D c (r + 1) ⟨_, hx⟩, psi_cls D c (k := k) ⟨by rw [smul_smul, ← hd], by rw [hk]; exact hy⟩⟩

end GlobalTheory.PerfdLat.FrobQuot

namespace GlobalTheory.PerfdLat.FrobQuot

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

def actP (r : ℕ) : S.R ⧸ Ideal.span {(p : S.R)} →+* AddMonoid.End (QQ D c r) :=
  Ideal.Quotient.lift _ (Module.toAddMonoidEnd S.R (QQ D c r)) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine AddMonoidHom.ext fun q => ?_
    change (b * (p : S.R)) • q = 0
    rw [mul_smul, p_smul_QQ, smul_zero]

theorem quotientAction_mk (r : ℕ) (a : S.R) (q : QQ D c r) : actP D c r (Ideal.Quotient.mk _ a) q = a • q := by
  rw [actP, Ideal.Quotient.lift_mk]
  rfl

def bil (r : ℕ) : S.R ⧸ Ideal.span {(p : S.R)} →+ QQ D c (r + 1) →+ QQ D c r where
  toFun s := AddMonoidHom.comp (actP D c r s) (psi D c r)
  map_zero' := by rw [map_zero]; exact AddMonoidHom.zero_comp _
  map_add' s t := by rw [map_add]; exact AddMonoidHom.add_comp _ _ _

theorem bil_mk (r : ℕ) (a : S.R) (q : QQ D c (r + 1)) : bil D c r (Ideal.Quotient.mk _ a) q = a • psi D c r q :=
  quotientAction_mk D c r a _

end GlobalTheory.PerfdLat.FrobQuot

namespace GlobalTheory.PerfdLat

open FrobQuot in

theorem frobenius_quot_T : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R)
    (c : ConstTate (eps S) G), ∀ r, ∃ ψ : QQ D c (r + 1) →+ QQ D c r,
      (∀ (k : Fin G.height → Ainf p S.R) (x : H D c (r + 1)) (y : H D c r), k ∈ K D c (r + 2) →
        (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ k = (zeta S.ε (r + 2) - 1) • (x : Fin G.height → S.R) →
        (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (piMap WittVector.frobenius _ k) =
          (zeta S.ε (r + 1) - 1) • (y : Fin G.height → S.R) →
        ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      ∀ f : S.R →+* S.R ⧸ Ideal.span {(p : S.R)}, (∀ a, f a = Ideal.Quotient.mk _ (a ^ p)) →
        ∃ e : (ModuleCat.extendScalars f).obj (ModuleCat.of S.R (QQ D c (r + 1))) ≃+ QQ D c r,
          ∀ (a : S.R) (x : QQ D c (r + 1)),
            e ((Ideal.Quotient.mk _ a : S.R ⧸ Ideal.span {(p : S.R)}) ⊗ₜ[S.R, f] x) = a • ψ x := by
  intro p _ D S G c r
  refine ⟨psi D c r, fun k x y _ hx hy => psi_cls D c (k := k) ⟨hx, hy⟩, fun f hf => ?_⟩
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of _ (S.R ⧸ Ideal.span {(p : S.R)}))
  let toM : S.R ⧸ Ideal.span {(p : S.R)} → M := fun s => s
  let B : M →+ QQ D c (r + 1) →+ QQ D c r := bil D c r
  have hB : ∀ (a : S.R) (m : M) (n : QQ D c (r + 1)), B (a • m) n = B m (a • n) := by
    intro a m n
    obtain ⟨m', hm⟩ := Ideal.Quotient.mk_surjective (show S.R ⧸ Ideal.span {(p : S.R)} from m)
    have h1 : (show S.R ⧸ Ideal.span {(p : S.R)} from a • m) = Ideal.Quotient.mk _ (a ^ p * m') := by
      change f a * _ = _
      rw [hf, ← hm, map_mul]
    change bil D c r (show S.R ⧸ Ideal.span {(p : S.R)} from a • m) n =
      bil D c r (show S.R ⧸ Ideal.span {(p : S.R)} from m) (a • n)
    rw [h1, ← hm, bil_mk, bil_mk, psi_smul, smul_smul, mul_comm]
  let T := TensorProduct.liftAddHom B hB
  have hT : ∀ (a : S.R) (x : QQ D c (r + 1)),
      T (toM (Ideal.Quotient.mk _ a) ⊗ₜ[S.R] x) = a • psi D c r x := fun a x => by
    rw [TensorProduct.liftAddHom_tmul]
    exact bil_mk D c r a x
  have hfs : ∀ s : S.R ⧸ Ideal.span {(p : S.R)}, ∃ d, f d = s := by
    intro s
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨a, rfl⟩ := S.surj s'
    exact ⟨fontaineTheta S.R p (phiInv p S.R a), by rw [hf, map_pow, CycElem.theta_phiInv_pow]⟩
  have hone : ∀ t : TensorProduct S.R M (QQ D c (r + 1)), ∃ q, t = toM (Ideal.Quotient.mk _ 1) ⊗ₜ[S.R] q := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul s q =>
      obtain ⟨d, hd⟩ := hfs s
      refine ⟨d • q, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      exact (hd.symm.trans (mul_one (f d)).symm).trans
        (congrArg (f d * ·) (map_one (Ideal.Quotient.mk (Ideal.span {(p : S.R)}))).symm)
    | add t t' ht ht' =>
      obtain ⟨q, rfl⟩ := ht
      obtain ⟨q', rfl⟩ := ht'
      exact ⟨q + q', (TensorProduct.tmul_add _ _ _).symm⟩
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun t ht => ?_
    obtain ⟨q, rfl⟩ := hone t
    rw [hT, one_smul] at ht
    rw [psi_injective D c r (ht.trans (map_zero _).symm), TensorProduct.tmul_zero]
  have hsurj : Function.Surjective T := by
    intro y
    obtain ⟨q, rfl⟩ := psi_surjective D c r y
    exact ⟨_, (hT 1 q).trans (one_smul _ _)⟩
  exact ⟨AddEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.PerfdLat
