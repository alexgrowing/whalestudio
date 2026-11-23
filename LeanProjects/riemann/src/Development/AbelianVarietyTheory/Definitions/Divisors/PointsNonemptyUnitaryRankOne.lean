import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def grp (G : HTGroup p) (β : G.Cˣ) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | (y.1 : G.C) * β * sh G y.1 = algebraMap ℚ G.C y.2 * β ∧ 0 < (y.2 : ℚ)}
  one_mem' := ⟨by simp [sh], by simp⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h2, hs⟩ ⟨h2', hs'⟩
    refine ⟨?_, ?_⟩
    · change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
      change (y' : G.C) * β * sh G y' = algebraMap ℚ G.C s' * β at h2'
      change ((y * y' : G.Cˣ) : G.C) * β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * β * (sh G y' * sh G y) = y * (y' * β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
    · change 0 < ((s * s' : ℚˣ) : ℚ)
      rw [Units.val_mul]; exact mul_pos hs hs'
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h2, hs⟩
    change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
    refine ⟨?_, ?_⟩
    · change ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs' : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs', mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]
    · change 0 < ((s⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val]; exact inv_pos.2 hs

def toAfF (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) :
    grp G β →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp (grp G β).subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.1
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def toP1 (G : HTGroup p) (β : G.Cˣ) : grp G β →* Gr G 1 :=
  ((inclG G 1).comp (locC G)).comp (grp G β).subtype

def toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : grp G β →* GL (Fin G.n) ℂ :=
  (Units.map (G.psi v).toMonoidHom).comp ((MonoidHom.fst _ _).comp (grp G β).subtype)

def herm (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Matrix (Fin G.n) (Fin G.n) ℂ :=
  G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)

def PosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type :=
  {x : Fin G.n → ℂ // 0 < (star x ⬝ᵥ (herm G v β *ᵥ x)).re}

abbrev Dat (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := (G.GAf × Gr G 1) × PosV G v β

def Same (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : Dat G v β) : Prop :=
  ∃ (y : grp G β) (k : G.GAf × Gr G 1) (c : ℂ), k.1 ∈ Kf ∧ k.2 ∈ K' ∧ c ≠ 0 ∧
    b.1 = ((toAfF G β x t hx y, toP1 G β y) : G.GAf × Gr G 1) * a.1 * k ∧
    b.2.1 = c • ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)

def Pts (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  Quot (Same G v β x t hx Kf K')

def FixL (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : Fin G.n → ℂ) : Prop :=
  ∃ c : ℂ, (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = c • z

def Stab (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) : Type :=
  {y : grp G β // a.1.1⁻¹ * toAfF G β x t hx y * a.1.1 ∈ Kf ∧ a.1.2⁻¹ * toP1 G β y * a.1.2 ∈ K' ∧
    FixL G v β y a.2.1}

def cxSumAt (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Pts G v β x t hx Kf K',
    ((Nat.card (Stab G v β x t hx Kf K' (Quot.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : grp G β, if FixL G v β y (Quot.out q).2.1 then
        f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
          f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) else 0

structure Form (G : HTGroup p) where

  β : G.Cˣ
  sym : sh G β = β
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t
  trivR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1

def Form.Rel {G : HTGroup p} (P Q : Form G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y)

def FCls (G : HTGroup p) : Type := Quot (Form.Rel (G := G))

def cxSum (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (P : Form G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  cxSumAt G v wt P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf f K' f'

def cxTotal (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : FCls G, cxSum G v wt (Quot.out q) Kf f K' f'

def RegAf (G : HTGroup p) (g : G.GAf) : Prop :=
  ∃ w : AwayP p, ∀ a b : w.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute a ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute b ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute a b

def CxCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsSimple G → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (wt : Polynomial G.F → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotal G v wt L.K.toSubgroup f K' f' = fullSum G wt L.K.toSubgroup f 1 K' f'

def Form.one (G : HTGroup p) : Form G := ⟨1, sh_one_eq G, ⟨1, 1, by simp [Triv, inC]⟩, ⟨1, by simp [Triv, inC]⟩⟩

theorem triv_norm (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y : G.Cˣ) :
    Triv G R (y * sh G y) (Units.map (inC G R).toMonoidHom y⁻¹) 1 := by
  have e1 : (starT G.star R (inC G R ((y⁻¹ : G.Cˣ) : G.C))).unop = inC G R (sh G ((y⁻¹ : G.Cˣ) : G.C)) :=
    starT_tmul G.star R 1 _
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  show inC G R ((y⁻¹ : G.Cˣ) : G.C) * inC G R (y * sh G y) * (starT G.star R (inC G R ((y⁻¹ : G.Cˣ) : G.C))).unop = _
  rw [e1, ← map_mul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, e, map_one, Units.val_one, map_one]

def Form.norm (G : HTGroup p) (y : G.Cˣ) : Form G where
  β := ⟨y * sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C) * (y⁻¹ : G.Cˣ), by
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      rw [mul_assoc, ← mul_assoc (sh G y), e, one_mul, Units.mul_inv], by
      have e : sh G ((y⁻¹ : G.Cˣ) : G.C) * sh G y = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
      rw [mul_assoc, ← mul_assoc ((y⁻¹ : G.Cˣ) : G.C), Units.inv_mul, one_mul, e]⟩
  sym := by
    show sh G (y * sh G y) = y * sh G y
    simp only [sh, map_mul, MulOpposite.unop_mul, G.star_star]
  trivAf := ⟨_, 1, triv_norm G _ y⟩
  trivR := ⟨_, triv_norm G _ y⟩

def Form.ofPair {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

theorem herm_one (G : HTGroup p) (v : InfinitePlace G.F) : herm G v 1 = G.gram v := by
  simp [herm]

theorem nonempty_posV_of_mark {G : HTGroup p} (P : Pair G) (μ : ℂ) (h : P.Mark μ) :
    ∃ v, sigPosH (G.gram_herm v) = 1 ∧ Nonempty (PosV G v P.β) := by
  obtain ⟨v, hv, x, -, hx⟩ := h
  exact ⟨v, hv, ⟨⟨x, hx⟩⟩⟩

theorem fixL_one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (z : Fin G.n → ℂ) : FixL G v β 1 z :=
  ⟨1, by simp [toV]⟩

theorem same_refl (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Same G v β x t hx Kf K' a a :=
  ⟨1, 1, 1, Kf.one_mem, K'.one_mem, one_ne_zero, by simp, by simp [toV]⟩

def Stab.one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Stab G v β x t hx Kf K' a :=
  ⟨1, by simpa using Kf.one_mem, by simpa using K'.one_mem, fixL_one G v β _⟩

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

theorem points_nonempty_unitaryRankOne : ∃ v, sigPosH ((ex 1 one_ne_zero).gram_herm v) = 1 ∧
    ∀ x t hx Kf K', Nonempty (Pts (ex 1 one_ne_zero) v exPair.β x t hx Kf K') := by
  obtain ⟨μ, hμ⟩ := exPair_mark
  obtain ⟨v, hv, ⟨z⟩⟩ := nonempty_posV_of_mark _ μ hμ
  exact ⟨v, hv, fun x t hx Kf K' => ⟨Quot.mk _ (1, z)⟩⟩

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

example : ((exPair.γ, exPair.c) : _ × ℚˣ) ∈ grp (ex 1 one_ne_zero) exPair.β :=
  ⟨exPair.sim, by show (0:ℚ) < 5; norm_num⟩

theorem finitePlacesAway_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (AwayP p) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (p+1)
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hqp
  refine ⟨⟨⟨Ideal.span {(q:ℤ)}, (Ideal.span_singleton_prime hq'.ne_zero).2 hq', by simpa using hqp.ne_zero⟩, fun h => ?_⟩⟩
  have h1 : (q:ℤ) ∣ (p:ℤ) := Ideal.mem_span_singleton.1 (by
    have : (p:ℤ) ∈ Ideal.span {(p:ℤ)} := Ideal.mem_span_singleton_self _
    rw [← h] at this; exact this)
  have h2 : q ∣ p := Int.natCast_dvd_natCast.1 h1
  have := Nat.le_of_dvd (Fact.out : p.Prime).pos h2
  omega

theorem regAf_of_comm (G : HTGroup p) (hc : ∀ a b : G.C, a * b = b * a) (g : G.GAf) : RegAf G g := by
  obtain ⟨w⟩ := finitePlacesAway_nonempty p
  have key : ∀ a b : w.1.adicCompletion ℚ ⊗[ℚ] G.C, a * b = b * a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | tmul r x =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | tmul s y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s, hc x y]
  exact ⟨w, fun a b _ _ => key a b⟩

theorem sigG_one (G : HTGroup p) (g : Gr G 1) : sigG G 1 g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · show GlobalTheory.LKLoc.sig p (Q0 p) 1 1 g.1 = g.1
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact DFunLike.congr_fun (frobQ_degree_one p) ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)) i j)
  · show sigRes p (G.Fw i) G.n 1 (g.2 i) = g.2 i
    rw [sigRes_degree_one]; rfl

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

theorem hyps_ex : IsSimple (ex 1 one_ne_zero) ∧ (∃ v, sigPosH ((ex 1 one_ne_zero).gram_herm v) = 1) ∧
    ∃ (L : (ex 1 one_ne_zero).Level) (f : (ex 1 one_ne_zero).GAf → ℂ) (K' : Subgroup (Gr (ex 1 one_ne_zero) 1))
      (f' : Gr (ex 1 one_ne_zero) 1 → ℂ), f 1 = 1 ∧ f' 1 = 1 ∧
      IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f ∧ (∀ g, f g ≠ 0 → RegAf (ex 1 one_ne_zero) g) ∧
      IsTest (sigG (ex 1 one_ne_zero) 1) (KHT 5 (ex 1 one_ne_zero).m (ex 1 one_ne_zero).n 1 (ex 1 one_ne_zero).Fw) K' f' := by
  obtain ⟨μ, v, hv, -⟩ := exPair_mark
  obtain ⟨L⟩ := GlobalTheory.LKTrip.LevelExists.level_exists 5 (ex 1 one_ne_zero)
  refine ⟨isSimple_unitaryRankOne, ⟨v, hv⟩, L, _, _, _, ?_, ?_, isTest_indicator _ _ (by simp), fun g _ => regAf_of_comm _ ?_ g,
    isTest_indicator _ _ ?_⟩
  · exact Set.indicator_of_mem (Subgroup.one_mem _) _
  · exact Set.indicator_of_mem (Subgroup.one_mem _) _
  · intro a b
    have key : ∀ a b : Matrix (Fin 1) (Fin 1) QI, a * b = b * a := by
      intro a b; ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, mul_comm]
    exact key a b
  · rintro _ ⟨k, hk, rfl⟩
    rw [sigG_one]; exact hk

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSum G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSum, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) : ((Form.one G).β : G.C) = 1 := rfl

end GlobalTheory.LKCx
