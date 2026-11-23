import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAltSucc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace Staircase

structure DblData (R : Type) [CommRing R] where
  D : ℕ → ℕ → Type
  [gD : ∀ p q, AddCommGroup (D p q)]
  [mD : ∀ p q, Module R (D p q)]
  v : ∀ p q, D p q →ₗ[R] D (p + 1) q
  h : ∀ p q, D p q →ₗ[R] D p (q + 1)
  comm : ∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)
  A : ℕ → Type
  [gA : ∀ p, AddCommGroup (A p)]
  [mA : ∀ p, Module R (A p)]
  dA : ∀ p, A p →ₗ[R] A (p + 1)
  a : ∀ p, A p →ₗ[R] D p 0
  C : ℕ → Type
  [gC : ∀ q, AddCommGroup (C q)]
  [mC : ∀ q, Module R (C q)]
  dC : ∀ q, C q →ₗ[R] C (q + 1)
  c : ∀ q, C q →ₗ[R] D 0 q

attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC

variable {R : Type} [CommRing R]

structure DblData.Good (X : DblData R) : Prop where
  ha : ∀ p, (X.a (p + 1)).comp (X.dA p) = (X.v p 0).comp (X.a p)
  hc : ∀ q, (X.c (q + 1)).comp (X.dC q) = (X.h 0 q).comp (X.c q)
  ka : ∀ p, LinearMap.ker (X.a p) = ⊥
  ra : ∀ p, LinearMap.ker (X.h p 0) = LinearMap.range (X.a p)
  rh : ∀ p q, LinearMap.ker (X.h p (q + 1)) = LinearMap.range (X.h p q)
  kc : ∀ q, LinearMap.ker (X.c q) = ⊥
  rc : ∀ q, LinearMap.ker (X.v 0 q) = LinearMap.range (X.c q)
  rv : ∀ p q, LinearMap.ker (X.v (p + 1) q) = LinearMap.range (X.v p q)

namespace DblData

theorem comm_apply (X : DblData R) (p q : ℕ) (z : X.D p q) :
    X.v p (q + 1) (X.h p q z) = X.h (p + 1) q (X.v p q z) :=
  LinearMap.congr_fun (X.comm p q) z

def shift (X : DblData R) : DblData R where
  D p q := X.D (p + 1) q
  v p q := X.v (p + 1) q
  h p q := X.h (p + 1) q
  comm p q := X.comm (p + 1) q
  A p := X.A (p + 1)
  dA p := X.dA (p + 1)
  a p := X.a (p + 1)
  C q := LinearMap.range (X.v 0 q)
  dC q := (X.h 1 q).restrict (fun x hx => by
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨X.h 0 q z, X.comm_apply 0 q z⟩)
  c q := (LinearMap.range (X.v 0 q)).subtype

def up (X : DblData R) (n : ℕ) : X.D 0 n →ₗ[R] X.shift.C n := (X.v 0 n).rangeRestrict

theorem up_surj (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by
  have hw : (w : LinearMap.range (X.v 0 n)).1 ∈ LinearMap.range (X.v 0 n) := (w : LinearMap.range (X.v 0 n)).2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩

namespace Good

theorem shift {X : DblData R} (hX : X.Good) : X.shift.Good where
  ha p := hX.ha (p + 1)
  hc q := LinearMap.ext fun _ => rfl
  ka p := hX.ka (p + 1)
  ra p := hX.ra (p + 1)
  rh p q := hX.rh (p + 1) q
  kc q := Submodule.ker_subtype _
  rc q := by
    show LinearMap.ker (X.v 1 q) = LinearMap.range (LinearMap.range (X.v 0 q)).subtype
    rw [Submodule.range_subtype]
    exact hX.rv 0 q
  rv p q := hX.rv (p + 1) q

theorem a_d {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) :
    X.a (p + 1) (X.dA p x) = X.v p 0 (X.a p x) :=
  LinearMap.congr_fun (hX.ha p) x

theorem c_d {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) :
    X.c (q + 1) (X.dC q y) = X.h 0 q (X.c q y) :=
  LinearMap.congr_fun (hX.hc q) y

theorem a_injective {X : DblData R} (hX : X.Good) (p : ℕ) : Function.Injective (X.a p) :=
  LinearMap.ker_eq_bot.mp (hX.ka p)

theorem c_injective {X : DblData R} (hX : X.Good) (q : ℕ) : Function.Injective (X.c q) :=
  LinearMap.ker_eq_bot.mp (hX.kc q)

theorem ex_a {X : DblData R} (hX : X.Good) (p : ℕ) {z : X.D p 0} (hz : X.h p 0 z = 0) :
    ∃ x, X.a p x = z := by
  have hm : z ∈ LinearMap.ker (X.h p 0) := LinearMap.mem_ker.mpr hz
  rw [hX.ra p] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_h {X : DblData R} (hX : X.Good) (p q : ℕ) {z : X.D p (q + 1)} (hz : X.h p (q + 1) z = 0) :
    ∃ w, X.h p q w = z := by
  have hm : z ∈ LinearMap.ker (X.h p (q + 1)) := LinearMap.mem_ker.mpr hz
  rw [hX.rh p q] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_c {X : DblData R} (hX : X.Good) (q : ℕ) {z : X.D 0 q} (hz : X.v 0 q z = 0) :
    ∃ y, X.c q y = z := by
  have hm : z ∈ LinearMap.ker (X.v 0 q) := LinearMap.mem_ker.mpr hz
  rw [hX.rc q] at hm
  exact LinearMap.mem_range.mp hm

theorem hh {X : DblData R} (hX : X.Good) (p q : ℕ) (z : X.D p q) : X.h p (q + 1) (X.h p q z) = 0 := by
  have hm : X.h p q z ∈ LinearMap.ker (X.h p (q + 1)) := by
    rw [hX.rh p q]; exact LinearMap.mem_range_self _ z
  exact LinearMap.mem_ker.mp hm

theorem ha0 {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by
  have hm : X.a p x ∈ LinearMap.ker (X.h p 0) := by
    rw [hX.ra p]; exact LinearMap.mem_range_self _ x
  exact LinearMap.mem_ker.mp hm

theorem vc0 {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) : X.v 0 q (X.c q y) = 0 := by
  have hm : X.c q y ∈ LinearMap.ker (X.v 0 q) := by
    rw [hX.rc q]; exact LinearMap.mem_range_self _ y
  exact LinearMap.mem_ker.mp hm

end Good

def Rel : (n : ℕ) → (X : DblData R) → X.A n → X.C n → Prop
  | 0, X => fun x y => X.a 0 x = X.c 0 y
  | n + 1, X => fun x y => ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z)

theorem rel_zero {X : DblData R} {x : X.A 0} {y : X.C 0} : Rel 0 X x y ↔ X.a 0 x = X.c 0 y := Iff.rfl

theorem rel_succ {n : ℕ} {X : DblData R} {x : X.A (n + 1)} {y : X.C (n + 1)} :
    Rel (n + 1) X x y ↔ ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z) :=
  Iff.rfl

theorem Rel.zero : ∀ (n : ℕ) (X : DblData R), Rel n X 0 0
  | 0, X => rel_zero.mpr (by rw [map_zero, map_zero])
  | n + 1, X => rel_succ.mpr ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact Rel.zero n X.shift⟩

theorem Rel.add : ∀ (n : ℕ) (X : DblData R) {x₁ x₂ : X.A n} {y₁ y₂ : X.C n},
    Rel n X x₁ y₁ → Rel n X x₂ y₂ → Rel n X (x₁ + x₂) (y₁ + y₂)
  | 0, X, _, _, _, _, h₁, h₂ => rel_zero.mpr (by rw [map_add, map_add, rel_zero.mp h₁, rel_zero.mp h₂])
  | n + 1, X, _, _, _, _, h₁, h₂ => by
      obtain ⟨z₁, e₁, r₁⟩ := rel_succ.mp h₁
      obtain ⟨z₂, e₂, r₂⟩ := rel_succ.mp h₂
      refine rel_succ.mpr ⟨z₁ + z₂, by rw [map_add, map_add, e₁, e₂], ?_⟩
      rw [map_add]
      exact Rel.add n X.shift r₁ r₂

theorem Rel.smul : ∀ (n : ℕ) (X : DblData R) (r : R) {x : X.A n} {y : X.C n},
    Rel n X x y → Rel n X (r • x) (r • y)
  | 0, X, r, _, _, h₁ => rel_zero.mpr (by rw [map_smul, map_smul, rel_zero.mp h₁])
  | n + 1, X, r, _, _, h₁ => by
      obtain ⟨z, e, r₁⟩ := rel_succ.mp h₁
      refine rel_succ.mpr ⟨r • z, by rw [map_smul, map_smul, e], ?_⟩
      rw [map_smul]
      exact Rel.smul n X.shift r r₁

def relSub (n : ℕ) (X : DblData R) : Submodule R (X.A n × X.C n) where
  carrier := {p | Rel n X p.1 p.2}
  add_mem' h₁ h₂ := Rel.add n X h₁ h₂
  zero_mem' := Rel.zero n X
  smul_mem' r _ hp := Rel.smul n X r hp

theorem cocycle : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x y, Rel n X x y → X.dA n x = 0 ∧ X.dC n y = 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x y hr
    have hr' := rel_zero.mp hr
    refine ⟨hX.a_injective 1 ?_, hX.c_injective 1 ?_⟩
    · rw [hX.a_d, hr', hX.vc0, map_zero]
    · rw [hX.c_d, ← hr', hX.ha0, map_zero]
  | succ n ih =>
    intro X hX x y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    refine ⟨(ih X.shift hX.shift x (X.up n z) hr).1, hX.c_injective (n + 2) ?_⟩
    rw [hX.c_d, ← hz, hX.hh, map_zero]

theorem exA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX x hx
    have hv : X.v 0 0 (X.a 0 x) = 0 := by rw [← hX.a_d, hx, map_zero]
    obtain ⟨y, hy⟩ := hX.ex_c 0 hv
    exact ⟨y, rel_zero.mpr hy.symm⟩
  | succ n ih =>
    intro X hX x hx
    obtain ⟨w, hw⟩ := ih X.shift hX.shift x hx
    obtain ⟨z, rfl⟩ := X.up_surj n w
    have hc := (cocycle n X.shift hX.shift x (X.up n z) hw).2
    have h1 : X.h 1 n (X.v 0 n z) = 0 := by
      have := congrArg (X.shift.c (n + 1)) hc
      rw [map_zero] at this
      exact this
    have h2 : X.v 0 (n + 1) (X.h 0 n z) = 0 := by rw [X.comm_apply]; exact h1
    obtain ⟨y, hy⟩ := hX.ex_c (n + 1) h2
    exact ⟨y, rel_succ.mpr ⟨z, hy.symm, hw⟩⟩

theorem exC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, X.dC n y = 0 → ∃ x, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX y hy
    have hh0 : X.h 0 0 (X.c 0 y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨x, hx⟩ := hX.ex_a 0 hh0
    exact ⟨x, rel_zero.mpr hx⟩
  | succ n ih =>
    intro X hX y hy
    have hh0 : X.h 0 (n + 1) (X.c (n + 1) y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨z, hz⟩ := hX.ex_h 0 n hh0
    have hd : X.shift.dC n (X.up n z) = 0 := by
      apply hX.shift.c_injective (n + 1)
      rw [map_zero]
      show X.h 1 n (X.v 0 n z) = 0
      rw [← X.comm_apply, hz, hX.vc0]
    obtain ⟨x, hx⟩ := ih X.shift hX.shift (X.up n z) hd
    exact ⟨x, rel_succ.mpr ⟨z, hz, hx⟩⟩

theorem bdA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x₀ : X.A n, Rel (n + 1) X (X.dA n x₀) 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x₀
    refine rel_succ.mpr ⟨X.a 0 x₀, by rw [hX.ha0, map_zero], rel_zero.mpr ?_⟩
    exact hX.a_d 0 x₀
  | succ n ih =>
    intro X hX x₀
    refine rel_succ.mpr ⟨0, by rw [map_zero, map_zero], ?_⟩
    rw [map_zero]
    exact ih X.shift hX.shift x₀

theorem bdC (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by
  refine rel_succ.mpr ⟨X.c n y₀, (hX.c_d n y₀).symm, ?_⟩
  have hu : X.up n (X.c n y₀) = 0 := by
    apply hX.shift.c_injective n
    rw [map_zero]
    exact hX.vc0 n y₀
  rw [hu]
  exact Rel.zero n X.shift

theorem kerC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, Rel n X 0 y → y ∈ bdry X.dC n := by
  intro n
  induction n with
  | zero =>
    intro X hX y hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.c_injective 0 (by rw [← hr', map_zero]))
  | succ n ih =>
    intro X hX y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hb := ih X.shift hX.shift (X.up n z) hr
    show y ∈ LinearMap.range (X.dC n)
    rcases n with _ | m
    · have hb0 : X.up 0 z = 0 := (Submodule.mem_bot R).mp hb
      have hv : X.v 0 0 z = 0 := by
        have := congrArg (X.shift.c 0) hb0
        rw [map_zero] at this
        exact this
      obtain ⟨y₀, hy₀⟩ := hX.ex_c 0 hv
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective 1 ?_⟩
      rw [hX.c_d, hy₀, hz]
    · have hb' : X.up (m + 1) z ∈ LinearMap.range (X.shift.dC m) := hb
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hb'
      obtain ⟨z', rfl⟩ := X.up_surj m w
      have e : X.v 0 (m + 1) (X.h 0 m z') = X.v 0 (m + 1) z := by
        rw [X.comm_apply]
        exact congrArg (X.shift.c (m + 1)) hw
      obtain ⟨y₀, hy₀⟩ := hX.ex_c (m + 1) (show X.v 0 (m + 1) (z - X.h 0 m z') = 0 by rw [map_sub, e, sub_self])
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective (m + 2) ?_⟩
      rw [hX.c_d, hy₀, map_sub, hX.hh, sub_zero, hz]

theorem kerA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, Rel n X x 0 → x ∈ bdry X.dA n := by
  intro n
  induction n with
  | zero =>
    intro X hX x hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.a_injective 0 (by rw [hr', map_zero]))
  | succ n ih =>
    intro X hX x hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hz0 : X.h 0 n z = 0 := by rw [hz, map_zero]
    show x ∈ LinearMap.range (X.dA n)
    rcases n with _ | m
    · obtain ⟨x₀, hx₀⟩ := hX.ex_a 0 hz0
      have hr' := rel_zero.mp hr
      refine LinearMap.mem_range.mpr ⟨x₀, hX.a_injective 1 ?_⟩
      rw [hX.a_d, hx₀]
      exact hr'.symm
    · obtain ⟨z', hz'⟩ := hX.ex_h 0 m hz0
      have hu : X.up (m + 1) z = X.shift.dC m (X.up m z') := by
        apply hX.shift.c_injective (m + 1)
        show X.v 0 (m + 1) z = X.h 1 m (X.v 0 m z')
        rw [← hz', X.comm_apply]
      rw [hu] at hr
      have h0 := bdC m X.shift hX.shift (X.up m z')
      have hs : Rel (m + 1) X.shift x 0 := by
        have h1 : (x, X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := hr
        have h2 : ((0 : X.shift.A (m + 1)), X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := h0
        have h3 : Rel (m + 1) X.shift (x - (0 : X.A (m + 1 + 1))) (X.shift.dC m (X.up m z') - X.shift.dC m (X.up m z')) :=
          (relSub (m + 1) X.shift).sub_mem h1 h2
        rw [sub_zero, sub_self] at h3
        exact h3
      exact ih X.shift hX.shift x hs

end DblData

theorem graph_equiv {M N M' N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (dM : M →ₗ[R] M') (dN : N →ₗ[R] N') (BM : Submodule R M) (BN : Submodule R N)
    (G : Submodule R (M × N))
    (hZ : ∀ x y, (x, y) ∈ G → dM x = 0 ∧ dN y = 0)
    (hM : ∀ x, dM x = 0 → ∃ y, (x, y) ∈ G)
    (hN : ∀ y, dN y = 0 → ∃ x, (x, y) ∈ G)
    (hBM : ∀ x ∈ BM, (x, (0 : N)) ∈ G) (hBN : ∀ y ∈ BN, ((0 : M), y) ∈ G)
    (hKM : ∀ x, (x, (0 : N)) ∈ G → x ∈ BM) (hKN : ∀ y, ((0 : M), y) ∈ G → y ∈ BN) :
    Nonempty ((LinearMap.ker dM ⧸ BM.comap (LinearMap.ker dM).subtype) ≃ₗ[R]
      (LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype)) := by
  classical
  choose f hf using fun x : LinearMap.ker dM => hM x.1 (LinearMap.mem_ker.mp x.2)
  have hfz : ∀ x, f x ∈ LinearMap.ker dN := fun x => LinearMap.mem_ker.mpr (hZ _ _ (hf x)).2
  let g : LinearMap.ker dM → LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    fun x => Submodule.Quotient.mk ⟨f x, hfz x⟩
  have key : ∀ (x : LinearMap.ker dM) (y : LinearMap.ker dN), ((x : M), (y : N)) ∈ G →
      g x = Submodule.Quotient.mk y := by
    intro x y hxy
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.mem_comap]
    apply hKN
    have := G.sub_mem (hf x) hxy
    rw [Prod.mk_sub_mk, sub_self] at this
    exact this
  let F : LinearMap.ker dM →ₗ[R] LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    { toFun := g
      map_add' := fun x₁ x₂ => by
        rw [key (x₁ + x₂) (⟨f x₁, hfz x₁⟩ + ⟨f x₂, hfz x₂⟩) (G.add_mem (hf x₁) (hf x₂))]
        rfl
      map_smul' := fun r x => by
        rw [key (r • x) (r • ⟨f x, hfz x⟩) (G.smul_mem r (hf x))]
        rfl }
  have hQ : BM.comap (LinearMap.ker dM).subtype ≤ LinearMap.ker F := by
    intro x hx
    rw [LinearMap.mem_ker]
    change g x = 0
    rw [key x 0 (hBM x.1 hx)]
    rfl
  let Φ := (BM.comap (LinearMap.ker dM).subtype).liftQ F hQ
  have inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change g x = 0 at hq
    have hq' : f x ∈ BN := by
      have := (Submodule.Quotient.mk_eq_zero _).mp hq
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    apply hKM
    have := G.sub_mem (hf x) (hBN _ hq')
    rw [Prod.mk_sub_mk, sub_zero, sub_self] at this
    exact this
  have surj : Function.Surjective Φ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := hN y.1 (LinearMap.mem_ker.mp y.2)
    refine ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr (hZ _ _ hx).1⟩, ?_⟩
    exact key _ y hx
  exact ⟨LinearEquiv.ofBijective Φ ⟨inj, surj⟩⟩

namespace DblData

theorem bdryA (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (x : X.A n), x ∈ bdry X.dA n → Rel n X x 0
  | 0, x, hx => by
      have hx0 : x = 0 := (Submodule.mem_bot R).mp hx
      subst hx0
      exact Rel.zero 0 X
  | n + 1, x, hx => by
      obtain ⟨x₀, rfl⟩ := LinearMap.mem_range.mp hx
      exact bdA n X hX x₀

theorem bdryC (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (y : X.C n), y ∈ bdry X.dC n → Rel n X 0 y
  | 0, y, hy => by
      have hy0 : y = 0 := (Submodule.mem_bot R).mp hy
      subst hy0
      exact Rel.zero 0 X
  | n + 1, y, hy => by
      obtain ⟨y₀, rfl⟩ := LinearMap.mem_range.mp hy
      exact bdC n X hX y₀

theorem equiv (X : DblData R) (hX : X.Good) (n : ℕ) : Nonempty (H X.dA n ≃ₗ[R] H X.dC n) :=
  graph_equiv (X.dA n) (X.dC n) (bdry X.dA n) (bdry X.dC n) (relSub n X)
    (fun x y hr => cocycle n X hX x y hr) (fun x hx => exA n X hX x hx) (fun y hy => exC n X hX y hy)
    (fun x hx => bdryA X hX n x hx) (fun y hy => bdryC X hX n y hy)
    (fun x hr => kerA n X hX x hr) (fun y hr => kerC n X hX y hr)

end DblData

end Staircase

theorem Staircase.proof : Staircase.Statement := by
  intro R _ D _ _ v h A _ _ dA a C _ _ dC c hvh ha hc ka ra rh kc rc rv n
  exact Staircase.DblData.equiv
    { D := D, v := v, h := h, comm := hvh, A := A, dA := dA, a := a, C := C, dC := dC, c := c }
    ⟨ha, hc, ka, ra, rh, kc, rc, rv⟩ n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
