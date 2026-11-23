import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.IsSuccSubset

namespace ReciprocityTheory.Coh

open Cx Function

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem hom_H_smul {A : Cx R} (i : Hom A A) (t : R) (hi : ∀ n x, i.f n x = t • x) (n : ℕ)
    (x : A.H n) : i.H n x = t • x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    show Submodule.Quotient.mk (i.Z n z) = t • Submodule.Quotient.mk z
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hi n z.1)

end SlopeTestRemainingChoices

section Aux2

theorem tower_family {X : ℕ → Type*} (f : ∀ k, X (k + 1) → X k) (hf : ∀ k, Surjective (f k)) :
    ∀ (m : ℕ) (y : X m), ∃ z : ∀ k, X k, (∀ k, f k (z (k + 1)) = z k) ∧ z m = y := by
  intro m
  induction m generalizing X with
  | zero =>
    intro y
    let z : ∀ k, X k := fun k => Nat.rec (motive := fun k => X k) y
      (fun k zk => Classical.choose (hf k zk)) k
    exact ⟨z, fun k => Classical.choose_spec (hf k (z k)), rfl⟩
  | succ m ih =>
    intro y
    obtain ⟨z', hz', hm⟩ := ih (X := fun k => X (k + 1)) (fun k => f (k + 1)) (fun k => hf (k + 1)) y
    refine ⟨fun k => match k with | 0 => f 0 (z' 0) | k + 1 => z' k, fun k => ?_, hm⟩
    cases k with
    | zero => rfl
    | succ k => exact hz' k

variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

noncomputable def descend (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) : P →ₗ[R] Q :=
  (LinearMap.ker p).liftQ g h ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap

theorem descend_apply (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) (x : M) : descend p hp g h (p x) = g x := by
  have : (p.quotKerEquivOfSurjective hp).symm (p x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [descend, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, this,
    Submodule.liftQ_apply]

theorem isFiniteLength_of_exact {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Exact f g)
    (hM : IsFiniteLength R M) (hP : IsFiniteLength R P) : IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at *
  obtain ⟨_, _⟩ := hM
  obtain ⟨_, _⟩ := hP
  have e : LinearMap.range f = LinearMap.ker g := h.linearMap_ker_eq.symm
  exact ⟨isNoetherian_of_range_eq_ker f g e, isArtinian_of_range_eq_ker f g e⟩

theorem mem_smul_top_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ J) hx ?_ ?_
    · intro a ha m _ i; exact J.mul_mem_right _ ha
    · intro a b ha hb i; exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [show x = ∑ i, x i • Pi.single i (1 : R) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

theorem isPrecomplete_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  have key : ∀ k (x : ι → R), x ∈ I ^ k • (⊤ : Submodule R (ι → R)) ↔
      ∀ i, x i ∈ I ^ k • (⊤ : Submodule R R) := by
    intro k x
    rw [mem_smul_top_pi]
    simp only [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ l : R, ∀ n, f n i ≡ l [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => f n i) fun {m n} hmn => ?_
    have := (hf hmn)
    rw [SModEq.sub_mem] at this ⊢
    exact (key m _).1 this i
  choose l hl using hc
  refine ⟨l, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hl i n)

end Aux2

section Tower

variable {R : Type u} [CommRing R] (t : R) {A : ℕ → Cx R} {τ : ∀ m, Hom (A (m + 1)) (A m)}
  {L : Cx R} {π : ∀ m, Hom L (A m)}

theorem tower_pi_surj (hT : IsTowerLim A τ L π) (m n : ℕ) : Surjective ((π m).f n) := by
  intro y
  obtain ⟨z, hz, hm⟩ := tower_family (X := fun k => (A k).X n) (fun k => (τ k).f n)
    (fun k => hT.surj k n) m y
  obtain ⟨x, hx⟩ := hT.lift n z hz
  exact ⟨x, (hx m).trans hm⟩

def smulHom (L : Cx R) (t : R) : Hom L L := ⟨fun _ => t • LinearMap.id, fun n x => by simp⟩

theorem smulHom_f (L : Cx R) (t : R) (n : ℕ) (x : L.X n) : (smulHom L t).f n x = t • x := rfl

theorem pow_torsionfree (htf : ∀ n (x : L.X n), t • x = 0 → x = 0) (n : ℕ) :
    ∀ k (x : L.X n), t ^ k • x = 0 → x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; exact htf n x (ih _ (by rw [smul_smul, ← pow_succ]; exact hx))

variable (hT : IsTowerLim A τ L π) (htf : ∀ n (x : L.X n), t • x = 0 → x = 0)
  (hk : ∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y)

include hT htf hk

theorem ses_smul : SES (smulHom L t) (π 0) where
  inj n := (injective_iff_map_eq_zero _).2 fun x hx => htf n x hx
  exact n y := by
    rw [hk 0 n y]
    simp only [zero_add, pow_one, Set.mem_range, smulHom_f]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  surj n := tower_pi_surj hT 0 n

theorem ker_le_ker_smul (m n : ℕ) : LinearMap.ker ((π 0).f n) ≤
    LinearMap.ker ((π (m + 1)).f n ∘ₗ (t ^ (m + 1) • LinearMap.id)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (hk 0 n x).1 hx
  show (π (m + 1)).f n (t ^ (m + 1) • t ^ (0 + 1) • y) = 0
  rw [hk, smul_smul, ← pow_add]
  exact ⟨y, by ring_nf⟩

noncomputable def jf (m n : ℕ) : (A 0).X n →ₗ[R] (A (m + 1)).X n :=
  descend ((π 0).f n) (tower_pi_surj hT 0 n) _ (ker_le_ker_smul t hT htf hk m n)

theorem jf_apply (m n : ℕ) (x : L.X n) :
    jf t hT htf hk m n ((π 0).f n x) = (π (m + 1)).f n (t ^ (m + 1) • x) :=
  descend_apply _ _ _ _ x

noncomputable def jHom (m : ℕ) : Hom (A 0) (A (m + 1)) where
  f n := jf t hT htf hk m n
  comm n a := by
    obtain ⟨x, rfl⟩ := tower_pi_surj hT 0 n a
    rw [← (π 0).comm, jf_apply, jf_apply, ← (π (m + 1)).comm]
    simp only [map_smul]

theorem ses_j (m : ℕ) : SES (jHom t hT htf hk m) (τ m) where
  inj n := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ := tower_pi_surj hT 0 n a
    change jf t hT htf hk m n _ = 0 at ha
    rw [jf_apply, hk] at ha
    obtain ⟨y, hy⟩ := ha
    have : x = t • y := by
      refine sub_eq_zero.1 (pow_torsionfree t htf n (m + 1) _ ?_)
      rw [smul_sub, hy, smul_smul, ← pow_succ, sub_self]
    rw [hk 0 n]
    exact ⟨y, by simpa using this⟩
  exact n z := by
    obtain ⟨x, rfl⟩ := tower_pi_surj hT (m + 1) n z
    rw [hT.compat, hk]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(π 0).f n y, jf_apply t hT htf hk m n y⟩
    · rintro ⟨a, ha⟩
      obtain ⟨y, rfl⟩ := tower_pi_surj hT 0 n a
      change jf t hT htf hk m n _ = _ at ha
      rw [jf_apply] at ha
      have h2 : (π (m + 1)).f n (x - t ^ (m + 1) • y) = 0 := by rw [map_sub, ha, sub_self]
      obtain ⟨w, hw⟩ := (hk (m + 1) n _).1 h2
      refine ⟨y + t • w, ?_⟩
      rw [smul_add, smul_smul, ← pow_succ, ← hw]
      abel
  surj n := hT.surj m n

end Tower

theorem modT_holds : ModTStatement.{u} := by
  intro R _ A C i p t δ hi hs hc n
  obtain ⟨⟨δ0, hc0, hl⟩, huniq⟩ := lES_holds R A A C i p hs
  obtain rfl : δ = δ0 := huniq δ δ0 hc hc0
  refine ⟨fun x => ?_, hl.exC n, fun x => ?_⟩
  · rw [hl.exB n x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
  · rw [LinearMap.mem_range, ← hom_H_smul i t hi (n + 1) x]
    exact (hl.exA n x).symm

theorem finGen_holds : FinGenStatement.{u} := by
  intro R _ t _ A τ L π hT htf hk h0
  have hfl : ∀ m n, IsFiniteLength R ((A m).H n) := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      intro n
      obtain ⟨⟨δ, _, hl⟩, _⟩ := lES_holds R (A 0) (A (m + 1)) (A m) (jHom t hT htf hk m) (τ m)
        (ses_j t hT htf hk m)
      exact isFiniteLength_of_exact _ _ (hl.exB n) (h0 n) (ih n)
  intro n
  refine ⟨?_, fun m => hfl m n⟩
  have hkill : ∀ m (z : (A m).H n), t ^ (m + 1) • z = 0 := by
    intro m z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [← Submodule.Quotient.mk_smul]
      have : t ^ (m + 1) • w = 0 := by
        apply Subtype.ext
        obtain ⟨l, hl⟩ := tower_pi_surj hT m n w.1
        show t ^ (m + 1) • w.1 = 0
        rw [← hl, ← map_smul, hk]
        exact ⟨l, rfl⟩
      rw [this, Submodule.Quotient.mk_zero]
  have hmem : ∀ k (x : L.H n), x ∈ Ideal.span {t} ^ k • (⊤ : Submodule R (L.H n)) ↔
      ∃ y, x = t ^ k • y := by
    intro k x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [eq_comm]
  have : IsHausdorff (Ideal.span {t}) (L.H n) := by
    refine ⟨fun x hx => ?_⟩
    refine (tower_holds R A τ L π hT n).2 (fun k _ m => ?_) x (fun m => ?_)
    · exact (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl m k)).2
    · have h1 := SModEq.sub_mem.1 (hx (m + 1))
      rw [sub_zero] at h1
      obtain ⟨y, rfl⟩ := (hmem (m + 1) x).1 h1
      rw [map_smul, hkill]
  obtain ⟨⟨δ, hc, _⟩, _⟩ := lES_holds R L L (A 0) (smulHom L t) (π 0) (ses_smul t hT htf hk)
  have hmt := (modT_holds R L (A 0) (smulHom L t) (π 0) t δ (fun _ _ => rfl)
    (ses_smul t hT htf hk) hc n).1
  have hmem1 : ∀ x : L.H n, x ∈ Ideal.span {t} • (⊤ : Submodule R (L.H n)) ↔ ∃ y, x = t • y := by
    intro x
    simpa using hmem 1 x
  have hle : Ideal.span {t} • (⊤ : Submodule R (L.H n)) ≤ LinearMap.ker ((π 0).H n) := by
    intro x hx
    exact (hmt x).2 ((hmem1 x).1 hx)
  let q := (Ideal.span {t} • (⊤ : Submodule R (L.H n))).liftQ ((π 0).H n) hle
  have hq : Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero, hmem1]
      exact (hmt x).1 hz
  have : IsNoetherian R ((A 0).H n) := (isFiniteLength_iff_isNoetherian_isArtinian.1 (h0 n)).1
  have : Module.Finite R (L.H n ⧸ Ideal.span {t} • (⊤ : Submodule R (L.H n))) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R)
    (M := L.H n ⧸ Ideal.span {t} • (⊤ : Submodule R (L.H n)))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {t}) (Fin r → R) := isPrecomplete_pi _
  have hsurj : Surjective ((Ideal.span {t} • (⊤ : Submodule R (L.H n))).mkQ ∘ₗ
      Fintype.linearCombination R s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end ReciprocityTheory.Coh
