import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift
open Filter Topology

noncomputable section

namespace GlobalTheory.TateTop

section Dual

variable {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]

omit [Finite M] in
theorem dual_inj : ∃ F : Module.Dual (ZMod n) M → AddChar M ℂ, Function.Injective F :=
  ⟨fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom, fun φ ψ h => by
    ext m
    exact ZMod.injective_stdAddChar (DFunLike.congr_fun h m)⟩

theorem finite_dual : Finite (Module.Dual (ZMod n) M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := M →ₗ[ZMod n] ZMod n))

theorem card_dual_le : Nat.card (Module.Dual (ZMod n) M) ≤ Nat.card M := by
  classical
  obtain ⟨F, hF⟩ := dual_inj (n := n) (M := M)
  have := Fintype.ofFinite M
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_fintype_card (α := AddChar M ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card] at h

theorem exists_dual_ne_zero {x : M} (hx : x ≠ 0) : ∃ φ : Module.Dual (ZMod n) M, φ x ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := x)).2 hx
  have hζ := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  have h : ∀ m : M, ∃ k : ZMod n, ZMod.stdAddChar k = ψ m := fun m => by
    have h1 : ψ m ^ n = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul,
        AddChar.map_zero_eq_one]
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨((k : ℤ) : ZMod n), ?_⟩
    rw [ZMod.stdAddChar_coe, ← hk, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  choose f hf using h
  let F : M →+ ZMod n := AddMonoidHom.mk' f fun a b => ZMod.injective_stdAddChar (by
    rw [AddChar.map_add_eq_mul, hf, hf, hf, AddChar.map_add_eq_mul])
  refine ⟨F.toZModLinearMap n, fun h0 => hψ ?_⟩
  have h1 : f x = 0 := h0
  rw [← hf, h1, AddChar.map_zero_eq_one]

theorem eval_bijective : Function.Bijective (Module.Dual.eval (ZMod n) M) := by
  have := finite_dual (n := n) (M := M)
  have := finite_dual (n := n) (M := Module.Dual (ZMod n) M)
  have hinj : Function.Injective (Module.Dual.eval (ZMod n) M) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_dual_ne_zero (n := n) h
    exact hφ (DFunLike.congr_fun hx φ)
  exact hinj.bijective_of_nat_card_le (card_dual_le.trans card_dual_le)

end Dual

section Level

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

def IsCoc (χ : G →* ℤ_[l]ˣ) {A : Type} [AddCommGroup A] [Module ℤ_[l] A] (z : G × G → A) : Prop :=
  IsLocallyConstant z ∧
    ∀ g h k, (χ g : ℤ_[l]) • z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0

def cob (χ : G →* ℤ_[l]ˣ) {A : Type} [AddCommGroup A] [Module ℤ_[l] A] (b : G → A) (p : G × G) : A :=
  (χ p.1 : ℤ_[l]) • b p.2 - b (p.1 * p.2) + b p.1

def Gen (χ : G →* ℤ_[l]ˣ) (r : ℕ) (c : G × G → ℤ_[l]) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M], (∀ m : M, (l : ℤ_[l]) ^ r • m = 0) →
    (∀ x : M, IsCoc χ fun p => c p • x) ∧
    (∀ z : G × G → M, IsCoc χ z →
      ∃ (x : M) (b : G → M), IsLocallyConstant b ∧ ∀ p, z p = c p • x + cob χ b p) ∧
    (∀ (x : M) (b : G → M), IsLocallyConstant b → (∀ p, c p • x = cob χ b p) → x = 0)

variable {χ : G →* ℤ_[l]ˣ} {M : Type} [AddCommGroup M] [Module ℤ_[l] M] {r : ℕ}

theorem dvd_iff_toZModPow (a : ℤ_[l]) : (l : ℤ_[l]) ^ r ∣ a ↔ PadicInt.toZModPow r a = 0 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]

theorem smul_congr (hM : ∀ m : M, (l : ℤ_[l]) ^ r • m = 0) {a a' : ℤ_[l]}
    (h : (l : ℤ_[l]) ^ r ∣ a - a') (m : M) : a • m = a' • m := by
  obtain ⟨w, hw⟩ := h
  rw [← sub_eq_zero, ← sub_smul, hw, mul_smul, hM]

theorem smul_eq_val (hM : ∀ m : M, (l : ℤ_[l]) ^ r • m = 0) (a : ℤ_[l]) (m : M) :
    a • m = (PadicInt.toZModPow r a).val • m := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
  apply smul_congr hM
  rw [dvd_iff_toZModPow, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem lc_smul (hM : ∀ m : M, (l : ℤ_[l]) ^ r • m = 0) {X : Type} [TopologicalSpace X]
    {f : X → ℤ_[l]} (hf : Continuous f) {b : X → M} (hb : IsLocallyConstant b) :
    IsLocallyConstant fun x => f x • b x := by
  simp only [smul_eq_val hM]
  have h1 : IsLocallyConstant fun x => PadicInt.toZModPow r (f x) :=
    (IsLocallyConstant.iff_continuous _).2 ((continuous_toZModPow r).comp hf)
  exact h1.comp₂ hb fun a m => a.val • m

theorem isCoc_cob [ContinuousMul G] (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (hM : ∀ m : M, (l : ℤ_[l]) ^ r • m = 0) {b : G → M} (hb : IsLocallyConstant b) :
    IsCoc χ (cob χ b) := by
  refine ⟨((lc_smul hM (hχ.comp continuous_fst) (hb.comp_continuous continuous_snd)).sub
    (hb.comp_continuous continuous_mul)).add (hb.comp_continuous continuous_fst), fun g h k => ?_⟩
  simp only [cob, map_mul, Units.val_mul, mul_assoc]
  module

theorem IsCoc.add {z z' : G × G → M} (h : IsCoc χ z) (h' : IsCoc χ z') :
    IsCoc χ fun p => z p + z' p :=
  ⟨h.1.add h'.1, fun g k m => by
    have e := h.2 g k m
    have e' := h'.2 g k m
    linear_combination (norm := module) e + e'⟩

theorem Gen.congr {c c' : G × G → ℤ_[l]} (h : Gen χ r c) (hc : ∀ p, (l : ℤ_[l]) ^ r ∣ c' p - c p) :
    Gen χ r c' := by
  intro M _ _ _ hM
  have e : ∀ p (x : M), c' p • x = c p • x := fun p x => smul_congr hM (hc p) x
  simp only [e]
  exact h M hM

theorem Gen.mono {c : G × G → ℤ_[l]} (h : Gen χ (r + 1) c) : Gen χ r c :=
  fun M _ _ _ hM => h M fun m => by rw [pow_succ, mul_smul, hM]

theorem Gen.twist [ContinuousMul G] (hχ : Continuous fun g => (χ g : ℤ_[l])) {c : G × G → ℤ_[l]}
    (h : Gen χ r c) {u : ℤ_[l]} (hu : IsUnit u) {β : G → ℤ_[l]} (hβ : IsLocallyConstant β) :
    Gen χ r fun p => c p * u + cob χ β p := by
  intro M _ _ _ hM
  obtain ⟨h1, h2, h3⟩ := h M hM
  obtain ⟨u, rfl⟩ := hu
  have e : ∀ p (x : M), (c p * u + cob χ β p) • x =
      c p • ((u : ℤ_[l]) • x) + cob χ (fun g => β g • x) p := fun p x => by
    simp only [cob, smul_eq_mul]
    module
  have hl : ∀ x : M, IsLocallyConstant fun g => β g • x := fun x => hβ.comp fun a => a • x
  have es : ∀ (b b' : G → M) p, cob χ (b - b') p = cob χ b p - cob χ b' p := fun b b' p => by
    simp only [cob, Pi.sub_apply]
    module
  simp only [e]
  refine ⟨fun x => (h1 _).add (isCoc_cob hχ hM (hl x)), fun z hz => ?_, fun x b hb hx => ?_⟩
  · obtain ⟨x, b, hb, hz⟩ := h2 z hz
    refine ⟨((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x, b - fun g => β g • (((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x),
      hb.sub (hl _), fun p => ?_⟩
    rw [es, hz, smul_smul (u : ℤ_[l]), Units.mul_inv, one_smul]
    abel
  · have h4 := h3 ((u : ℤ_[l]) • x) (b - fun g => β g • x) (hb.sub (hl _)) fun p => by
      rw [es, ← hx p]; abel
    exact (u.isUnit.smul_eq_zero).1 h4

theorem Gen.step [ContinuousMul G] (hχ : Continuous fun g => (χ g : ℤ_[l])) {c c' : G × G → ℤ_[l]}
    (h : Gen χ r c) (h' : Gen χ (r + 1) c') :
    ∃ c'' : G × G → ℤ_[l], Gen χ (r + 1) c'' ∧ ∀ p, (l : ℤ_[l]) ^ r ∣ c'' p - c p := by
  have hl : l.Prime := Fact.out
  rcases r with _ | r
  · exact ⟨c', h', fun p => by simp⟩
  have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set π : ℤ_[l] →+* ZMod (l ^ (r + 1)) := PadicInt.toZModPow (r + 1) with hπ
  let : Module ℤ_[l] (ZMod (l ^ (r + 1))) := Module.compHom _ π
  have hs : ∀ (a : ℤ_[l]) (m : ZMod (l ^ (r + 1))), a • m = π a * m := fun _ _ => rfl
  have h0 : π ((l : ℤ_[l]) ^ (r + 1)) = 0 := (dvd_iff_toZModPow _).1 dvd_rfl
  have hM : ∀ m : ZMod (l ^ (r + 1)), (l : ℤ_[l]) ^ (r + 1) • m = 0 := fun m => by
    rw [hs, h0, zero_mul]
  obtain ⟨h1, -, h3⟩ := h _ hM
  obtain ⟨x, b, hb, hx⟩ := (h'.mono _ hM).2.1 _ (h1 1)
  simp only [cob, hs, mul_one] at hx
  have hu : IsUnit ((x.val : ℕ) : ℤ_[l]) := by
    by_contra hu
    obtain ⟨w, hw⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hu)
    have hw' := congrArg π hw
    rw [map_natCast, ZMod.natCast_zmod_val, map_mul] at hw'
    have h4 := h3 (π ((l : ℤ_[l]) ^ r)) (fun g => π ((l : ℤ_[l]) ^ r) * b g)
      (hb.comp fun a => π ((l : ℤ_[l]) ^ r) * a) fun p => by
        simp only [cob, hs]
        rw [pow_succ (l : ℤ_[l]), map_mul] at h0
        rw [hx p, hw']
        linear_combination π (c' p) * π w * h0
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff,
      Nat.pow_dvd_pow_iff_le_right hl.one_lt] at h4
    omega
  refine ⟨_, h'.twist hχ hu (β := fun g => (((b g).val : ℕ) : ℤ_[l]))
    (hb.comp fun a => ((a.val : ℕ) : ℤ_[l])), fun p => ?_⟩
  rw [dvd_iff_toZModPow, ← hπ]
  simp only [cob, smul_eq_mul, map_sub, map_add, map_mul π, map_natCast, ZMod.natCast_zmod_val, hx p,
    sub_self]

theorem exists_lim (a : ℕ → ℤ_[l]) (h : ∀ n, (l : ℤ_[l]) ^ n ∣ a (n + 1) - a n) :
    ∃ L : ℤ_[l], ∀ n, (l : ℤ_[l]) ^ n ∣ L - a n := by
  have hv : ∀ n m (x : ℤ_[l]), n ≤ m →
      (l : ℤ_[l]) ^ n ∣ x - (((PadicInt.toZModPow m x).val : ℕ) : ℤ_[l]) := fun n m x hnm => by
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    refine (pow_dvd_pow _ hnm).trans ?_
    rw [dvd_iff_toZModPow, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  let f : ℕ → ℤ := fun n => ((PadicInt.toZModPow n (a n)).val : ℕ)
  have hf : ∀ n, (l : ℤ) ^ n ∣ f (n + 1) - f n := fun n => by
    rw [← PadicInt.pow_p_dvd_int_iff]
    have := ((h n).sub (hv n (n + 1) (a (n + 1)) (by omega))).add (hv n n (a n) le_rfl)
    convert this using 1
    simp only [f]
    push_cast
    ring
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub f l hf), fun n => ?_⟩
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [dvd_iff_toZModPow, map_sub, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub f l hf n]
  simp [f]

theorem exists_gen_all [ContinuousMul G] (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (h : ∀ r, ∃ c, Gen χ (r + 1) c) : ∃ c, ∀ r, Gen χ r c := by
  have st : ∀ r (c : {c // Gen χ r c}), ∃ c' : {c // Gen χ (r + 1) c},
      ∀ p, (l : ℤ_[l]) ^ r ∣ c'.1 p - c.1 p := fun r c => by
    obtain ⟨c', hc'⟩ := h r
    obtain ⟨c'', h1, h2⟩ := c.2.step hχ hc'
    exact ⟨⟨c'', h1⟩, h2⟩
  choose T hT using st
  obtain ⟨c₀, hc₀⟩ := h 0
  let C : ∀ r, {c // Gen χ r c} := fun r => Nat.rec ⟨c₀, hc₀.mono⟩ T r
  have hC : ∀ p n, (l : ℤ_[l]) ^ n ∣ (C (n + 1)).1 p - (C n).1 p := fun p n => hT n (C n) p
  choose L hL using fun p => exists_lim (fun n => (C n).1 p) (hC p)
  exact ⟨L, fun r => (C r).2.congr fun p => hL p r⟩

theorem IsCoc.map {N : Type} [AddCommGroup N] [Module ℤ_[l] N] (f : M →ₗ[ℤ_[l]] N) {z : G × G → M}
    (h : IsCoc χ z) : IsCoc χ fun p => f (z p) :=
  ⟨h.1.comp f, fun g k m => by
    have e := congrArg f (h.2 g k m)
    simpa only [map_sub, map_add, map_smul, map_zero] using e⟩

theorem finite_span (htor : ∀ a : M, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) {S : Set M} (hS : S.Finite) :
    ∃ r : ℕ, Finite (Submodule.span ℤ_[l] S) ∧
      ∀ m : Submodule.span ℤ_[l] S, (l : ℤ_[l]) ^ r • m = 0 := by
  choose e he using htor
  obtain ⟨r, hr⟩ := (hS.image e).bddAbove
  have hM : ∀ m : Submodule.span ℤ_[l] S, (l : ℤ_[l]) ^ r • m = 0 := fun m => by
    have h1 : Submodule.span ℤ_[l] S ≤ Submodule.torsionBy ℤ_[l] M ((l : ℤ_[l]) ^ r) :=
      Submodule.span_le.2 fun a ha => by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (hr ⟨a, ha, rfl⟩)
        rw [SetLike.mem_coe, Submodule.mem_torsionBy_iff, hk, pow_add, mul_smul, he, smul_zero]
    exact Subtype.ext (h1 m.2)
  refine ⟨r, ?_, hM⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have := Module.Finite.span_of_finite ℤ_[l] hS
  let : Module (ZMod (l ^ r)) (Submodule.span ℤ_[l] S) := AddCommGroup.zmodModule fun m => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow, hM]
  let f : Submodule.span ℤ_[l] S →ₛₗ[(PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r))]
      Submodule.span ℤ_[l] S :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        rw [id, id, smul_eq_val hM, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_zmod_val] }
  have : Module.Finite (ZMod (l ^ r)) (Submodule.span ℤ_[l] S) :=
    Module.Finite.of_surjective f Function.surjective_id
  exact @Module.finite_of_finite (ZMod (l ^ r)) _ _ _ _ _ this

theorem h2_equiv_of_torsion_character [CompactSpace G] {c : G × G → ℤ_[l]} (h : ∀ r, Gen χ r c)
    (htor : ∀ a : M, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) {O : Type} [CommRing O] [Module O M]
    [SMulCommClass ℤ_[l] O M] (π : Representation O G M) (hπ : ∀ g x, π g x = (χ g : ℤ_[l]) • x) :
    Nonempty (ReciprocityTheory.Def.H2 π ⊤ ≃ₗ[O] M) := by
  have hZ : ∀ z : G × G → M, z ∈ ReciprocityTheory.Def.Z2 π ⊤ ↔ IsCoc χ z := fun z => by
    refine ⟨fun hz => ⟨hz.1.1, fun g k m => ?_⟩, fun hz => ⟨⟨hz.1, fun _ => trivial⟩, ?_⟩⟩
    · rw [← hπ]
      exact congrFun hz.2 (g, k, m)
    · funext x
      have := hz.2 x.1 x.2.1 x.2.2
      rw [← hπ] at this
      exact this
  have hd : ∀ b : G → M, ReciprocityTheory.Def.d1 π b = cob χ b := fun b => by
    funext p
    rw [cob, ← hπ]
    rfl
  have h1 : ∀ x : M, IsCoc χ fun p => c p • x := fun x => by
    obtain ⟨r, hf, hM⟩ := finite_span htor (Set.finite_singleton x)
    exact ((h r _ hM).1 ⟨x, Submodule.subset_span rfl⟩).map (Submodule.subtype _)
  let Φ : M →ₗ[O] ReciprocityTheory.Def.Z2 π ⊤ :=
    { toFun := fun x => ⟨fun p => c p • x, (hZ _).2 (h1 x)⟩
      map_add' := fun x y => Subtype.ext (funext fun p => smul_add _ _ _)
      map_smul' := fun a x => Subtype.ext (funext fun p => smul_comm _ _ _) }
  refine ⟨(LinearEquiv.ofBijective ((Submodule.mkQ _).comp Φ) ⟨?_, fun y => ?_⟩).symm⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, hb, hbx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
    rw [hd] at hbx
    obtain ⟨r, hf, hM⟩ := finite_span htor (hb.1.range_finite.insert x)
    have h3 := (h r _ hM).2.2 ⟨x, Submodule.subset_span (Set.mem_insert _ _)⟩
      (fun g => ⟨b g, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨g, rfl⟩)⟩)
      (IsLocallyConstant.desc _ Subtype.val hb.1 Subtype.val_injective)
      fun p => Subtype.ext (congrFun hbx p).symm
    exact congrArg Subtype.val h3
  · obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hz' := (hZ z).1 hz
    obtain ⟨r, hf, hM⟩ := finite_span htor hz'.1.range_finite
    obtain ⟨x, b, hb, hx⟩ := (h r _ hM).2.1 (fun p => ⟨z p, Submodule.subset_span ⟨p, rfl⟩⟩)
      ⟨IsLocallyConstant.desc _ Subtype.val hz'.1 Subtype.val_injective,
        fun g k m => Subtype.ext (hz'.2 g k m)⟩
    refine ⟨x, Eq.symm ((Submodule.Quotient.eq _).2 ?_)⟩
    refine Submodule.mem_map.2 ⟨fun g => (b g : M), ⟨hb.comp _, fun _ => trivial⟩, ?_⟩
    rw [hd]
    funext p
    exact (sub_eq_of_eq_add' (congrArg Subtype.val (hx p))).symm

omit [TopologicalSpace G] in
theorem cob_comp {G' : Type} [Group G'] (φ : G' →* G) (b : G → M) (p : G' × G') :
    cob (χ.comp φ) (b ∘ φ) p = cob χ b (φ p.1, φ p.2) := by
  simp [cob]

theorem IsCoc.comp {G' : Type} [Group G'] [TopologicalSpace G'] (φ : G' →* G) (hφ : Continuous φ)
    {z : G × G → M} (h : IsCoc χ z) : IsCoc (χ.comp φ) fun p => z (φ p.1, φ p.2) :=
  ⟨h.1.comp_continuous (hφ.prodMap hφ), fun g k m => by
    simpa only [map_mul, MonoidHom.comp_apply] using h.2 (φ g) (φ k) (φ m)⟩

theorem Gen.transport {G' : Type} [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) {c : G × G → ℤ_[l]} (h : Gen χ r c) :
    Gen (χ.comp φ.toMonoidHom) r fun p => c (φ p.1, φ p.2) := by
  intro M _ _ _ hM
  obtain ⟨h1, h2, h3⟩ := h M hM
  have e : (χ.comp φ.toMonoidHom).comp φ.symm.toMonoidHom = χ := by ext g; simp
  refine ⟨fun x => (h1 x).comp φ.toMonoidHom hφ, fun z hz => ?_, fun x b hb hx => ?_⟩
  · have hz' := hz.comp φ.symm.toMonoidHom hφ'
    rw [e] at hz'
    obtain ⟨x, b, hb, hx⟩ := h2 _ hz'
    refine ⟨x, b ∘ φ.toMonoidHom, hb.comp_continuous hφ, fun p => ?_⟩
    rw [cob_comp]
    simpa using hx (φ p.1, φ p.2)
  · refine h3 x (b ∘ φ.symm.toMonoidHom) (hb.comp_continuous hφ') fun p => ?_
    rw [← e, cob_comp]
    simpa using hx (φ.symm p.1, φ.symm p.2)

def scalRep {R : Type} [CommRing R] (ψ : G →* Rˣ) (M : Type) [AddCommGroup M] [Module R M] :
    Representation R G M where
  toFun g := (ψ g : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g k := by ext; simp [smul_smul, mul_comm]

open ReciprocityTheory.Gal in

theorem exists_gen (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (h1 : Nonempty (H2 ((charRep (redChar χ r)).comp (MonoidHom.id G)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)))
    (h2 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) G M), ContAction rho →
      Function.Bijective (cup20 (redChar χ r) rho (MonoidHom.id G))) :
    ∃ c, Gen χ r c := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e⟩ := h1
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e.symm 1)
  refine ⟨fun p => (((c.1 p).val : ℕ) : ℤ_[l]), fun M _ _ _ hM => ?_⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule fun m => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow, hM]⟩
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hs : ∀ (a : ℤ_[l]) (m : M), a • m = PadicInt.toZModPow r a • m := fun a m => by
    rw [smul_eq_val hM, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_zmod_val]
  let rho : Representation (ZMod (l ^ r)) G M := scalRep (redChar χ r) M
  have hrho : ∀ (g : G) (m : M), (χ g : ℤ_[l]) • m = rho g m := fun g m => hs _ _
  have hcont : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ r) × M => q.1 • q.2)).comp
      ((((continuous_toZModPow r).comp hχ).comp continuous_fst).prodMk continuous_snd)
  have hbij := h2 M rho hcont
  have hZ : ∀ z : G × G → M, IsCoc χ z ↔ z ∈ Z2 (rho.comp (MonoidHom.id G)) := fun z => by
    simp only [IsCoc, IsLocallyConstant.iff_continuous, hrho]
    rfl
  have hd : ∀ (b : G → M) p, cob χ b p = d1 (rho.comp (MonoidHom.id G)) b p := fun b p => by
    rw [cob, hrho]
    rfl
  have hT : ∀ x : M, (fun p => c.1 p • x) ∈ Z2 (rho.comp (MonoidHom.id G)) := fun x => by
    refine ⟨(continuous_of_discreteTopology (f := fun a : ZMod (l ^ r) => a • x)).comp c.2.1,
      fun g k m => ?_⟩
    have h3 := congrArg (fun a : ZMod (l ^ r) => a • x) (c.2.2 g k m)
    simp only [sub_smul, add_smul, zero_smul] at h3
    rw [← h3]
    congr 3
    exact (mul_smul _ _ _).symm
  have hcup : ∀ (x : M) (φ : H0 ((twDual (redChar χ r) rho).comp (MonoidHom.id G))),
      e (cup20 (redChar χ r) rho (MonoidHom.id G) (Submodule.Quotient.mk ⟨_, hT x⟩) φ) = φ.1 x :=
    fun x φ => by
      have h3 : cup20 (redChar χ r) rho (MonoidHom.id G) (Submodule.Quotient.mk ⟨_, hT x⟩) φ =
          Submodule.Quotient.mk (φ.1 x • c) := by
        refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
        change φ.1 (c.1 p • x) = φ.1 x * c.1 p
        rw [mul_comm]
        exact LinearMap.map_smul (show M →ₗ[ZMod (l ^ r)] ZMod (l ^ r) from φ.1) _ _
      rw [h3, Submodule.Quotient.mk_smul, hc, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul,
        mul_one]
  let inv : Module.Dual (ZMod (l ^ r)) M →ₗ[ZMod (l ^ r)]
      H0 ((twDual (redChar χ r) rho).comp (MonoidHom.id G)) :=
    { toFun := fun φ => ⟨TDual.mk φ, fun g => TDual.ext fun m => by
        change (redChar χ r g : ZMod (l ^ r)) * φ ((redChar χ r g⁻¹ : ZMod (l ^ r)) • m) = φ m
        rw [map_smul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
          Units.val_one, one_mul]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simp only [hZ, hd, hs (_ : ℕ), map_natCast, ZMod.natCast_zmod_val, IsLocallyConstant.iff_continuous]
  refine ⟨hT, fun z hz => ?_, fun x b hb hx => ?_⟩
  · obtain ⟨x, hx⟩ := (eval_bijective (n := l ^ r) (M := M)).2 (e.toLinearMap ∘ₗ
      (cup20 (redChar χ r) rho (MonoidHom.id G) (Submodule.Quotient.mk ⟨z, hz⟩)) ∘ₗ inv)
    have h3 : (Submodule.Quotient.mk ⟨z, hz⟩ : H2 (rho.comp (MonoidHom.id G))) =
        Submodule.Quotient.mk ⟨_, hT x⟩ := by
      apply hbij.1
      ext φ
      apply e.injective
      rw [hcup]
      exact (DFunLike.congr_fun hx φ.1).symm
    obtain ⟨b, hb, hbz⟩ := (Submodule.Quotient.eq _).1 h3
    exact ⟨x, b, hb, fun p => eq_add_of_sub_eq' (congrFun hbz p).symm⟩
  · have h3 : (Submodule.Quotient.mk ⟨_, hT x⟩ : H2 (rho.comp (MonoidHom.id G))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨b, hb, funext fun p => (hx p).symm⟩
    by_contra hx0
    obtain ⟨φ, hφ⟩ := exists_dual_ne_zero (n := l ^ r) hx0
    have h4 := hcup x (inv φ)
    rw [h3, map_zero, LinearMap.zero_apply, map_zero] at h4
    exact hφ h4.symm

end Level

section Coeff

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  {O : Type} [CommRing O] [Algebra O LL]

theorem exists_pow_smul_mem (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∀ x : LL, ∃ n : ℕ, ∀ a : ℤ_[l], algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n * a) * x ∈
      Set.range (algebraMap O LL) := by
  obtain ⟨-, -, h1, h2, h3⟩ := hO
  intro x
  have hc : Continuous fun a : ℚ_[l] => a • x := continuous_id.smul continuous_const
  have h4 := hc.continuousAt (x := 0) (h3.mem_nhds ⟨0, by simp⟩)
  rw [Filter.mem_map, Metric.mem_nhds_iff] at h4
  obtain ⟨ε, hε, h5⟩ := h4
  obtain ⟨n, hn⟩ := exists_zpow_neg_lt (l := l) hε
  refine ⟨n, fun a => ?_⟩
  rw [← Algebra.smul_def]
  apply h5
  rw [mem_ball_zero_iff, norm_mul, Padic.norm_p_pow]
  exact (mul_le_of_le_one_right (by positivity) a.2).trans_lt hn

theorem exists_ringHom (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ ι : ℤ_[l] →+* O, ∀ a, algebraMap O LL (ι a) = algebraMap ℚ_[l] LL a := by
  obtain ⟨n, hn⟩ := exists_pow_smul_mem hO 1
  obtain ⟨⟨_, _, _⟩, -⟩ := hO
  have hinj := IsFractionRing.injective O LL
  have h : ∀ a : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL a := fun a => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
    obtain ⟨o, ho⟩ := hn w
    refine ⟨o + (a.appr n : O), ?_⟩
    have h1 : (a : ℚ_[l]) = (l : ℚ_[l]) ^ n * w + (a.appr n : ℚ_[l]) := by
      rw [eq_add_of_sub_eq hw]
      push_cast
      rw [← eq_add_of_sub_eq hw]
    rw [map_add, ho, mul_one, h1, map_add, map_natCast, map_natCast]
  choose f hf using h
  exact ⟨{ toFun := f
           map_one' := hinj (by simp [hf])
           map_mul' := fun a b => hinj (by simp [hf])
           map_zero' := hinj (by simp [hf])
           map_add' := fun a b => hinj (by simp [hf]) }, hf⟩

end Coeff

theorem tate_h2_of_local_duality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (D : Formalism.BasicNotions.D7) : adm3 D := by
  intro l _ K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = ((D.loc l).χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← (D.loc l).PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL (((D.loc l).PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
