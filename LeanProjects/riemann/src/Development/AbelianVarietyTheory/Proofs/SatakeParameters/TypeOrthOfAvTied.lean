import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.GaloisLevelStructure.Checks

namespace GlobalTheory.TypeOrthogonality

open ComplexConjugate

theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hherm : ∀ x ∈ S, ∀ y ∈ S, B x y = starRingEnd ℂ (B y x))
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < (B x x).re) (u : V) :
    ∃ p ∈ S, ∀ w ∈ S, B (u - p) w = 0 := by
  letI core : InnerProductSpace.Core ℂ S :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (B y x) = B x y
        rw [hherm x x.2 y y.2]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (B x x)
        by_cases hx : (x : V) = 0
        · simp [hx]
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show B ((x : V) + y) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • (x : V)) y = starRingEnd ℂ r * B x y
        simp
      definite := fun x hx => by
        by_contra h
        have h' : (x : V) ≠ 0 := fun e => h (Subtype.ext e)
        have := hpos x x.2 h'
        change B x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup S := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore core.toCore
  let ℓ : S →ₗ[ℂ] ℂ := (B u).comp S.subtype
  let ℓc : StrongDual ℂ S := LinearMap.toContinuousLinearMap ℓ
  let p : S := (InnerProductSpace.toDual ℂ S).symm ℓc
  refine ⟨p, p.2, fun w hw => ?_⟩
  have key : inner ℂ p (⟨w, hw⟩ : S) = ℓc ⟨w, hw⟩ := InnerProductSpace.toDual_symm_apply
  change B p w = B u w at key
  rw [map_sub, LinearMap.sub_apply, key, sub_self]

end GlobalTheory.TypeOrthogonality

namespace GlobalTheory.TypeOrthogonality

open ComplexConjugate NumberField Formalism.L2 ReciprocityTheory.Aut Formalism.AUTREP

section grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_conj {M : ℕ} {κ l : GAf L n} (hκ : κ ∈ Umax L n) (hl : NG.Cong L n M l) :
    NG.Cong L n M (κ⁻¹ * l * κ) := by
  refine ⟨(Umax L n).mul_mem ((Umax L n).mul_mem ((Umax L n).inv_mem hκ) hl.1) hκ, fun i j => ?_⟩
  choose Y hY e using hl.2
  have hi : κ⁻¹ ∈ Umax L n := (Umax L n).inv_mem hκ
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hK
  set Ki : Matrix (Fin n) (Fin n) (AL L) := (((κ⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hKi
  have hKK : Ki * K = 1 := by
    rw [hKi, hK, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hA : ((l.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 + (M : AL L) • Matrix.of Y := by
    ext a b
    have := e a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hprod : (((κ⁻¹ * l * κ).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = Ki * (1 + (M : AL L) • Matrix.of Y) * K := by
    rw [← hA]; simp [hKi, hK, Subgroup.coe_mul, Units.val_mul]
  refine ⟨(Ki * Matrix.of Y * K) i j, ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ (hκ b j)
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hi i a) (hY a b)
  · rw [hprod]
    have : Ki * (1 + (M : AL L) • Matrix.of Y) * K - 1 = (M : AL L) • (Ki * Matrix.of Y * K) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hKK, add_sub_cancel_left, Matrix.mul_smul, Matrix.smul_mul]
    have h2 := congrFun (congrFun this i) j
    simpa [Matrix.sub_apply, Matrix.smul_apply] using h2

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

theorem rt_rt_inv (h : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h⁻¹ f) = f := by
  rw [rt_rt, mul_inv_cancel]; funext g; simp [NG.rt]

end grp

end GlobalTheory.TypeOrthogonality

namespace GlobalTheory.TypeOrthogonality

open ComplexConjugate NumberField Formalism.L2 ReciprocityTheory.Aut Formalism.AUTREP

section core

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W]

def fixN (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (N : ℕ) : Submodule ℂ (GAf L n → W) where
  carrier := {f | ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun hf hf' κ hκ g => by simp [hf κ hκ g, hf' κ hκ g]
  smul_mem' := fun c f hf κ hκ g => by simp [hf κ hκ g]

theorem rt_of_mem_fixN {N : ℕ} {f : GAf L n → W} (hf : f ∈ fixN L n W N) {κ : GAf L n}
    (hκ : NG.Cong L n N κ) : NG.rt L n κ f = f := by
  funext g; exact hf κ hκ g

theorem fixN_mono {N M : ℕ} {f : GAf L n → W} (hf : f ∈ fixN L n W N) : f ∈ fixN L n W (N * M) :=
  fun κ hκ g => hf κ (NG.Cong.of_mul_left L n hκ) g

theorem fixN_mono' {N M : ℕ} {f : GAf L n → W} (hf : f ∈ fixN L n W M) : f ∈ fixN L n W (N * M) :=
  fun κ hκ g => hf κ (NG.Cong.of_mul_right L n hκ) g

theorem rt_mem_fixN {N : ℕ} {f : GAf L n → W} (hf : f ∈ fixN L n W N) {κ : GAf L n}
    (hκ : κ ∈ Umax L n) : NG.rt L n κ f ∈ fixN L n W N := by
  intro l hl g
  have := hf _ (cong_conj hκ hl) (g * κ)
  show f (g * l * κ) = f (g * κ)
  rw [← this]; congr 1; group

variable (ρ : Representation ℂ (GQ L n) W) (B : (GAf L n → W) →ₗ⋆[ℂ] (GAf L n → W) →ₗ[ℂ] ℂ)

def Good : Prop := ∀ f ∈ NG.AFall L n ρ, ∀ f' ∈ NG.AFall L n ρ, B f f' = starRingEnd ℂ (B f' f) ∧
  (f ≠ 0 → 0 < (B f f).re) ∧ ∀ h, B (NG.rt L n h f) (NG.rt L n h f') = B f f'

variable {ρ B}

theorem proj_unique (hB : Good ρ B) {S : Submodule ℂ (GAf L n → W)} (hS : S ≤ NG.AFall L n ρ)
    {u p q : GAf L n → W} (hp : p ∈ S) (hq : q ∈ S) (hpu : ∀ w ∈ S, B (u - p) w = 0)
    (hqu : ∀ w ∈ S, B (u - q) w = 0) : p = q := by
  by_contra hne
  have hm : q - p ∈ S := S.sub_mem hq hp
  have h1 := (hB _ (hS hm) _ (hS hm)).2.1 (sub_ne_zero.2 (Ne.symm hne))
  have : B (q - p) (q - p) = B (u - p) (q - p) - B (u - q) (q - p) := by
    rw [← LinearMap.sub_apply, ← map_sub]; congr 2; abel
  rw [this, hpu _ hm, hqu _ hm, sub_zero] at h1
  simp at h1

theorem proj_level (hB : Good ρ B) (hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}))
    {U : Submodule ℂ (GAf L n → W)} (hU : NG.IsSubrep ρ U) {N : ℕ} (hN : 0 < N) (u : GAf L n → W) :
    ∃ p ∈ U ⊓ fixN L n W N, ∀ w ∈ U ⊓ fixN L n W N, B (u - p) w = 0 := by
  have hle : U ⊓ fixN L n W N ≤ Submodule.span ℂ
      {f | f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g} :=
    fun f hf => Submodule.subset_span ⟨hU.le hf.1, hf.2⟩
  haveI := hfin N hN
  haveI : FiniteDimensional ℂ ↥(U ⊓ fixN L n W N) := Submodule.finiteDimensional_of_le hle
  exact exists_proj B (U ⊓ fixN L n W N) (fun x (hx : x ∈ U ⊓ fixN L n W N) y (hy : y ∈ U ⊓ fixN L n W N) => (hB x (hU.le hx.1) y (hU.le hy.1)).1)
    (fun x (hx : x ∈ U ⊓ fixN L n W N) h => (hB x (hU.le hx.1) x (hU.le hx.1)).2.1 h) u

end core

end GlobalTheory.TypeOrthogonality

namespace GlobalTheory.TypeOrthogonality

open ComplexConjugate NumberField Formalism.L2 ReciprocityTheory.Aut Formalism.AUTREP

section core2

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GQ L n) W} {B : (GAf L n → W) →ₗ⋆[ℂ] (GAf L n → W) →ₗ[ℂ] ℂ}

theorem inv_mem_cong {N : ℕ} {κ : GAf L n} (hκ : NG.Cong L n N κ) : κ⁻¹ ∈ Umax L n :=
  (Umax L n).inv_mem hκ.1

theorem proj_all (hB : Good ρ B) (hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}))
    {U : Submodule ℂ (GAf L n → W)} (hU : NG.IsSubrep ρ U) (u : GAf L n → W) (hu : u ∈ NG.AFall L n ρ) :
    ∃ p ∈ U, ∀ w ∈ U, B (u - p) w = 0 := by
  obtain ⟨N, hN, huN⟩ := hu.2
  have huN' : u ∈ fixN L n W N := huN
  obtain ⟨p, hp, hpu⟩ := proj_level hB hfin hU hN u
  refine ⟨p, hp.1, fun w hw => ?_⟩
  obtain ⟨M, hM, hwM⟩ := (hU.le hw).2
  have hwM' : w ∈ fixN L n W M := hwM
  have hK : 0 < N * M := Nat.mul_pos hN hM
  obtain ⟨q, hq, hqu⟩ := proj_level hB hfin hU hK u
  have hSK : U ⊓ fixN L n W (N * M) ≤ NG.AFall L n ρ := fun x hx => hU.le hx.1

  have hqN : q ∈ fixN L n W N := by
    intro κ hκ g
    have hrq : NG.rt L n κ q ∈ U ⊓ fixN L n W (N * M) := ⟨hU.stable κ q hq.1, rt_mem_fixN hq.2 hκ.1⟩
    have key : ∀ w' ∈ U ⊓ fixN L n W (N * M), B (u - NG.rt L n κ q) w' = 0 := by
      intro w' hw'
      have hw'' : NG.rt L n κ⁻¹ w' ∈ U ⊓ fixN L n W (N * M) :=
        ⟨hU.stable _ w' hw'.1, rt_mem_fixN hw'.2 (inv_mem_cong hκ)⟩
      have e1 : u - NG.rt L n κ q = NG.rt L n κ (u - q) := by
        rw [map_sub, rt_of_mem_fixN huN' hκ]
      have huq : u - q ∈ NG.AFall L n ρ := (NG.AFall L n ρ).sub_mem hu (hU.le hq.1)
      rw [e1, ← rt_rt_inv κ w', (hB _ huq _ (hSK hw'')).2.2 κ]
      exact hqu _ hw''
    have := proj_unique hB hSK hrq hq key hqu
    exact congrFun this g
  have hSN : U ⊓ fixN L n W N ≤ NG.AFall L n ρ := fun x hx => hU.le hx.1
  have hqp : q = p := proj_unique hB hSN (show q ∈ U ⊓ fixN L n W N from ⟨hq.1, hqN⟩) hp
    (fun w' hw' => hqu w' ⟨hw'.1, fixN_mono hw'.2⟩) hpu
  rw [← hqp]
  exact hqu w ⟨hw, fixN_mono' hwM'⟩

end core2

end GlobalTheory.TypeOrthogonality

namespace GlobalTheory.TypeOrthogonality

open ComplexConjugate NumberField Formalism.L2 ReciprocityTheory.Aut Formalism.AUTREP

section schur

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GQ L n) W} {B : (GAf L n → W) →ₗ⋆[ℂ] (GAf L n → W) →ₗ[ℂ] ℂ}

theorem orth_of_not_iso (hB : Good ρ B) (hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}))
    {U U' : Submodule ℂ (GAf L n → W)} (hU : NG.IsIrrRep ρ U) (hU' : NG.IsIrrRep ρ U')
    (hne : ¬ NG.IsoRep U U') : ∀ u ∈ U, ∀ w ∈ U', B u w = 0 := by
  classical

  let Z : Submodule ℂ (GAf L n → W) :=
    { carrier := {u | u ∈ U ∧ ∀ w ∈ U', B u w = 0}
      zero_mem' := ⟨U.zero_mem, fun w _ => by simp⟩
      add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, fun w hw => by simp [ha.2 w hw, hb.2 w hw]⟩
      smul_mem' := fun c u hu => ⟨U.smul_mem c hu.1, fun w hw => by simp [hu.2 w hw]⟩ }
  have hZ : NG.IsSubrep ρ Z := by
    refine ⟨fun u hu => hU.1.le hu.1, fun h u hu => ⟨hU.1.stable h u hu.1, fun w hw => ?_⟩⟩
    rw [← rt_rt_inv h w, (hB _ (hU.1.le hu.1) _ (hU'.1.le (hU'.1.stable _ w hw))).2.2 h]
    exact hu.2 _ (hU'.1.stable _ w hw)
  rcases hU.2.2 Z hZ (fun u hu => hu.1) with h0 | hall
  swap
  · intro u hu w hw
    have : u ∈ Z := hall ▸ hu
    exact this.2 w hw
  exfalso
  apply hne
  have hex : ∀ u : U, ∃ p, p ∈ U' ∧ ∀ w ∈ U', B ((u : GAf L n → W) - p) w = 0 := fun u => by
    obtain ⟨p, hp, h⟩ := proj_all hB hfin hU'.1 u (hU.1.le u.2)
    exact ⟨p, hp, h⟩
  have uniq : ∀ (u : GAf L n → W) (p q : GAf L n → W), p ∈ U' → q ∈ U' → (∀ w ∈ U', B (u - p) w = 0) →
      (∀ w ∈ U', B (u - q) w = 0) → p = q := fun u p q hp hq h1 h2 => proj_unique hB hU'.1.le hp hq h1 h2
  let φ : U →ₗ[ℂ] U' :=
    { toFun := fun u => ⟨Classical.choose (hex u), (Classical.choose_spec (hex u)).1⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        refine uniq ((a : GAf L n → W) + b) _ _ (Classical.choose_spec (hex (a + b))).1
          (U'.add_mem (Classical.choose_spec (hex a)).1 (Classical.choose_spec (hex b)).1)
          ?_ ?_
        · simpa using (Classical.choose_spec (hex (a + b))).2
        · intro w hw
          have e : (a : GAf L n → W) + b - (Classical.choose (hex a) + Classical.choose (hex b)) =
            ((a : GAf L n → W) - Classical.choose (hex a)) + (b - Classical.choose (hex b)) := by abel
          rw [e, map_add, LinearMap.add_apply, (Classical.choose_spec (hex a)).2 w hw,
            (Classical.choose_spec (hex b)).2 w hw, add_zero]
      map_smul' := fun c a => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        refine uniq (c • (a : GAf L n → W)) _ _ (Classical.choose_spec (hex (c • a))).1
          (U'.smul_mem c (Classical.choose_spec (hex a)).1) ?_ ?_
        · simpa using (Classical.choose_spec (hex (c • a))).2
        · intro w hw
          rw [← smul_sub, map_smulₛₗ, LinearMap.smul_apply, (Classical.choose_spec (hex a)).2 w hw, smul_zero] }
  have hφ : ∀ u : U, ∀ w ∈ U', B ((u : GAf L n → W) - (φ u : GAf L n → W)) w = 0 :=
    fun u => (Classical.choose_spec (hex u)).2
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h1 := hφ u
    rw [hu] at h1
    have hz : (u : GAf L n → W) ∈ Z := ⟨u.2, fun w hw => by simpa using h1 w hw⟩
    rw [h0] at hz
    simp only [Submodule.mem_bot] at hz ⊢
    exact Subtype.ext hz
  have heq : ∀ (h : GAf L n) (f f' : U), (f' : GAf L n → W) = NG.rt L n h (f : GAf L n → W) →
      ((φ f' : U') : GAf L n → W) = NG.rt L n h ((φ f : U') : GAf L n → W) := by
    intro h f f' e
    refine uniq (f' : GAf L n → W) _ _ (φ f').2 (hU'.1.stable h _ (φ f).2) (hφ f') fun w hw => ?_
    have hm : (f : GAf L n → W) - (φ f : GAf L n → W) ∈ NG.AFall L n ρ :=
      (NG.AFall L n ρ).sub_mem (hU.1.le f.2) (hU'.1.le (φ f).2)
    rw [e, ← map_sub, ← rt_rt_inv h w, (hB _ hm _ (hU'.1.le (hU'.1.stable _ w hw))).2.2 h]
    exact hφ f _ (hU'.1.stable _ w hw)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    let R : Submodule ℂ (GAf L n → W) := (LinearMap.range φ).map U'.subtype
    have hR : NG.IsSubrep ρ R := by
      refine ⟨fun x hx => ?_, fun h x hx => ?_⟩
      · obtain ⟨y, -, rfl⟩ := hx
        exact hU'.1.le y.2
      · obtain ⟨y, ⟨f, rfl⟩, rfl⟩ := hx
        refine ⟨φ ⟨NG.rt L n h f, hU.1.stable h _ f.2⟩, ⟨_, rfl⟩, ?_⟩
        exact heq h f _ rfl
    have hRle : R ≤ U' := fun x hx => by
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    rcases hU'.2.2 R hR hRle with hb | ht
    · exfalso
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff U).1 hU.2.1
      have : ((φ ⟨x, hx⟩ : U') : GAf L n → W) ∈ R := ⟨_, ⟨_, rfl⟩, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      have h2 : φ ⟨x, hx⟩ = 0 := Subtype.ext this
      rw [← map_zero φ] at h2
      exact hx0 (congrArg Subtype.val (hinj h2))
    · rw [eq_top_iff]
      rintro y -
      have : (y : GAf L n → W) ∈ R := by rw [ht]; exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      have hzy' : z = y := Subtype.ext hzy
      subst hzy'
      exact hz
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun h f f' e => heq h f f' e⟩

end schur

end GlobalTheory.TypeOrthogonality

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.ThetaExh

theorem typeOrth_of_avTied : ∀ (D : D7) (M : Formalism.L2.MtFam D) (V : Formalism.L2.AVTied D M) (i : D.nd.Loc) (B : (Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ⋆[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] ℂ), (∀ f ∈ Formalism.L2.NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ, ∀ f' ∈ Formalism.L2.NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ, B f f' = starRingEnd ℂ (B f' f) ∧ (f ≠ 0 → 0 < (B f f).re) ∧ ∀ h, B (Formalism.L2.NG.rt D.host.E D.R.nV h f) (Formalism.L2.NG.rt D.host.E D.R.nV h f') = B f f') → (∀ x y, inner ℂ x y = B ((M.loc i).real x) ((M.loc i).real y)) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ Formalism.L2.NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E D.R.nV N κ → ∀ g, f (g * κ) = f g})) → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  intro D M V i B hB hinner hfin P P' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  rw [hinner]
  rw [V.typeV, Submodule.mem_comap] at hx hy
  have hgood : GlobalTheory.TypeOrthogonality.Good (M.loc i).wt.ρ B := hB

  have hni : ∀ U U', Formalism.L2.NG.IsIrrRep (M.loc i).wt.ρ U → Formalism.L2.NG.IsoRep (V.S i P) U →
      Formalism.L2.NG.IsIrrRep (M.loc i).wt.ρ U' → Formalism.L2.NG.IsoRep (V.S i P') U' → ¬ Formalism.L2.NG.IsoRep U U' := by
    intro U U' _ h1 _ h2 h3
    exact hne (V.inj i P P' ((h1.trans h3).trans (h2.symm (V.irr i P').1.stable)))
  have step : ∀ U, Formalism.L2.NG.IsIrrRep (M.loc i).wt.ρ U → Formalism.L2.NG.IsoRep (V.S i P) U → ∀ a ∈ U,
      ∀ b ∈ Formalism.L2.NG.isoTyp (M.loc i).wt.ρ (V.S i P'), B a b = 0 := by
    intro U hU h1 a ha b hb
    have hle : Formalism.L2.NG.isoTyp (M.loc i).wt.ρ (V.S i P') ≤ LinearMap.ker (B a) := by
      refine sSup_le fun U' hU' => ?_
      intro c hc
      exact GlobalTheory.TypeOrthogonality.orth_of_not_iso hgood hfin hU hU'.1 (hni U U' hU h1 hU'.1 hU'.2) a ha c hc
    exact hle hb
  have hle : Formalism.L2.NG.isoTyp (M.loc i).wt.ρ (V.S i P) ≤ LinearMap.ker (B.flip ((M.loc i).real y)) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    exact step U hU.1 hU.2 a ha _ hy
  exact hle hx

end GlobalTheory.ThetaExh
