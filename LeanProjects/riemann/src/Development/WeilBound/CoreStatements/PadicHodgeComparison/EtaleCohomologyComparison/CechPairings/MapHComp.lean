import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
theorem CrystallineSemistableComparison.P.cls_surj : ∀ {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ), (∀ x : K.H n, ∃ a ha, x = K.cls a ha) ∧ (∀ (a : K.X n) ha, K.cls a ha = 0 ↔ a ∈ K.B n) ∧ (∀ (a b : K.X n) ha hb, K.cls a ha = K.cls b hb ↔ a - b ∈ K.B n) ∧ (∀ (a b : K.X n) ha hb hab, K.cls (a + b) hab = K.cls a ha + K.cls b hb) ∧ (∀ (r : R) (a : K.X n) ha hb, K.cls (r • a) hb = r • K.cls a ha) := by
  intro R _ K n
  refine ⟨fun x => ?_, fun a ha => ?_, fun a b ha hb => ?_, fun a b ha hb hab => rfl, fun r a ha hb => rfl⟩
  · obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨a, ha, rfl⟩
  · exact Submodule.Quotient.mk_eq_zero _
  · exact Submodule.Quotient.eq _

theorem CrystallineSemistableComparison.P.mapH_cls : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'} (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (hb : L.d n (φ.f n a) = 0), φ.mapH n (K.cls a ha) = L.cls (φ.f n a) hb := by
  intro R R' _ _ σ K L φ n a ha hb
  rfl

theorem CrystallineSemistableComparison.P.mapH_comp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {σ : R →+* R'} {σ' : R' →+* R''} {σ'' : R →+* R''} [RingHomCompTriple σ σ' σ''] {K : Cx.{w} R} {L : Cx.{w'} R'} {M : Cx.{w''} R''} (φ : Cx.Hom K L σ) (ψ : Cx.Hom L M σ') (n : ℕ) (x : K.H n), (φ.comp ψ : Cx.Hom K M σ'').mapH n x = ψ.mapH n (φ.mapH n x) := by
  intro R R' R'' _ _ _ σ σ' σ'' _ K L M φ ψ n x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem CrystallineSemistableComparison.P.mapH_bij : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'} (φ : Cx.Hom K L σ), (∀ n, Function.Bijective (φ.f n)) → ∀ n, Function.Bijective (φ.mapH n) := by
  intro R R' _ _ σ K L φ h n
  have hz : ∀ a : K.X n, K.d n a = 0 → L.d n (φ.f n a) = 0 := fun a ha => by rw [φ.comm, ha, map_zero]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 x
    rw [CrystallineSemistableComparison.P.mapH_cls φ n a ha (hz a ha), (CrystallineSemistableComparison.P.cls_surj L n).2.1] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj K n).2.1]
    cases n with
    | zero =>
      have : φ.f 0 a = 0 := hx
      exact (h 0).1 (this.trans (map_zero _).symm)
    | succ n =>
      obtain ⟨y, hy⟩ := hx
      obtain ⟨b, rfl⟩ := (h n).2 y
      exact ⟨b, (h (n + 1)).1 (by rw [← φ.comm, hy])⟩
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L n).1 y
    obtain ⟨a, rfl⟩ := (h n).2 b
    exact ⟨K.cls a ((h (n + 1)).1 (by rw [← φ.comm, hb, map_zero])), rfl⟩

theorem CrystallineSemistableComparison.P.mapH_htpy : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'} (φ ψ : Cx.Hom K L σ) (h : ∀ n, K.X (n + 1) → L.X n), (∀ x, K.d 0 x = 0 → φ.f 0 x = ψ.f 0 x) → (∀ n x, K.d (n + 1) x = 0 → φ.f (n + 1) x - ψ.f (n + 1) x = L.d n (h n x)) → ∀ n x, φ.mapH n x = ψ.mapH n x := by
  intro R R' _ _ σ K L φ ψ h h0 h1 n x
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 x
  rw [CrystallineSemistableComparison.P.mapH_cls φ n a ha (by rw [φ.comm, ha, map_zero]), CrystallineSemistableComparison.P.mapH_cls ψ n a ha (by rw [ψ.comm, ha, map_zero]),
    (CrystallineSemistableComparison.P.cls_surj L n).2.2.1]
  cases n with
  | zero => rw [h0 a ha, sub_self]; exact Submodule.zero_mem _
  | succ n => exact ⟨h n a, (h1 n a ha).symm⟩

theorem CrystallineSemistableComparison.P.upTo_alg : ∀ {R : Type} [CommRing R] {M : Type w} {N : Type w'} {P : Type w''} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (s s' : R), (UpTo s f → UpTo s' g → UpTo (s * s') (g ∘ₗ f)) ∧ (UpTo s f → UpTo s' (g ∘ₗ f) → UpTo (s * s') g) ∧ (UpTo s g → UpTo s' (g ∘ₗ f) → UpTo (s * s') f) ∧ (UpTo s f → UpTo (s * s') f) ∧ (UpTo (1 : R) f ↔ Function.Bijective f) := by
  intro R _ M N P _ _ _ _ _ _ f g s s'
  refine ⟨fun hf hg => ⟨fun x hx => ?_, fun z => ?_⟩, fun hf hg => ⟨fun y hy => ?_, fun z => ?_⟩,
    fun hg hf => ⟨fun x hx => ?_, fun y => ?_⟩, fun hf => ⟨fun x hx => ?_, fun y => ?_⟩, ⟨fun h => ⟨?_, fun y => ?_⟩, fun h => ⟨fun x hx => ?_, fun y => ?_⟩⟩⟩
  · rw [mul_smul]
    exact hf.1 _ (by rw [map_smul]; exact hg.1 _ hx)
  · obtain ⟨y, hy⟩ := hg.2 z
    obtain ⟨x, hx⟩ := hf.2 y
    exact ⟨x, by rw [LinearMap.comp_apply, hx, map_smul, hy, mul_smul]⟩
  · obtain ⟨x, hx⟩ := hf.2 y
    have := hg.1 x (by rw [LinearMap.comp_apply, hx, map_smul, hy, smul_zero])
    rw [mul_comm, mul_smul, ← hx, ← map_smul, this, map_zero]
  · obtain ⟨x, hx⟩ := hg.2 z
    exact ⟨s • f x, by rw [map_smul, mul_smul]; exact congrArg _ hx⟩
  · rw [mul_smul, hf.1 x (by rw [LinearMap.comp_apply, hx, map_zero]), smul_zero]
  · obtain ⟨x, hx⟩ := hf.2 (g y)
    have := hg.1 (f x - s' • y) (by rw [map_sub, map_smul, sub_eq_zero]; exact hx)
    rw [smul_sub, sub_eq_zero] at this
    exact ⟨s • x, by rw [map_smul, this, mul_smul]⟩
  · rw [mul_comm, mul_smul, hf.1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := hf.2 y
    exact ⟨s' • x, by rw [map_smul, hx, mul_comm, mul_smul]⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using h.1 x hx
  · simpa using h.2 y
  · rw [one_smul]; exact h.1 (hx.trans (map_zero f).symm)
  · simpa using h.2 y

theorem CrystallineSemistableComparison.P.lim_upTo : ∀ {R : Type} [CommRing R] {S : Sys.{w} R} {S' : Sys.{w'} R} (φ : Sys.Hom S S' (RingHom.id R)) (s : R), (∀ n, UpTo s (φ.f n)) → UpTo (s ^ 2) φ.lim := by
  intro R _ S S' φ s h
  constructor
  · intro x hx
    refine Subtype.ext (funext fun n => ?_)
    have : s • x.1 n = 0 := (h n).1 _ (congrFun (congrArg Subtype.val hx) n)
    change (s ^ 2) • x.1 n = 0
    rw [pow_two, mul_smul, this, smul_zero]
  · intro y
    choose x hx using fun n => (h n).2 (y.1 n)
    refine ⟨⟨fun n => s • x n, fun n => ?_⟩, Subtype.ext (funext fun n => ?_)⟩
    · have := (h n).1 (S.r n (x (n + 1)) - x n) (by rw [map_sub, ← φ.comm, hx, hx, map_smul, y.2 n, sub_self])
      rw [smul_sub, sub_eq_zero] at this
      rw [map_smul, this]
    · change φ.f n (s • x n) = (s ^ 2) • y.1 n
      rw [map_smul, hx, pow_two, mul_smul]

theorem CrystallineSemistableComparison.P.pow_ideal : ∀ {R : Type} [CommRing R] (I : Ideal R), (∀ N : ℕ, I ≤ Ideal.span ((fun a => a ^ N) '' (I : Set R))) → ∀ (N : ℕ) (P : R → Prop), P 0 → (∀ a b, P a → P b → P (a + b)) → (∀ r a, P a → P (r * a)) → (∀ a ∈ I, P (a ^ N)) → ∀ s ∈ I, P s := by
  intro R _ I hI N P h0 hadd hmul h s hs
  refine Submodule.span_induction (p := fun x _ => P x) ?_ h0 (fun a b _ _ => hadd a b) (fun r a _ => hmul r a) (hI N hs)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

theorem CrystallineSemistableComparison.P.pow_upTo : ∀ {R : Type} [CommRing R] (I : Ideal R), (∀ N : ℕ, I ≤ Ideal.span ((fun a => a ^ N) '' (I : Set R))) → ∀ (N : ℕ) {M : Type w} {M' : Type w'} {M'' : Type w''} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M''] [Module R M] [Module R M'] [Module R M''] (f : M →ₗ[R] M') (g : M' →ₗ[R] M''), ((∀ a ∈ I, InjUpTo (a ^ N) f) → ∀ s ∈ I, InjUpTo s f) ∧ ((∀ a ∈ I, SurjUpTo (a ^ N) f) → ∀ s ∈ I, SurjUpTo s f) ∧ ((∀ a ∈ I, UpTo (a ^ N) f) → Almost I f) ∧ ((∀ a ∈ I, ExactUpTo (a ^ N) f g) → ∀ s ∈ I, ExactUpTo s f g) := by
  intro R _ I hI N M M' M'' _ _ _ _ _ _ f g
  have h1 : (∀ a ∈ I, InjUpTo (a ^ N) f) → ∀ s ∈ I, InjUpTo s f :=
    CrystallineSemistableComparison.P.pow_ideal I hI N (fun s => InjUpTo s f) (fun x _ => zero_smul _ _)
      (fun a b ha hb x hx => by rw [add_smul, ha x hx, hb x hx, add_zero])
      (fun r a ha x hx => by rw [mul_smul, ha x hx, smul_zero])
  have h3 : ∀ y, (∀ a ∈ I, ∃ x, f x = a ^ N • y) → ∀ s ∈ I, ∃ x, f x = s • y := fun y =>
    CrystallineSemistableComparison.P.pow_ideal I hI N (fun s => ∃ x, f x = s • y) ⟨0, by simp⟩
      (fun a b ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩)
      (fun r a ⟨x, hx⟩ => ⟨r • x, by rw [map_smul, hx, mul_smul]⟩)
  have h2 : (∀ a ∈ I, SurjUpTo (a ^ N) f) → ∀ s ∈ I, SurjUpTo s f := fun h s hs y => h3 y (fun a ha => h a ha y) s hs
  exact ⟨h1, h2, fun h s hs => ⟨h1 (fun a ha => (h a ha).1) s hs, h2 (fun a ha => (h a ha).2) s hs⟩,
    fun h s hs y hy => h3 y (fun a ha => h a ha y hy) s hs⟩
