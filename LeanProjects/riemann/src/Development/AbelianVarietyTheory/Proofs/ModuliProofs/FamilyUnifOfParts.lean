import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def InGenus (D : Datum H) (l : Level H) (σ : KA l →+* ℂ) (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) : Prop :=
  D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
    (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
    (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
    σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M'

def Unif {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧
    (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧
    (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))

theorem isPeriod_transport {D' D'' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (gam : D'.La ≃ₗ[𝓞 E] D''.La)
    (hgam : ∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsPeriod D'' ty (P.comp gam.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have hr : (P.comp gam.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨gam.symm a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨gam a, by simp⟩
  refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
  · simpa using h1 a (gam.symm x) i
  · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
  · have := hgam (gam.symm x) (gam.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [this, ← h7]; rfl

theorem level_pos (l : Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem exists_inGenus (D : Datum H) (l : Level H) (σ : KA l →+* ℂ)
    (hs : ∀ (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 →
      ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν) : ∃ t, InGenus D l σ D t := by
  have hprim : IsPrimitiveRoot (σ (baseKA l).ζ) l.A := (baseKA l).ζ_prim.map_of_injective σ.injective
  obtain ⟨i, -, hi, hζ⟩ := (Complex.isPrimitiveRoot_iff _ _ l.A_pos.ne').mp hprim
  obtain ⟨s, c, hc⟩ := hs { l with A := 1, A_pos := one_pos } l.A (-(i : ℤ)) l.A_pos
    (Nat.isCoprime_iff_coprime.mpr hi).neg_left (by simp)
  refine ⟨s.f l.M', rfl, rfl, s.f, s.ν, fun n m hn hm a => ?_, fun n hn => ?_, s.mult, ?_, rfl⟩
  · obtain ⟨b, hb⟩ := s.tower n m hn hm a
    exact ⟨b, by rw [← hb]; abel⟩
  · obtain ⟨g, hg⟩ := s.inv n hn
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      obtain ⟨b, hb⟩ := (hg a).1
      exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul]; abel⟩
    · rintro ⟨e, rfl⟩
      exact ⟨s.f n e, map_nsmul _ _ _⟩
    · obtain ⟨b, hb⟩ := (hg a').2
      exact ⟨g a', -b, by rw [smul_neg, ← hb]; abel⟩
  · have hA : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.A_pos.ne'
    have h1 : (s.ν l.A : ℂ) = -(i : ℂ) + l.A * c := by
      have : s.ν l.A = -(i : ℤ) + l.A * c := by linarith
      rw [this]; push_cast; ring
    rw [← hζ, h1, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨c, by field_simp; ring⟩

theorem triv_iff {D D' : Datum H} (l : Level H) (t : D.La →ₗ[𝓞 E] D'.La)
    (ht : ∀ b, ∃ a e, b = t a + l.M' • e) (gam : D'.La ≃ₗ[𝓞 E] D'.La) (I : Ideal (𝓞 E)) (n : ℕ) (hn : n ∣ l.M') :
    (∀ a ∈ I • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t a + n • x) ↔
      ∀ a ∈ I • (⊤ : Submodule (𝓞 E) D'.La), ∃ x, gam a = a + n • x := by
  obtain ⟨k, hk⟩ := hn
  constructor
  · intro h b hb
    refine Submodule.smul_induction_on hb (fun c hc b' _ => ?_) ?_
    · obtain ⟨a, e, rfl⟩ := ht b'
      obtain ⟨x, hx⟩ := h (c • a) (Submodule.smul_mem_smul hc trivial)
      refine ⟨x + k • (gam (c • e) - c • e), ?_⟩
      rw [smul_add, ← t.map_smul, map_add, hx, smul_comm c, map_nsmul, smul_add, ← mul_smul, hk, smul_sub]
      abel
    · rintro x y ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u + v, by rw [map_add, hu, hv, smul_add]; abel⟩
  · intro h a ha
    refine h _ (Submodule.smul_induction_on ha (fun c hc a' _ => ?_) fun x y hx hy => ?_)
    · rw [t.map_smul]; exact Submodule.smul_mem_smul hc trivial
    · rw [map_add]; exact add_mem hx hy

theorem triv_iff_top {D D' : Datum H} (l : Level H) (t : D.La →ₗ[𝓞 E] D'.La)
    (ht : ∀ b, ∃ a e, b = t a + l.M' • e) (gam : D'.La ≃ₗ[𝓞 E] D'.La) (n : ℕ) (hn : n ∣ l.M') :
    (∀ a, ∃ x, gam (t a) = t a + n • x) ↔ ∀ a, ∃ x, gam a = a + n • x := by
  simpa using triv_iff l t ht gam ⊤ n hn

theorem quasiCompact_str {D : Datum H} {l : Level H} (Xo : Moduli D l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hi, h⟩ := Xo.qproj
  have := isProper_str (KA l) N
  rw [← h]
  infer_instance

def cls {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (y : Sp ℂ ⟶ Xo.X) : Set (Σ D' : Datum H, D.La →ₗ[𝓞 E] D'.La) :=
  {x | InGenus D l σ x.1 x.2 ∧ ∃ P e, Unif Xo σ ty x.1 x.2 P y e}

section Fixed

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (perObj : ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), InGenus D l σ D' t →
    IsPeriod D' ty P → ∃ y e, Unif Xo σ ty D' t P y e)
  (upUniq : ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ))
    (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) e e', Unif Xo σ ty D' t P y e → Unif Xo σ ty D'' t' P' y' e' →
    (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧
      (∀ a, ∃ x, gam (t a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)))

include upUniq in

theorem point_eq {D' : Datum H} {t : D.La →ₗ[𝓞 E] D'.La} {P : D'.La →+ (Fin g → ℂ)} {y y' : Sp ℂ ⟶ Xo.X} {e e'}
    (h : Unif Xo σ ty D' t P y e) (h' : Unif Xo σ ty D' t P y' e') : y = y' :=
  (upUniq _ _ _ _ _ _ _ _ _ _ h h').mpr ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
    fun _ _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩, fun _ => rfl⟩

include perObj upUniq in
theorem cls_subset {y y' : Sp ℂ ⟶ Xo.X} {x} (hx : x ∈ cls Xo σ ty y) (hx' : x ∈ cls Xo σ ty y') :
    cls Xo σ ty y ⊆ cls Xo σ ty y' := by
  rintro x' ⟨hg', P', e', hu'⟩
  obtain ⟨-, P, e, hu⟩ := hx
  obtain ⟨-, P₂, e₂, hu₂⟩ := hx'
  obtain ⟨gam, h, h1, h2, h3, -⟩ := (upUniq _ _ _ _ _ _ _ _ _ _ hu hu').mp rfl
  obtain ⟨y'', e'', hu''⟩ := perObj _ _ _ hg' (isPeriod_transport gam h1 hu₂.2.1)
  have : y' = y'' := (upUniq _ _ _ _ _ _ _ _ _ _ hu₂ hu'').mpr
    ⟨gam, LinearEquiv.refl _ _, h1, h2, h3, fun a => by simp⟩
  subst this
  exact ⟨hg', _, _, hu''⟩

include perObj upUniq in

theorem cls_eq {y y' : Sp ℂ ⟶ Xo.X} {x} (hx : x ∈ cls Xo σ ty y) (hx' : x ∈ cls Xo σ ty y') :
    cls Xo σ ty y = cls Xo σ ty y' :=
  (cls_subset perObj upUniq hx hx').antisymm (cls_subset perObj upUniq hx' hx)

end Fixed

end GlobalTheory.UnifParts

namespace GlobalTheory

open UnifParts

theorem familyUnif_of_parts : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
    : Datum H) (g : ℕ) (ty : Fin g → (E →+*
    ℂ)), IsTypeFn H D.p D.q ty → ∃ P, IsPeriod D ty P) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶
    Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧
    ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left)
    ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a)))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ
    : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin
    g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z +
    w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a)))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ
    : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t'
    : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y'
    : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶
    Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧
    Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod
    D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P'
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞
    E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam
    b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t
    a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a))) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ
    : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f
    : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) /
    l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧
    IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
    IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left)) → (∀ (k : Type) [Field
    k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶
    X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d →
    ℂ) → (Sp ℂ ⟶
    X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y
    b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g →
    ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k
    1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ
    Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1
    bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (N : ℕ) (ν
    : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧ (l.A
    : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞
    E) D.La)) ∧ ∀ a, D.ModN l.A (g.f l.A a - a)) → N1c := by
  intro perExist ptUnif perObj upUniq locLift holU compFin thetaFam simMult E _ _ _ H D l Xo σ g ty h1 h2 h3
  replace ptUnif : ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ x, x ∈ cls Xo σ ty y := fun y hy => by
    obtain ⟨D', t, P, e, hg, hu⟩ := ptUnif E H D l Xo σ g ty h1 h2 h3 y hy
    exact ⟨⟨D', t⟩, hg, P, e, hu⟩
  replace perObj : ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), InGenus D l σ D' t →
      IsPeriod D' ty P → ∃ y e, Unif Xo σ ty D' t P y e := perObj E H D l Xo σ g ty h1 h2 h3
  replace upUniq := upUniq E H D l Xo σ g ty h1 h2 h3
  replace locLift := locLift E H D l Xo σ g ty h1 h2 h3
  replace holU := holU E H D l Xo σ g ty h1 h2 h3
  replace thetaFam := thetaFam E H D l Xo σ g ty h1 h2 h3
  have hfin : (cls Xo σ ty '' {x | x ≫ Xo.s = spMap σ}).Finite := by
    refine compFin (KA l) σ Xo.X Xo.s D.dim _ (cls Xo σ ty) Xo.smooth (quasiCompact_str Xo)
      fun B y hB hy hh b₀ hb₀ => ?_
    obtain ⟨x, hg, P₀, e₀, hu⟩ := ptUnif _ (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb', -, -, -, -, hub⟩ := locLift x.1 x.2 _ B y b₀ P₀ e₀ hB hb₀ hy hh hu
    filter_upwards [hB'.mem_nhds hb'] with b hb
    exact cls_eq perObj upUniq (x := x) ⟨hg, _, _, hub b hb⟩ ⟨hg, _, _, hu⟩
  have hne : (cls Xo σ ty '' {x | x ≫ Xo.s = spMap σ}).Nonempty := by
    obtain ⟨t, ht⟩ := exists_inGenus D l σ fun l' N ν a b c =>
      (simMult E H D l' N ν a b c).imp fun _ h => h.1
    obtain ⟨P, hP⟩ := perExist E H D g ty h3
    obtain ⟨y, e, hu⟩ := perObj D t P ht hP
    exact ⟨_, y, hu.1, rfl⟩
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin _ (h := hfin.to_subtype)
  have hn : 0 < n := Fin.pos (φ ⟨_, hne.some_mem⟩)
  have hY : ∀ i, ∃ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ ∧ cls Xo σ ty y = φ.symm i := fun i => (φ.symm i).2
  choose Y hYσ hY using hY
  choose x hx using fun i => ptUnif _ (hYσ i)
  have hue : ∀ i (P : (x i).1.La →+ (Fin g → ℂ)), ∃ (y : Sp ℂ ⟶ Xo.X)
      (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)),
      IsPeriod (x i).1 ty P → Unif Xo σ ty (x i).1 (x i).2 P y e := fun i P => by
    by_cases hP : IsPeriod (x i).1 ty P
    · obtain ⟨y, e, h⟩ := perObj _ _ P (hx i).1 hP
      exact ⟨y, e, fun _ => h⟩
    · exact ⟨Y i, fun _ => 1, fun h => absurd h hP⟩
  choose u ex hu using hue
  have hcls : ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i, x i ∈ cls Xo σ ty y := fun y hy => by
    refine ⟨φ ⟨_, y, hy, rfl⟩, ?_⟩
    have := hx (φ ⟨_, y, hy, rfl⟩)
    rwa [hY, Equiv.symm_apply_apply] at this
  have hts : ∀ i, (∀ a, (∃ b, (x i).2 a = l.M' • b) ↔ ∃ b, a = l.M' • b) ∧
      ∀ b, ∃ a e, b = (x i).2 a + l.M' • e := fun i => by
    obtain ⟨-, -, f, ν, -, hf, -, -, ht⟩ := (hx i).1
    rw [ht]
    exact hf _ (level_pos l)
  have hhol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((x i).1.La →+ (Fin g → ℂ))), IsOpen B →
      IsHolPeriods (x i).1 ty B P → IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left) :=
    fun i m B P hB hP => holU _ _ m B P (fun b => u i (P b)) (fun b => ex i (P b)) (hx i).1 hB hP
      fun b hb => hu i _ (hP.1 b hb)
  refine ⟨{ n := n
            n_pos := hn
            Di := fun i => (x i).1
            sig := fun i => ⟨(hx i).1.1, (hx i).1.2.1⟩
            t := fun i => (x i).2
            t_inj := fun i => (hts i).1
            t_surj := fun i => (hts i).2
            u := u
            ex := ex
            over_σ := fun i P hP => (hu i P hP).1
            ex_add := fun i P hP => (hu i P hP).2.2.1.1
            ex_onto := fun i P hP => (hu i P hP).2.2.1.2.1
            ex_ker := fun i P hP => (hu i P hP).2.2.2.1
            ex_lin := fun i P hP => (hu i P hP).2.2.2.2.1
            ex_weil := fun i P hP => (hu i P hP).2.2.2.2.2.1
            ex_eta := fun i P hP => (hu i P hP).2.2.2.2.2.2.1
            ex_etaA := fun i P hP => (hu i P hP).2.2.2.2.2.2.2
            onto := fun y hy => ?_
            disj := fun i j P P' hP hP' h => ?_
            fibre := fun i P P' hP hP' => ?_
            hol := hhol
            ex_diff := fun i P hP => (hu i P hP).2.2.1.2.2.2
            theta := fun i m B P bas sgn h τ hB hc hP hb hτ =>
              thetaFam _ _ m B P (fun b => u i (P b)) (fun b => ex i (P b)) bas sgn h τ
                (fun b hb => hu i _ (hP.1 b hb)) hb hτ hB hc hP (hhol i m B P hB hP).1 (hhol i m B P hB hP).2
            lift := fun m B y hB hy hh b₀ hb₀ => ?_ }⟩
  · obtain ⟨i, -, P, e, h⟩ := hcls y hy
    exact ⟨i, P, h.2.1, point_eq upUniq (hu i P h.2.1) h⟩
  · have hi : cls Xo σ ty (Y i) = cls Xo σ ty (u i P) :=
      cls_eq perObj upUniq (hx i) ⟨(hx i).1, _, _, hu i P hP⟩
    have hj : cls Xo σ ty (Y j) = cls Xo σ ty (u j P') :=
      cls_eq perObj upUniq (hx j) ⟨(hx j).1, _, _, hu j P' hP'⟩
    apply φ.symm.injective
    apply Subtype.ext
    rw [← hY, ← hY, hi, hj, h]
  · rw [upUniq _ _ _ _ _ _ _ _ _ _ (hu i P hP) (hu i P' hP')]
    refine exists_congr fun gam => exists_congr fun h => ?_
    rw [triv_iff l _ (hts i).2 gam _ l.M (Nat.dvd_lcm_left _ _),
      triv_iff_top l _ (hts i).2 gam l.A (Nat.dvd_lcm_right _ _)]
  · obtain ⟨i, -, P₀, e₀, h⟩ := hcls _ (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb', hsub, -, hP, -, hub⟩ := locLift _ _ m B y b₀ P₀ e₀ hB hb₀ hy hh h
    exact ⟨B', i, P, hB', hb', hsub, hP, fun b hb => point_eq upUniq (hu i _ (hP.1 b hb)) (hub b hb)⟩

end GlobalTheory
