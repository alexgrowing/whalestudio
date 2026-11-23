import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.SimMb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H)

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  have h1 := H.bar_eq (H.bar a)
  have h2 := H.bar_eq a
  exact h1.trans (by rw [h2, IsCMField.complexConj_apply_apply])

theorem bar_mem {a : 𝓞 E} (ha : a ∈ l.Mb) : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) :=
  Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha

theorem M_mem : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  exact (Ideal.mem_inf.mp (Ideal.mul_le_inf h)).1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
theorem _root_.GlobalTheory.SimMb.mem_of_modN {x : D.La} (hx : D.ModN l.M x) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := hx
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le.2 fun r hr s _ => Ideal.mul_mem_right s _ hr) h1
  have hb : l.M • b = ((l.M : ℕ) : 𝓞 E) • b := (Nat.cast_smul_eq_nsmul (𝓞 E) l.M b).symm
  rw [hb]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem level_Mb_ne_bot : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have h2 := l.three_le
  norm_cast at h1
  omega

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in

theorem _root_.GlobalTheory.SimMb.exists_left_inv (g : D.La →ₗ[𝓞 E] D.La)
    (hg : ∀ x, g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ h : D.La →ₗ[𝓞 E] D.La, ∀ x, h (g x) - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  classical
  haveI := D.fin
  haveI := D.proj
  set P := l.Mb • (⊤ : Submodule (𝓞 E) D.La) with hP
  have hgP : P ≤ P.comap g := by
    rw [hP, Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  set gbar := P.mapQ P g hgP with hgbar
  have hinj : Function.Injective gbar := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P y
    rw [LinearMap.mem_ker, hgbar, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hg x hy
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ (level_Mb_ne_bot l)
  have : Module.Finite (𝓞 E ⧸ l.Mb) (D.La ⧸ P) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  have : Finite (D.La ⧸ P) := Module.finite_of_finite (𝓞 E ⧸ l.Mb)
  have hsurj : Function.Surjective gbar := Finite.injective_iff_surjective.1 hinj
  set e := LinearEquiv.ofBijective gbar ⟨hinj, hsurj⟩ with he
  obtain ⟨h, hh⟩ := Module.projective_lifting_property P.mkQ ((e.symm : _ →ₗ[𝓞 E] _) ∘ₗ P.mkQ)
    (Submodule.mkQ_surjective P)
  refine ⟨h, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hh (g x)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at h1
  rw [← Submodule.Quotient.eq, h1]
  have h2 : (Submodule.Quotient.mk (g x) : D.La ⧸ P) = e (Submodule.Quotient.mk x) := by
    rfl
  rw [h2, LinearEquiv.symm_apply_apply]

end GlobalTheory.SimMb

namespace GlobalTheory

open SimMb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem conjO_conjO_unimodular_class_representatives (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.coe_injective
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem exists_mul_eq_level_mul_of_mem_Mb {α β : 𝓞 E} (hα : α ∈ l.Mb)
    (hβ : β ∈ Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb) : ∃ c : 𝓞 E, α * β = (l.M : 𝓞 E) * c := by
  have h1 : α * β ∈ l.Mb * Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb := Ideal.mul_mem_mul hα hβ
  rw [l.prod, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem exists_smul_eq_level_smul_of_mem_map_bar_Mb {β : 𝓞 E} (hβ : β ∈ Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb)
    {y : D.La} (hy : y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ z : D.La, β • y = ((l.M : ℕ) : 𝓞 E) • z := by
  refine Submodule.smul_induction_on
    (p := fun y => ∃ z : D.La, β • y = ((l.M : ℕ) : 𝓞 E) • z) hy ?_ ?_
  · intro m hm n _
    obtain ⟨c, hc⟩ := exists_mul_eq_level_mul_of_mem_Mb l hm hβ
    refine ⟨c • n, ?_⟩
    rw [smul_smul, mul_comm β m, hc, mul_smul]
  · intro y₁ y₂ h₁ h₂
    obtain ⟨z₁, hz₁⟩ := h₁
    obtain ⟨z₂, hz₂⟩ := h₂
    exact ⟨z₁ + z₂, by rw [smul_add, hz₁, hz₂, smul_add]⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem level_dvd_EF_level_smul (x z : D.La) :
    (l.M : ℤ) ∣ D.EF x (((l.M : ℕ) : 𝓞 E) • z) := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  exact Dvd.intro _ rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
  (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) in
private theorem level_dvd_EF_mul_smul_of_mem_Mb {α β : 𝓞 E} (hα : α ∈ l.Mb)
    (hβ : β ∈ Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb) (x y : D.La) :
    (l.M : ℤ) ∣ D.EF x ((α * β) • y) := by
  obtain ⟨c, hc⟩ := exists_mul_eq_level_mul_of_mem_Mb l hα hβ
  rw [hc, mul_smul]
  exact level_dvd_EF_level_smul D l x _

theorem _root_.GlobalTheory.exists_sim_of_aut_mod : ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (A : ℕ)
    (g : D.La →ₗ[NumberField.RingOfIntegers E] D.La), 1 ≤ D.p + D.q → 0 < A → A.Coprime l.M →
    (∀ x, g x ∈ l.Mb • (⊤ : Submodule (NumberField.RingOfIntegers E) D.La) →
      x ∈ l.Mb • (⊤ : Submodule (NumberField.RingOfIntegers E) D.La)) →
    ∃ ω : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, (∀ x, ω.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (NumberField.RingOfIntegers E) D.La)) ∧
      (∀ x, D.ModN A (ω.f A x - x)) ∧ (A : ℤ) ∣ ω.ν A - 1 := by
  intro E _ _ _ H D l A g hpq hA hcop hg
  set P := l.Mb • (⊤ : Submodule (NumberField.RingOfIntegers E) D.La) with hP
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.SimMb.exists_left_inv D l g hg
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.SimLift.exists_rep D (fun a b => D.EF a (h b))
    (fun a a' b => by simp) (fun a b b' => by simp) (fun c a b => by simp [D.adj, map_smul])
  have h1 : (1 : NumberField.RingOfIntegers E) ∈ l.Mb ⊔ Ideal.map
      (H.bar : NumberField.RingOfIntegers E →+* NumberField.RingOfIntegers E) l.Mb := by
    rw [l.coprime]
    exact Submodule.mem_top
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.1 h1
  have hbe : H.bar e ∈ Ideal.map
      (H.bar : NumberField.RingOfIntegers E →+* NumberField.RingOfIntegers E) l.Mb :=
    Ideal.mem_map_of_mem _ he
  have hbe' : H.bar e' ∈ l.Mb := by
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_of_equiv H.bar e').1 he'
    rw [conjO_conjO_unimodular_class_representatives]
    exact hy
  set f1 : D.La →ₗ[NumberField.RingOfIntegers E] D.La := e' • g + e • u with hf1

  have hcross : ∀ a b, (l.M : ℤ) ∣ D.EF (e • u a) (e' • g b) - D.EF (e • a) (e' • b) := by
    intro a b
    rw [D.adj, D.adj, hu, smul_smul, smul_smul, map_smul]
    obtain ⟨z, hz⟩ := exists_smul_eq_level_smul_of_mem_map_bar_Mb D l hbe (hh b)
    have : (H.bar e * e') • h (g b) = (H.bar e * e') • b + e' • (((l.M : ℕ) : NumberField.RingOfIntegers E) • z) := by
      rw [← hz, smul_smul, mul_comm e' (H.bar e), ← smul_add, add_sub_cancel]
    rw [this, map_add, add_sub_cancel_left]
    rw [smul_comm]
    exact level_dvd_EF_level_smul D l _ _
  have hF : ∀ a b, (l.M : ℤ) ∣ D.EF (f1 a) (f1 b) - D.EF a b := by
    intro a b
    have ha : a = e • a + e' • a := by rw [← add_smul, hee, one_smul]
    have hb : b = e • b + e' • b := by rw [← add_smul, hee, one_smul]
    have hgg : (l.M : ℤ) ∣ D.EF (e' • g a) (e' • g b) := by
      rw [D.adj, smul_smul]
      exact level_dvd_EF_mul_smul_of_mem_Mb D l hbe' he' _ _
    have huu : (l.M : ℤ) ∣ D.EF (e • u a) (e • u b) := by
      rw [D.adj, smul_smul, mul_comm]
      exact level_dvd_EF_mul_smul_of_mem_Mb D l he hbe _ _
    have hee1 : (l.M : ℤ) ∣ D.EF (e • a) (e • b) := by
      rw [D.adj, smul_smul, mul_comm]
      exact level_dvd_EF_mul_smul_of_mem_Mb D l he hbe _ _
    have hee2 : (l.M : ℤ) ∣ D.EF (e' • a) (e' • b) := by
      rw [D.adj, smul_smul]
      exact level_dvd_EF_mul_smul_of_mem_Mb D l hbe' he' _ _
    have hca := hcross a b
    have hcb := hcross b a
    rw [_root_.GlobalTheory.SimLift.form_skew D (e • u b), _root_.GlobalTheory.SimLift.form_skew D (e • b)] at hcb
    have hexp : D.EF (f1 a) (f1 b) - D.EF a b =
        D.EF (e' • g a) (e' • g b) + D.EF (e • u a) (e • u b) - D.EF (e • a) (e • b)
          - D.EF (e' • a) (e' • b) + (D.EF (e • u a) (e' • g b) - D.EF (e • a) (e' • b))
          - (-D.EF (e' • g a) (e • u b) - -D.EF (e' • a) (e • b)) := by
      have hab : D.EF a b = D.EF (e • a + e' • a) (e • b + e' • b) := by rw [← ha, ← hb]
      rw [hab]
      simp only [hf1, LinearMap.add_apply, LinearMap.smul_apply, map_add, LinearMap.add_apply]
      ring
    rw [hexp]
    exact dvd_sub (dvd_add (dvd_sub (dvd_sub (dvd_add hgg huu) hee1) hee2) hca) hcb
  obtain ⟨t, s, hst⟩ := (Nat.isCoprime_iff_coprime.2 hcop : IsCoprime (A : ℤ) (l.M : ℤ))
  set f0 : D.La →ₗ[NumberField.RingOfIntegers E] D.La :=
    (s * l.M) • LinearMap.id + (t * A) • f1 with hf0
  have hform : ∀ a b, ((l.M * A : ℕ) : ℤ) ∣ D.EF (f0 a) (f0 b) - 1 * D.EF a b := by
    intro a b
    obtain ⟨k, hk⟩ := hF a b
    refine ⟨s * t * (D.EF a (f1 b) + D.EF (f1 a) b - 2 * D.EF a b) + t ^ 2 * A * k, ?_⟩
    simp only [hf0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
      map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (t ^ 2 * (A : ℤ) ^ 2) * hk + D.EF a b * (t * A + s * l.M + 1) * hst
  obtain ⟨ω, hω, hν⟩ := _root_.GlobalTheory.exists_sim_lift E H D (l.M * A) f0 1
    (Nat.mul_pos hM hA) isCoprime_one_left hform
  refine ⟨ω, fun x => ?_, fun x => ?_, ?_⟩
  · have k1 : D.ModN l.M (ω.f (l.M * A) x - ω.f l.M x) := ω.tower l.M A hM hA x
    have k2 : D.ModN l.M (ω.f (l.M * A) x - f0 x) := _root_.GlobalTheory.SimAlg.modN_of_mul (hω x)
    have k3 : D.ModN l.M (f0 x - f1 x) := by
      refine ⟨s • (x - f1 x), ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      simp only [hf0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      linear_combination (norm := module) hst • f1 x
    have k4 : f1 x - g x ∈ P := by
      have : f1 x - g x = e • (u x - g x) := by
        simp only [hf1, LinearMap.add_apply, LinearMap.smul_apply]
        linear_combination (norm := module) hee • g x
      rw [this, hP]
      exact Submodule.smul_mem_smul he Submodule.mem_top
    have : ω.f l.M x - g x = (ω.f (l.M * A) x - f0 x) - (ω.f (l.M * A) x - ω.f l.M x)
        + (f0 x - f1 x) + (f1 x - g x) := by abel
    rw [this]
    exact P.add_mem (P.add_mem (P.sub_mem (_root_.GlobalTheory.SimMb.mem_of_modN D l k2)
      (_root_.GlobalTheory.SimMb.mem_of_modN D l k1)) (_root_.GlobalTheory.SimMb.mem_of_modN D l k3)) k4
  · have k1 : D.ModN A (ω.f (A * l.M) x - ω.f A x) := ω.tower A l.M hA hM x
    have k2 : D.ModN A (ω.f (A * l.M) x - f0 x) := by
      have k := hω x
      rw [mul_comm] at k
      exact _root_.GlobalTheory.SimAlg.modN_of_mul k
    have k3 : D.ModN A (f0 x - x) := by
      refine ⟨t • (f1 x - x), ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      simp only [hf0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      linear_combination (norm := module) hst • x
    have k1' := _root_.GlobalTheory.SimAlg.modN_neg k1
    rw [neg_sub] at k1'
    exact _root_.GlobalTheory.SimLift.modN_trans D k1' (_root_.GlobalTheory.SimLift.modN_trans D k2 k3)
  · obtain ⟨a0, b0, hab⟩ := _root_.GlobalTheory.SimAlg.exists_form_eq_one hpq
    have d1 : (A : ℤ) ∣ ω.ν (A * l.M) - ω.ν A := _root_.GlobalTheory.SimAlg.dvd_mult_tower ω hA hM hab
    rw [mul_comm] at d1
    have d2 : (A : ℤ) ∣ ω.ν (l.M * A) - 1 :=
      Dvd.dvd.trans (by push_cast; exact Dvd.intro_left _ rfl) hν
    have : ω.ν A - 1 = (ω.ν (l.M * A) - 1) - (ω.ν (l.M * A) - ω.ν A) := by ring
    rw [this]
    exact dvd_sub d2 d1

end GlobalTheory
