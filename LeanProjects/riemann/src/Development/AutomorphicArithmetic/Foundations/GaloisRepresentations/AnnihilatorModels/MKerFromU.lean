import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

section Helpers
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem cpow {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (h : T ⟶ A) (n : ℕ) :
    f ≫ (h ^ n) = (f ≫ h) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem powc {A B T : Over S} [GrpObj A] [GrpObj B] (h : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (h ^ n) ≫ f = (h ≫ f) ^ n := by
  exact map_pow (IsMonHom.monoidHom f T) h n

private abbrev sc (o : Obj b N s) (x : 𝓞 D.F) : o.A ⟶ o.A := o.act.act (algebraMap (𝓞 D.F) D.O x)

private instance sc_hom (o : Obj b N s) (x : 𝓞 D.F) : IsMonHom (sc o x) := o.act.hom _

private theorem sc_add (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x + y) = sc o x * sc o y := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x + y)) = _
  rw [map_add]
  exact o.act.add _ _

private theorem sc_mul (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x * y) = sc o y ≫ sc o x := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x * y)) = _
  rw [map_mul]
  exact o.act.mul _ _

private theorem sc_one (o : Obj b N s) : sc o 1 = 𝟙 o.A := by
  show o.act.act (algebraMap (𝓞 D.F) D.O 1) = _
  rw [map_one]
  exact o.act.one

private theorem sc_zero (o : Obj b N s) : sc o 0 = 1 := by
  have h := sc_add o 0 0
  rw [add_zero] at h
  open GrpObj in exact mul_eq_left.mp h.symm

private theorem sc_nat (o : Obj b N s) (n : ℕ) : sc o (n : 𝓞 D.F) = (𝟙 o.A) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, sc_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, sc_add, ih, sc_one, pow_succ]

private theorem sc_killed (o : Obj b N s) {T : Over S} (z : T ⟶ o.A) {c : ℕ} (hz : z ^ c = 1) (t : 𝓞 D.F) :
    z ≫ sc o (t * (c : 𝓞 D.F)) = 1 := by
  rw [sc_mul, sc_nat, ← Category.assoc, cpow, Category.comp_id, hz]
  have h := powc z (sc o t) 0
  rwa [pow_zero, pow_zero] at h

end Helpers

private theorem bar_bar {p : ℕ} [Fact p.Prime] (D : Datum p) (a : 𝓞 D.F) : D.bar (D.bar a) = a := by
  rw [RingOfIntegers.ext_iff, D.bar_eq, D.bar_eq, IsCMField.complexConj_apply_apply]

private theorem one_comp_monHom' {S : Scheme.{0}} {T A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B)
    [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  have h := powc (1 : T ⟶ A) f 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_one_grpObj {S : Scheme.{0}} {X T A : Over S} [GrpObj A] (f : X ⟶ T) :
    f ≫ (1 : T ⟶ A) = 1 := by
  have h := cpow f (1 : T ⟶ A) 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_mul_grpObj {S : Scheme.{0}} {T A B : Over S} [GrpObj B] (f : T ⟶ A)
    (h₁ h₂ : A ⟶ B) : f ≫ (h₁ * h₂) = (f ≫ h₁) * (f ≫ h₂) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem comp_id_pow_eq_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (f : T ⟶ A) (n : ℕ) :
    f ≫ (𝟙 A ^ n) = f ^ n := by
  rw [cpow, Category.comp_id]

theorem UpperTheory.Gal.crystallineComparison.Mod.kerFromU_of :
    UElt → PairCalc → Adjoint → DivC → KerFromU := by
  intro hU hP hA hD p _ D R _ b N r w hw hle k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hiff T g hg
  have cpos := h1.pos
  obtain ⟨⟨e, rfl⟩, hm1, hl1, -, -, ψ₁', hm1', hψ₁a, hψ₁b⟩ := id h1
  obtain ⟨-, hm2, hl2, -, -, ψ₂', hm2', hψ₂a, hψ₂b⟩ := id h2
  haveI := hm1
  haveI := hm1'
  haveI := hm2
  haveI := hm2'
  obtain ⟨α, hα1, hα2, -⟩ := hU p D r w hw hle e
  have kill : ∀ {T' : Over (Sp k)} (u : T' ⟶ o.A), u ^ (p ^ e) = 1 → ∀ t : 𝓞 D.F,
      t ∈ Ideal.span {(p : 𝓞 D.F) ^ e} → u ≫ sc o t = 1 := by
    intro T' u hu t ht
    obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [← Nat.cast_pow]
    exact sc_killed o u hu t'
  have uk : ∀ (o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ],
      (∀ c', o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') → ∀ (T' : Over (Sp k)) (u : T' ⟶ o.A),
      u ≫ ψ = 1 → u ^ (p ^ e) = 1 → UKer r o ψ T' (u ≫ sc o α) := by
    intro o' ψ _ hl T' u hu hpu
    refine ⟨?_, e, ?_⟩
    · have hl' : sc o α ≫ ψ = ψ ≫ sc o' α := hl _
      rw [Category.assoc, hl', ← Category.assoc, hu, one_comp_monHom']
    · intro a ha
      show (u ≫ sc o α) ≫ sc o a = 1
      rw [Category.assoc, ← sc_mul]
      exact kill u hpu _ (hα1 a ha)
  have gpow : g ^ (p ^ e) = 1 := by
    rw [← comp_id_pow_eq_pow g (p ^ e), ← hψ₁a, ← Category.assoc, hg, one_comp_monHom']
  have dec : g = (g ≫ sc o α) * (g ≫ sc o (D.bar α)) := by
    rw [← comp_mul_grpObj, ← sc_add]
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.mp hα2
    have hsum : α + D.bar α = 1 + t' * ((p ^ e : ℕ) : 𝓞 D.F) := by
      rw [Nat.cast_pow, ht']
      ring
    rw [hsum, sc_add, comp_mul_grpObj, sc_one, Category.comp_id, sc_killed o g gpow t',
      _root_.mul_one]
  have hA1 : (g ≫ sc o α) ≫ ψ₂ = 1 := ((hiff T _).1 (uk o₁ ψ₁ hl1 T g hg gpow)).1
  obtain ⟨ν, hν, hνc⟩ := (hD (Sp k) o₂.A o₁.A o₂.ab (p ^ e) cpos).1 (ψ₂' ≫ sc o α ≫ ψ₁)
    inferInstance (by
      intro T' t ht
      have hu2 : (t ≫ ψ₂') ≫ ψ₂ = 1 := by
        rw [Category.assoc, hψ₂b, comp_id_pow_eq_pow, ht]
      have hu3 : (t ≫ ψ₂') ^ (p ^ e) = 1 := by
        rw [← powc, ht, one_comp_monHom']
      have h' := ((hiff T' _).2 (uk o₂ ψ₂ hl2 T' _ hu2 hu3)).1
      simpa only [Category.assoc] using h')
  haveI := hν
  have hfac : ν ≫ ψ₁' = ψ₂' ≫ sc o α := by
    refine (hD (Sp k) o₂.A o.A o₂.ab (p ^ e) cpos).2 _ _ inferInstance inferInstance ?_
    rw [← powc, hνc]
    simp only [Category.assoc, hψ₁a]
    rw [← Category.assoc, comp_id_pow_eq_pow]
  have h3 : ∀ (T' : Over (Sp k)) (x y : T' ⟶ o.A) (a : 𝓞 D.F),
      evc o.isLB (x ≫ sc o a) y = evc o.isLB x (y ≫ sc o (D.bar a)) :=
    (hP p D R b N (Sp k) s o).2.2.1
  have hB : (g ≫ sc o (D.bar α)) ≫ ψ₂ = 1 := by
    obtain ⟨e', hcop, hnd⟩ := (hP p D R b N (Sp k) s o₂).2.2.2.1
    have zc : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ (p ^ e) = 1 := by
      rw [Category.assoc, ← powc, gpow, one_comp_monHom']
    have ze : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ e' = 1 := by
      apply hnd
      have ad2 := (hA p D R b N k s (p ^ e) o o₂ ψ₂ ψ₂' h2 hm2' hψ₂b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g ≫ sc o (D.bar α)) (fst o₂.A T)).1
      simp only [Category.assoc] at ad2 ⊢
      rw [ad2, ← Category.assoc, h3, bar_bar, Category.assoc, ← hfac, ← Category.assoc]
      have ad1 := (hA p D R b N k s (p ^ e) o o₁ ψ₁ ψ₁' h1 hm1' hψ₁b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g) (fst o₂.A T ≫ ν)).1
      rw [← ad1, Category.assoc, hg, comp_one_grpObj]
      exact GlobalTheory.AbDual.IsAdditive.evc_one o₁.isLB (hP p D R b N (Sp k) s o₁).1 _
    have hgcd := pow_gcd_eq_one.2 ⟨ze, zc⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e hcop), pow_one] at hgcd
  have mm : ∀ a a' : T ⟶ o.A, (a * a') ≫ ψ₂ = (a ≫ ψ₂) * (a' ≫ ψ₂) :=
    fun a a' => (IsMonHom.monoidHom ψ₂ T).map_mul a a'
  rw [dec, mm, hA1, hB, _root_.one_mul]
