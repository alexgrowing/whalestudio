import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameterStatement

noncomputable section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

namespace GlobalTheory.K5.Reb

def RebT {p : ℕ} [Fact p.Prime] (Ω : Type) [Field Ω] (_ψ : O0 p →+* Ω) : Type := Ω

section Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]

instance (ψ : O0 p →+* Ω) : Field (RebT Ω ψ) := inferInstanceAs (Field Ω)

instance (ψ : O0 p →+* Ω) : Algebra (O0 p) (RebT Ω ψ) := ψ.toAlgebra

end Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω}

theorem mem_range (hψ : IsReb T L ψ) (a : O0 p) : ∃ b, ψ b = algebraMap (O0 p) Ω a := by
  have h : algebraMap (O0 p) Ω a ∈ ψ.range := by
    rw [hψ.rng, Subalgebra.mem_toSubring]
    exact Subalgebra.algebraMap_mem _ a
  exact RingHom.mem_range.1 h

def jf (hψ : IsReb T L ψ) (a : O0 p) : O0 p := (mem_range hψ a).choose

theorem jf_spec (hψ : IsReb T L ψ) (a : O0 p) : ψ (jf hψ a) = algebraMap (O0 p) Ω a :=
  (mem_range hψ a).choose_spec

def jj (hψ : IsReb T L ψ) : O0 p →+* O0 p where
  toFun := jf hψ
  map_one' := hψ.inj (by rw [jf_spec, map_one, map_one])
  map_mul' a b := hψ.inj (by rw [jf_spec, map_mul, map_mul, jf_spec, jf_spec])
  map_zero' := hψ.inj (by rw [jf_spec, map_zero, map_zero])
  map_add' a b := hψ.inj (by rw [jf_spec, map_add, map_add, jf_spec, jf_spec])

theorem comp_jj (hψ : IsReb T L ψ) : ψ.comp (jj hψ) = algebraMap (O0 p) Ω :=
  RingHom.ext (jf_spec hψ)

theorem isInt_iff (hψ : IsReb T L ψ) (x : Ω) : @IsInt p _ (RebT Ω ψ) _ _ x ↔ IsInt p x := by
  constructor
  · rintro ⟨f, hf, h⟩
    let A := Algebra.adjoin (O0 p) {T.qq L}
    have hq : IsIntegral (O0 p) (T.qq L) := by
      refine ⟨X ^ (p ^ L) - C (qO p), monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ?_⟩
      rw [← aeval_def]
      simp [GlobalTheory.K5.Basic.qq_pow]
    haveI : Algebra.IsIntegral (O0 p) A := Algebra.IsIntegral.adjoin (by rintro _ rfl; exact hq)
    let g : O0 p →+* A := ψ.codRestrict A (fun b => by
      have := ψ.mem_range_self b
      rw [hψ.rng] at this
      exact this)
    have hA : IsIntegral A x := by
      refine ⟨f.map g, hf.map g, ?_⟩
      rw [eval₂_map]
      have e : (algebraMap A Ω).comp g = ψ := RingHom.ext fun _ => rfl
      rw [e]
      exact h
    exact isIntegral_trans x hA
  · rintro ⟨f, hf, h⟩
    refine ⟨f.map (jj hψ), hf.map _, ?_⟩
    show eval₂ ψ x (f.map (jj hψ)) = 0
    rw [eval₂_map]
    rw [comp_jj]
    exact h

theorem cong_iff (hψ : IsReb T L ψ) (k : ℕ) (x y : Ω) :
    @Cong p _ (RebT Ω ψ) _ _ k x y ↔ Cong p k x y := by
  constructor
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).1 hz, e⟩
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).2 hz, e⟩

theorem isClo (hΩ : IsClo p Ω) (hψ : IsReb T L ψ) : IsClo p (RebT Ω ψ) where
  inj := hψ.inj
  alg := by
    refine ⟨fun (x : Ω) => ?_⟩
    obtain ⟨f, hf, h⟩ := hΩ.alg.isAlgebraic x
    have hinj : Function.Injective (jj hψ) := by
      intro a b hab
      apply hΩ.inj
      rw [← comp_jj hψ, RingHom.comp_apply, RingHom.comp_apply, hab]
    refine ⟨f.map (jj hψ), (Polynomial.map_ne_zero_iff hinj).2 hf, ?_⟩
    show eval₂ ψ x (f.map (jj hψ)) = 0
    rw [eval₂_map, comp_jj, ← aeval_def]
    exact h
  clo := hΩ.clo

theorem zp_eq (hψ : IsReb T L ψ) (z : ℤ_[p]) :
    ψ (algebraMap ℤ_[p] (O0 p) z) = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) := by
  have e : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.C z) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
    congr 1
    show HahnSeries.ofPowerSeries ℤ ℤ_[p] (algebraMap ℤ_[p] (PowerSeries ℤ_[p]) z) = _
    rw [← HahnSeries.ofPowerSeries_C]
    rfl
  rw [e]
  have hp0 : (p : ℤ) ^ L ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
  · by_cases hi : i = 0
    · subst hi; simp [HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ L * i ≠ 0 := mul_ne_zero hp0 hi
      simp [HahnSeries.C_apply, HahnSeries.coeff_single, hi, this]
  · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem isAlgZp_iff (hψ : IsReb T L ψ) (x : Ω) : @IsAlgZp p _ (RebT Ω ψ) _ _ x ↔ IsAlgZp p x := by
  have hc : ψ.comp (algebraMap ℤ_[p] (O0 p)) = (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) :=
    RingHom.ext (zp_eq hψ)
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    have h' : eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0 := h
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def] at h'
    exact h'
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    show eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def]
    exact h

def tw (hψ : IsReb T L ψ) : GlobalTheory.K5.Tower p (RebT Ω ψ) where
  ζ := T.ζ
  qq k := T.qq (L + k)
  prim := T.prim
  ζpow := T.ζpow
  q0 := hψ.par.symm
  qpow k := T.qpow (L + k)

def down (hψ : IsReb T L ψ) (g : Gal p (RebT Ω ψ)) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : Ω ≃+* Ω)) (fun a => by
    obtain ⟨b, hb⟩ := mem_range hψ a
    rw [← hb]
    exact g.commutes b)

theorem down_mul (hψ : IsReb T L ψ) (g h : Gal p (RebT Ω ψ)) : down hψ (g * h) = down hψ g * down hψ h :=
  AlgEquiv.ext fun _ => rfl

theorem fix_range (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) (a : O0 p) : g (ψ a) = ψ a := by
  have h1 : ψ a ∈ (Algebra.adjoin (O0 p) {T.qq L}).toSubring := hψ.rng ▸ ψ.mem_range_self a
  have h2 : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by rintro x rfl; exact hg)
  exact (AlgHom.mem_equalizer _ _ _).1 (h2 h1)

def up (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) : Gal p (RebT Ω ψ) :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : RebT Ω ψ ≃+* RebT Ω ψ)) (fun a => fix_range hψ g hg a)

theorem isAlgZp_zeta (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) : IsAlgZp p (T.ζ L) := by
  refine ⟨X ^ (p ^ L) - C 1, (monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).ne_zero, ?_⟩
  simp [(T.prim L).pow_eq_one]

theorem mem_H (hψ : IsReb T L ψ) {g : Gal p (RebT Ω ψ)} (hg : g ∈ Ggeo p (RebT Ω ψ)) :
    down hψ g ∈ Ggeo p Ω ⊓ Gn T L := by
  have hgeo : down hψ g ∈ Ggeo p Ω := fun x hx => hg x ((isAlgZp_iff hψ x).2 hx)
  refine Subgroup.mem_inf.2 ⟨hgeo, (GlobalTheory.K5.Basic.mem_gn T L _).2 ⟨hgeo _ (isAlgZp_zeta T L), ?_⟩⟩
  have h : g (ψ (qO p)) = ψ (qO p) := g.commutes (qO p)
  rw [hψ.par] at h
  exact h

theorem exists_up (hψ : IsReb T L ψ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    ∃ g' : Gal p (RebT Ω ψ), g' ∈ Ggeo p (RebT Ω ψ) ∧ down hψ g' = g := by
  have hg1 := (Subgroup.mem_inf.1 hg).1
  have hq := ((GlobalTheory.K5.Basic.mem_gn T L g).1 (Subgroup.mem_inf.1 hg).2).2
  exact ⟨up hψ g hq, fun x hx => hg1 x ((isAlgZp_iff hψ x).1 hx), AlgEquiv.ext fun _ => rfl⟩

theorem h1_geometric_level_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong p n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong p n ((p : Ω) ^ c * o) 0) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummer_cocycle_twisted_coboundary p hp2
  refine ⟨c, fun Ω _ _ hΩ T L n _ lq hlq => ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_reparametrizationByTowerParameter p Ω hΩ T L
  have hk : IsKum (tw hψ) n (Ggeo p (RebT Ω ψ)) ((tw hψ).qq n) (fun g => lq (down hψ g)) :=
    fun g hg => hlq (down hψ g) (mem_H hψ hg)
  obtain ⟨h1, h2⟩ := hc (RebT Ω ψ) (isClo hΩ hψ) (tw hψ) n (fun _ => 0) _ hk
  constructor
  · intro a ha hcoc
    have hlc : IntegralLocallyConstCochainModPow n (Ggeo p (RebT Ω ψ)) (fun g => a (down hψ g)) := by
      refine ⟨fun g hg => (isInt_iff hψ _).2 (ha.1 _ (mem_H hψ hg)), fun g hg => ?_⟩
      obtain ⟨S, hS⟩ := ha.2 _ (mem_H hψ hg)
      exact ⟨S, fun h hh hx => (cong_iff hψ n _ _).2 (hS _ (mem_H hψ hh) hx)⟩
    have hco : IsTwistedOneCocycle 0 n (Ggeo p (RebT Ω ψ)) (fun _ => 0) (fun g => a (down hψ g)) := by
      intro g hg h hh
      simp only [pow_zero, one_mul]
      rw [down_mul]
      exact (cong_iff hψ n _ _).2 (hcoc _ (mem_H hψ hg) _ (mem_H hψ hh))
    obtain ⟨o, ho, hof, x, hx, hxc⟩ := h1 _ hlc hco
    refine ⟨o, (isInt_iff hψ o).1 ho, fun g hg => ?_, x, (isInt_iff hψ x).1 hx, fun g hg => ?_⟩
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      exact hof g' hg'
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      have e := hxc g' hg'
      rw [pow_zero, one_mul] at e
      exact (cong_iff hψ n _ _).1 e
  · intro o ho hof hcob
    obtain ⟨x, hx, hxc⟩ := hcob
    refine (cong_iff hψ n _ _).1 (h2 o ((isInt_iff hψ o).2 ho) (fun g hg => hof _ (mem_H hψ hg))
      ⟨x, (isInt_iff hψ x).2 hx, fun g hg => ?_⟩)
    rw [pow_zero, one_mul]
    exact (cong_iff hψ n _ _).2 (hxc _ (mem_H hψ hg))

end GlobalTheory.K5.Reb
