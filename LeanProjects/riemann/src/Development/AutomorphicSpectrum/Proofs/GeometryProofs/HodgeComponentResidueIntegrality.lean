import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTStalk

section Lattices

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem mem_htW_iff (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨Submodule.zero_mem _, fun d _ => by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun d hd => ?_⟩
      rw [smul_add]
      exact Submodule.add_mem _ (hx.2 d hd) (hy.2 d hd)
    | smul c x _ hx =>
      refine ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem (c : Ω) hx.1, fun d hd => ?_⟩
      have h : σ d • c • x = c • σ d • x := smul_comm _ _ _
      rw [h]
      exact Submodule.smul_mem _ c (hx.2 d hd)
  · exact fun h => Submodule.subset_span h

theorem mem_htW_iff_forms (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, ∀ d ∈ 𝔡, σ d * w e ∈ regAt ξ q := by
  rw [mem_htW_iff]
  refine and_congr_right fun he => ⟨fun h w hw d hd => ?_, fun h d hd => ?_⟩
  · have := ((M.mem_htDual_iff L n ρ σ q _).1 (h d hd)).2 w hw
    simpa [map_smul, smul_eq_mul] using this
  · refine (M.mem_htDual_iff L n ρ σ q _).2 ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem _ he, fun w hw => ?_⟩
    simpa [map_smul, smul_eq_mul] using h w hw d hd

end Lattices

theorem forall_different_iff {o Ω E : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field E] [NumberField E]
    (A : Subalgebra o Ω) (B : Subring Ω) (hA : ∀ a : A, (a : Ω) ∈ B) (σ : E →+* Ω) (ds : A)
    (hds : GeneratesDiff σ ds) (t : Ω) :
    (∀ x ∈ differentIdeal ℤ (𝓞 E), σ (x : E) * t ∈ B) ↔ (ds : Ω) * t ∈ B := by
  constructor
  · intro h
    have h1 : algebraMap A Ω ds ∈ Submodule.span A {algebraMap A Ω ds} :=
      Submodule.subset_span rfl
    rw [hds] at h1
    have h2 : ∀ z ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}, z * t ∈ B := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact h x hx
      | zero => simpa using B.zero_mem
      | add u v _ _ hu hv =>
        rw [add_mul]
        exact B.add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) * t = (a : Ω) * (u * t) := by
          rw [Algebra.smul_def, mul_assoc]
          rfl
        rw [this]
        exact B.mul_mem (hA a) hu
    exact h2 _ h1
  · intro h x hx
    have h1 : σ (x : E) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← hds, Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    have : σ (x : E) * t = (a : Ω) * ((ds : Ω) * t) := by
      rw [← ha, Algebra.smul_def, mul_assoc]
      rfl
    rw [this]
    exact B.mul_mem (hA a) h

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem inv_natCast_mem {p : ℕ} (hp : p.Prime) {q : Cpt 𝔐.ξ} (hq : InFibre 𝔐.ξ p q) (b : ℕ) (hb : ¬ p ∣ b) :
    ((b : Ω))⁻¹ ∈ regAt 𝔐.ξ q := by
  have hZ := ModelTest.overZp_of_inFibre 𝔐 hp q hq
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one => simpa using (regAt 𝔐.ξ q).one_mem
  | prime r hr =>
    have hne : r ≠ p := by
      rintro rfl
      exact hb dvd_rfl
    have hu : unitAt 𝔐.ξ q (r : Ω) := by
      by_contra hnot
      exact hne (hZ r hr hnot)
    exact hu.2.2
  | mul a b ha hb' =>
    have h1 : ¬ p ∣ a := fun h => hb (h.mul_right b)
    have h2 : ¬ p ∣ b := fun h => hb (h.mul_left a)
    rw [Nat.cast_mul, mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (ha h1) (hb' h2)

theorem chart_mem_regAt {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {s : ∀ k, J k} {q : Cpt 𝔐.ξ} (hs : InChart 𝔐.ξ (mseg y) s q) (hq : InFibre 𝔐.ξ p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  obtain ⟨a, ha⟩ := a
  change a ∈ regAt 𝔐.ξ q
  change a ∈ Algebra.adjoin o _ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hs.2 j
  | algebraMap r =>
    obtain ⟨u, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    rw [h, div_eq_mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (intCast_mem _ u) (inv_natCast_mem 𝔐 hp hq b hb)
  | add u v _ _ hu hv => exact (regAt 𝔐.ξ q).add_mem hu hv
  | mul u v _ _ hu hv => exact (regAt 𝔐.ξ q).mul_mem hu hv

end Model

theorem mem_V_inl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hD hpS τ σ hσ s ds hds q hs hq e
  have hp : p.Prime := Fact.out
  have hV : 𝔐.V (Sum.inl τ) q = 𝔐.HT p (Sum.inl τ) q :=
    Lat.patch_of_unique S _ _ hpS hq fun p' hp' h =>
      ModelTest.overZp_of_inFibre 𝔐 hp q hq p' (𝔐.S_prime p' hp') h
  have hE : e ∈ GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (Sum.inl τ)) ↔ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ := by
    rw [LatBasic.mem_eigSp]
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  have hA := chart_mem_regAt 𝔐 hp ho hs hq
  have hO : omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li)) :=
    hD.om'_loc s q hs hq
  rw [hV]
  change e ∈ 𝔐.M.htW _ _ _ _ _ q ↔ _
  rw [mem_htW_iff_forms, hE]
  refine and_congr_right fun _ => ?_
  have hT : ∀ w : Module.Dual Ω 𝔐.Li,
      (∀ d ∈ differentIdeal ℤ (𝓞 E), 𝔐.emb (Sum.inl τ) d * w e ∈ regAt 𝔐.ξ q) ↔
        (ds : Ω) * w e ∈ regAt 𝔐.ξ q := fun w => by
    rw [← forall_different_iff _ _ hA σ ds hds]
    simp only [hσ]
  constructor
  · intro h w hw
    have hw' : w ∈ omP 𝔐 p q := by
      rw [hO]
      exact Submodule.subset_span hw
    exact (hT w).1 (h w hw')
  · intro h w hw
    rw [show 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = omP 𝔐 p q from rfl, hO] at hw
    refine (hT w).2 ?_
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simpa using (regAt 𝔐.ξ q).zero_mem
    | add u v _ _ hu hv =>
      have : (ds : Ω) * (u + v) e = (ds : Ω) * u e + (ds : Ω) * v e := by
        rw [LinearMap.add_apply, mul_add]
      rw [this]
      exact (regAt 𝔐.ξ q).add_mem hu hv
    | smul a u _ hu =>
      have : (ds : Ω) * (a • u) e = (a : Ω) * ((ds : Ω) * u e) := by
        change (ds : Ω) * ((a : Ω) • u) e = _
        rw [LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact (regAt 𝔐.ξ q).mul_mem a.2 hu

end GlobalTheory.CompanionTheory.Ar.Flat.HTStalk
