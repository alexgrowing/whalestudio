import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

instance factPrime (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def chi (H : Host E) : DirichletCharacter ℂ H.d := (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def dlogL (H : Host E) : ℝ := (deriv (chi H).LFunction 1 / (chi H).LFunction 1).re

def logOmCurve (H : Host E) : ℝ := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) - dlogL H

def logOm (H : Host E) : ℝ := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - dlogL H

theorem chi_ne_one (H : Host E) : chi H ≠ 1 := by
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  rw [chi, MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)]
  exact quadraticChar_ne_one h2

theorem LFunction_ne_zero (H : Host E) :
    (chi H).LFunction 1 ≠ 0 ∧ DifferentiableAt ℂ (chi H).LFunction 1 :=
  ⟨DirichletCharacter.LFunction_apply_one_ne_zero (chi_ne_one H),
    (chi H).differentiableAt_LFunction 1 (Or.inr (chi_ne_one H))⟩

def IsLinePeriod {H : Host E} {K : Type} [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (τ : 𝓞 E →+* 𝓞 K)
    (x : ℝ) : Prop :=
  ∃ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h ∧ (F.eigLat T.t.act τ).FG ∧
    latRank K (F.eigLat T.t.act τ) = 1 ∧ x = 2 * deg h (F.eigLat T.t.act τ)

variable {H : Host E}

section Curve

variable {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'}

def IsCurveFibre (f : R →+* R') (C : Ell H R ω) (C' : Ell H R' ω') (φ : C'.P.A.left ⟶ C.P.A.left) : Prop :=
  ω' = f ω ∧ IsPolFibre f C.P C'.P φ ∧ (∀ a, (C'.act.act a).left ≫ φ = φ ≫ (C.act.act a).left) ∧
    IsVecOver f φ C.v C'.v

def IsPrincipalAt (C : Ell H R ω) (s : R →+* ℂ) : Prop :=
  ∀ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ C.P.A.left), IsPolFibre s C.P Q ψ → ∀ u : HolUnif Q.A Q.L Q.g,
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * s ω)

structure IsCurveExp (C : Ell H R ω) (s : R →+* ℂ) (e : ℂ → (Over.mk (spMap s) ⟶ C.P.A)) : Prop where
  add : ∀ z w, e (z + w) = e z * e w
  onto : Function.Surjective e
  ker : ∀ z, e z = 1 ↔ ∃ m n : ℤ, z = m + n * s ω
  hol : IsHolTo Set.univ fun z => (e z).left

end Curve

def HasPeriod {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) : Prop :=
  ∃ n : (M →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ ∀ r, IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
    x = -meanLog M n

theorem HasPeriod.unique {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} {C : Ell H (𝓞 M) ω} {x y : ℝ}
    (hx : HasPeriod C x) (hy : HasPeriod C y) : x = y := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n', hn', rfl⟩ := hy
  rw [show n = n' from funext fun s => ((hn' s).2 _).1 (((hn s).2 _).2 rfl)]

section Family

variable {R : Type} [CommRing R] {ω : R}

structure IsHomFam (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H} (L : Submodule (𝓞 E) D.La)
    (φ : L → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ a, IsMonHom (φ a)
  add : ∀ a b, φ (a + b) = φ a * φ b
  smul : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s
  lin : ∀ (k : OK H) a, C.act.act k ≫ φ a = φ a ≫ t.act.act (k : 𝓞 E)

structure IsPolFam (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H} (L : Submodule (𝓞 E) D.La) (ε : ℤˣ)
    (φ : L → (C.P.A ⟶ t.G)) : Prop extends IsHomFam C t L φ where
  lam : ∃ h, IsKForm D ε h ∧ ∀ a b : L, LamEq t.PP.L (φ a) (φ b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A)

theorem isPolFam_of_isTen {C : Ell H R ω} {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H} (hh : IsKForm D ε h)
    {T : PAT H (Sp R)} (X : IsTen C D h T) : IsPolFam C T.t (⊤ : Submodule (𝓞 E) D.La) ε fun a => X.ten.tmul a.1 :=
  { hom := fun _ => inferInstance
    add := fun a b => X.ten.tmul_add a.1 b.1
    smul := fun s a => X.lin s a.1
    lin := fun k a => (X.ten.isLinearHom_tmul a.1).comm k
    lam := ⟨h, hh, fun a b => X.lam a.1 b.1⟩ }

end Family

structure IsExp {S : Scheme.{0}} (t : SAB H S) (y : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (ex : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop where
  period : IsPeriod D ty Pe
  add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ Pe.range
  lin : ∀ (a : 𝓞 E) z, ex (fun k => ty k (a : E) * z k) = ex z ≫ t.act.act a
  hol : IsHolTo Set.univ fun z => (ex z).left
  weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
    Out.WeilIs t.G t.PP.L k (ex ((k : ℂ)⁻¹ • Pe a)) (ex ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

theorem isHolTo_comp {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} {c : V → W} (hc : Differentiable ℂ c) (hB : ∀ z, c z ∈ B)
    (h : IsHolTo B y) : IsHolTo Set.univ fun z => y (c z) := fun U f => by
  obtain ⟨h₁, h₂⟩ := h U f
  refine ⟨?_, h₂.comp hc.differentiableOn fun z hz => ⟨hB z, hz.2⟩⟩
  convert h₁.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨hB z, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem isExp_of_familyUnif {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) : IsExp Xo.univ.t (FU.u i Pe) (FU.Di i) ty Pe (FU.ex i Pe) := by
  have h₀ : IsHolPeriods (FU.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => Pe) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h₁ := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ h₀).2
  have hc : Differentiable ℂ fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z) := by fun_prop
  have h₂ := isHolTo_comp hc (B := Set.univ ×ˢ Set.univ) (fun _ => Set.mk_mem_prod trivial trivial) h₁
  refine ⟨hP, FU.ex_add i Pe hP, FU.ex_onto i Pe hP, FU.ex_ker i Pe hP, FU.ex_lin i Pe hP, ?_, ?_⟩
  · simpa only [] using h₂
  · exact FU.ex_weil i Pe hP

def IsFamExp {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H}
    (L : Submodule (𝓞 E) D.La) (φ : L → (C.P.A ⟶ t.G)) (s : R →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (e : ℂ → (Over.mk (spMap s) ⟶ C.P.A))
    (ex : (Fin g → ℂ) → (Over.mk (spMap s) ⟶ t.G)) : Prop :=
  IsCurveExp C s e ∧ IsExp t (spMap s) D ty Pe ex ∧ ∀ (a : L) (z : ℂ), e z ≫ φ a = ex (z • Pe a)

def typeVal (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

structure LatData {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (Λ : ℝ) where
  A : Bool → Datum H
  sigP : (A true).p = 1 ∧ (A true).q = 0
  sigM : (A false).p = 0 ∧ (A false).q = 1
  ψ : ∀ j : Fin D.p ⊕ Fin D.q, (A j.isLeft).La →ₗ[𝓞 E] D.La
  hh : Fin D.p ⊕ Fin D.q → 𝓞 E
  pure : ∀ j a, ψ j a ∈ PureType.lat hP (typeVal H j.isLeft)
  form : ∀ j a b, D.EF (ψ j a) (ψ j b) = (A j.isLeft).EF (hh j • a) b
  span : ∀ x : D.La, ∃ N : ℕ, 0 < N ∧ N • x ∈ ⨆ j, LinearMap.range (ψ j)
  one_le : 1 ≤ Λ
  bound : ∀ j (τ : E →+* ℂ), ‖τ (hh j : E)‖ ≤ Λ ^ 2

namespace LatData

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} {Λ : ℝ}

def IsConj (X : LatData hP Λ) : Prop :=
  ∃ κ : (X.A true).La ≃ₗ[𝓞 E] (X.A false).La, ∀ a b, (X.A false).EF (κ a) (κ b) = -(X.A true).EF a b

def IsRealisedBy (X : LatData hP Λ) {K : Type} [Field K] [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ}
    (Y : CMObj H K ρ σ₁ D.p D.q) : Prop :=
  σ₁ (ρ : K) = H.rt0 ∧ Y.hh = X.hh ∧
  ∃ (g₁ : Bool → ℕ) (ty₁ : ∀ b, Fin (g₁ b) → (E →+* ℂ)) (Pe₁ : ∀ b, (X.A b).La →+ (Fin (g₁ b) → ℂ))
    (ex₁ : ∀ b, (Fin (g₁ b) → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (Y.A b).t.G))
    (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ Y.B.t.G)),
    (∀ b, IsExp (Y.A b).t _ (X.A b) (ty₁ b) (Pe₁ b) (ex₁ b)) ∧ IsExp Y.B.t _ D ty Pe ex ∧
    ∀ j, ∃ M : (Fin (g₁ j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ a, M (Pe₁ _ a) = Pe (X.ψ j a)) ∧
      ∀ z, ex₁ _ z ≫ Y.φ j = ex (M z)

end LatData

theorem nonempty_latData {D D' : Datum H} (hp : D.p = 1) (hq : D.q = 0) (h' : D'.p = 0 ∧ D'.q = 1) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H 1 0 ty) {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) :
    Nonempty (LatData hP 1) := by
  have he : IsEmpty (Fin D.q) := hq ▸ inferInstanceAs (IsEmpty (Fin 0))
  refine ⟨⟨fun b => match b with | true => D | false => D', ⟨hp, hq⟩, h',
    fun j => match j with | .inl _ => LinearMap.id | .inr k => he.elim k, fun _ => 1, ?_, ?_, ?_, le_rfl, by simp⟩⟩
  · rintro (j | k) a
    · show _ ∈ PureType.lat hP H.rt0
      rw [PureType.lat_eq_top hP hty]; trivial
    · exact he.elim k
  · rintro (j | k) a b
    · rw [one_smul]; rfl
    · exact he.elim k
  · intro x
    refine ⟨1, one_pos, Submodule.mem_iSup_of_mem (.inl ⟨0, by omega⟩) ⟨x, (one_smul _ x).symm⟩⟩

section Degree

variable {K : Type} [Field K] [NumberField K]

def IsDegDe (x : KeyIn K) (δ : ℝ) : Prop :=
  ∃ (oa : HeightOneSpectrum (𝓞 K) → ℤ) (nth : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ a M, KeyPow.IsLocalModel x 𝔭 a M ∧ 𝔭.valuation K a = WithZero.exp (-oa 𝔭)) ∧
    (Function.support oa).Finite ∧
    (∀ σ, 0 < nth σ ∧ ∃ (x' : KeyIn ℂ) (nη : ℝ), KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) nη) ∧
    δ = (∑ᶠ 𝔭, (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) + (1 / 2) * ∑ σ, Real.log (nth σ)) /
      Module.finrank ℚ K

def IsDegDeOf (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) : Prop :=
  ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left), IsPolFibre (algebraMap (𝓞 K) K) P x.P φ ∧ IsDegDe x δ

theorem deg_formula (h : KeyDegreeSt) (x : KeyIn K) (oa od : HeightOneSpectrum (𝓞 K) → ℤ) (nth nη : (K →+* ℂ) → ℝ)
    (h₁ : ∀ 𝔭, ∃ a M, KeyPow.IsLocalModel x 𝔭 a M ∧
      𝔭.valuation K a = WithZero.exp (-oa 𝔭) ∧ 𝔭.valuation K M.det = WithZero.exp (-od 𝔭))
    (h₂ : ∀ σ : K →+* ℂ, ∃ x' : KeyIn ℂ, KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) (nη σ))
    (ha : (Function.support oa).Finite) (hd : (Function.support od).Finite) :
    IsDegDe x ((1 / 2) * ((∑ᶠ 𝔭, (od 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) -
      (1 / 2) * ∑ σ, Real.log (nη σ)) / Module.finrank ℚ K) + x.P.g / 4 * Real.log (2 * Real.pi)) := by
  obtain ⟨hpos, -, e⟩ := h K x oa od nth nη h₁ h₂
  refine ⟨oa, nth, fun 𝔭 => ?_, ha, fun σ => ⟨(hpos σ).1, ?_⟩, ?_⟩
  · obtain ⟨a, M, p, q, -⟩ := h₁ 𝔭; exact ⟨a, M, p, q⟩
  · obtain ⟨x', p, q⟩ := h₂ σ; exact ⟨x', _, p, q⟩
  have hf : ∀ (c : HeightOneSpectrum (𝓞 K) → ℤ) (r : ℝ), (Function.support c).Finite →
      (Function.support fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
        r * ((c 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal))).Finite :=
    fun c r hc => hc.subset fun 𝔭 h𝔭 h0 => h𝔭 (by simp [h0])
  have e2 : ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), ((8 * oa 𝔭 - 4 * od 𝔭 : ℤ) : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) =
      8 * ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) -
        4 * ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), (od 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
    rw [mul_finsum, mul_finsum, ← finsum_sub_distrib (hf oa 8 ha) (hf od 4 hd)]
    exact finsum_congr fun 𝔭 => by push_cast; ring
  rw [e2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  field_simp
  linarith

end Degree

end GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter
end
