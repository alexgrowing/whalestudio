import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg)

noncomputable section

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

structure IsPreFamily (x : (Σ k, J k) → Ω) (p : ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O)
    (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
    (RC : Subalgebra O C), IsTestPt p (chartRing O (mseg x) c) RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      ((D c).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

def coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) : AddSubgroup (Fin m → Ω) :=
  ⨅ (q : Cpt ξ) (_ : InChart ξ (mseg y) c q) (_ : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q),
    (L q).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom

def IsFamilyOf (y : (Σ k, J k) → Ω) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) (L L' Lc Lc' : Sg → Lat ξ V)
    (b : ∀ τ, Fin (r τ) → V) (bc : ∀ τ, Fin (s τ) → V) : Prop :=
  ∀ c, mseg y c ≠ 0 → ∀ τ, (D c).lie τ = coordLat O y (L τ) (b τ) c ∧ (D c).W τ = coordLat O y (L' τ) (b τ) c ∧
    (D c).om τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc τ) (bc τ) c) ∧
    (D c).omHT τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc' τ) (bc τ) c)

def FamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (_hpos : 0 < D.p + D.q := by assumption),
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ t₀, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H)
        (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (w : O)
        (σ : Sg → F →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap),
        t₀ ∈ Set.range e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ IsPreFamily O y p w σ φ' Df ∧
        IsFamilyOf O y Df (fun τ => 𝔐.dR (e τ)) (fun τ => 𝔐.HT p (e τ)) (fun τ => 𝔐.dR (e τ).swap)
          (fun τ => 𝔐.HT p (e τ).swap) (fun τ => b (e τ)) fun τ => b (e τ).swap

def WholeFamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (_hpos : 0 < D.p + D.q := by assumption) (g : ℕ) (b : Module.Basis (Fin g) Ω 𝔐.Li), ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∃ (w : O) (σ : Unit → ZMod p →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω (ZMod p) (g + g) Unit (fun _ => g) fun _ => g),
        IsPreFamily O y p w σ 1 Df ∧
        IsFamilyOf O y Df (fun _ => 𝔐.M.lat) (fun _ => 𝔐.wholeW (p ^ 𝔐.R p)) (fun _ => 𝔐.M.lat)
          (fun _ => 𝔐.wholeW (p ^ 𝔐.R p)) (fun _ => b) fun _ => b

namespace Fam

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem mem_coordLat_iff (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) (a : Fin m → Ω) :
    a ∈ coordLat O y L b c ↔ ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) →
      ∑ i, a i • b i ∈ L q := by
  simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem coordLat_mono (y : (Σ k, J k) → Ω) {L L' : Lat ξ V} (h : ∀ q, L q ≤ L' q) {m : ℕ} (b : Fin m → V)
    (c : ∀ k, J k) : coordLat O y L b c ≤ coordLat O y L' b c := fun a ha =>
  (mem_coordLat_iff O y L' b c a).2 fun q h1 h2 => h q ((mem_coordLat_iff O y L b c a).1 ha q h1 h2)

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem chartRing_le_regAt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) (h1 : InChart ξ (mseg y) c q)
    (h2 : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h1.2 j
  | algebraMap o => exact h2 o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem smul_mem_coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) {t : Ω}
    (ht : t ∈ chartRing O (mseg y) c) {a : Fin m → Ω} (ha : a ∈ coordLat O y L b c) :
    t • a ∈ coordLat O y L b c := by
  rw [mem_coordLat_iff] at ha ⊢
  intro q h1 h2
  have := (L q).smul_mem ⟨t, chartRing_le_regAt O y c q h1 h2 ht⟩ (ha q h1 h2)
  have e : ∑ i, (t • a) i • b i = t • ∑ i, a i • b i := by simp [Finset.smul_sum, mul_smul]
  rw [e]; exact this

def unitLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Lat ξ Ω := fun q => Submodule.span (regAt ξ q) {1}

theorem mem_unitLat (q : Cpt ξ) (a : Ω) : a ∈ unitLat ξ q ↔ a ∈ regAt ξ q := by
  rw [unitLat, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    simp [Subring.smul_def]
  · intro h
    exact ⟨⟨a, h⟩, by simp [Subring.smul_def]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem mem_coordLat_unitLat (y : (Σ k, J k) → Ω) (h : CoordTie O ξ (mseg y)) (c : ∀ k, J k) (hc : mseg y c ≠ 0)
    (t : Ω) (a : Fin 1 → Ω) :
    a ∈ coordLat O y (unitLat ξ) (fun _ : Fin 1 => t) c ↔ a 0 * t ∈ chartRing O (mseg y) c := by
  rw [mem_coordLat_iff]
  simp only [Fin.sum_univ_one, smul_eq_mul, mem_unitLat]
  refine ⟨fun H => (h.ring c hc _).2 fun q hq => H q hq fun o => ?_,
    fun H q h1 h2 => chartRing_le_regAt O y c q h1 h2 H⟩
  exact (h.ring c hc _).1 (Subalgebra.algebraMap_mem _ o) q hq

omit [∀ k, Fintype (J k)] in

theorem isPreFamily_of_lattice_family_two (x : (Σ k, J k) → Ω) (p : ℕ) (w : O)
    (σ : Sg → ZMod 2 →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg)
    (D : (∀ k, J k) → LieLatticeData Ω (ZMod 2) n Sg r s) (h : IsLatticeFamily O x p w (fun _ a => (a.val : O)) φ D) :
    IsPreFamily O x p w σ φ D := by
  refine ⟨h.famM, h.fam, ⟨h.char.1, h.char.2.1, h.char.2.2.1⟩, h.base, fun c hc C _ _ _ _ RC hT χ _ => ?_⟩
  have := h.test c hc C RC hT
  rw [← IsScalarTower.algebraMap_apply] at this
  convert this using 3 with τ a
  have h1 : (1 : ZMod 2).val = 1 := by decide
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simp
  · simp [h1]

omit [∀ k, Fintype (J k)] in

theorem not_isPreFamily_of_irreducible (x : (Σ k, J k) → Ω) {p : ℕ} (hp : 3 ≤ p) (hi : Irreducible (p : O)) (w : O)
    (σ : Sg → F →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) :
    ¬ IsPreFamily O x p w σ φ D := by
  intro h
  obtain ⟨u, hu, e⟩ := h.char.2.1
  exact not_irreducible_pow (x := w) (n := p - 1) (by omega) (e ▸ (irreducible_isUnit_mul hu).2 hi)

end Fam

end

end GlobalTheory.CompanionTheory.Ar
