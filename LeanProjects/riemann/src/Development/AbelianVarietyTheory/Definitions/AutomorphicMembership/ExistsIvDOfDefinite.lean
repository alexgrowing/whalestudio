import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.Toroidal

namespace GlobalTheory.LocM

section Inv

structure InvFun (O : Type) [CommRing O] : Type where

  toFun : ∀ n : ℕ, ((Fin n → O) → (Fin n → O) → ℝ) → ℝ

  inv : ∀ (n m : ℕ) (r : (Fin n → O) →ₗ[O] (Fin m → O)), Function.Surjective r →
    ∀ B, toFun n (fun a b => B (r a) (r b)) = toFun m B

  zero : ∀ B, toFun 0 B = 0

namespace InvFun

variable {O : Type} [CommRing O] (φ : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

theorem toFun_pull_eq {n m : ℕ} {r : (Fin n → O) →ₗ[O] X} {s : (Fin m → O) →ₗ[O] X} (hr : Function.Surjective r)
    (hs : Function.Surjective s) (B : X → X → ℝ) :
    φ.toFun n (fun a b => B (r a) (r b)) = φ.toFun m (fun a b => B (s a) (s b)) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property r s hr
  obtain ⟨k, hk⟩ := Module.projective_lifting_property s r hs
  let P : (Fin (n + m) → O) →ₗ[O] (Fin n → O) := LinearMap.funLeft O O (Fin.castAdd m)
  let Q : (Fin (n + m) → O) →ₗ[O] (Fin m → O) := LinearMap.funLeft O O (Fin.natAdd n)
  have h1 : Function.Surjective (P + h ∘ₗ Q) := fun a => ⟨Fin.append a 0, by
    have e : Q (Fin.append a 0) = 0 := by ext i; simp [Q]
    have e' : P (Fin.append a 0) = a := by ext i; simp [P]
    simp [e, e']⟩
  have h2 : Function.Surjective (k ∘ₗ P + Q) := fun a => ⟨Fin.append 0 a, by
    have e : Q (Fin.append 0 a) = a := by ext i; simp [Q]
    have e' : P (Fin.append 0 a) = 0 := by ext i; simp [P]
    simp [e, e']⟩
  rw [← φ.inv _ _ _ h1, ← φ.inv _ _ _ h2]
  have e : ∀ a, r ((P + h ∘ₗ Q) a) = s ((k ∘ₗ P + Q) a) := fun a => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    rw [← LinearMap.comp_apply r h, hh, ← LinearMap.comp_apply s k, hk]
  simp only [e]

variable (X) in

def eval [Module.Finite O X] (B : X → X → ℝ) : ℝ :=
  φ.toFun (Module.Finite.exists_fin' O X).choose fun a b =>
    B ((Module.Finite.exists_fin' O X).choose_spec.choose a) ((Module.Finite.exists_fin' O X).choose_spec.choose b)

theorem eval_eq [Module.Finite O X] {n : ℕ} {r : (Fin n → O) →ₗ[O] X} (hr : Function.Surjective r) (B : X → X → ℝ) :
    φ.eval X B = φ.toFun n fun a b => B (r a) (r b) :=
  φ.toFun_pull_eq (Module.Finite.exists_fin' O X).choose_spec.choose_spec hr B

theorem eval_pi (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : φ.eval (Fin n → O) B = φ.toFun n B :=
  φ.eval_eq (r := LinearMap.id) Function.surjective_id B

theorem eval_comp [Module.Finite O X] [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r)
    (B : X₁ → X₁ → ℝ) : φ.eval X (fun a b => B (r a) (r b)) = φ.eval X₁ B := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hs, φ.eval_eq (r := r ∘ₗ s) (hr.comp hs)]
  rfl

theorem eval_equiv [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) (B : X₁ → X₁ → ℝ) :
    φ.eval X (fun a b => B (e a) (e b)) = φ.eval X₁ B := φ.eval_comp (r := e.toLinearMap) e.surjective B

theorem eval_of_subsingleton [Module.Finite O X] [Subsingleton X] (B : X → X → ℝ) : φ.eval X B = 0 := by
  rw [φ.eval_eq (n := 0) (r := 0) (fun x => ⟨0, Subsingleton.elim _ _⟩), φ.zero]

variable (O) in

def minVal : InvFun O where
  toFun _ B := sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0}
  inv n m r hr B := by
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, map_zero]
    exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩
  zero B := by
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨y, h⟩, h'⟩ => h' (by rw [← h, Subsingleton.elim y 0])

theorem minVal_three : (minVal ℤ).eval ℤ (fun a b => 3 * a * b) = 3 := by
  rw [(minVal ℤ).eval_eq (n := 1) (r := LinearMap.proj 0) fun x => ⟨fun _ => x, rfl⟩]
  refine IsLeast.csInf_eq ⟨⟨⟨fun _ => 1, by simp⟩, by simp⟩, ?_⟩
  rintro x ⟨⟨y, rfl⟩, h⟩
  have h0 : y 0 ≠ 0 := fun e => h (by simp [e])
  have : (1 : ℝ) ≤ (y 0 : ℝ) * y 0 := by exact_mod_cast (show 1 ≤ y 0 * y 0 from mul_self_pos.2 h0)
  simp only [LinearMap.proj_apply]
  nlinarith

def evalZ [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) : ℝ := φ.eval X fun a b => (β a b : ℝ)

def LinearOn [Module.Finite O X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → φ.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φ.evalZ (γ i)

variable {φ} in

theorem LinearOn.eval_eq_sum [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : φ.LinearOn γ) {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ → X₁ → ℝ} {c : Fin m → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ a b, B (r a) (r b) = ∑ i, c i * (γ i a b : ℝ)) :
    φ.eval X₁ B = ∑ i, c i * φ.evalZ (γ i) := by
  rw [← φ.eval_comp hr, ← h c hc]
  simp only [hB]

end InvFun

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {m : ℕ}

def IsPiece (N : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Prop :=
  (∀ i, (ℓ (γ i) : ℝ) = N * φ.evalZ (γ i)) ∧
    ∀ β ∈ levelForms H 1 X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β

def IsStrictAt (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ IsPiece H φ N γ ℓ ∧
    ∀ β ∈ levelForms H 1 X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i

variable {H φ} in

theorem IsPiece.exists_eq_mul {N M : ℕ} (hM : M ≠ 0) {γ : Fin m → levelForms H M X}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h : IsPiece H φ N (fun i => γ i) ℓ) (i : Fin m) :
    ∃ z : ℤ, N * φ.evalZ (γ i : LinearMap.BilinForm ℤ X) = M * z := by
  obtain ⟨δ, -, e⟩ := (mem_levelForms_iff_smul hM).1 (γ i).2
  exact ⟨ℓ δ, by rw [← h.1 i]; simp only [e, map_smul, smul_eq_mul]; push_cast; rfl⟩

end Inv

section Ord

variable {R : Type} [CommRing R]

def OrdGe (h : R) (i : ℚ) (n : ℕ) (I₁ I₂ : Ideal R) : Prop :=
  Ideal.span {h ^ (i.den * n)} * (I₂ ^ i.num.toNat * I₁ ^ (-i.num).toNat) ≤ I₁ ^ i.num.toNat * I₂ ^ (-i.num).toNat

theorem ordGe_zero (h : R) (n : ℕ) (I₁ I₂ : Ideal R) : OrdGe h 0 n I₁ I₂ := by simp [OrdGe]

theorem OrdGe.map {S : Type} [CommRing S] (f : R →+* S) {h : R} {i : ℚ} {n : ℕ} {I₁ I₂ : Ideal R}
    (H : OrdGe h i n I₁ I₂) : OrdGe (f h) i n (I₁.map f) (I₂.map f) := by
  have := Ideal.map_mono (f := f) H
  simpa only [OrdGe, Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_pow] using this

theorem ordGe_span_iff {h g₁ g₂ : R} {i : ℚ} {n : ℕ} : OrdGe h i n (Ideal.span {g₁}) (Ideal.span {g₂}) ↔
    g₁ ^ i.num.toNat * g₂ ^ (-i.num).toNat ∣ h ^ (i.den * n) * (g₂ ^ i.num.toNat * g₁ ^ (-i.num).toNat) := by
  simp only [OrdGe, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_le_span_singleton]

example : OrdGe (8 : ℤ) 3 1 (Ideal.span {2}) (Ideal.span {1}) ∧ ¬ OrdGe (8 : ℤ) 4 1 (Ideal.span {2}) (Ideal.span {1}) ∧
    OrdGe (8 : ℤ) 3 2 (Ideal.span {8}) (Ideal.span {2}) ∧ ¬ OrdGe (8 : ℤ) 4 2 (Ideal.span {8}) (Ideal.span {2}) := by
  simp only [ordGe_span_iff]
  decide

example : OrdGe (2 : ℤ) (-1) 1 (Ideal.span {1}) (Ideal.span {2}) ∧
    ¬ OrdGe (1 : ℤ) (-1) 1 (Ideal.span {1}) (Ideal.span {2}) := by
  simp only [ordGe_span_iff]
  decide

end Ord

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

instance finite_pelUnif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    Module.Finite (𝓞 E) P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _

theorem Mdl.isOpen_opn (Z : Mdl Y i₀) : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen

def Mdl.opnO (Z : Mdl Y i₀) : Z.X.Opens := ⟨Z.opn, Z.isOpen_opn⟩

def Mdl.bd (Z : Mdl Y i₀) : Closeds Z.X := ⟨Z.opnᶜ, Z.isOpen_opn.isClosed_compl⟩

def idlAlong {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) : Ideal R :=
  (FinalTheorems.stalkId I (ξ (closedPoint R))).map (Scheme.stalkClosedPointTo ξ).hom

theorem stalkId_top {X : Scheme.{0}} (x : X) : FinalTheorems.stalkId (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  refine top_le_iff.1 (le_trans ?_ (le_iSup₂_of_le (⟨U, hU⟩ : X.affineOpens) hx le_rfl))
  simp [Ideal.map_top]

theorem idlAlong_top {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) : idlAlong ⊤ ξ = ⊤ := by
  rw [idlAlong, stalkId_top, Ideal.map_top]

def Mdl.IsToricChart (Z : Mdl Y i₀) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ Z.X)
    {t : SAB H (Sp (ChartRing k m d))} (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H Z.i.l.M' P.D.toPre.X) : Prop :=
  ξ (closedPoint _) ∈ Z.genO ∧
  IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
  idlAlong (Scheme.IdealSheafData.vanishingIdeal Z.bd) ξ = Ideal.span {∏ i, bdParam k m d i} ∧
  (∀ q : Sp (ChartRing k m d), ξ q ∈ Z.bd ↔ ∏ i, bdParam k m d i ∈ q.asIdeal) ∧
  Nonempty (SABMap t (Y Z.i).t (ξ ≫ Z.π)) ∧ P.TorsionIso ∧
  IsMonomial P.D.toPre (bdParam k m d) (fun i => γ i) ∧ IsPartOfBasis γ

structure FanFun (Y : LocalSystem Xo p W) (i₀ i : Idx H p) : Type where

  Z : Mdl Y i₀

  lvl : Z.i = i

  noFlag : ∀ σ, Z.ty σ = ∅

  φ : InvFun (𝓞 E)

  n : ℕ

  n_pos : 0 < n

  D₁ : Z.Idl

  D₂ : Z.Idl

  chart : ∀ x ∈ Z.genO, x ∈ Z.bd → ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ Z.X)
    (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H Z.i.l.M' P.D.toPre.X) (a b : Fin m → ℕ),
    ξ (closedPoint _) = x ∧ Z.IsToricChart ξ P γ ∧ φ.LinearOn (fun i => (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
    idlAlong D₁.1 ξ = Ideal.span {∏ i, bdParam k m d i ^ a i} ∧
    idlAlong D₂.1 ξ = Ideal.span {∏ i, bdParam k m d i ^ b i} ∧
    ∀ i, (a i : ℝ) - b i = n * φ.evalZ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)

def IsCommonMod (Z Z' : Mdl Y i₀) {M : Scheme.{0}} (f : M ⟶ Z.genO.toScheme) (g : M ⟶ Z'.X) : Prop :=
  IsNormalScheme M ∧ IsProper f ∧ IsIso ((f ≫ Z.genO.ι) ∣_ Z.opnO) ∧ Dense ((f ≫ Z.genO.ι) ⁻¹' Z.opn) ∧ Corr Z Z' ∧
    ∀ (k : Type) [Field k] (w : Sp k ⟶ M), Set.range (w ≫ f ≫ Z.genO.ι) ⊆ Z.opn →
      NatImg Z Z' (w ≫ f ≫ Z.genO.ι) (w ≫ g)

def idlAt {M X : Scheme.{0}} (I : X.IdealSheafData) (g : M ⟶ X) (x : M) : Ideal (M.presheaf.stalk x) :=
  (FinalTheorems.stalkId I (g x)).map (g.stalkMap x).hom

def FanFun.DivGe {i₁ : Idx H p} (φ : FanFun Y i₀ i₁) (Z : Mdl Y i₀) (F : Z.X.Modules) (et : Γ(F, Z.genO)) (i : ℚ) : Prop :=
  ∃ (M : Scheme.{0}) (f : M ⟶ Z.genO.toScheme) (g : M ⟶ φ.Z.X), IsCommonMod Z φ.Z f g ∧
    ∀ (x : M) (U : Z.X.Opens) (_ : IsAffineOpen U) (hU : U ≤ Z.genO) (hx : (f ≫ Z.genO.ι) x ∈ U)
      (lam : Γ(F, U) →ₗ[Γ(Z.X, U)] Γ(Z.X, U)),
      OrdGe (((f ≫ Z.genO.ι).stalkMap x).hom ((Z.X.presheaf.germ U _ hx).hom
        (lam ((F.presheaf.map (homOfLE hU).op).hom et)))) i φ.n (idlAt φ.D₁.1 g x) (idlAt φ.D₂.1 g x)

theorem FanFun.divGe_zero_iff {i₁ : Idx H p} (φ : FanFun Y i₀ i₁) (Z : Mdl Y i₀) (F : Z.X.Modules) (et : Γ(F, Z.genO)) :
    φ.DivGe Z F et 0 ↔ ∃ (M : Scheme.{0}) (f : M ⟶ Z.genO.toScheme) (g : M ⟶ φ.Z.X), IsCommonMod Z φ.Z f g :=
  ⟨fun ⟨M, f, g, h, _⟩ => ⟨M, f, g, h⟩, fun ⟨M, f, g, h⟩ => ⟨M, f, g, h, fun _ _ _ _ _ _ => ordGe_zero _ _ _ _⟩⟩

def Mdl.unitIdl (Z : Mdl Y i₀) : Z.Idl := ⟨⊤, fun x hx => by
  rw [Scheme.IdealSheafData.support_top] at hx
  exact (show x ∈ (∅ : Set Z.X) from hx).elim⟩

structure PolData (Y : LocalSystem Xo p W) (i₀ i : Idx H p) : Type where

  Z : Mdl Y i₀

  lvl : Z.i = i

  noFlag : ∀ σ, Z.ty σ = ∅

  φ : InvFun (𝓞 E)

  m' : ℕ

  m'_pos : 0 < m'

  D : Z.Idl

  chart : ∀ x ∈ Z.genO, x ∈ Z.bd → ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ Z.X)
    (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H Z.i.l.M' P.D.toPre.X) (a : Fin m → ℕ),
    ξ (closedPoint _) = x ∧ Z.IsToricChart ξ P γ ∧ φ.LinearOn (fun i => (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
    (∃ ℓ, IsPiece H φ m' (fun i => (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ℓ) ∧
    IsStrictAt H φ (fun i => (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
    idlAlong D.1 ξ = Ideal.span {∏ i, bdParam k m d i ^ a i} ∧
    ∀ i, (a i : ℝ) = m' * φ.evalZ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)

namespace PolData

variable {i : Idx H p} (d : PolData Y i₀ i)

def toFanFun : FanFun Y i₀ i where
  Z := d.Z
  lvl := d.lvl
  noFlag := d.noFlag
  φ := d.φ
  n := d.m'
  n_pos := d.m'_pos
  D₁ := d.D
  D₂ := d.Z.unitIdl
  chart x hx hb := by
    obtain ⟨k, _, m, e, ξ, t, P, γ, a, h1, h2, h3, -, -, h6, h7⟩ := d.chart x hx hb
    exact ⟨k, _, m, e, ξ, t, P, γ, a, 0, h1, h2, h3, h6, (idlAlong_top ξ).trans (by simp), fun j => by simpa using h7 j⟩

def π : d.Z.X ⟶ (Y i).X := d.Z.π ≫ eqToHom (congrArg (fun j => (Y j).X) d.lvl)

theorem π_mem_iff (x : d.Z.X) : d.π x ∈ Set.range (Y i).j ↔ x ∈ d.Z.opn := by
  obtain ⟨Z, rfl, _⟩ := d
  simp [π, Pre.opn]

end PolData

instance Mdl.isProper_π (Z : Mdl Y i₀) : IsProper Z.π := by
  have := isProper_toroidalModel_structureMap (Y Z.i)
  have : IsProper (Z.π ≫ (Y Z.i).s) := by
    rw [Z.π_s, Pre.s]
    have := isProper_str (Z.i.c.V W) Z.n
    infer_instance
  exact IsProper.of_comp Z.π (Y Z.i).s

namespace PolData

variable {Z₀ : Mdl Y i₀} [IsIso Z₀.π] (d : PolData Y i₀ Z₀.i)

def ρ : d.Z.genO.toScheme ⟶ Z₀.X := d.Z.genO.ι ≫ d.π ≫ inv Z₀.π

@[reassoc] theorem ρ_π : d.ρ ≫ Z₀.π = d.Z.genO.ι ≫ d.π := by simp [ρ]

instance quasiCompact_ρ : QuasiCompact d.ρ := by
  have : IsAffineHom d.Z.genO.ι := by unfold Mdl.genO; infer_instance
  unfold ρ π
  infer_instance

theorem ρ_mem_opn_iff (x : d.Z.genO.toScheme) : d.ρ x ∈ Z₀.opn ↔ d.Z.genO.ι x ∈ d.Z.opn := by
  rw [← d.π_mem_iff, ← Scheme.Hom.comp_apply, ← d.ρ_π, Scheme.Hom.comp_apply]
  rfl

def idealQ : d.Z.genO.toScheme.IdealSheafData := d.D.1.comap d.Z.genO.ι

def jIdl : Z₀.Idl :=
  ⟨d.idealQ.map d.ρ, fun x hx => by
    rw [Scheme.IdealSheafData.support_map] at hx
    refine closure_minimal (t := Z₀.opnᶜ) ?_ Z₀.isOpen_opn.isClosed_compl hx
    rintro _ ⟨y, hy, rfl⟩ h
    rw [idealQ, Scheme.IdealSheafData.support_comap] at hy
    exact d.D.2 _ hy ((d.ρ_mem_opn_iff y).1 h)⟩

theorem le_jIdl_iff (I : Z₀.X.IdealSheafData) : I ≤ d.jIdl.1 ↔ I.comap d.ρ ≤ d.idealQ :=
  Scheme.IdealSheafData.le_map_iff_comap_le

theorem jIdl_eq_map_comap (ρQ : d.Z.genO.toScheme ⟶ Z₀.genO.toScheme) (h : ρQ ≫ Z₀.genO.ι = d.ρ) :
    d.jIdl.1 = (d.idealQ.map ρQ).map Z₀.genO.ι := by
  rw [← Scheme.IdealSheafData.map_comp, h]; rfl

end PolData

def PolData.ofNoBoundary (Z : Mdl Y i₀) (h : ∀ σ, Z.ty σ = ∅) (hb : ∀ x ∈ Z.genO, x ∈ Z.opn) (φ : InvFun (𝓞 E)) :
    PolData Y i₀ Z.i where
  Z := Z
  lvl := rfl
  noFlag := h
  φ := φ
  m' := 1
  m'_pos := one_pos
  D := Z.unitIdl
  chart x hx hx' := (hx' (hb x hx)).elim

theorem PolData.jIdl_ofNoBoundary (Z : Mdl Y i₀) [IsIso Z.π] (h : ∀ σ, Z.ty σ = ∅) (hb : ∀ x ∈ Z.genO, x ∈ Z.opn)
    (φ : InvFun (𝓞 E)) : (PolData.ofNoBoundary Z h hb φ).jIdl.1 = ⊤ :=
  top_le_iff.1 ((PolData.le_jIdl_iff _ _).2 (by
    rw [Scheme.IdealSheafData.comap_top]
    exact (Scheme.IdealSheafData.comap_top _).ge))

theorem Mdl.mem_range_of_mem_genO (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : x ∈ Z.genO) :
    Z.π x ∈ Set.range (genι (Y Z.i)) := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  have hp' : (p : Z.i.c.F) ∈ (Z.i.c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp hp').1
  have h1 : Z.s x ∈ (Sp (Z.i.c.V W)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Z.i.c.V W))).inv (p : Z.i.c.V W)) := by
    refine (Scheme.Hom.mem_preimage Z.s).1 ?_
    rw [Scheme.preimage_basicOpen_top, map_natCast, map_natCast]
    exact hx
  rw [basicOpen_eq_of_affine] at h1
  have h2 : (Z.s x).asIdeal = ⊥ := by
    by_contra h
    have hm := eq_maximalIdeal ((Z.s x).isPrime.isMaximal h)
    refine h1 ?_
    rw [hm, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hp'
  rw [Scheme.Pullback.range_fst]
  refine ⟨closedPoint _, ?_⟩
  rw [← Scheme.Hom.comp_apply, Z.π_s]
  refine PrimeSpectrum.ext (h2 ▸ ?_)
  change Ideal.comap (Z.i.c.V W).subtype (maximalIdeal _) = ⊥
  rw [maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ Subtype.val_injective

theorem Mdl.mem_opn_of_dim_eq_zero (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (h : Dw.dim = 0) (Z : Mdl Y i₀) :
    ∀ x ∈ Z.genO, x ∈ Z.opn := fun x hx => by
  obtain ⟨y, hy⟩ := Z.mem_range_of_mem_genO hp hW hx
  obtain ⟨z, rfl⟩ := surjective_jQ_of_dim_eq_zero (Y Z.i) h y
  exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans hy⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev At.PL (ct : At S κ p) : Type := FanFun ct.Y ⟨κ.l, κ.c, κ.good p ct.hp⟩ ct.Xm.i

def At.phiAt (ct : At S κ p) (φ : ct.PL) {Z : ct.Mdl} (y : ct.Pt Z) : ℝ := φ.φ.eval (ct.Ylat y) (ct.dat y).beta

abbrev At.IvD (ct : At S κ p) (b : Option ℕ) : Type := PolData ct.Y ⟨κ.l, κ.c, κ.good p ct.hp⟩ (ct.B.X b).i

def At.jIdl (ct : At S κ p) (b : Option ℕ) (d : ct.IvD b) : ct.Idl (ct.B.X b) :=
  haveI := ct.B.iso b
  d.jIdl

theorem At.phiAt_eq_sum (ct : At S κ p) (φ : ct.PL) {Z : ct.Mdl} (y : ct.Pt Z) {X : Type} [AddCommGroup X]
    [Module (𝓞 D.host.E) X] [Module.Finite (𝓞 D.host.E) X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : φ.φ.LinearOn γ) {r : X →ₗ[𝓞 D.host.E] ct.Ylat y} (hr : Function.Surjective r) {c : Fin m → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ a b, (ct.dat y).beta (r a) (r b) = ∑ i, c i * (γ i a b : ℝ)) :
    ct.phiAt φ y = ∑ i, c i * φ.φ.evalZ (γ i) := h.eval_eq_sum hr hc hB

theorem At.phiAt_congr (ct : At S κ p) (φ : ct.PL) {Z Z' : ct.Mdl} (y : ct.Pt Z) (y' : ct.Pt Z')
    (e : ct.Ylat y ≃ₗ[𝓞 D.host.E] ct.Ylat y') (h : ∀ a b, (ct.dat y').beta (e a) (e b) = (ct.dat y).beta a b) :
    ct.phiAt φ y = ct.phiAt φ y' := by
  rw [At.phiAt, At.phiAt, ← φ.φ.eval_equiv e]
  simp only [h]

theorem At.exists_IvD_of_definite (ct : At S κ p) (h : S.Dw.p = 0 ∨ S.Dw.q = 0) (b : Option ℕ) :
    ∃ d : ct.IvD b, (ct.jIdl b d).1 = ⊤ :=
  haveI := ct.B.iso b
  ⟨_, PolData.jIdl_ofNoBoundary _ (ct.B.ty b) (Mdl.mem_opn_of_dim_eq_zero ct.hp.ne_zero ct.hW
    (by rcases h with h | h <;> simp [Datum.dim, h]) _) (InvFun.minVal _)⟩

def At.IvD.toPL {ct : At S κ p} (d : ct.IvD none) : ct.PL := PolData.toFanFun d

def torTrue (ct : At S κ p) : TorSt ct where
  PL := ct.PL
  phiAt φ _ y := ct.phiAt φ y
  phiAt_zero φ _ _ _ := φ.φ.eval_of_subsingleton _
  divGe {Z} F et i φ := φ.DivGe Z F.toMod et i
  IvD := ct.IvD
  jIdl := ct.jIdl

end GlobalTheory.LocM
