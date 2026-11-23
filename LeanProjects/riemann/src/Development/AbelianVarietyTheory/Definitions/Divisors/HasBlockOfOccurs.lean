import Mathlib
import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.LocalToGlobal.Divisibility.RowLat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal

namespace GlobalTheory.ExpFrame

section Algebra

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def grp (g : ι → GL (Fin N) O) : Module.End O (NablaT O N lam) :=
  RealLocalDeltaNabla.nablaRep O (fun _ => N) (fun _ => N) (fun τ => res N (lam τ)) g

def IsProj (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) : Prop :=
  ∀ (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O) →
    a (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)

def alg : Subalgebra O (Module.End O (NablaT O N lam)) :=
  Algebra.adjoin O (Set.range (grp O N lam) ∪ {a | ∃ τ w, IsProj O N lam τ w a})

def grpA (g : ι → GL (Fin N) O) : alg O N lam := ⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩

end Algebra

def Linked (l N : ℕ) {ι : Type} (lam mu : ι → ℕ → ℕ) : Prop :=
  ∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧
    (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))

structure Frame (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) : Type 1 where

  O : Type
  [cO : CommRing O]
  [dO : IsDomain O]
  [vO : IsDiscreteValuationRing O]
  [zO : CharZero O]

  emb : O →+* PadicAlgCl l

  G : Type
  [gG : Group G]

  Γ : Subgroup G

  K : Subgroup G

  kap : K →* (ι → GL (Fin N) O)

  chi : K →* Oˣ

  I : Type

  tr : I → Finset G

  cst : I → O

attribute [instance] Frame.cO Frame.dO Frame.vO Frame.zO Frame.gG

namespace Frame

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N)

def Triv (g : F.G) : Prop := ∃ h : g ∈ F.K, F.kap ⟨g, h⟩ = 1 ∧ F.chi ⟨g, h⟩ = 1

structure Ok : Prop where

  ring : Function.Injective F.emb ∧ ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧
    Set.range F.emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}

  classes : ∃ S : Finset F.G, ∀ g, ∃ γ ∈ F.Γ, ∃ s ∈ S, ∃ κ ∈ F.K, g = γ * s * κ

  tame : ∀ g, Finite {γ : F.Γ // g⁻¹ * (γ : F.G) * g ∈ F.K} ∧ ¬ l ∣ Nat.card {γ : F.Γ // g⁻¹ * (γ : F.G) * g ∈ F.K}

  perm : ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
    (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ

  comm : ∀ i j, ∃ σ : F.tr i × F.tr j ≃ F.tr j × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

variable (lam : ι → ℕ → ℕ)

def IsJ (jK : F.K →* alg F.O N lam) : Prop := ∀ κ, jK κ = (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)

abbrev T : Type := MvPolynomial F.I F.O

def IsHecke (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
    [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)] : Prop :=
  (∀ (c : F.O) (f : Forms F.O (A := alg F.O N lam) F.Γ jK W), (C c : F.T) • f = c • f) ∧
  ∀ i (f : Forms F.O (A := alg F.O N lam) F.Γ jK W) (g : F.G), (((X i : F.T) • f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g =
    F.cst i • ∑ s ∈ F.tr i, (f : F.G → W) (g * s)

def setting (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
    [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (m : Ideal F.T) [m.IsPrime] : HidaSetting ι N lam where
  O := F.O
  A := alg F.O N lam
  G := F.G
  Γ := F.Γ
  K := F.K
  jK := jK
  T := F.T
  S := m.primeCompl

def latN : AddSubgroup (NablaT (PadicAlgCl l) N lam) :=
  AddSubgroup.closure {y | ∃ (c : F.O) (x : ∀ τ, dualWeyl (PadicAlgCl l) N N (res N (lam τ))),
    (∀ τ, ∃ x0 ∈ dualWeyl F.O N N (res N (lam τ)), MvPolynomial.map F.emb x0 = x τ) ∧ y = F.emb c • PiTensorProduct.tprod _ x}

def latD : AddSubgroup (NablaT (PadicAlgCl l) N lam) :=
  AddSubgroup.closure {y | ∃ (c : F.O) (x : ∀ τ, dualWeyl (PadicAlgCl l) N N (res N (lam τ))),
    (∀ τ, ∃ x0 ∈ weyl F.O N N le_rfl (res N (lam τ)), MvPolynomial.map F.emb x0 = x τ) ∧ y = F.emb c • PiTensorProduct.tprod _ x}

def IsForm (mu : ι → ℕ → ℕ) (f : F.G → NablaT (PadicAlgCl l) N mu) : Prop :=
  (∀ γ ∈ F.Γ, ∀ g, f (γ * g) = f g) ∧
    ∀ (κ : F.K) g, F.emb (F.chi κ) • grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)) (f (g * κ)) = f g

def IsEigFn (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (f : F.G → NablaT (PadicAlgCl l) N mu) : Prop :=
  f ≠ 0 ∧ F.IsForm mu f ∧ ∀ i g, F.emb (F.cst i) • ∑ s ∈ F.tr i, f (g * s) = θ i • f g

def IsEig (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) : Prop := ∃ f, F.IsEigFn mu θ f

def Over (θ : F.I → PadicAlgCl l) (m : Ideal F.T) : Prop :=
  (∀ i, ‖θ i‖ ≤ 1) ∧ ∀ p : F.T, p ∈ m ↔ ‖eval₂ F.emb θ p‖ < 1

end Frame

section Reading

open Formalism.L2.DIV

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} (B : BlockDat K G0 Pl0)

structure Reads (w : HeightOneSpectrum (𝓞 K)) where

  e0 : K →+* PadicAlgCl l

  ix : F.I → B.Pl × ℕ

  rd : B.S.Forms →ₛₗ[e0] (F.G → NablaT (PadicAlgCl l) N lam)
  place : ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1
  range : ∀ x : 𝓞 K, e0 x ∈ Set.range F.emb
  form : ∀ f, F.IsForm lam (rd f)
  indep : ∀ (n : ℕ) (f : Fin n → B.S.Forms), LinearIndependent K f → LinearIndependent (PadicAlgCl l) fun a => rd (f a)
  hecke : ∀ i f g, rd (B.op (ix i) f) g = F.emb (F.cst i) • ∑ s ∈ F.tr i, rd f (g * s)
  nab : ∀ f : B.S.Forms, (∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c) → ∀ g, rd f g ∈ F.latN lam
  del : ∀ f : B.S.Forms, (∀ g, rd f g ∈ F.latD lam) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ c, s • (f : B.S.Cl → B.S.V) c ∈ B.S.Del c

variable {F lam B}

def Reads.Occurs {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (Z : Submodule K B.S.Forms) (θ : F.I → PadicAlgCl l) : Prop :=
  ∃ f ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z), F.IsEigFn lam θ f

def Reads.HasBlock {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (θ : F.I → PadicAlgCl l) : Prop :=
  ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, θ i = R.e0 (x (R.ix i))

theorem eq_one_of_occurs {L V J : Type} [Field L] [AddCommGroup V] [Module L V] {op : J → Module.End L V} {x : J → L}
    (hx : Formalism.L2.Col.Occurs op x) {j : J} (hj : op j = 1) : x j = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hx
  have h := Formalism.L2.Col.eigAt_le op x j hv
  rw [Module.End.mem_maxGenEigenspace, hj] at h
  obtain ⟨k, hk⟩ := h
  have e : (1 : Module.End L V) - x j • 1 = (1 - x j) • 1 := by rw [sub_smul, one_smul]
  rw [e, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero] at hk
  exact (sub_eq_zero.1 (eq_zero_of_pow_eq_zero (hk.resolve_right hv0))).symm

theorem Reads.hasBlock_of_occurs {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (h0 : ∀ P, B.op (P, 0) = 1) {x : B.Pl × ℕ → K}
    (hx : Formalism.L2.Col.Occurs B.op x) (hb : Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x) : R.HasBlock fun i => R.e0 (x (R.ix i)) :=
  ⟨x, fun P => eq_one_of_occurs hx (h0 P), hb, fun _ => rfl⟩

end Reading

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

def CrysWith [IsAlgClosure E Ω] {n : ℕ} (r : G E Ω →* GL (Fin n) (Qbar l)) (J : (E →+* Qbar l) → Multiset ℤ) : Prop :=
  Continuous r ∧ ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
      IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (J τ)

variable (E Ω l) in

def BlockPair [IsAlgClosure E Ω] (n t : ℕ) (J : (E →+* Qbar l) → Fin n → ℤ) (bot : (E →+* Qbar l) → ℤ) : Prop :=
  ∃ (r : G E Ω →* GL (Fin n) (Qbar l)) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : Fin t → G E Ω →* (Qbar l)ˣ),
    a + t = n ∧ CrysWith r (fun τ => Finset.univ.val.map (J τ)) ∧ Continuous ρ ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 (χ s)) fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    ∀ σ k, ‖((r σ).val.charpoly - (ρ σ).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s σ : (Qbar l)ˣ) : Qbar l))).coeff k‖ < 1

def IsFrobPerm (σ : Equiv.Perm (E →+* Qbar l)) : Prop :=
  ∀ τ (x : 𝓞 E), ‖σ τ (x : E) - τ (x : E) ^ l‖ < 1

def cj [IsCMField E] (τ : E →+* Qbar l) : E →+* Qbar l := τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom

def IsHalf [IsCMField E] {ι : Type} (inc : ι → (E →+* Qbar l)) : Prop :=
  Function.Injective inc ∧ (∀ τ τ', cj (inc τ) ≠ inc τ') ∧ ∀ i, ∃ τ, i = inc τ ∨ i = cj (inc τ)

variable (Ω) in

def BlockFor [IsCMField E] [IsAlgClosure E Ω] {ι : Type} (inc : ι → (E →+* Qbar l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) : Prop :=
  ∃ (ep : (E →+* Qbar l) → (E →+* Qbar l)) (J : (E →+* Qbar l) → Fin P.Nr → ℤ) (bot : (E →+* Qbar l) → ℤ),
    (ep = id ∨ ep = cj) ∧ BlockPair E Ω l P.Nr P.t J bot ∧
    ∀ τ, (∀ a : Fin P.Nr, J (ep (inc τ)) a = Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) a ∧ J (ep (cj (inc τ))) a = (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (Fin.rev a)) ∧
      bot (ep (inc τ)) = W.bot P τ ∧ bot (ep (cj (inc τ))) = (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1)

variable (E Ω l) in

structure FrobNorm (Pl : Type) where

  lab : Pl → HeightOneSpectrum (𝓞 E)

  sgn : ℤˣ

  tw : G E Ω →* (Qbar l)ˣ
  cont : Continuous tw
  cofin : {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range lab}.Finite

def FrobNorm.Reads [IsAlgClosure E Ω] {Pl : Type} (Fn : FrobNorm E Ω l Pl) (n : ℕ) (θ : Pl → ℕ → Qbar l) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ (P : Pl) (B : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) B (Fn.lab P) → IsFrob (F := E) B (normV (Fn.lab P)) σ →
    (cp (σ ^ (Fn.sgn : ℤ))).reverse = Formalism.L2.Col.heckePolyOf n (Ideal.absNorm (Fn.lab P).asIdeal)
      fun k => θ P k * ((Fn.tw (σ ^ (Fn.sgn : ℤ)) : (Qbar l)ˣ) : Qbar l) ^ k

def IsJumps [IsCMField E] {ι : Type} (inc : ι → (E →+* Qbar l)) (ep : (E →+* Qbar l) → (E →+* Qbar l)) (N h : ℕ) (mu : ι → ℕ → ℕ)
    (J : (E →+* Qbar l) → Fin N → ℤ) : Prop :=
  ∀ τ (a : Fin N), J (ep (inc τ)) a = Formalism.CohomologicalDescent.UnitNormBounds.UN N (mu τ) a ∧ J (ep (cj (inc τ))) a = (h : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN N (mu τ) (Fin.rev a)

def sysOf {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) (θ : I → Qbar l) (P : Pl) (k : ℕ) : Qbar l :=
  if h : 1 ≤ k ∧ k ≤ n then θ (pt P ⟨k - 1, by omega⟩) else 1

variable (Ω) in

def GalSide [IsCMField E] [IsAlgClosure E Ω] {ι : Type} [DecidableEq ι] (inc : ι → (E →+* Qbar l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr)
    (Bk : (F.I → Qbar l) → Prop) : Prop :=
  ∃ (Pl : Type) (pt : Pl → Fin P.Nr → F.I) (Fn : FrobNorm E Ω l Pl) (ep : (E →+* Qbar l) → (E →+* Qbar l)), (ep = id ∨ ep = cj) ∧
    (∀ mu θ, (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → ∃ (r : G E Ω →* GL (Fin P.Nr) (Qbar l)) (J : (E →+* Qbar l) → Fin P.Nr → ℤ),
      IsJumps inc ep P.Nr (h0 P) mu J ∧ CrysWith r (fun τ => Finset.univ.val.map (J τ)) ∧
        Fn.Reads P.Nr (sysOf P.Nr pt θ) fun σ => (r σ).val.charpoly) ∧
    ∀ θ, F.IsEig W.lam θ → Bk θ → ∃ (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : Fin P.t → G E Ω →* (Qbar l)ˣ)
      (bot : (E →+* Qbar l) → ℤ), a + P.t = P.Nr ∧ Continuous ρ ∧
      (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 (χ s)) fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
      (∀ τ, bot (ep (inc τ)) = W.bot P τ ∧ bot (ep (cj (inc τ))) = (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1)) ∧
      Fn.Reads P.Nr (sysOf P.Nr pt θ) fun σ =>
        (ρ σ).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s σ : (Qbar l)ˣ) : Qbar l))

end Galois

section Link

open Formalism.L2.DIV Formalism.L2.Col

theorem sysOf_zero {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) (θ : I → Qbar l) (P : Pl) :
    sysOf n pt θ P 0 = 1 := by simp [sysOf]

theorem sysOf_succ {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) (θ : I → Qbar l) (P : Pl) (k : Fin n) :
    sysOf n pt θ P (k + 1) = θ (pt P k) := by
  have h : 1 ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ n := ⟨by omega, k.2⟩
  simp [sysOf, h]

theorem Reads.HasBlock.dvd {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} {R : Reads F lam B w} {θ : F.I → PadicAlgCl l} (h : R.HasBlock θ)
    {Pl : Type} (pt : Pl → Fin B.n → F.I) (P : Pl) (Q : B.Pl) (hQ : ∀ k, R.ix (pt P k) = (Q, (k : ℕ) + 1)) :
    (B.bl.map fun ν => blockPoly (R.e0 (ν Q)) (B.q Q) B.t).prod ∣ heckePolyOf B.n (B.q Q) (sysOf B.n pt θ P) := by
  obtain ⟨x, h0, hb, hθ⟩ := h
  have h1 := Polynomial.map_dvd R.e0 (hb Q)
  have e1 : ((B.bl.map fun ν => blockPoly (ν Q) (B.q Q) B.t).prod).map R.e0 =
      (B.bl.map fun ν => blockPoly (R.e0 (ν Q)) (B.q Q) B.t).prod := by
    rw [Polynomial.map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun ν _ => ?_
    simp [blockPoly, Polynomial.map_prod]
  have e2 : (heckePoly B.n B.q x Q).map R.e0 = heckePolyOf B.n (B.q Q) (sysOf B.n pt θ P) := by
    rw [heckePoly, heckePolyOf, heckePolyOf, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : R.e0 (x (Q, k)) = sysOf B.n pt θ P k := by
      rcases k with _ | k
      · rw [h0, map_one, sysOf_zero]
      · have hk' : k < B.n := by have := Finset.mem_range.1 hk; omega
        rw [sysOf_succ B.n pt θ P ⟨k, hk'⟩, hθ, hQ]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul, map_mul, this]
    simp
  rwa [e1, e2] at h1

end Link

end GlobalTheory.ExpFrame

end
