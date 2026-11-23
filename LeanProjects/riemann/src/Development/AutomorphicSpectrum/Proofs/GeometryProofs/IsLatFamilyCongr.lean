import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBoundAllPlaces
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

open GlobalTheory.CompanionTheory.Ar.BT

abbrev TorsT (E : Type) [Field E] [NumberField E] (N n : ℕ) : Type :=
  Multiplicative (Fin N → (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}))

def qmk {E : Type} [Field E] [NumberField E] {N : ℕ} (n : ℕ) (x : Fin N → 𝓞 E) : TorsT E N n :=
  Multiplicative.ofAdd fun i => Ideal.Quotient.mk _ (x i)

def qhom {E : Type} [Field E] [NumberField E] (N n : ℕ) : Multiplicative (Fin N → 𝓞 E) →* TorsT E N n :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i => Ideal.Quotient.mk _ (x i)
      map_zero' := by ext i; simp
      map_add' := fun a b => by ext i; simp }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

structure GenPts (𝔐 : HodgeCpt Y S y) (n : ℕ) where

  pt : TorsT E (D.p + D.q) n →* (Over.mk 𝔐.ξ ⟶ 𝔐.t.G)
  inj : Function.Injective pt
  onto : ∀ g : Over.mk 𝔐.ξ ⟶ 𝔐.t.G, g ^ n = 1 ↔ ∃ t, pt t = g
  lin : ∀ (a : 𝓞 E) (x : Fin (D.p + D.q) → 𝓞 E), pt (qmk n (a • x)) = pt (qmk n x) ≫ 𝔐.t.act.act a

structure GenTors (𝔐 : HodgeCpt Y S y) (p : ℕ) where

  t₁ : GenPts 𝔐 p

  t₂ : GenPts 𝔐 (p ^ 𝔐.R p)
  compat : ∀ x : Fin (D.p + D.q) → 𝓞 E, t₂.pt (qmk _ (p ^ (𝔐.R p - 1) • x)) = t₁.pt (qmk p x)

  ζ : Ω
  ζ_prim : IsPrimitiveRoot ζ (p ^ 𝔐.R p)

  e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p)
  alt : ∀ x, e x x = 0
  adj : ∀ (a : 𝓞 E) (x x' : Fin (D.p + D.q) → 𝓞 E), e (a • x) x' = e x (H.bar a • x')
  e_surj : ∀ f : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p), ∃ x, e x = f
  e_inj : ∀ x, e x = 0 → ∃ x', x = (p ^ 𝔐.R p) • x'
  weil : ∀ (x x' : Fin (D.p + D.q) → 𝓞 E) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (g g' : Over.mk (spMap i ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (u : kˣ), g.left = spMap i ≫ (t₂.pt (qmk _ x)).left →
      g'.left = spMap i ≫ (t₂.pt (qmk _ x')).left →
      (Out.WeilIs 𝔐.t.G 𝔐.t.PP.L (p ^ 𝔐.R p) g g' (unitOn u) ↔ (u : k) = i (ζ ^ (e x x').val))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

abbrev CR (O : Type) [CommRing O] [Algebra O Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) : Subalgebra O Ω :=
  chartRing O (mseg y) c

def fracToField {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) : FractionRing R →+* Ω :=
  IsFractionRing.lift (g := algebraMap R Ω) Subtype.val_injective

def PtsAgree {𝔐 : HodgeCpt Y S y} {O : Type} [CommRing O] [Algebra O Ω] {R : Subalgebra O Ω} {T : Type} [CommGroup T]
    (Γ : QFGroup R T) (i : Γ.G.left ⟶ 𝔐.t.G.left) (pt : T →* (Over.mk 𝔐.ξ ⟶ 𝔐.t.G)) : Prop :=
  ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i

structure ChartPack {𝔐 : HodgeCpt Y S y} {p : ℕ} (G : GenTors 𝔐 p) (O : Type) [CommRing O] [Algebra O Ω]
    (c : ∀ k, J k) where

  x : Spec (CommRingCat.of (CR O y c)) ⟶ 𝔐.X
  x_gen : spMap (algebraMap (CR O y c) Ω) ≫ x = 𝔐.ξ

  L : Type
  [acg : AddCommGroup L]
  [mod : Module (CR O y c) L]
  fin : Module.Finite (CR O y c) L
  proj : Module.Projective (CR O y c) L
  M : LieModel 𝔐.t.G x L
  ρ : 𝓞 E →+* Module.End (CR O y c) L
  act : M.IsActOf 𝔐.t.act.act ρ

  toLi : L →ₗ[CR O y c] 𝔐.Li
  toLi_bc : IsBaseChange Ω toLi
  toLi_pt : ∀ v, (𝔐.M.pt (toLi v)).left = spMap (dualMap (algebraMap (CR O y c) Ω)) ≫ (M.pt v).left

  j : Module.Dual (CR O y c) L →ₗ[CR O y c] Module.Dual Ω 𝔐.Li
  j_bc : IsBaseChange Ω j
  j_apply : ∀ u v, j u (toLi v) = algebraMap (CR O y c) Ω (u v)

  Γ₁ : QFGroup (CR O y c) (TorsT E (D.p + D.q) p)
  i₁ : Γ₁.G.left ⟶ 𝔐.t.G.left
  tors₁ : Γ₁.IsTorsionAlong 𝔐.t.G x p i₁
  pts₁ : PtsAgree Γ₁ i₁ G.t₁.pt

  Γ₂ : QFGroup (CR O y c) (TorsT E (D.p + D.q) (p ^ 𝔐.R p))
  i₂ : Γ₂.G.left ⟶ 𝔐.t.G.left
  tors₂ : Γ₂.IsTorsionAlong 𝔐.t.G x (p ^ 𝔐.R p) i₂
  pts₂ : PtsAgree Γ₂ i₂ G.t₂.pt

  ζ : (CR O y c)ˣ
  ζ_eq : ((ζ : CR O y c) : Ω) = G.ζ

  Dh : HT.HTChart (CR O y c) Ω (HT.cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)
  Dh_e : Dh.e = G.e
  Dh_act : ∀ (a : 𝓞 E) (u : Module.Dual Ω 𝔐.Li), Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a)
  isHT : IsHTChartOf Dh Γ₂ i₂ M ρ j (qhom _ _) ζ

attribute [instance] ChartPack.acg ChartPack.mod

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

def IsSec {p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : Prop :=
  (∀ a, pq (sc a) = a) ∧ ∀ u a, pq u = 0 → u * sc a = 0

def toN {N p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (a : Fin N → F) : TorsT E N p :=
  Multiplicative.ofAdd fun i => sc (a i)

def fromN {N p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (t : TorsT E N p) : Fin N → F :=
  fun i => pq (Multiplicative.toAdd t i)

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def funLat (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : AddSubgroup ((Fin (D.p + D.q) → F) → Ω) :=
  (Subalgebra.toSubmodule (P.Γ₁.btOrder ⊤)).toAddSubgroup.map
    { toFun := fun f a => ((f (toN sc a) : CR O y c') : Ω)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

def thLat (P : ChartPack G O c') (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))
    {r : ℕ} (v : Fin r → 𝔐.Li) : AddSubgroup (((Fin (D.p + D.q) → F) → Ω) × (Fin r → Ω)) :=
  AddSubgroup.closure {z | z.1 ∈ funLat P sc ∧ z.1 0 = 0 ∧ ∃ (f : TorsT E (D.p + D.q) p → CR O y c')
    (u : Module.Dual (CR O y c') P.L), (∀ t, ((f t : CR O y c') : Ω) = z.1 (fromN pq t)) ∧
      P.Γ₁.IsDerAtOne P.i₁ P.M p f u ∧ ∀ k, z.2 k = P.j u (v k)}

def gamLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω) {r n : ℕ} (W : AddSubgroup (Fin r → Ω))
    (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) : AddSubgroup ((Fin r → Ω) × (Fin n → Ω)) where
  carrier := {z | w • z.1 ∈ W ∧ z.2 - i z.1 ∈ stdLat R (Fin n)}
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨by simpa [smul_add] using W.add_mem h1 h1', ?_⟩
    have := (stdLat R (Fin n)).add_mem h2 h2'
    convert this using 1
    simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  zero_mem' := ⟨by simpa using W.zero_mem, by simpa using (stdLat R (Fin n)).zero_mem⟩
  neg_mem' := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    refine ⟨by simpa [smul_neg] using W.neg_mem h1, ?_⟩
    have := (stdLat R (Fin n)).neg_mem h2
    convert this using 1
    simp only [Prod.fst_neg, Prod.snd_neg, map_neg]; abel

def delLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω) {s n : ℕ} (om : AddSubgroup (Fin s → Ω))
    (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)) : AddSubgroup ((Fin n → Ω) × (Fin s → Ω)) where
  carrier := {z | w • z.1 ∈ stdLat R (Fin n) ∧ z.2 - q z.1 ∈ om}
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨by simpa [smul_add] using (stdLat R (Fin n)).add_mem h1 h1', ?_⟩
    have := om.add_mem h2 h2'
    convert this using 1
    simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  zero_mem' := ⟨by simpa using (stdLat R (Fin n)).zero_mem, by simpa using om.zero_mem⟩
  neg_mem' := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    refine ⟨by simpa [smul_neg] using (stdLat R (Fin n)).neg_mem h1, ?_⟩
    have := om.neg_mem h2
    convert this using 1
    simp only [Prod.fst_neg, Prod.snd_neg, map_neg]; abel

def qMap (P : ChartPack G O c') {s : ℕ} (v : Fin s → 𝔐.Li) :
    (Fin (D.p + D.q) → Ω) →ₗ[Ω] (Fin s → Ω) :=
  Fintype.linearCombination Ω fun (i : Fin (D.p + D.q)) (k : Fin s) => P.Dh.h (Pi.single i 1) (v k)

def SeqHyp {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω) {r s n : ℕ} (W : AddSubgroup (Fin r → Ω))
    (om : AddSubgroup (Fin s → Ω)) (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)) : Prop :=
  (∀ a ∈ W, i a ∈ stdLat R (Fin n)) ∧ (∀ b ∈ stdLat R (Fin n), q b ∈ om) ∧
  (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) ∧
  (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) ∧
  ∀ z ∈ om, ∃ b ∈ stdLat R (Fin n), z - q b ∈ mulLat w om

def DualSeq (P : ChartPack G O c') (σ : E →+* Ω) (m : ℕ) {r : ℕ} (W : AddSubgroup (Fin r → Ω)) (v : Fin r → 𝔐.Li)
    (i : (Fin r → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)) : Prop :=
  ∀ a ∈ W, ∀ j, ∃ z ∈ CR O y c', ∑ l, i a l * P.Dh.gram σ 1 l j =
    P.Dh.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F] {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p}
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]

def IsOrbit (𝔐 : HodgeCpt Y S y) (p : ℕ) (φ : Equiv.Perm (CMType H ⊕ CMType H)) (t₀ : CMType H ⊕ CMType H) {Sg : Type}
    (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (w : O)
    (σ : Sg → F →+* IsLocalRing.ResidueField O) : Prop :=
  t₀ ∈ Set.range e ∧ Function.Injective e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ Function.Surjective pq ∧
  (∀ τ (a : 𝓞 E), ∃ o : O, algebraMap O Ω o = 𝔐.emb (e τ) a ∧
    IsLocalRing.residue O o = σ τ (pq (Ideal.Quotient.mk _ a))) ∧
  (∀ t, (∀ (a : 𝓞 E) (o : O), algebraMap O Ω o = 𝔐.emb t a →
    (IsLocalRing.residue O o = 0 ↔ pq (Ideal.Quotient.mk _ a) = 0)) → t ∈ Set.range e) ∧
  ((p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)) ∧
  HT.IsCp p (algebraMap O Ω w)

variable {O} {Sg : Type} {c' : ∀ k, J k}

def chartD (e : Sg → CMType H ⊕ CMType H) (b : ∀ t, Fin (labelRk D t) → 𝔐.Li)
    (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O)
    (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)) :
    LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap where
  M := funLat P sc
  lie τ := coordLat O y (𝔐.dR (e τ)) (b (e τ)) c'
  W τ := coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c'
  om τ := dotDual (CR O y c') (coordLat O y (𝔐.dR (e τ).swap) (b (e τ).swap) c')
  omHT τ := dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')
  Gam τ := gamLat (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (i τ)
  Del τ := delLat (CR O y c') (algebraMap O Ω w)
    (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (qMap P (b (e τ).swap))
  Th τ := thLat P pq sc (b (e τ))

def zeroD (F : Type) (n : ℕ) (Sg : Type) (r s : Sg → ℕ) : LieLatticeData Ω F n Sg r s :=
  ⟨⊥, fun _ => ⊥, fun _ => ⊥, fun _ => ⊥, fun _ => ⊥, fun _ => ⊥, fun _ => ⊥, fun _ => ⊥⟩

open Classical in

def famD (e : Sg → CMType H ⊕ CMType H) (b : ∀ t, Fin (labelRk D t) → 𝔐.Li)
    (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O)
    (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c')
    (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)) (c' : ∀ k, J k) :
    LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap :=
  if h : mseg y c' ≠ 0 then chartD e b pq sc w (P c' h) (i c') else zeroD F _ Sg _ _

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

section Assemble

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F] {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] {Sg : Type}

theorem famD_pos (e : Sg → CMType H ⊕ CMType H) (b : ∀ t, Fin (labelRk D t) → 𝔐.Li)
    (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O)
    (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c')
    (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)) (c' : ∀ k, J k)
    (h : mseg y c' ≠ 0) : famD e b pq sc w P i c' = chartD e b pq sc w (P c' h) (i c') := by
  rw [famD, dif_pos h]

theorem isLatFamily_congr {V : Type} [AddCommGroup V] [Module Ω V] {o : Type} [CommRing o] [Algebra o Ω]
    {A B : (∀ k, J k) → AddSubgroup V} (h : ∀ c', mseg y c' ≠ 0 → A c' = B c') (hA : IsLatFamily o y A) :
    IsLatFamily o y B := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [← h s hs] at hv ⊢
    exact h1 s hs a ha v hv
  · rw [← h s hs] at hv
    rw [← h t ht]
    exact h2 s t hs ht v hv

end Assemble

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
