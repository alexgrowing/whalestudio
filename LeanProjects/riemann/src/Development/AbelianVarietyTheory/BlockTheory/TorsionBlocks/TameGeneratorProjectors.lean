import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

def IdealsPrimeTo {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) : Type :=
  {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ I ⊔ q = ⊤}

def rayClassNumber {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) : ℕ :=
  Nat.card (Quot fun I J : IdealsPrimeTo q => ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ q ∧ b - 1 ∈ q ∧
    Ideal.span {a} * I.1 = Ideal.span {b} * J.1)

def rayPrimes {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (x : ℝ) : Set (Ideal (𝓞 K)) :=
  {P | P.IsPrime ∧ (Ideal.absNorm P).Prime ∧ (Ideal.absNorm P : ℝ) ≤ x ∧
    ∃ π : 𝓞 K, π - 1 ∈ q ∧ P = Ideal.span {π}}

def ThornerZaman (K : Type) [Field K] [NumberField K] (q : Ideal (𝓞 K)) (c₀ c₂ : ℝ) : Prop :=
  let DK : ℝ := |(NumberField.discr K : ℝ)|
  let n : ℕ := Module.finrank ℚ K
  let Q : ℝ := Ideal.absNorm q
  c₂ ≤ DK * (n : ℝ) ^ n → ∀ x : ℝ,
    DK ^ 694 * Q ^ 521 + DK ^ 232 * Q ^ 367 * (n : ℝ) ^ (290 * n) +
      (DK * Q * (n : ℝ) ^ n) ^ ((1 : ℝ) / 1000) * Q ≤ x →
    c₀ * ((DK * Q * (n : ℝ) ^ n) ^ 5)⁻¹ * x / ((rayClassNumber q : ℝ) * Real.log x) ≤
      ((rayPrimes q x).ncard : ℝ)

variable (D : D7)

def cE : ℕ := D.host.QS * D.host.q * D.host.d

def cEIdeal : Ideal (𝓞 D.host.K) := Ideal.span {((cE D : ℕ) : 𝓞 D.host.K)}

def Admissible (g : ℕ) : Prop :=
  g.Prime ∧ ∃ π : 𝓞 D.host.K, π - 1 ∈ cEIdeal D ∧ Algebra.norm ℤ π = (g : ℤ)

def AdmissiblePrimesWithConstant (c₁ : ℝ) : Prop :=
  ∀ (N : ℕ) (X : ℝ), c₁ ≤ (cE D : ℝ) → c₁ ≤ (D.host.d : ℝ) → 21 ≤ N → 0 < X →
    (N : ℝ) ^ 4 * (cE D : ℝ) ^ 500 ≤ (X / (cE D : ℝ) ^ 20) ^ ((1 : ℝ) / 4) →
    Real.log X ≤ (cE D : ℝ) →
    ∃ Y : ℝ, X / (cE D : ℝ) ^ 20 ≤ Y ∧ Y ≤ X / 2 ∧
      (∃ g₁ g₂ : ℕ, g₁ ≠ g₂ ∧ Admissible D g₁ ∧ Admissible D g₂ ∧
        Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
        Formalism.CyclotomicNorms.BB N g₁ ∩ Formalism.CyclotomicNorms.BB N g₂ = ∅) ∧
      Y / (cE D : ℝ) ^ 20 ≤ (({g : ℕ | Admissible D g ∧ Y ≤ g ∧ (g : ℝ) ≤ 2 * Y}).ncard : ℝ)

abbrev GalE : Type := G D.host.E D.nd.Om

def OnW (σ : D.what₂.FT) : Prop := ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥

def OccursOnLevelZero (σ : D.what₂.FT) : Prop := (∃ a, D.what₂.ft a = σ) ∨ ∃ a, D.what₂.ft0 a = σ

def IsBaseChange (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧
  (∀ τ, (isoInf D.nd D.naut Sig τ).Nodup ∧ ∀ z ∈ isoInf D.nd D.naut Sig τ, ∃ n : ℤ, z = (n : ℂ)) ∧
  (∀ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    isoLoc D.nd D.naut Sig w = D.naut.locW i σ w) ∧
  (∀ k v, D.nd.lab k σ v =
    D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
  D.ntypes.bc σ = Multiset.ofList (Sig.map fun p => (p.a, p.d))

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.mono0 (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) ↔
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

def IsReduction {a l : ℕ} [Fact l.Prime] (red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l)
    (r : GalE D →* GL (Fin a) (Qbar l)) (ρ : GalE D →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsOpen (ρ.ker : Set (GalE D)) ∧ IsSSRep ρ ∧ ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
    p.map red = ((ρ g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def ResidualTie (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  ∀ w : D.what₂.places.Pl,
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ∃ (ι : Qbar (D.what₂.places.resChar w) ≃+* ℂ)
      (red : Zbar (D.what₂.places.resChar w) →+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w))
      (r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))),
      (∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1) ∧
      IsGaloisRepOf D π _ ι r ∧ IsReduction D red r (D.ntypes.rbar σ w) ∧
      ∀ k, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 →
        ∀ z : Zbar (D.what₂.places.resChar w), (z : Qbar _) = ι.symm (D.ntypes.teichC k x) →
          red z = D.ntypes.iota k v w x

def toFb (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) : Fb (D.host.g k) (D.host.g_prime k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))

def ExtendsConj (e : D.nd.Om ≃+* D.nd.Om) : Prop :=
  ∀ x : D.host.E, e (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)

def IsTameGenOver (k : Fin 2) (v : D.nd.PlG k) (t : GalE D) : Prop :=
  t = D.ntypes.tg k v ∨
    ∃ e : D.nd.Om ≃+* D.nd.Om, ExtendsConj D e ∧ ∀ y, t (e y) = e (D.ntypes.tg k v y)

def IrredClauses {l : ℕ} [Fact l.Prime] (ρ : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  Formalism.CyclotomicNorms.IrredOn ρ ⊤ ∧
  ∀ (L : IntermediateField D.host.E D.nd.Om), FiniteDimensional D.host.E L → IsGalois D.host.E L →
    Group.IsSolvable (L ≃ₐ[D.host.E] L) →
    ∀ i : Fin 2, l ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g i) →
    (∀ w ∈ placesOver D.host.E (D.host.g i), Ine (F := D.host.E) (D.nd.plOm.1 w) ≤ L.fixingSubgroup) →
    Formalism.CyclotomicNorms.IrredOn ρ L.fixingSubgroup ∧
    Submodule.span (Formalism.CyclotomicNorms.Fbar l) ((fun h => ((ρ h : GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l))) '' (L.fixingSubgroup : Set (GalE D))) = ⊤

def IrreducibleGoodBaseChange : Prop :=
  ∀ σ : D.what₂.FT, D.nd.goodRow σ → (OnW D σ ∨ OccursOnLevelZero D σ) →
    ∃ π : D.naut.CG D.R.r,

      (D.naut.csd π ∧ D.naut.ralg π ∧ IsBaseChange D σ [⟨D.R.r, π, 1⟩] ∧ D.ntypes.cuspidal σ ∧
        ResidualTie D σ π ∧
        ∀ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
          D.naut.locG π w = D.naut.locW i σ w) ∧

      (∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
        (∃ r, IsGaloisRepOf D π l ι r) ∧
        ∀ r, IsGaloisRepOf D π l ι r →
          (∀ red ρ, IsReduction D red r ρ → IrredClauses D ρ) ∧
          ∀ k : Fin 2, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) (t : GalE D), IsTameGenOver D k v t →
            ∀ (j : Fin D.R.m) (α : Qbar l),
              ((r t : GL (Fin D.R.r) (Qbar l)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar l)).charpoly.IsRoot α →
              ¬ ‖α - ι.symm (D.ntypes.teichC k (toFb D k (D.nd.chiT k v j)))‖ < 1 ∧
              ¬ ‖α - (ι.symm (D.ntypes.teichC k (toFb D k (D.nd.chiT k v j))))⁻¹‖ < 1) ∧

      ∀ w : D.what₂.places.Pl,
        haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
        IrredClauses D (D.ntypes.rbar σ w) ∧
        ∀ k : Fin 2, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) (t : GalE D),
          IsTameGenOver D k v t → ∀ j : Fin D.R.m,
            ¬ ((D.ntypes.rbar σ w t : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly.IsRoot
              (D.ntypes.iota k v w (toFb D k (D.nd.chiT k v j))) ∧
            ¬ ((D.ntypes.rbar σ w t : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly.IsRoot
              (D.ntypes.iota k v w (toFb D k (D.nd.chiT k v j)⁻¹))

abbrev G0 : Type := G0g D.nd

def eTuple (f : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]) : MonoidAlgebra ℂ (G0 D) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0 D =>
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (f kv.1 kv.2)).coeff (g kv)

def ProjectorA : Prop :=
  (∀ γ, D.ntypes.e0.coeff γ ∈ D.ntypes.Qchi) ∧
  (∀ γ, IsIntegral ℤ ((Nat.card (G0 D) : ℂ) * D.ntypes.e0.coeff γ)) ∧
  (∀ a, D.ntypes.e0 * a = a * D.ntypes.e0) ∧
  (∀ γ, D.ntypes.e0.coeff γ⁻¹ = starRingEnd ℂ (D.ntypes.e0.coeff γ)) ∧
  D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0

def ProjectorB : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0 D) V),
    (∀ a, Commute (ρ.asAlgebraHom D.ntypes.e0) (ρ.asAlgebraHom a)) ∧
    (∀ T : Module.End ℂ V, (∀ γ, Commute T (ρ γ)) → Commute (ρ.asAlgebraHom D.ntypes.e0) T) ∧
    ∀ (Γ : Type) [Group Γ] (ρ' : Representation ℂ Γ V), (∀ h γ, Commute (ρ' h) (ρ γ)) →
      ∀ b, Commute (ρ.asAlgebraHom D.ntypes.e0) (ρ'.asAlgebraHom b)

def ProjectorC : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDedekindDomain O] [Field K] [CharZero K] [Algebra O K]
    [IsFractionRing O K] (ψ : D.ntypes.Qchi →+* K),
    (∀ x : D.ntypes.Qchi, IsIntegral ℤ x → ψ x ∈ (algebraMap O K).range) →
    (∃ e : MonoidAlgebra K (G0 D),
      ∀ γ, ∃ x : D.ntypes.Qchi, (x : ℂ) = D.ntypes.e0.coeff γ ∧ e.coeff γ = ψ x) ∧
    ∀ e : MonoidAlgebra K (G0 D),
      (∀ γ, ∃ x : D.ntypes.Qchi, (x : ℂ) = D.ntypes.e0.coeff γ ∧ e.coeff γ = ψ x) →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
      (ρ : Representation K (G0 D) V) (M : Submodule O V),
      M.FG → Submodule.span K (M : Set V) = ⊤ → (∀ γ, ∀ x ∈ M, ρ γ x ∈ M) →
      (∀ x ∈ M, (Nat.card (G0 D) : K) • ρ.asAlgebraHom e x ∈ M ∧
        (Nat.card (G0 D) : K) • ρ.asAlgebraHom e x ∈ LinearMap.range (ρ.asAlgebraHom e)) ∧
      (∀ y ∈ M, y ∈ LinearMap.range (ρ.asAlgebraHom e) → ∃ x ∈ M, ρ.asAlgebraHom e x = y) ∧
      ∀ x ∈ M, ∃ u ∈ M, ∃ u' ∈ M, u ∈ LinearMap.range (ρ.asAlgebraHom e) ∧
        u' ∈ LinearMap.range (ρ.asAlgebraHom (1 - e)) ∧ (Nat.card (G0 D) : K) • x = u + u'

def ProjectorD : Prop :=
  ∀ σ' : D.ntypes.Par,
    (∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ F ∈ D.ntypes.MtPar μ j σ',
      (D.ntypes.goodPar σ' → D.ntypes.onMt μ j D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt μ j D.ntypes.e0 F = 0)) ∧
    ∀ μ, ∀ F ∈ D.ntypes.AmbPar μ σ',
      (D.ntypes.goodPar σ' → D.ntypes.onAmb μ D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onAmb μ D.ntypes.e0 F = 0)

def ProjectorProperties : Prop := ProjectorA D ∧ ProjectorB D ∧ ProjectorC D ∧ ProjectorD D

abbrev VK (i : D.nd.Loc) : Type := FractionRing (D.nd.O i) ⊗[D.nd.O i] D.nd.Mt i

def iotaK (i : D.nd.Loc) : FractionRing (D.nd.O i) →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)

def IsInducedEndomorphism (i : D.nd.Loc) (e : Module.End (FractionRing (D.nd.O i)) (VK D i)) : Prop :=
  ∀ x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 (D.what₂.jMt _ _ x) →
    e (D.nd.prMt i x) = D.nd.prMt i y

def InAnn (i : D.nd.Loc) (f : D.nd.T i) : Prop :=
  ∀ u ∈ MtUp D.nd i (D.nd.Z i),
    (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u ∈ MtLow D.nd i (D.nd.Z i)

def annAt (i : D.nd.Loc) (π : D.nd.X i) : Ideal (D.nd.O i) :=
  Ideal.span {c | ∃ f : D.nd.T i, InAnn D i f ∧ c = (f : D.nd.X i → D.nd.O i) π}

def eUp (i : D.nd.Loc) (e : Module.End (FractionRing (D.nd.O i)) (VK D i)) :
    Submodule (D.nd.O i) (VK D i) :=
  (MtUp D.nd i (D.nd.Z i)).map (e.restrictScalars (D.nd.O i))

def LengthDroppingInequality : Prop :=
  ∀ i : D.nd.Loc, (∀ k, D.nd.l i ≠ D.host.g k) →
    (∃ e, IsInducedEndomorphism D i e) ∧ ∀ e, IsInducedEndomorphism D i e →
      (∀ π, π ∈ D.nd.Zgood i ↔
        π ∈ D.nd.Z i ∧ ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, e u = u) ∧
      (∀ π ∈ D.nd.Z i, π ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, e u = 0) ∧
      (∀ π ∈ D.nd.Z i, annAt D i π ≠ ⊥ ∧ ccAt (D.nd.T i) (D.nd.Z i) π ≤ annAt D i π) ∧
      MtLow D.nd i (D.nd.Zgood i) ≤ eUp D i e ∧
      Module.length (D.nd.O i) (↥(eUp D i e) ⧸ (MtLow D.nd i (D.nd.Zgood i)).comap (eUp D i e).subtype) ≠ ⊤ ∧
      lenUnit (O := D.nd.O i) (D.nd.l i)
          (↥(eUp D i e) ⧸ (MtLow D.nd i (D.nd.Zgood i)).comap (eUp D i e).subtype) ≤
        ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ) *
          (lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ annAt D i π) +
            (padicValNat (D.nd.l i) (Nat.card (G0 D)) : ℚ))

def PsdProjectorDiscarding : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (Q Pr : H →ₗ[ℂ] H) (Ds s η δ : ℝ),
    (Module.finrank ℂ H : ℝ) ≤ (1 + s) * Ds → 0 < Ds → 0 ≤ s → Q.IsPositive →
    (LinearMap.trace ℂ H (Q * Q)).re ≤ (1 + η) * (LinearMap.trace ℂ H Q).re ^ 2 / Ds →
    0 ≤ η → η ≤ 1 → Pr.IsSymmetric → Pr * Pr = Pr →
    (Module.finrank ℂ (LinearMap.range Pr) : ℝ) ≤ δ * Ds → 2 * δ < 1 →
    let P : H →ₗ[ℂ] H := 1 - Pr
    let Q₀ : H →ₗ[ℂ] H := P * Q * P
    let D₀ : ℕ := Module.finrank ℂ (LinearMap.range P)
    (1 - Real.sqrt (2 * δ)) * (LinearMap.trace ℂ H Q).re ≤ (LinearMap.trace ℂ H Q₀).re ∧
    (LinearMap.trace ℂ H (Q₀ * Q₀)).re ≤ (LinearMap.trace ℂ H (Q * Q)).re ∧
    (0 < D₀ → (LinearMap.trace ℂ H (Q₀ * Q₀)).re ≤
      (1 + η) * (1 + s) * ((1 - Real.sqrt (2 * δ)) ^ 2)⁻¹ * (LinearMap.trace ℂ H Q₀).re ^ 2 / D₀) ∧
    ∀ (C : Type) [NormedAddCommGroup C] [InnerProductSpace ℂ C] [FiniteDimensional ℂ C]
      (B : C →ₗ[ℂ] H) (c : ℝ), 0 ≤ c →
      ((c : ℂ) • (LinearMap.adjoint B ∘ₗ B) - (c : ℂ) • (LinearMap.adjoint B ∘ₗ P ∘ₗ B)).IsPositive

def dualLabel (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  C (f.coeff 0)⁻¹ * f.reverse

def LabelLaws : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).Monic ∧ (D.naut.items₂ k _ L).natDegree ≤ D.naut.lpDim L ∧
    (∀ s : ℝ, D.naut.items₂ k _ (D.naut.lpTw L s) = D.naut.items₂ k _ L) ∧
    (∀ χ : D.naut.LP (D.naut.plGw k v), D.naut.lpDim χ = 1 → D.naut.unr χ →
      D.naut.items₂ k _ (D.naut.lpChar L χ) = D.naut.items₂ k _ L) ∧
    ((D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) →
        D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L)

def ConjDualInertia : Prop :=
  ∀ {a : ℕ} (π : D.naut.CG a), D.naut.csd π → ∀ w w' : PlE D.host, IsConjPl D.host w w' →
    ∀ e : D.nd.Om ≃+* D.nd.Om, ExtendsConj D e →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ e y ∈ D.nd.plOm.1 w') →
    ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ∀ s' : GalE D, (∀ y, s' (e y) = e (s y)) →
      (D.naut.inePol (D.naut.locG π w') s').roots = (D.naut.inePol (D.naut.locG π w) s).roots.map (·⁻¹)

def BaseChangeRows : Prop :=
  ∀ σ, OnW D σ → ∃ Sig, IsBaseChange D σ Sig ∧ ∀ π, Sig = [⟨D.R.r, π, 1⟩] → ResidualTie D σ π

def TransferRows : Prop :=
  ∀ σ, OccursOnLevelZero D σ → (∀ v, Squarefree (D.nd.lab 0 σ v)) →
    (∀ a, 0 < a → a < D.R.r → ∃ v, ¬ ∃ q, q ∣ D.nd.lab 0 σ v ∧ q.natDegree = a) →
    D.what₂.isot D.R.m σ ≠ ⊥

def GaloisReps : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, IsGaloisRepOf D π l ι r

def GaloisOnSeries : Prop :=
  ∀ (k : Fin 2) (α : ℂ ≃+* ℂ) (f f' : (ZMod (D.host.g k))[X]),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    f.Monic → f.natDegree = D.R.r → f.coeff 0 ≠ 0 → Squarefree f →
    f'.Monic → f'.natDegree = D.R.r → f'.coeff 0 ≠ 0 →
    (Formalism.CyclotomicNorms.rootsBar f').map (D.ntypes.teichC k) =
      (Formalism.CyclotomicNorms.rootsBar f).map (fun x => α (D.ntypes.teichC k x)) →
    ∀ γ, (D.ntypes.eSer k f').coeff γ = α ((D.ntypes.eSer k f).coeff γ)

def LabelsMatch (σ' : D.ntypes.Par) (f : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X])
    (J : Finset (Fin D.R.m)) : Prop :=
  (∀ k v, f k v * ∏ j ∈ J, (X - C (D.nd.chiT k v j : ZMod (D.host.g k))) ^ D.R.t =
    D.ntypes.labPar k σ' v * ∏ j ∈ J, (X - C (D.nd.chiT k v j : ZMod (D.host.g k))) ^ D.R.t) ∨
  ∀ k v, f k v * ∏ j ∈ J, (X - C (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) ^ D.R.t =
    dualLabel D k (D.ntypes.labPar k σ' v) *
      ∏ j ∈ J, (X - C (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) ^ D.R.t

def TypesAndSupport : Prop :=
  ∀ (σ' : D.ntypes.Par) (f : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]),
    (∀ μ (j : Fin D.R.m), ∀ F ∈ D.ntypes.MtPar μ ((j : ℕ) + 1) σ',
      D.ntypes.onMt μ ((j : ℕ) + 1) (eTuple D f) F ≠ 0 → LabelsMatch D σ' f {j}) ∧
    ∀ μ, ∀ F ∈ D.ntypes.AmbPar μ σ',
      D.ntypes.onAmb μ (eTuple D f) F ≠ 0 → LabelsMatch D σ' f Finset.univ

def restC (i : D.nd.Loc) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ P ∈ {P | D.naut.ptV i P = none}, D.naut.typeV i P

def EigenTie (i : D.nd.Loc) : Prop :=
  (∀ (n : ℕ) (c : Fin n → FractionRing (D.nd.O i)) (x : Fin n → D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    (∑ a, c a • D.nd.prMt i (x a) = 0 ↔ ∑ a, iotaK D i (c a) • D.what₂.jMt _ _ (x a) ∈ restC D i) ∧
    ∀ π, (∑ a, c a • D.nd.prMt i (x a) ∈ heckeEig (D.nd.T i) (D.nd.act i) π ↔
      ∑ a, iotaK D i (c a) • D.what₂.jMt _ _ (x a) ∈ eigC D.nd D.naut i π ⊔ restC D i)) ∧
  ∀ P z, ∀ F ∈ D.naut.typeV i P, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) z F ∈ D.naut.typeV i P

def PointParameter (i : D.nd.Loc) : Prop :=
  ∀ π ∈ D.nd.Z i, ∃ (σ' : D.ntypes.Par) (Sig : List (Part D.naut.CG)),
    (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
    ∀ P, D.naut.ptV i P = some π →
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)

def StableLatticeOfForms (i : D.nd.Loc) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (FractionRing (D.nd.O i)) V) (_ : Module (D.nd.O i) V)
    (_ : IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V)
    (ρ : Representation (FractionRing (D.nd.O i)) (G0 D) V) (M : Submodule (D.nd.O i) V)
    (κ : VK D i →ₗ[FractionRing (D.nd.O i)] V),
    M.FG ∧ Submodule.span (FractionRing (D.nd.O i)) (M : Set V) = ⊤ ∧ (∀ γ, ∀ x ∈ M, ρ γ x ∈ M) ∧
    Function.Injective κ ∧ (∀ u, κ u ∈ M ↔ u ∈ MtIn D.nd i) ∧
    ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0 D))) (zK : MonoidAlgebra (FractionRing (D.nd.O i)) (G0 D)),
      (∀ γ, iotaK D i (zK.coeff γ) = z.1.coeff γ) →
      ∀ x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
        D.what₂.jMt _ _ y = D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) z (D.what₂.jMt _ _ x) →
        ρ.asAlgebraHom zK (κ (D.nd.prMt i x)) = κ (D.nd.prMt i y)

structure Admitted (c₀ c₂ : ℝ) : Prop where
  primes : ThornerZaman D.host.K (cEIdeal D) c₀ c₂
  labels : LabelLaws D
  conjDual : ConjDualInertia D
  baseChange : BaseChangeRows D
  transfer : TransferRows D
  galois : GaloisReps D
  series : GaloisOnSeries D
  types : TypesAndSupport D
  semisimple : D.nd.EigSpan
  setting : ∀ i : D.nd.Loc, (∀ k, D.nd.l i ≠ D.host.g k) →
    EigenTie D i ∧ PointParameter D i ∧ StableLatticeOfForms D i

def Stmt : Prop :=
  ∀ (D : D7) (c₀ c₁ c₂ : ℝ), 0 < c₀ → max (2 ^ 14 / c₀) c₂ ≤ c₁ → Admitted D c₀ c₂ →
    AdmissiblePrimesWithConstant D c₁ ∧ IrreducibleGoodBaseChange D ∧ ProjectorProperties D ∧ LengthDroppingInequality D ∧ PsdProjectorDiscarding

example (g : ℕ) (h : Admissible D g) : 2 ≤ g := h.1.two_le

end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
