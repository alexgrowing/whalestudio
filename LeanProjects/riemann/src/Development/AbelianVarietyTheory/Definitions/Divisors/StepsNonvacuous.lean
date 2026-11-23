import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

abbrev jet {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) : J.B := taylor (n + 1) J.t f

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E} {n : ℕ}
  {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n}

structure Germ (Y : Family J T.X T.δ T.low) : Type 1 where

  B : Type
  [cr : CommRing B]
  [alg : Algebra ℂ B]
  smooth : Algebra.Smooth ℂ B

  X : Obj (FR E) 𝔠 (Sp B)

  δ : X.DetGen

  j : B →ₐ[ℂ] J.B

  q : Y.X'.A.left ⟶ X.A.left
  pull : Y.X'.IsPullBy X (spMap (j : B →+* J.B)) q

  δ'' : Y.X'.DetGen
  corr : Obj.DetCorr (j : B →+* J.B) q δ.1 δ''.1

  e : J.B
  he : Y.δ'.1 = e • δ''.1

  U : Set (I → ℂ)
  isOpen : IsOpen U
  zero : 0 ∈ U

  y : (I → ℂ) → (B →ₐ[ℂ] ℂ)
  hol : ∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U
  jet_eq : ∀ b, j b = jet J fun z ↦ y z b

attribute [instance] Germ.cr Germ.alg

structure Coord (ε : ℤˣ) {Y : Family J T.X T.δ T.low} (G : Germ Y) : Type 1 where

  V : Set (I → ℂ)
  isOpen : IsOpen V
  zero : 0 ∈ V
  sub : V ⊆ G.U

  X : (I → ℂ) → Obj (FR E) 𝔠 (Sp ℂ)

  q : ∀ z, (X z).A.left ⟶ G.X.A.left
  pull : ∀ z, (X z).IsPullBy G.X (spMap (G.y z : G.B →+* ℂ)) (q z)
  mor : ∀ z, GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 ℂ) (𝟙 _) (X z).A (G.y z : G.B →+* ℂ) (spMap (G.y z : G.B →+* ℂ)) (q z)

  δ : ∀ z, (X z).DetGen
  corr : ∀ z, Obj.DetCorr (G.y z : G.B →+* ℂ) (q z) G.δ.1 (δ z).1

  ζ : (I → ℂ) → I → ℂ
  ζ_hol : DifferentiableOn ℂ ζ V
  ζ_zero : ζ 0 = 0
  ζ_mem : ∀ z ∈ V, ζ z ∈ polydisc I

  U : ∀ z ∈ V, Unif φ L (ζ z) (X z)
  e_eq : ∀ z hz, (U z hz).e = T.U.e

  C : (I → ℂ) → ℂ
  det : ∀ z hz, (U z hz).IsDet (δ z).1 (C z)

  P₀ : T.U.u.Λ →+ HdR T.X.A
  per : IsPeriodMap ε T.U.u P₀

  P : ∀ z, T.U.u.Λ →+ HdR (X z).A
  lie : ∀ z hz (x : T.U.u.Λ), ∃ v, IsLieImage (P z x) v ∧
    (U z hz).u.IsDiff (fun a ↦ x.1 a + ζ z (T.U.e a) * starRingEnd ℂ (x.1 a)) v
  P_hol : ∀ x (c : primDR G.X.A), DifferentiableOn ℂ (fun z ↦ P z x ((mor z).pull c)) V
  horiz : ∀ (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    (x : T.U.u.Λ) (d : Crys J.κ (spMap J.π) T.X.A), Y.mor.Corr (P₀ x) d → ∀ c : primDR G.X.A,
    crysToDR J.κ Y.pull.grp d (m'.pull c) = jet J fun z ↦ P z x ((mor z).pull c)

def AllFam (Q : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E) (n : ℕ)
    (T : CxPt 𝔠 φ L) (J : JetRing ℂ I n), Family J T.X T.δ T.low → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ)
    (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ (n : ℕ) (T : CxPt 𝔠 φ (lattice c y)) (J : JetRing ℂ I n)
    (Y : Family J T.X T.δ T.low), Q E I 𝔠 φ (lattice c y) n T J Y

def Chart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n)
    (X' : Obj F 𝔠 (Sp J.B)), ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (X : Obj F 𝔠 (Sp B))
      (_ : X.DetGen) (j : B →ₐ[ℂ] J.B) (q : X'.A.left ⟶ X.A.left), X'.IsPullBy X (spMap (j : B →+* J.B)) q

def HolLift : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) (j : B →ₐ[ℂ] J.B),
    ∃ (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U ∧ 0 ∈ U ∧ (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) ∧
      ∀ b, j b = jet J fun z ↦ y z b

def JetCalc : Prop :=
  ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n),
    (∀ f, AnalyticAt ℂ f 0 → ∀ (ν : Idx I n) (u : List I), (∀ i, u.count i = ν.1 i) → J.b.repr (jet J f) ν = iterD u f 0) ∧
    (∀ f g, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → jet J (f * g) = jet J f * jet J g ∧ jet J (f + g) = jet J f + jet J g) ∧
    (∀ f g, f =ᶠ[𝓝 0] g → jet J f = jet J g) ∧ (∀ a : ℂ, jet J (fun _ ↦ a) = algebraMap ℂ J.B a) ∧
    (∀ i, jet J (fun z ↦ z i) = J.t i) ∧ (∀ i, J.π (J.t i) = 0) ∧ ∀ s : Fin (n + 1 + 1) → I, ∏ a, J.t (s a) = 0

def JetChain : Prop :=
  ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) (ζ : (I → ℂ) → I → ℂ) (a : I → ℂ) (g : (I → ℂ) → ℂ),
    AnalyticAt ℂ ζ 0 → ζ 0 = 0 → AnalyticAt ℂ g 0 → (∀ i, jet J (fun z ↦ ζ z i) = a i • J.t i) →
    ∀ (ν : Idx I n) (u : List I), (∀ i, u.count i = ν.1 i) → J.b.repr (jet J (g ∘ ζ)) ν = iterD u g 0 * ∏ i, a i ^ ν.1 i

def DiagFrame : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) → (F →+* ℂ)), Function.Injective e →
      (∀ (a : 𝓞 F) w, u.ex (fun j ↦ e j (a : F) * w j) = u.ex w ≫ X.rm.act a) →
      ∃ (u' : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (h : Fin (Module.finrank ℚ F) → ℝ), u'.ex = u.ex ∧
        ∃ χ, u'.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ

def GermEx : Prop := AllFam fun _ _ _ _ _ _ _ _ _ _ _ Y ↦ Nonempty (Germ Y)

def CoordEx : Prop := ∃ ε, AllFam fun _ _ _ _ _ _ _ _ _ _ _ Y ↦ ∀ G : Germ Y, Nonempty (Coord ε G)

def JetZeta : Prop := ∃ s : ℤˣ, ∀ ε : ℤˣ, AllFam fun _ _ _ _ _ _ _ _ _ T J Y ↦ ∀ (G : Germ Y) (K : Coord ε G) i,
  jet J (fun z ↦ K.ζ z i) = ((((s * ε : ℤˣ) : ℤ) : ℂ) * T.A i) • J.t i

def JetDet : Prop := ∀ ε : ℤˣ, AllFam fun _ _ _ _ _ _ _ _ _ T J Y ↦ ∀ (G : Germ Y) (K : Coord ε G),
  AnalyticAt ℂ K.C 0 ∧ G.e * jet J K.C = algebraMap ℂ J.B T.C

def Steps : Prop := Chart ∧ HolLift ∧ JetCalc ∧ JetChain ∧ DiagFrame ∧ GermEx ∧ CoordEx ∧ JetZeta ∧ JetDet

namespace Check

open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf)

theorem jet_const (J : JetRing ℂ I n) (a : ℂ) : jet J (fun _ ↦ a) = algebraMap ℂ J.B a := by
  unfold jet taylor
  rw [Finset.sum_range_succ']
  simp [iteratedFDeriv_const_of_ne, Algebra.algebraMap_eq_smul_one]

theorem jet_congr (J : JetRing ℂ I n) {f g : (I → ℂ) → ℂ} (h : f =ᶠ[𝓝 0] g) : jet J f = jet J g := by
  unfold jet taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem jet_linear (J : JetRing ℂ I n) (l : (I → ℂ) →L[ℂ] ℂ) : jet J l = ∑ i, l (Pi.single i 1) • J.t i := by
  have h1 : fderiv ℂ l = fun _ ↦ l := funext fun _ ↦ l.fderiv
  unfold jet taylor
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero]
  · rw [← (Equiv.funUnique (Fin 1) I).symm.sum_comp]
    simp [h1]
  · intro k _
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_succ_apply_right, h1, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp

theorem jet_coord (J : JetRing ℂ I n) (i : I) : jet J (fun z ↦ z i) = J.t i := by
  refine (jet_linear J (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i)).trans ?_
  simp [Pi.single_apply]

theorem t_ne_zero (J : JetRing ℂ I n) (i : I) : J.t i ≠ 0 := J.b.ne_zero _

theorem jet_aeval_X (J : JetRing ℂ I n) (i : I) :
    MvPolynomial.aeval J.t (MvPolynomial.X i : MvPolynomial I ℂ) =
      jet J fun z ↦ MvPolynomial.aeval z (MvPolynomial.X i : MvPolynomial I ℂ) := by
  simp [jet_coord]

theorem coord_nonempty (h1 : JetRingEx) (h2 : JetLift) (h3 : JetBC) (h4 : ModelAlg) (h5 : GermEx) (h6 : CoordEx)
    (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ) (hK : Module.finrank ℚ K = 2) (hd : 0 < d)
    (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf io 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (hio : ∀ i, (φ i).comp (algebraMap K E) = io) (c : Ideal (OF E)) (y : (Af E)ˣ) (hc : c ≠ ⊥) (n : ℕ) :
    ∃ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (J : JetRing ℂ I n) (Y : Family J T.X T.δ T.low) (G : Germ Y) (ε : ℤˣ),
      Nonempty (Coord ε G) ∧ ∀ i, T.A i ≠ 0 := by
  obtain ⟨𝔠, X₀, δ₀, N, T, hA, hO, -, hT⟩ := h4 K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc
  obtain ⟨J₀⟩ := h1 Qb I n
  obtain ⟨J⟩ := h1 ℂ I n
  obtain ⟨Y₀⟩ := h2 (FR E) 𝔠 Qb I n J₀ X₀ δ₀ N hA
  obtain ⟨Y, -⟩ := h3 E I 𝔠 φ _ Qb _ n J₀ J X₀ δ₀ N Y₀ T hO
  obtain ⟨G⟩ := h5 E I 𝔠 φ c y hφ hc n T J Y
  obtain ⟨ε, h⟩ := h6
  exact ⟨𝔠, T, J, Y, G, ε, h E I 𝔠 φ c y hφ hc n T J Y G, fun i ↦ (hT i).1⟩

theorem steps_nonvacuous (h : Steps) (h1 : JetRingEx) (h2 : JetLift) (h3 : JetBC) (h4 : ModelAlg)
    (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ) (hK : Module.finrank ℚ K = 2) (hd : 0 < d)
    (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf io 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (hio : ∀ i, (φ i).comp (algebraMap K E) = io) (c : Ideal (OF E)) (y : (Af E)ˣ) (hc : c ≠ ⊥) (n : ℕ) :
    ∃ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (J : JetRing ℂ I n) (Y : Family J T.X T.δ T.low) (G : Germ Y) (ε : ℤˣ)
      (C : Coord ε G), (∀ i, jet J (fun z ↦ C.ζ z i) ≠ 0 ∧ ¬ (fun z ↦ C.ζ z i) =ᶠ[𝓝 0] fun _ ↦ 0) ∧
        G.e * jet J C.C = algebraMap ℂ J.B T.C := by
  obtain ⟨-, -, -, -, -, h5, h6, ⟨s, hZ⟩, hD⟩ := h
  obtain ⟨𝔠, T, J, Y, G, ε, ⟨C⟩, hA⟩ := coord_nonempty h1 h2 h3 h4 h5 h6 K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc n
  refine ⟨𝔠, T, J, Y, G, ε, C, fun i ↦ ?_, (hD ε E I 𝔠 φ c y hφ hc n T J Y G C).2⟩
  have h0 : jet J (fun z ↦ C.ζ z i) ≠ 0 := by
    rw [hZ ε E I 𝔠 φ c y hφ hc n T J Y G C i]
    haveI := Module.Free.of_basis J.b
    exact smul_ne_zero (mul_ne_zero (Int.cast_ne_zero.2 (Units.ne_zero _)) (hA i)) (t_ne_zero J i)
  exact ⟨h0, fun he ↦ h0 (by rw [jet_congr J he, jet_const, map_zero])⟩

end Check

end GlobalTheory.LatJet.An
