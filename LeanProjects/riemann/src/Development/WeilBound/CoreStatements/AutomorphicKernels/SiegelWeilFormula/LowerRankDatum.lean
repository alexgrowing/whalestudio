import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def zOf {n : ℕ} (y : GR n) : Matrix (Fin n) (Fin n) ℂ :=
  (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂) * (u1 (mR y))⁻¹

def IsHolW {n : ℕ} (p q : ℕ) (e : ℤ) (φ : GR n → ℂ) : Prop :=
  ∃ H : (Fin n → Fin n → ℂ) → ℂ, DifferentiableOn ℂ H {Z | ((-(Complex.I / 2)) • (Matrix.of Z - (Matrix.of Z)ᴴ)).PosDef} ∧
    ∀ y, φ y = F0 p q e y * H (if q = 0 then zOf y else -(zOf y)ᴴ)

def HolLead : Prop :=
  ∀ (m n p q : ℕ) (e : ℤ), 1 ≤ m → m < n → (p = m ∧ q = 0 ∨ p = 0 ∧ q = m) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ), Continuous ι →
      (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
        ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 p q e y') →
      ∀ (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), IsOpen U → IsRightDomain U → s₀ ∈ U →
        (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
        (∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
            ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
          ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g) →
        ∀ j : ℕ, (∀ i < j, ∀ g, iteratedDeriv i (Ê · g) s₀ = 0) →
          (∀ ψ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n, (∀ x, mR (nb x) = nU (herm x)) →
            ∀ (g : G) (a b : GR n), ∫ x, iteratedDeriv j (Ê · (g * ι (a * nb x * b))) s₀ * ψ x = 0) →
          ∀ g, IsHolW p q e fun y => iteratedDeriv j (Ê · (g * ι y)) s₀

def HolT : Prop :=
  (∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y) ∧
  ∀ (n p q : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ι : GR n →* G), Continuous ι →
    ∀ A : G → ℂ, Continuous A → (∀ g, IsHolW p q e fun y => A (g * ι y)) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : X → G) (u : X → ℂ) (C : Set G), IsCompact C →
      (∀ x, c x ∈ C) → (∀ x, ‖u x‖ ≤ 1) → (∀ y, AEStronglyMeasurable (fun x => A (c x * ι y) * u x) ν) →
      IsHolW p q e fun y => ∫ x, A (c x * ι y) * u x ∂ν

def GenStep : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), Continuous ι →
      (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
        ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ ∀ P, sec P (x * ι y') = S * sL P y') →
      Continuous (I 1) → (∀ P g (k : GR n), InK (mR k) → I P (g * ι k) = I (ρ k P) g) →
      (∀ g a b P, I (hOp ε c a b P) g = 0) →
      (∀ (g : G) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (H : GR n → ℂ → ℂ), IsOpen U ∧
        (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => H y.1 y.2) (Set.univ ×ˢ U) ∧
        ∀ y, DifferentiableOn ℂ (H y) U ∧ (∀ t : ℝ, H y t = I 1 (g * ι (y * a t))) ∧
          ∀ r : ℕ, iteratedDeriv r (H y) 0 = I ((dil c X ^ r) 1) (g * ι y)) →
      (∃ (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
        (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
        ∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
            ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g c‖ ≤ u c) ∧
          ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) →
      (∀ g, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) s₀ (I 1 g)) →
      ∀ P g, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec P x) g) s₀ (I P g)

def RD.vac {d : SD σ} (R : RD d) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ, g ∈ SB _ ∧
    f = fun X => (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2}

structure LowerRankDatum (d : SD σ) : Type 1 where
  n : ℕ
  Y : Spc F E n
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  ok : Wk (σ := σ) d.B d.A Y d.r d.s d.χ κ dd om S l b K a d.μ d.D

attribute [instance] LowerRankDatum.fin

abbrev LowerRankDatum.sd {d : SD σ} (L : LowerRankDatum d) : SD σ :=
  { B := d.B, m := d.m, n := L.n, A := d.A, Y := L.Y, r := d.r, s := d.s, χ := d.χ, κ := L.κ, dd := L.dd, om := L.om, S := L.S,
    l := L.l, b := L.b, K := L.K, a := L.a, μ := d.μ, D := d.D, bs := d.bs, ok := L.ok }

structure LD (d : SD σ) extends LowerRankDatum d where
  i₀ : Fin d.n
  em : Fin n → Fin d.n
  inj : Function.Injective em
  rng : ∀ i, i ≠ i₀ ↔ i ∈ Set.range em
  j : G2 σ Y →* d.G
  cont : Continuous j
  j_in : ∀ g, (inFrame d.b (j g)).submatrix (Sum.map em em) (Sum.map em em) = inFrame b g
  j_out : ∀ g, ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
  res : ∀ Φ ∈ d.sch, ∀ Φ' ∈ toLowerRankDatum.sd.sch,
    (∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → toLowerRankDatum.sd.T Φ' (X.submatrix id em) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a i₀ = 0) → toLowerRankDatum.sd.T (om g Φ') (X.submatrix id em) = d.T (d.om (j g) Φ) X

namespace LD

variable {d : SD σ} (L : LD d)

def IsRes (Φ : d.Fn) (Φ' : L.sd.Fn) : Prop :=
  Φ' ∈ L.sd.sch ∧ ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → L.sd.T Φ' (X.submatrix id L.em) = d.T Φ X

def ratV : AddSubgroup (Fin L.n → AE F E) := AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _))

def UData (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E)) : Prop :=
  (∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) 0 0 a') ∧
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain L.ratV 𝓤 ν ∧ ν 𝓤 = 1

def IsSub (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) : Prop :=
  (∀ i, T.1.1 L.i₀ i = 0 ∧ T.1.1 i L.i₀ = 0) ∧ T'.1.1 = T.1.1.submatrix L.em L.em

end LD

def MainV (c : ℂ) {d : SD σ} (R : RD d) : Prop := ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)

def MainC (c : ℂ) (d : SD σ) : Prop := ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)

def WhitAt (c : ℂ) (d : SD σ) (Φ : d.Fn) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))

def EisWk : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁

def WhitEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m = d.n → ∀ Φ, d.KFin Φ → WhitAt 2 d Φ

def WhitLow : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), d.m < d.n → ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → WhitAt 0 d Φ

def MainEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m = d.n → MainC 2 d

def LDEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), 2 ≤ d.n → Nonempty (LD d)

def VacK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), (∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac) ∧ R.vac ≤ R.fock ∧
  ∀ (L : LD d) (R' : RD L.sd), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac

def IwaQ : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ x : d.G, ∃ (q : d.G) (g : L.sd.G) (k : d.G) (r : ℝ) (c : ℂ), k ∈ d.K ∧
  x = q * L.j g * k ∧ 0 < r ∧ (∀ g' : L.sd.G, d.a (L.j g' * x) = r * L.a (g' * g)) ∧
  ∀ Φ ∈ d.sch, ∀ g' (X : Mx F E d.m d.n), (∀ a, X a L.i₀ = 0) →
    d.T (d.om (L.j g' * q) Φ) X = c * d.T (d.om (L.j g') Φ) X

def CTSplit : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∃ c₂ : d.G → ℂ,
    (∀ x, ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
      fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
        ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1 + c₂ x) ∧
    ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
      c₂ (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * c₂ x

def UEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), (∃ uM ν 𝓤, L.UData uM ν 𝓤) ∧ ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ w (φ : d.G → ℂ), Continuous φ →
  (∀ u ∈ L.ratV, ∀ x, φ (uM u * x) = φ x) →
  (∀ u (y : GR d.n), uM u = R.ι w y → ∀ x, φ (uM u * x) = φ x) → ∀ u x, φ (uM u * x) = φ x

def FcConj : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
  (∀ T, ¬ IsND T → ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x, fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x)) ∧
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ u ∈ L.ratV, ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x

def OrbRes : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), (d.m < d.n → ∀ T, IsND T → ∀ Φ, d.orb T Φ = 0) ∧
  ∀ (L : LD d) T T', L.IsSub T T' → ∀ Φ Φ', L.IsRes Φ Φ' → d.orb T Φ = L.sd.orb T' Φ'

def Step : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ R' : RD L.sd, d.m < d.n → MainV 2 R' → MainV 2 R

def StepOf : Prop :=
  HolLead → HolT → TAll → ThetaCoef → AuxiliaryPrimeFunction → CoefEx → FockMem → LiftEx → LocOpEx → LocInst → GSplit → PolyKFin → SecK → EisWk →
    LamBd → LamSing → FourierZero → Unfold → WhitLow → VacK → IwaQ → CTSplit → UEx → FcConj → OrbRes → Step

def VacAll : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ c : ℂ, MainV c R → MainC c d

def VacAllOf : Prop :=
  GenStep → TAll → AuxiliaryPrimeFunction → FockMem → LiftEx → LocOpEx → LocInst → GSplit → GIinv → GIdil → KFinPoly → PolyKFin → SecK → EisWk →
    VacAll

def MainLe : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m ≤ d.n → MainC 2 d

def MainLeOf : Prop := RDEx → LDEx → VacK → PolyKFin → MainEq → Step → VacAll → MainLe

def FieldOf : Prop := EisBL → SecK → SWStdLt → MainLe → SiegelWeilStd

end PositivityTheory.SiegelWeilFormula

end
