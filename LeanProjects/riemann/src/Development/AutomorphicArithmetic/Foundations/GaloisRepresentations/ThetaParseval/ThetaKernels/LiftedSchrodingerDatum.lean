import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SWStdLtK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsS

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def RD_k.vac {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ, g ∈ SB _ ∧
    f = fun X => (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2}
structure LiftedSchrodingerDatum (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type 1 where
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
  ok : _root_.PositivityTheory.SiegelWeilFormula.Wk_k (σ := σ) d.B d.A Y d.r d.s d.χ κ dd om S l b K a d.μ d.D
attribute [instance] _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum.fin
abbrev LiftedSchrodingerDatum.sd {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d) : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ :=
  { B := d.B, m := d.m, n := L.n, A := d.A, Y := L.Y, r := d.r, s := d.s, χ := d.χ, κ := L.κ, dd := L.dd, om := L.om, S := L.S,
    l := L.l, b := L.b, K := L.K, a := L.a, μ := d.μ, D := d.D, bs := d.bs, ok := L.ok }
structure LD_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) extends _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d where
  i₀ : Fin d.n
  em : Fin n → Fin d.n
  inj : Function.Injective em
  rng : ∀ i, i ≠ i₀ ↔ i ∈ Set.range em
  j : G2 σ Y →* d.G
  cont : Continuous j
  j_in : ∀ g, (inFrame d.b (j g)).submatrix (Sum.map em em) (Sum.map em em) = inFrame b g
  j_out : ∀ g, ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
  res : ∀ Φ ∈ d.sch, ∀ Φ' ∈ toLiftedSchrodingerDatum.sd.sch,
    (∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T Φ' (X.submatrix id em) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T (om g Φ') (X.submatrix id em) = d.T (d.om (j g) Φ) X
namespace LD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsRes (Φ : d.Fn) (Φ' : L.sd.Fn) : Prop :=
  Φ' ∈ L.sd.sch ∧ ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → L.sd.T Φ' (X.submatrix id L.em) = d.T Φ X
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.ratV : AddSubgroup (Fin L.n → AE F E) := AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _))
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.UData (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E)) : Prop :=
  (∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) 0 0 a') ∧
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain L.ratV 𝓤 ν ∧ ν 𝓤 = 1
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsSub (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) : Prop :=
  (∀ i, T.1.1 L.i₀ i = 0 ∧ T.1.1 i L.i₀ = 0) ∧ T'.1.1 = T.1.1.submatrix L.em L.em
end LD
def MainV_k (c : ℂ) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Prop := ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def MainC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Prop := ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def WhitAt_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
def EisWk_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁
def WhitEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 2 d Φ
def WhitLow_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), d.m < d.n → ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 0 d Φ
def MainEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def LDEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), 2 ≤ d.n → Nonempty (_root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def VacK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), (∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac) ∧ R.vac ≤ R.fock ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac
def IwaQ_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ x : d.G, ∃ (q : d.G) (g : L.sd.G) (k : d.G) (r : ℝ) (c : ℂ), k ∈ d.K ∧
  x = q * L.j g * k ∧ 0 < r ∧ (∀ g' : L.sd.G, d.a (L.j g' * x) = r * L.a (g' * g)) ∧
  ∀ Φ ∈ d.sch, ∀ g' (X : Mx F E d.m d.n), (∀ a, X a L.i₀ = 0) →
    d.T (d.om (L.j g' * q) Φ) X = c * d.T (d.om (L.j g') Φ) X
def CTSplit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∃ c₂ : d.G → ℂ,
    (∀ x, ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
      fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
        ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1 + c₂ x) ∧
    ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
      c₂ (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * c₂ x
def UEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), (∃ uM ν 𝓤, L.UData uM ν 𝓤) ∧ ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ w (φ : d.G → ℂ), Continuous φ →
  (∀ u ∈ L.ratV, ∀ x, φ (uM u * x) = φ x) →
  (∀ u (y : GR d.n), uM u = R.ι w y → ∀ x, φ (uM u * x) = φ x) → ∀ u x, φ (uM u * x) = φ x
def FcConj_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
  (∀ T, ¬ IsND T → ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x, fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x)) ∧
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ u ∈ L.ratV, ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x
def OrbRes_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (d.m < d.n → ∀ T, IsND T → ∀ Φ, d.orb T Φ = 0) ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) T T', L.IsSub T T' → ∀ Φ Φ', L.IsRes Φ Φ' → d.orb T Φ = L.sd.orb T' Φ'
def Step_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd, d.m < d.n → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R
def StepOf_k : Prop :=
  HolLead → HolT → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k →
    _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k → _root_.PositivityTheory.SiegelWeilFormula.UEx_k → _root_.PositivityTheory.SiegelWeilFormula.FcConj_k → _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k
def VacAll_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ c : ℂ, _root_.PositivityTheory.SiegelWeilFormula.MainV_k c R → _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d
def MainLe_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m ≤ d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def MainLeOf_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.MainEq_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k
def FieldOf_k : Prop := _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k → _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k
end PositivityTheory.SiegelWeilFormula
end
end
