import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName

open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

def smSubM (r : ℕ) (TT : ℝ) (m : ℕ∞) : Subalgebra ℂ (MA.Qp r TT → ℂ) where
  carrier := {f | ContDiffOn ℝ (smM m) (MA.ext f) (MA.Qset r TT)}
  mul_mem' {f g} hf hg := (hf.mul hg).congr fun x hx => by simp [MA.ext, hx]
  add_mem' {f g} hf hg := (hf.add hg).congr fun x hx => by simp [MA.ext, hx]
  algebraMap_mem' z := (contDiffOn_const (c := z)).congr fun x hx => by simp [MA.ext, hx]

theorem smSubM_top : smSubM r TT ⊤ = MA.smSub r TT := rfl

theorem smSub_le (m : ℕ∞) : MA.smSub r TT ≤ smSubM r TT m := by
  intro f hf
  show ContDiffOn ℝ (smM m) (MA.ext f) (MA.Qset r TT)
  exact (show ContDiffOn ℝ MA.sm (MA.ext f) (MA.Qset r TT) from hf).of_le
    (WithTop.coe_le_coe.mpr le_top)

theorem smSubM_mono {m m' : ℕ∞} (h : m ≤ m') : smSubM r TT m' ≤ smSubM r TT m := by
  intro f hf
  show ContDiffOn ℝ (smM m) (MA.ext f) (MA.Qset r TT)
  exact (show ContDiffOn ℝ (smM m') (MA.ext f) (MA.Qset r TT) from hf).of_le (WithTop.coe_le_coe.mpr h)

end cls

section jets

variable {r : ℕ} {TT : ℝ}

def JetEq (m : ℕ∞) (q : MA.Qp r TT) (f g : MA.Qp r TT → ℂ) : Prop :=
  ∀ k : ℕ, (k : ℕ∞) ≤ m → iteratedFDeriv ℝ k (MA.ext f) q.1 = iteratedFDeriv ℝ k (MA.ext g) q.1

open scoped Classical in

def actJ (m : ℕ∞) (a : (MA.anQ r TT).Op) (u : MA.Qp r TT → ℂ) : MA.Qp r TT → ℂ :=
  fun q => if h : ∃ g : MA.SmQ r TT, JetEq m q g.1 u then (show MA.SmQ r TT from a (Classical.choose h)).1 q else 0

end jets

section ord

variable {r : ℕ} {TT : ℝ}

inductive Fac (r : ℕ) (TT : ℝ) : Type
  | mul (f : MA.SmQ r TT) : Fac r TT
  | eul (v : M.Var r) : Fac r TT

def Fac.op : Fac r TT → (MA.anQ r TT).Op
  | .mul f => (MA.anQ r TT).mulOp f
  | .eul v => MA.eulerQ v

def Fac.ord : Fac r TT → ℕ
  | .mul _ => 0
  | .eul _ => 1

def OpOrd (r : ℕ) (TT : ℝ) (d : ℕ) : Submodule ℂ (MA.anQ r TT).Op :=
  Submodule.span ℂ {a | ∃ l : List (Fac r TT), (l.map Fac.ord).sum ≤ d ∧ a = (l.map Fac.op).prod}

def PrOrd (d : ℕ) (a : (MA.anQ r TT).Pr) : Prop := a.1 ∈ OpOrd r TT d ∧ a.2.unop ∈ OpOrd r TT d

def AOrd (P : M.Par) (d : ℕ) (a : MA.A P (MA.DQ P)) : Prop := ∀ π π', PrOrd (TT := P.TT) d (a π π')

end ord

def JetLocal : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → ∀ m : ℕ∞, (d : ℕ∞) ≤ m →
    ∀ (q : MA.Qp r TT) (g g' : MA.SmQ r TT), JetEq m q g.1 g'.1 →
      (show MA.SmQ r TT from a g).1 q = (show MA.SmQ r TT from a g').1 q

def JetExists : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (m : ℕ∞) (u : MA.Qp r TT → ℂ), u ∈ smSubM r TT m → ∀ q : MA.Qp r TT,
    ∃ g : MA.SmQ r TT, JetEq m q g.1 u

def JetAgree : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → ∀ m : ℕ∞, (d : ℕ∞) ≤ m →
    ∀ g : MA.SmQ r TT, actJ m a g.1 = (show MA.SmQ r TT from a g).1

def JetReg : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → ∀ m : ℕ∞, (d : ℕ∞) ≤ m →
    ∀ u ∈ smSubM r TT m, actJ m a u ∈ smSubM r TT (m - d)

def JetComp : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d e : ℕ) (a b : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → b ∈ OpOrd r TT e → ∀ m : ℕ∞,
    ((d + e : ℕ) : ℕ∞) ≤ m → ∀ u ∈ smSubM r TT m, actJ (m - e) a (actJ m b u) = actJ m (a * b) u

def JetLin : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (d : ℕ) (a b : (MA.anQ r TT).Op), a ∈ OpOrd r TT d → b ∈ OpOrd r TT d → ∀ m : ℕ∞,
    (d : ℕ∞) ≤ m → ∀ u ∈ smSubM r TT m, ∀ z : ℂ,
      actJ m (a + b) u = actJ m a u + actJ m b u ∧ actJ m (z • a) u = z • actJ m a u

theorem jetAgree_of_local (h : JetLocal) : JetAgree := by
  intro r TT d a ha m hd g
  funext q
  have hex : ∃ g' : MA.SmQ r TT, JetEq m q g'.1 g.1 := ⟨g, fun _ _ => rfl⟩
  unfold actJ
  rw [dif_pos hex]
  exact h r TT d a ha m hd q _ g (Classical.choose_spec hex)

theorem jetExists_top (r : ℕ) (TT : ℝ) (u : MA.Qp r TT → ℂ) (hu : u ∈ smSubM r TT ⊤) (q : MA.Qp r TT) :
    ∃ g : MA.SmQ r TT, JetEq ⊤ q g.1 u :=
  ⟨⟨u, hu⟩, fun _ _ => rfl⟩

def HatSetOrdBound : Prop :=
  ∃ Cd : ℕ, ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L →
    (∀ X ∈ MA.hatSet P L, AOrd P (Cd * (P.r + 1)) X ∧ AOrd P (Cd * (P.r + 1)) (star X)) ∧
    (∀ b ∈ MA.bddSet P L, AOrd P 0 b) ∧
    ∀ (l : ℕ) (Y : ℂ), AOrd P (Cd * (P.r + 1)) (Wd.C0 (MA.startM P (MA.DQ P) l).QQ (MA.sites P (MA.DQ P)) Y) ∧
      AOrd P (Cd * (P.r + 1)) (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) Y)

section En

variable (P : M.Par) (m : ℕ∞)

def actAJ (a : MA.A P (MA.DQ P)) (u : M.Ty P → MA.Qp P.r P.TT → ℂ) : M.Ty P → MA.Qp P.r P.TT → ℂ :=
  fun π => ∑ π', actJ m (a π π').1 (u π')

def ipF (f g : M.Ty P → MA.Qp P.r P.TT → ℂ) : ℂ := ∑ π, ∫ q, f π q * conj (g π q) ∂MA.mu0 P.r P.TT

def phiA (φ : ℝ → ℝ) : MA.A P (MA.DQ P) :=
  MA.sc P (MA.DQ P) ((MA.DQ P).fnP (MA.toSm P fun q => ((φ (MA.Gq P q) : ℝ) : ℂ))
    (MA.toSm P fun q => ((φ (MA.Gq P q) : ℝ) : ℂ)))

def chiA (c : LE.Cut) (ε : ℝ) : MA.A P (MA.DQ P) := phiA P fun x => c.sc ε 1 x

def JDecayM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (j : M.Ty P → MA.Qp P.r P.TT → ℂ) (n : ℕ) : Prop :=
  ∀ w : List (MA.A P (MA.DQ P)), w.length ≤ n → (∀ a ∈ w, a ∈ MA.hatSet P L) → ∀ π,
    Integrable (fun q => ‖actAJ P m w.prod j π q‖ ^ 2) (MA.mu0 P.r P.TT)

def JAdjM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (j : M.Ty P → MA.Qp P.r P.TT → ℂ) (n : ℕ) : Prop :=
  ∀ (φ : ℝ → ℝ) (ε : ℝ), 0 < ε → LE.SmoothLog φ → (∀ x, x ≤ ε → φ x = 0) →
    (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ X ∈ MA.hatSet P L, ∀ v w : List (MA.A P (MA.DQ P)),
      v.length + w.length + 1 ≤ n → (∀ a ∈ v ++ w, a ∈ MA.hatSet P L) →
      ipF P (actAJ P m (X * phiA P φ * b * v.prod) j) (actAJ P m w.prod j) =
        ipF P (actAJ P m (phiA P φ * b * v.prod) j) (actAJ P m (star X * w.prod) j)

def JEigenM (j : M.Ty P → MA.Qp P.r P.TT → ℂ) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) : Prop :=
  ∀ Y : ℝ, actAJ P m (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ)) j =
    fun π q => (∏ s, ((Y : ℂ) + lam s)) * j π q

def truncatedEnergyAtOrder (l : ℕ) (j : M.Ty P → MA.Qp P.r P.TT → ℂ) (c : LE.Cut) (ε : ℝ) (w : List (Bool × ℝ)) : ℝ :=
  (ipF P (actAJ P m ((w.reverse.map fun x =>
      Wd.C0 (MA.startM P (MA.DQ P) l).QQ (MA.sites P (MA.DQ P)) (x.2 : ℂ)).prod * chiA P c ε) j)
    (actAJ P m (chiA P c ε) j)).re

end En

theorem level_system_admissibility_indep (P : M.Par) (l : ℕ) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)
    (j j' : M.Ty P → MA.SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (N : ℕ)
    (w : List (Bool × ℝ)) :
    ((MA.sysQ P l L j lam α β Lb c N).admitted w ↔ (MA.sysQ P l L j' lam α β Lb c N).admitted w) ∧
      (MA.sysQ P l L j lam α β Lb c N).size w = (MA.sysQ P l L j' lam α β Lb c N).size w :=
  ⟨Iff.rfl, rfl⟩

def LemmaEModelM : Prop :=
  ∃ C₂ C₆ Cn : ℝ, 0 < C₂ ∧ 0 < C₆ ∧
    ∀ (P : M.Par) (l : ℕ) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (m : ℕ) (j : M.Ty P → MA.Qp P.r P.TT → ℂ)
      (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β : ℝ) (c : LE.Cut) (Ntot : ℕ),
      (∀ π, j π ∈ smSubM P.r P.TT m) → Cn * ((P.k + 2 * P.r + 1 : ℕ) : ℝ) * ((Ntot : ℝ) + 1) * ((P.r : ℝ) + 1) ^ 2 ≤ (m : ℝ) →
      MA.HidaSetting P l L lam α β → JDecayM P m L j (2 * Ntot + 2) → JAdjM P m L j (2 * Ntot + 2) →
      JEigenM P m j lam → P.r + 1 ≤ Ntot →
      C₆ * ((P.k : ℝ) * Ntot * ((P.r : ℝ) + 1) ^ 2 + (Ntot : ℝ) ^ 2 * ((P.r : ℝ) + 1) ^ 2) ≤ β - α →
      ∀ w : List (Bool × ℝ),
        (MA.sysQ P l L 0 lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) c Ntot).admitted w → w.length ≤ Ntot →
        Filter.Tendsto (fun ε : ℝ => truncatedEnergyAtOrder P m l j c ε w) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((MA.sysQ P l L 0 lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) c Ntot).size w *
            ∫ q, ∑ π, ‖j π q‖ ^ 2 ∂MA.mu0 P.r P.TT))

def LemmaEModelMOfParts : Prop :=
  JetLocal → JetExists → JetReg → JetComp → JetLin → HatSetOrdBound → LE.LemmaE → LE.Constants → LemmaEModelM

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}

theorem fflM_top {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : FFlM ⊤ k r z z' π π' i Dm = Q.FFl k r z z' π π' i Dm := rfl

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def trJF (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    M.Ty (D.parOf S v) → MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ :=
  fun ρ q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))

def IsGaugeM (m : ℕ∞) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ J ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ Y : ℝ,
    trJF S T v e (Q.CV S.G.k S.G.r (Y : ℂ) J) =
      actAJ (D.parOf S v) m
        (Wd.C0 (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v))) (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (Y : ℂ))
        (trJF S T v e J)

def IsModelPlaceM (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (v : Fin S.f)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r) (m : ℕ)
    (j : M.Ty (D.parOf S v) → MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
    (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : ℝ) : Prop :=
  c.χ = χ ∧ 0 < Cm ∧ 0 < σ ∧ (∀ π, j π ∈ smSubM (D.parOf S v).r (D.parOf S v).TT m) ∧
  MA.HidaSetting (D.parOf S v) (S.l + 1) L lam (S.cutLo v) (S.cutHi v) ∧
  JDecayM (D.parOf S v) m L j (2 * S.Ntop + 2) ∧ JAdjM (D.parOf S v) m L j (2 * S.Ntop + 2) ∧
  JEigenM (D.parOf S v) m j lam ∧
  (∀ ε, 0 < ε → ∀ a : List C.Letter, D.AdmAt S v a →
    C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
      ((Cm * truncatedEnergyAtOrder (D.parOf S v) m (S.l + 1) j c (σ * ε) a : ℝ) : ℂ)) ∧
  ∀ Lb : ℝ, ∀ a : List C.Letter, D.AdmAt S v a →
    (MA.sysQ (D.parOf S v) (S.l + 1) L 0 lam (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
    (MA.sysQ (D.parOf S v) (S.l + 1) L 0 lam (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a

end place

def ModelPlaceBuilt4 : Prop :=
  ∀ Cn : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r) (m : ℕ)
        (j : M.Ty (D.parOf S v) → MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        Cn * ((2 * S.G.r + S.G.k + 1 : ℕ) : ℝ) * ((S.Ntop : ℝ) + 1) * ((S.G.r : ℝ) + 1) ^ 2 ≤ (m : ℝ) ∧ IsModelPlaceM S T f χ v L m j lam c Cm σ

def RegFFM : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ (v : Fin S.f) (m : ℕ),
      6 * ((S.G.r : ℝ) + 1) * m + 9 * ((S.G.r : ℝ) + 1) * ((2 * S.G.r + S.G.k + 1 : ℕ) : ℝ) ^ 2 ≤ A₀ →
      B.JF (T v).base (f v) ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
        ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def GaugeExistsM : Prop :=
  ∃ (Cc : ℝ) (Cg : ℕ), ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), IsFrame S T v e ∧
      ∀ m : ℕ, Cg * (2 * S.G.r + S.G.k + 1) * (S.G.r + 1) ≤ m → IsGaugeM m S T v e

def GaugeMOfGauge : Prop :=
  ∃ (Cc : ℝ) (Cg : ℕ), ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      ∀ m : ℕ, Cg * (2 * S.G.r + S.G.k + 1) * (S.G.r + 1) ≤ m → IsGaugeM m S T v e

def CutTrM : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (c : LE.Cut), c.χ = χ → ∀ ε : ℝ, 0 < ε →
      trJF S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) =
        fun ρ q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) * trJF S T v e (B.JF (T v).base (f v)) ρ q

def EnergyTrM : Prop :=
  ∃ (Cc Ce : ℝ), ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (m : ℕ), IsFrame S T v e → Ce * ((2 * S.G.r + S.G.k + 1 : ℕ) : ℝ) * ((S.Ntop : ℝ) + 1) * ((S.G.r : ℝ) + 1) ^ 2 ≤ (m : ℝ) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ a : List C.Letter, D.AdmAt S v a →
          C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
            ipF (D.parOf S v)
              (trJF S T v e (a.reverse.foldr (fun x J => (M.sgn (D.parOf S v) (S.l + 1)) • Q.CV S.G.k S.G.r (x.2 : ℂ) J)
                (B.JF (T v).base (D.cutF (T v).base χ (f v) ε))))
              (trJF S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)))

def JDecayTrM : Prop :=
  ∃ (Cc Cd : ℝ), ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r) (m : ℕ),
      IsFrame S T v e → IsGaugeM m S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → Cd * ((2 * S.G.r + S.G.k + 1 : ℕ) : ℝ) * ((S.Ntop : ℝ) + 1) * ((S.G.r : ℝ) + 1) ^ 2 ≤ (m : ℝ) →
      B.JF (T v).base (f v) ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      JDecayM (D.parOf S v) m L (trJF S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

def JAdjTrM : Prop :=
  ∃ (Cc Cd : ℝ), ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r) (m : ℕ),
      IsFrame S T v e → IsGaugeM m S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → Cd * ((2 * S.G.r + S.G.k + 1 : ℕ) : ℝ) * ((S.Ntop : ℝ) + 1) * ((S.G.r : ℝ) + 1) ^ 2 ≤ (m : ℝ) →
      B.JF (T v).base (f v) ∈ FFlM m S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      JAdjM (D.parOf S v) m L (trJF S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

def ModelPlaceBuilt4OfLeaves : Prop :=
  MA.ModelFrameAn → LamCfgInterlaces → AdmInCut → BesselEigen → EnergyReal →
    RegFFM → GaugeExistsM → CutTrM → EnergyTrM → JDecayTrM → JAdjTrM →
    JetLocal → JetExists → JetReg → JetComp → JetLin → HatSetOrdBound → ModelPlaceBuilt4

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
