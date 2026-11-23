import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev phiH (P : PAlg l ⥤ Type) (n j : ℕ) : MH P n j → MH P n j := (phiMor P n).pull j

variable (l) in

def tA : Acris l := ACris.periodT (untilt_epsilon (p := l))

variable (l) in

def phiA : Acris l →+* Acris l := ACris.phi ℂ_[l] l

def galA (g : K.fixingSubgroup) : Acris l →+* Acris l := ACris.galCris (IntermediateField.fixingSubgroupEquiv K g)

variable (l) in

def zA : ℤ_[l] →+* Acris l := (algebraMap (Ainf l) (Acris l)).comp (IsPerfectoidField.padicIntToWitt l)

structure PBg (l : ℕ) [Fact l.Prime] {A Γ : Type} [CommRing A] (t : A) (φA : A →+* A) (σA : Γ → (A →+* A)) (z : ℤ_[l] →+* A) : Type 1 where
  C : Type
  [ring : CommRing C]
  [alg : Algebra ℚ_[l] C]
  c : A →+* C
  φ : C →ₐ[ℚ_[l]] C
  σ : Γ → (C →ₐ[ℚ_[l]] C)
  t_unit : IsUnit (c t)
  loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a
  ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0
  φ_c : ∀ a, φ (c a) = c (φA a)
  σ_c : ∀ g a, σ g (c a) = c (σA g a)
  z_c : ∀ x : ℤ_[l], algebraMap ℚ_[l] C x = c (z x)

attribute [instance] PBg.ring PBg.alg

variable (l K) in

abbrev PB : Type 1 := PBg l (tA l) (phiA l) (galA (K := K)) (zA l)

abbrev MuMor (r : Res l K) (M : Model l K) (n : ℕ) :=
  CH.Mor (Wc.OM l (B.schFn M.p) r.ρ n) (B.Oc (B.schFn M.p) (okToOC l K) true n) r.w

def IsMu (r : Res l K) (M : Model l K) (n N : ℕ) (m : MuMor r M n) : Prop :=
  ∃ η : ∀ T, (m.G.obj T).B ≃+* T.B, (∀ T (x : (m.G.obj T).B), (show T.B from m.τ T x) = η T x) ∧
    (∀ T, IsDPMorphism (m.G.obj T).δ T.δ (η T).toRingHom) ∧ (∀ T, (m.G.obj T).J.map (η T).toRingHom = T.J) ∧
    (∀ T w, η T ((m.G.obj T).i w) = T.i (Pb.Mid.wn r n w)) ∧
    ∀ T (h : (m.G.obj T).J ≤ T.J.comap (η T).toRingHom) (φ : T.B ⧸ T.J →+* T.B ⧸ T.J), (∀ x, φ x = x ^ l ^ N) →
      (B.schFn M.p).Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J (η T).toRingHom h)) (m.G.obj T).y.1.2 =
        (B.schFn M.p).Pt.map (CommRingCat.ofHom φ) T.y.1.2

def levH {M : Model l K} {j : ℕ} (x : Pb.HL M j) (n : ℕ) : M.Hc true n j := (show (M.HS true j).lim from x).1 n

def betaM (M : Model l K) (n j : ℕ) (x : M.Hc true n j) : M.MH n j := B.β (B.schFn M.p) (okToOC l K) true n j x

def Pin {r : Res l K} {N : ℕ} (F : Pb.Fac r N) (M : Model l K) (j : ℕ) : Prop :=
  ∀ n, ∃ m : MuMor r M n, IsMu r M n N m ∧ ∀ y : Pb.LW r M j, levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n = m.pull j (y.1 n)

def BIn (M : Model l K) (j : ℕ) : Prop :=
  (∃ u : ℕ, (∀ y : (M.MS j).lim, ∃ x : Pb.HL M j, ∀ n, betaM M n j (levH x n) = tA l ^ u • y.1 n) ∧
    ∀ x : Pb.HL M j, (∀ n, betaM M n j (levH x n) = 0) → tA l ^ u • x = 0) ∧
  (∀ (x : Pb.HL M j) n, betaM M n j (levH (Pb.phiL M j x) n) = phiH M.P n j (betaM M n j (levH x n))) ∧
  ∀ g (x : Pb.HL M j) n, betaM M n j (levH (Pb.galL M j g x) n) =
    M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j (betaM M n j (levH x n))

def InvC (B₀ : PB l K) (r : Res l K) : Prop :=
  (∀ (g : K.fixingSubgroup) w, galA g (r.w w) = r.w w) ∧ ∀ x : B₀.C, (∀ g, B₀.σ g x = x) → ∃ (a : ℕ) (w : WittVector l r.k), (l : B₀.C) ^ a * x = B₀.c (r.w w)

def PinEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K)
  (f : ℕ), 0 < f → ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N ∧ ∃ F : Pb.Fac r N, ∀ M : Model l K, M.Sm → ∀ j, Pin F M j

def BInEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (M : Model l K), M.Sm → ∀ j, BIn M j

def EndEx : Prop := EtSideS → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K) (e' : EMap Model.Sm (dat Amp)), e.Good ∧ (per l K).Facts ∧
    EtSide (Model.Sm (l := l) (K := K)) ∧ (dat Amp).Laws Model.Sm ∧ Nonempty (BMap Model.Sm (dat Amp)) ∧ Nonempty (PMap Model.Sm (dat Amp)) ∧
    ∀ (M : Model l K) (a : (dat Amp).Ch M) (j : ℕ) (v : M.T j) (n : ℕ), (show (M.MS j).lim from e'.e a j v).1 n = e M n j (v.lev n)

def InvEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K),
  (∀ B₀ : PB l K, InvC B₀ r) ∧ ∃ (B₀ : PB l K) (ι : B₀.C →+* (per l K).B), Function.Injective ι ∧ (∀ a, ι (B₀.c a) = (per l K).i a) ∧
    ∀ z, ι (algebraMap ℚ_[l] B₀.C z) = (per l K).q z

end CrystallineSemistableComparison.crystallineComparison

end
