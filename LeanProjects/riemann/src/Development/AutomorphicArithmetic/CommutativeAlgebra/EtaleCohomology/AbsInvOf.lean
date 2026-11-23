import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def gRes (r : Res l K) : OK l K →+* Qo l := (Ideal.Quotient.mk _).comp (r.s.comp r.ρ)

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

def AbsCl : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K) (M : Model l K) (f N n j : ℕ),
  (∀ x : r.k, x ^ l ^ f = x) → ∀ (F : PQ M.p (gRes r) ⟶ PQ M.p (gRes r)) (ρ : M.P ⟶ PQ M.p (gRes r)), IsFr f F → IsRd N ρ →
  ∀ m : MuMor r M n, IsMu r M n N m → ∀ y, ∃ x : MH (PQ M.p (gRes r)) n j,
    (phiH _ n j)^[f] x = pullH F n j x ∧ betaM M n j (m.pull j y) = pullH ρ n j x

def AbsInvOf : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K) (B₀ : PB l K), InvC B₀ r →
  ∀ (e : E.EtFam l K), e.Good → ∀ (M : Model l K), M.Sm → ∀ (f N j : ℕ), (∀ x : r.k, x ^ l ^ f = x) → f ∣ N → Pb.Mid.TeichmullerCongruence r N →
  ∀ F : Pb.Fac r N, Pin F M j → BIn M j → ∀ ϖ : OK l K, ¬ IsUnit ϖ → AbsInv B₀ e M j f ϖ

def InjAbs : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop) (D : Dat R),
  R.Facts → EtSide G → D.Laws G → ∀ (e : EMap G D), BMap G D → PMap G D → ∀ M, G M → ∀ (a : D.Ch M) (j : ℕ) (ι : Type) [Fintype ι]
    (v : ι → M.T j) (c : ι → R.A) (u : ℕ), R.t ^ u • ∑ k, c k • e.e a j (v k) = 0 →
    ∀ f : Module.Dual ℚ_[l] (M.V j), ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0

def InjOf : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B₀ : PB l K) (ι : B₀.C →+* (per l K).B),
  Function.Injective ι → (∀ a, ι (B₀.c a) = (per l K).i a) → (∀ z, ι (algebraMap ℚ_[l] B₀.C z) = (per l K).q z) →
  ∀ (G : Model l K → Prop) (Amp : ∀ M : Model l K, E.LineData M.X → Prop), (per l K).Facts → EtSide G → (dat Amp).Laws G →
  ∀ (e : E.EtFam l K) (e' : EMap G (dat Amp)), BMap G (dat Amp) → PMap G (dat Amp) →
  (∀ (M : Model l K) (a : (dat Amp).Ch M) (j : ℕ) (v : M.T j) (n : ℕ), (show (M.MS j).lim from e'.e a j v).1 n = e M n j (v.lev n)) →
  ∀ M, G M → ∀ j, InjE B₀ e M j

end UpperTheory.Ru.crystallineComparison
