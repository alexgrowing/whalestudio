import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocFinal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum

noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hk_zero' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) : hk ρ K e 0 = 0 := by
  simp [hk]

theorem hk_supp (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v : V) :
    Function.HasFiniteSupport fun q : GL ι F ⧸ K => e q.out • ρ q.out v := by
  refine (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K he.1 e he.2.2.1).subset fun q hq => ?_
  intro h0
  exact hq (by simp [show e q.out = 0 from h0])

theorem hk_add' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v w : V) :
    hk ρ K e (v + w) = hk ρ K e v + hk ρ K e w := by
  unfold hk
  rw [← finsum_add_distrib (hk_supp ρ K e he v) (hk_supp ρ K e he w)]
  exact finsum_congr fun q => by rw [map_add, smul_add]

theorem hk_smul' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (c : ℂ) (v : V) :
    hk ρ K e (c • v) = c • hk ρ K e v := by
  unfold hk
  rw [smul_finsum]
  exact finsum_congr fun q => by rw [map_smul, smul_comm]

def hkEnd (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) :
    Module.End ℂ (fixed ρ K) where
  toFun v := ⟨hk ρ K e v.1, ((PositivityTheory.Rg.BcN.F2.Final.hkAlg F ι) K e e he he).2.2 V ρ v.1 v.2 |>.1⟩
  map_add' v w := Subtype.ext (hk_add' ρ K e he v.1 w.1)
  map_smul' c v := Subtype.ext (hk_smul' ρ K e c v.1)

theorem hkEnd_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (k : ℕ) :
    ∀ x : fixed ρ K, ((hkEnd ρ K e he ^ k) x).1 = (hk ρ K e)^[k] x.1 := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

theorem hk_iter_zero (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (k : ℕ) :
    (hk ρ K e)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, hk_zero', ih]

theorem nonnil_of_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e)
    [FiniteDimensional ℂ (fixed ρ K)] (m : ℕ) (hdim : Module.finrank ℂ (fixed ρ K) ≤ m) (u : V) (hu : u ∈ fixed ρ K)
    (hne : (hk ρ K e)^[m] u ≠ 0) : ∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0 := by
  intro r
  rcases le_total r m with hr | hr
  · refine ⟨u, hu, fun h0 => hne ?_⟩
    have : m = (m - r) + r := (Nat.sub_add_cancel hr).symm
    rw [this, Function.iterate_add_apply, h0, hk_iter_zero]
  · by_contra hall
    push_neg at hall
    set T := hkEnd ρ K e he
    have hker : LinearMap.ker (T ^ r) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by rw [hkEnd_pow]; exact hall x.1 x.2)
    have e1 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) (le_trans hdim hr)
    have e2 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) hdim
    have hm : (⟨u, hu⟩ : fixed ρ K) ∈ LinearMap.ker (T ^ m) := by
      rw [e2, ← e1, hker]; trivial
    rw [LinearMap.mem_ker] at hm
    apply hne
    have := congrArg Subtype.val hm
    rw [hkEnd_pow] at this
    exact this

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sub_of_pow {n : ℕ} (D : Pre E n) (w : Pl E) (K' : Subgroup (GLw n w)) (e : GLw n w → ℂ) (he : IsHk K' e)
    (P : SmIrr (GLw n w))
    (hkill : ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0)
    (m : ℕ) (hdim : Module.finrank ℂ (fixed (prodAt D w) K') < m) (u : _) (hu : u ∈ fixed (prodAt D w) K')
    (hne : (hk (prodAt D w) K' e)^[m - 1] u ≠ 0) : GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) := by
  have hsm : GlobalTheory.PRep.IsSmooth (prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : GlobalTheory.SmGL.HasFiniteLength (prodAt D w) :=
    PositivityTheory.Rg.BcN.F2.Final.prodFinLen (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i))
      (GlobalTheory.SmGL.stdBlocks D.N D.h) (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth)
      (fun i => (D.σ i w).irred)
  haveI : FiniteDimensional ℂ (fixed (prodAt D w) K') :=
    GlobalTheory.LeviFactor.finiteDimensional_fixed_of_hasFiniteLength
      (fun Y _ _ π hs hi => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible (w.adicCompletion E) (Fin n) Y π hs hi)
      hsm hfl K' he.1 he.2.1
  refine PositivityTheory.Rg.BcN.F2.Final.subOfNonNil' (w.adicCompletion E) (Fin n) K' e he P.V P.ρ P.smooth P.irred _
    (prodAt D w) hsm hfl ?_ ?_
  · intro W _ _ τ hs hi hsub hemp v hv
    exact hkill ⟨W, τ, hs, hi⟩ hsub hemp v hv
  · exact nonnil_of_pow (prodAt D w) K' e he (m - 1) (by omega) u hu hne

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
