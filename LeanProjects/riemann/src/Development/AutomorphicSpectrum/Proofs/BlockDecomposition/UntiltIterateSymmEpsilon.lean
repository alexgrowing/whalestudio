import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsRootProof

variable {l : ℕ} [hl : Fact l.Prime]

theorem iterate_symm_ofCompatible (y : ℕ → OC l) (hy : ∀ k, y (k + 1) ^ l = y k) (n : ℕ) :
    ((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (IsPerfectoidField.ofCompatible l y hy) =
      IsPerfectoidField.ofCompatible l (fun k => y (k + n))
        (fun k => by rw [show k + 1 + n = (k + n) + 1 by omega]; exact hy (k + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, AInf.frobeniusEquiv_symm_ofCompatible]
    congr 1
    funext k
    exact congrArg y (by omega)

theorem iterate_symm_pow (x : Ob l) (n : ℕ) :
    (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) x) ^ l ^ n = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem untilt_iterate_symm_epsilon (n : ℕ) :
    PreTilt.untilt (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l)) = rootSeqInt l n := by
  rw [epsilon, iterate_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible, zero_add]

theorem sharp_s_eq_oC_untilt (A : PAlg l) (x : Ob l) : A.sharp (A.s x) = A.oC (PreTilt.untilt x) := by
  have h : WittVector.teichmuller l (A.s x) = A.sW (WittVector.teichmuller l x) :=
    (WittVector.map_teichmuller l A.s x).symm
  change A.th (WittVector.teichmuller l (A.s x)) = _
  rw [h, ← PAlg.oC_theta0]
  exact congrArg A.oC (WittVector.fontaineTheta_teichmuller _)

theorem epsRoot : CrystallineSemistableComparison.E.EpsRoot := by
  intro l _ n
  exact ⟨((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l), iterate_symm_pow _ n, fun A => by
    rw [sharp_s_eq_oC_untilt, untilt_iterate_symm_epsilon]⟩

end GlobalTheory.CompanionTheory.EpsRootProof
