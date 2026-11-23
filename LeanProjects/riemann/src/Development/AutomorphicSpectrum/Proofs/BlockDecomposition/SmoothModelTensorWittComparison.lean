import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrisZeroSurjective
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcAcris

theorem pull_comm {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K) (j n : ℕ)
    (Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n)))) (a : AW r)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M n) :
    (toQ Q' ((base l).cris n)).pull j (idA r a • bWL r M n j y) =
      (base l).cris n a • (toQ Q' ((base l).cris n)).pull j
        ((B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y) := by
  have e : bWL r M n j y = (B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y :=
    congrArg (fun t => CH.Mor.pull t j y) (bWMorL_eq r M n)
  exact (congrArg (fun v => (toQ Q' ((base l).cris n)).pull j (idA r a • v)) e).trans
    (LinearMap.map_smulₛₗ ((toQ Q' ((base l).cris n)).pull j) (idA r a) _)

set_option maxHeartbeats 12000000 in

theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n,
    Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n)
      (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  intro l _ K r M hM j n
  letI := (Mid.wn r n).toAlgebra
  haveI : Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := GlobalTheory.T.flat_acris_truncated_witt r n
  obtain ⟨U⟩ := cov_of_sm M hM
  let m := nm r M n
  let Q : ObjectProperty (Thick (nlFun (Wc.pd l r.k n) l M.X M.p ((Wc.res l r.k n).comp r.ρ))) := St ⊤ {⊤}
  let Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n))) := St ⊤ {⊤}
  have hQ : ∀ T, Q T := st_all
  have hQ' : ∀ T, Q' T := st_all
  have h : ∀ T, Q' T → Q ((m.mor l).functor.obj T) := fun T _ => hQ _
  have ha : ∀ a, (m.smor Q Q' h).LeC a (oT Q) (oT Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_top _ a _ _ (oT_top Q')
  have hb : ∀ a, (m.smor Q Q' h).LeC a (oB Q) (oB Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_bot _ a _ _ fun T => oB_bot Q _
  have T := GlobalTheory.T.nilpotent_identity_morphism_compat (Fact.out : l.Prime).ne_zero (l_nil r n) m rfl rfl U Q Q' rfl rfl h ha hb j
  refine tens_change (A := AW r) (Ideal.Quotient.mk _) ((base l).cris n) (cris_surjective n) (fun w => rfl)
    Ideal.Quotient.mk_surjective ((l : WittVector l r.k) ^ n)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) ?_
    ((toQ Q (Ideal.Quotient.mk _)).pull j) (toQ_pull_bijective Q _ hQ j)
    ((toQ Q' ((base l).cris n)).pull j).toAddMonoidHom (toQ_pull_bijective Q' _ hQ' j)
    _ _ ?_ T
  · intro a h0
    obtain ⟨b, hb'⟩ := cris_ker n a h0
    refine ⟨b, hb'.trans ?_⟩
    change _ = r.w _ * b
    rw [map_pow, map_natCast]
  · intro a y
    have key := sqC_toQ m Q Q' h (Ideal.Quotient.mk _) ((base l).cris n) r.w (Mid.wn_mk r n) ((base l).cris n a)
      (ha _) (hb _) j y
    exact (pull_comm r M j n Q' a y).trans key.symm

end GlobalTheory.CompanionTheory.BcAcris
