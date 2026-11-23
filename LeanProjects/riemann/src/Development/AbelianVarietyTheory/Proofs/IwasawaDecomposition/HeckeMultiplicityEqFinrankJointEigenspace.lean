import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  NumberField IsDedekindDomain Polynomial Module Module.End

section Gen
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem heckeEig_mem_iff_gens (N : NData R H what₂) (i : N.Loc) (x : N.X i)
    (y : TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :
    y ∈ heckeEig (N.T i) (N.act i) x ↔ ∀ v k, SplitOut N i v → 1 ≤ k → k ≤ R.nV →
      ((N.act i (N.hT i v k)).baseChange (FractionRing (N.O i))) y =
        algebraMap (N.O i) (FractionRing (N.O i)) ((N.hT i v k : N.X i → N.O i) x) • y := by
  constructor
  · intro hy v k _ _ _
    exact mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy (N.hT i v k))
  · intro hy
    refine (Submodule.mem_iInf _).2 fun f => mem_eigenspace_iff.2 ?_
    obtain ⟨f, hf⟩ := f
    have hf' := hf
    rw [← N.T_gen i] at hf'
    suffices key : ∀ g (hg' : g ∈ Algebra.adjoin (N.O i) {g : N.X i → N.O i | ∃ v k, IsSplitPl H v ∧
        v ∉ placesOver H.E (N.l i) ∧ v ∉ N.S i ∧ v ∉ N.Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧
        g = (N.hT i v k : N.X i → N.O i)}), ∀ hg : g ∈ N.T i,
        ((N.act i ⟨g, hg⟩).baseChange (FractionRing (N.O i))) y =
          algebraMap (N.O i) (FractionRing (N.O i)) (g x) • y from key f hf' hf
    intro g hg'
    induction hg' using Algebra.adjoin_induction with
    | mem g hg0 =>
      intro hg
      obtain ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩ := hg0
      exact hy v k ⟨h1, h2, h3, h4⟩ h5 h6
    | algebraMap r =>
      intro hg
      have e : (⟨algebraMap (N.O i) (N.X i → N.O i) r, hg⟩ : N.T i) =
          algebraMap (N.O i) (N.T i) r := rfl
      rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
        LinearMap.baseChange_one]
      simp [algebraMap_smul]
    | add g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g + g', hg⟩ : N.T i) = ⟨g, m1⟩ + ⟨g', m2⟩ := rfl
      rw [e, map_add, LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2, Pi.add_apply, map_add,
        add_smul]
    | mul g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g * g', hg⟩ : N.T i) = ⟨g, m1⟩ * ⟨g', m2⟩ := rfl
      rw [e, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1,
        smul_smul, Pi.mul_apply, map_mul, mul_comm]

end Gen

section Spec
variable {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
  {X : LocNd (lay0 D)} {T : LocTw X}

theorem genAt_iff_splitOut (Sp : NdSpec Pl M C big X T) {j : ℕ} {w : D.what₂.places.Pl} {i : X.nd.Loc}
    (h : i ∈ X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
  obtain ⟨-, h2⟩ := (X.nd.locs_mem j w i).1 h
  have hl : X.nd.l i = D.what₂.places.resChar w := by rw [← X.nd.w_l i, h2]
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar w) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, ← Sp.Q_eq j w i h, hl]
  tauto

theorem mult_eq_finrank_jointEig (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D)
    (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ)
    (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i) :
    X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ)
      (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := by
  set Fam := (⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) with hFam_def
  have hFam : ∀ e, e ∈ Fam ↔ ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      Sp.B.hK j w v k e = algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) • e := by
    intro e
    simp only [Fam, Submodule.mem_iInf, mem_eigenspace_iff]
  have hval : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) =
      NCov.pt (Sp.ptX j w i h x).1 ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
    intro v k hvk
    simp only [NCov.pt]
    rw [Sp.ptX_hT j w i h x v k hvk]
  have hE : ∀ e, e ∈ Fam ↔ e ∈ NCov.E (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 := by
    intro e
    rw [hFam, NCov.mem_E_iff]
    constructor
    · rintro hy _ ⟨v, k, hvk, rfl⟩
      rw [← hval v k hvk]
      exact hy v k hvk
    · intro hy v k hvk
      rw [hval v k hvk]
      exact hy _ ⟨v, k, hvk, rfl⟩
  have hpsi : ∀ y, y ∈ heckeEig (X.nd.T i) (X.nd.act i) x ↔ Sp.Psi j w i h y ∈ Fam := by
    intro y
    rw [heckeEig_mem_iff_gens, hFam]
    constructor
    · intro hy v k hvk
      obtain ⟨hso, hk1, hk2⟩ := (genAt_iff_splitOut Sp h v k).2 hvk
      have e := congrArg (Sp.Psi j w i h) (hy v k hso hk1 hk2)
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ] at e
      rw [e]
      congr 1
      exact Sp.phK_alg j w i h _
    · intro hy v k hso hk1 hk2
      have hvk := (genAt_iff_splitOut Sp h v k).1 ⟨hso, hk1, hk2⟩
      apply Sp.Psi_inj j w i h
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ, hy v k hvk]
      congr 1
      exact (Sp.phK_alg j w i h _).symm
  let f : ↥(heckeEig (X.nd.T i) (X.nd.act i) x) →ₛₗ[(Sp.phK j w i h).toRingHom] Sp.B.V j w :=
    (Sp.Psi j w i h).comp (heckeEig (X.nd.T i) (X.nd.act i) x).subtype
  change Module.finrank _ ↥(heckeEig (X.nd.T i) (X.nd.act i) x) = _
  refine finrank_eq_of_semilinear (Sp.phK j w i h) f Fam ?_ ?_
  · intro a b hab
    exact Subtype.ext (Sp.Psi_inj j w i h hab)
  · intro e
    constructor
    · intro he
      have hp : e ∈ NCov.part (Formalism.L2.heckeAlg Sp.B j w) (Sp.mx j w i) := by
        have := NCov.E_le_part (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 ((hE e).1 he)
        rwa [(Sp.ptX j w i h x).2.1] at this
      obtain ⟨z, rfl⟩ := (Sp.Psi_range j w i h e).1 hp
      exact ⟨⟨z, (hpsi z).2 he⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact (hpsi z).1 hz

end Spec

end GlobalTheory.HeightCounting
