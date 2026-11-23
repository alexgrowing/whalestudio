import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.GaloisLevelStructure.Checks
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeSum

theorem orth_ker_eq_range_adjoint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) : (LinearMap.ker A)ᗮ = LinearMap.range (LinearMap.adjoint A) := by
  have h : (LinearMap.range (LinearMap.adjoint A))ᗮ = LinearMap.ker A := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
    constructor
    · intro hx
      exact ext_inner_left ℂ (fun y => by rw [hx y, inner_zero_right])
    · intro hx y
      rw [hx, inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

variable {D : D7}

def eqvMt {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j := by
  subst hμ; subst hj; exact LinearEquiv.refl ℂ _

theorem map_eqvMt_self {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = μ) (hj : j = j) (V : Submodule ℂ (D.what₂.Mt μ j)) :
    V.map (eqvMt hμ hj).toLinearMap = V :=
  Submodule.map_id V

theorem map_eqvMt_thetaT_isot {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) (σ : D.what₂.FT) :
    ((D.what₂.isot j' σ).map (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      (D.what₂.isot j σ).map (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem map_eqvMt_range_thetaT {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    (LinearMap.range (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      LinearMap.range (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem isoTyp_eq_of_isoRep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {M : MtFam D}

theorem typeV_of_transport (A : AVTied D M) (i : D.nd.Loc) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ' j' h1 h2).wt.W))
    (hirr : NG.IsIrrRep (M μ' j' h1 h2).wt.ρ S')
    (hne : (NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real ≠ ⊥) :
    ∃ P, ((NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real).map (eqvMt hμ hj).toLinearMap =
      D.naut.typeV i P := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := A.surj i S' hirr hne
  refine ⟨P, ?_⟩
  have e := isoTyp_eq_of_isoRep (M.loc i).wt.ρ (A.irr i P).1.stable hP
  rw [map_eqvMt_self, A.typeV i P, e]
  rfl

theorem eig_of_transport (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (V : Submodule ℂ (D.what₂.Mt μ' j')) (hV : V.map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P)
    (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hw : SplitOut D.nd i w) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k)
    (k2 : k ≤ D.R.nV) (c : ℂ)
    (hV' : ∀ y ∈ V, NG.tN (M μ' j' h1 h2).J s ϖ k ((M μ' j' h1 h2).real y) = c • (M μ' j' h1 h2).real y) :
    c = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) := by
  subst hμ; subst hj
  rw [map_eqvMt_self] at hV
  subst hV
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have e1 := A.eigen i P x hx w k s ϖ hw hc hu k1 k2 y hy
  have e2 := hV' y hy
  have hr : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  exact smul_left_injective ℂ hr (e2.symm.trans e1)

end GlobalTheory.EtaJoin.TypeSum

namespace GlobalTheory.EtaJoin.TypeSum

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → AVTied D M → SplitUnif D → TypeOrth D i →
    ThetaCut D (D.nd.mu i) (D.nd.j i) → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.ConclusionZ D →
    (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      Formalism.MainNotions.N.HG D.nd D.naut i' ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' σ) → ZSpec D i := by
  intro D M i HT A SU TO TC II PZ EX
  have hZ0 : Idx.Z0 D (D.nd.mu i) (D.nd.j i) = LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    unfold Idx.Z0
    rw [orth_ker_eq_range_adjoint]
    exact inf_eq_left.2 TC
  have hmu : ∀ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), D.nd.mu i' = D.nd.mu i := fun i' hi' => by
    rw [D.nd.mu_w, D.nd.mu_w, ((D.nd.locs_mem _ _ i').1 hi').2]
  let G : Set (D.naut.AV i) := {P | ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ x' ∈ Formalism.MainNotions.N.ZgoodN D.nd D.naut i',
    ∃ P' : D.naut.AV i', D.naut.ptV i' P' = some x' ∧ ∃ (hμ : D.nd.mu i' = D.nd.mu i) (hj : D.nd.j i' = D.nd.j i),
      (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P}

  have hin : ∀ P ∈ G, D.naut.typeV i P ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    rintro P ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    have hZ := (PZ i' ⟨x', hx'⟩).2.1
    have h1 : D.naut.typeV i' P' ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) := by
      refine le_trans ?_ (LinearMap.map_le_range (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i'))
        (p := Formalism.MainNotions.N.goodPartM D.nd D.naut i'))
      rw [hZ]
      refine le_trans ?_ (le_biSup (fun x => Formalism.MainNotions.N.eigC D.nd D.naut i' x) hx')
      unfold Formalism.MainNotions.N.eigC
      exact le_biSup (fun Q => D.naut.typeV i' Q) (show P' ∈ {Q | D.naut.ptV i' Q = some x'} from hP')
    rw [← he, ← map_eqvMt_range_thetaT hμ hj]
    exact Submodule.map_mono h1

  have hsub : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≤ ⨆ P ∈ G, D.naut.typeV i P := by
    rw [LinearMap.range_eq_map, ← ((II (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2).submodule_iSup_eq_top),
      Submodule.map_iSup]
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot (D.nd.j i) σ = ⊥
    · rw [h0, Submodule.map_bot]; exact bot_le
    obtain ⟨hg, i', hi', hHG, hAt⟩ := EX σ h0
    have hj : D.nd.j i' = D.nd.j i := ((D.nd.locs_mem _ _ i').1 hi').1
    have hμ := hmu i' hi'
    have h1 : D.what₂.isot (D.nd.j i') σ ≤ Formalism.MainNotions.N.goodPartM D.nd D.naut i' :=
      le_biSup (fun τ => D.what₂.isot (D.nd.j i') τ) (show σ ∈ {τ | D.nd.goodRow τ ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' τ} from ⟨hg, hAt⟩)
    have h2 := Submodule.map_mono (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) h1
    rw [(PZ i' hHG).2.1] at h2
    rw [← map_eqvMt_thetaT_isot hμ hj]
    refine le_trans (Submodule.map_mono h2) ?_
    rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun x' hx' => ?_
    unfold Formalism.MainNotions.N.eigC
    refine iSup₂_le fun P' hP' => ?_
    rw [← Submodule.map_le_iff_le_comap]
    have hne : (NG.isoTyp (M.loc i').wt.ρ (A.S i' P')).comap (M.loc i').real ≠ ⊥ := by
      rw [← A.typeV i' P']; exact D.naut.typeV_ne i' P'
    obtain ⟨P, hP⟩ := typeV_of_transport A i hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (A.S i' P') (A.irr i' P') hne
    have hT : (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P := by
      rw [A.typeV i' P']; exact hP
    rw [hT]
    exact le_biSup (fun Q => D.naut.typeV i Q) (show P ∈ G from ⟨i', hi', x', hx', P', hP', hμ, hj, hT⟩)
  have hZG : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = ⨆ P ∈ G, D.naut.typeV i P :=
    le_antisymm hsub (iSup₂_le hin)
  have hout : ∀ P, P ∉ G → D.naut.typeV i P ≤ (LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)))ᗮ := by
    intro P hP
    rw [← Submodule.isOrtho_iff_le]
    apply Submodule.IsOrtho.symm
    rw [Submodule.isOrtho_iff_le, hZG]
    refine iSup₂_le fun Q hQ => ?_
    rw [← Submodule.isOrtho_iff_le]
    exact TO Q P (fun h => hP (h ▸ hQ))
  unfold ZSpec
  rw [hZ0]
  intro P
  refine ⟨(em (P ∈ G)).elim (fun h => Or.inl (hin P h)) (fun h => Or.inr (hout P h)), fun x hx => ⟨fun hg => ?_, fun hb => hout P ?_⟩⟩
  · exact hin P ⟨i, (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, x, (D.Zgood_tie i x).1 hg, P, hx, rfl, rfl, map_eqvMt_self _ _ _⟩
  · rintro ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    obtain ⟨hj', hw'⟩ := (D.nd.locs_mem _ _ i').1 hi'
    by_cases hii : i' = i
    · subst hii
      rw [map_eqvMt_self] at he
      have hPP : P' = P := by
        by_contra hne
        have hd : Disjoint (D.naut.typeV i' P') (D.naut.typeV i' P) := (D.naut.typeV_indep i').pairwiseDisjoint hne
        rw [he] at hd
        exact D.naut.typeV_ne i' P (disjoint_self.1 hd)
      subst hPP
      rw [hx] at hP'
      cases hP'
      exact hb ((D.Zgood_tie _ _).2 hx')
    · obtain ⟨φ, hφ⟩ := HT.sameO i i' hj'.symm hw'.symm
      obtain ⟨v, k, hv, hv', k1, k2, hunit⟩ := HT.sep i i' φ hφ hj'.symm hw'.symm (Ne.symm hii) x x'
      obtain ⟨s, ϖ, hc, hu⟩ := SU v hv.1
      have e := eig_of_transport A i P x hx hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (D.naut.typeV i' P') he
        v k s ϖ hv hc hu k1 k2 _ (fun y hy => A.eigen i' P' x' hP' v k s ϖ hv' hc hu k1 k2 y hy)
      rw [hφ] at e
      have hinj : Function.Injective (iotaOC D i') := by
        intro a b h
        simp only [iotaOC, RingHom.coe_comp, Function.comp_apply] at h
        exact IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))
          ((D.naut.iotaQ i').injective ((D.naut.iotaQC i').injective h))
      rw [hinj e, sub_self] at hunit
      exact not_isUnit_zero hunit

end GlobalTheory.EtaJoin.TypeSum
