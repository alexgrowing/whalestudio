import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepFrameFiberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberInjectiveStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LocM.MapComp

namespace GlobalTheory.LocM.LatCover

theorem stepAt_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (g : Z.X ⟶ B.X) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (U U' : Z.X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U) (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ r hU m a → LatCover.StepAt Z B g L σ r hU' m (Matrix.GeneralLinearGroup.map (Z.X.presheaf.map (homOfLE hle).op).hom a) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z B g L σ r U U' hU hU' hle V n m a hs k _ φ v hv h hin j hj
  have e : spMap (φ.comp (Z.X.presheaf.map (homOfLE hle).op).hom) ≫ hU.fromSpec = spMap φ ≫ hU'.fromSpec := by
    rw [← sp_comp, Category.assoc, StepFrame.spMap_resR hU hU' hle]
  have key := hs k (φ.comp (Z.X.presheaf.map (homOfLE hle).op).hom)
  rw [e] at key
  exact key v hv h hin j hj

theorem exists_rows : ∀ (R K : Type) [CommRing R] [Field K] (φ : R →+* K) (n g : ℕ) (hg : g ≤ n) (A : Fin (g + 1) → GL (Fin n) R), ∃ M : Matrix (Fin n) (Fin n) R, φ M.det ≠ 0 ∧ ∀ i : Fin g, ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, M (Fin.castLE hg i) l = ((A i.succ)⁻¹ : GL (Fin n) R) l j := by
  intro R K _ _ φ n g hg A
  classical
  let κ : Fin n → Fin (g + 1) := fun i => ⟨min (i + 1) g, by omega⟩
  let col : Fin (g + 1) → Fin n → Fin n → R := fun r j l => ((A r)⁻¹ : GL (Fin n) R) l j
  have hind : ∀ r, LinearIndependent K fun j => fun l => φ (col r j l) := by
    intro r
    have hu : IsUnit (Matrix.transpose ((((A r)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map φ)) := by
      refine (Matrix.isUnit_transpose _).2 ?_
      have := (Matrix.GeneralLinearGroup.map φ (A r)⁻¹).isUnit
      exact this
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hκ : ∀ i : Fin n, (i : ℕ) + 1 ≤ n := fun i => i.2
  obtain ⟨s, hs⟩ := StepFrame.exists_choice (k := K) n
    (fun i j => fun l => φ (col (κ i) (Fin.castLE (hκ i) j) l))
    fun i => (hind (κ i)).comp _ (Fin.castLE_injective (hκ i))
  let M : Matrix (Fin n) (Fin n) R := fun i l => col (κ i) (Fin.castLE (hκ i) (s i)) l
  refine ⟨M, ?_, fun i => ?_⟩
  · have hu : IsUnit (M.map φ) := (Matrix.linearIndependent_rows_iff_isUnit).1 hs
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  · have e : κ (Fin.castLE hg i) = i.succ := Fin.ext (by simp [κ])
    have : ∀ r (_ : r = i.succ) (j : Fin n), (j : ℕ) < i + 1 → ∃ j' : Fin n, (j' : ℕ) < i + 1 ∧
        ∀ l, col r j l = ((A i.succ)⁻¹ : GL (Fin n) R) l j' := by
      rintro _ rfl j hj
      exact ⟨j, hj, fun l => rfl⟩
    exact this _ e _ (s _).2

theorem hasLatFlags_of_allSteps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ t ∈ allSteps L, Step.Holds t Z) → HasLatFlags Z L := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L hty h
  classical
  refine ⟨hty, fun x => ?_⟩
  obtain ⟨-, g, hg, -⟩ := h _ (mem_allSteps.2 ⟨Classical.arbitrary _, 0, Nat.zero_le _, rfl⟩)
  obtain ⟨V, n, m, hxV, hm⟩ := L.free (g x)
  choose U₀ hU₀ a₀ hx₀ hle₀ hst₀ using fun σ (r : Fin (Dw.mult σ + 1)) =>
    GlobalTheory.T.lattice_step_frame_fiber E H Dw Xo p W hp hW Y i₀ Z B L σ r (Nat.lt_succ_iff.1 r.2) g hg (h _ (mem_allSteps.2 ⟨σ, r, _, rfl⟩)) V n m hm x hxV
  have ho : IsOpen (⋂ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1), (U₀ q.1 q.2 : Set Z.X)) :=
    isOpen_iInter_of_finite fun q => (U₀ q.1 q.2).2
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 fun q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1) => hx₀ q.1 q.2) ho
  have hU : IsAffineOpen U := hU
  have hle' : ∀ σ r, U ≤ U₀ σ r := fun σ r => fun y hy => Set.mem_iInter.1 (hle hy) ⟨σ, r⟩
  let a : ∀ σ (r : Fin (Dw.mult σ + 1)), GL (Fin n) Γ(Z.X, U) := fun σ r =>
    Matrix.GeneralLinearGroup.map (Z.X.presheaf.map (homOfLE (hle' σ r)).op).hom (a₀ σ r)
  have hst : ∀ σ (r : Fin (Dw.mult σ + 1)), StepAt Z B g L σ r hU m (a σ r) := fun σ r =>
    stepAt_res E H Dw Xo p W Y i₀ Z B g L σ r _ U (hU₀ σ r) hU (hle' σ r) V n m (a₀ σ r) (hst₀ σ r)
  have hUV : U ≤ g ⁻¹ᵁ V := (hle' (Classical.arbitrary _) 0).trans (hle₀ _ _)
  have hmn : ∀ σ, Dw.mult σ ≤ n := fun σ =>
    GlobalTheory.T.lattice_frame_fiber_injective (GlobalTheory.T.lattice_frame_fiber_rank) E H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm σ _ (hst σ (Fin.last _)) x hx
  choose M hM hrow using fun σ =>
    exists_rows Γ(Z.X, U) (Z.X.residueField x) (Z.X.evaluation U x hx).hom n (Dw.mult σ) (hmn σ) (a σ)
  let f := ∏ σ, (M σ).det
  have hU' := hU.basicOpen f
  have hle₂ := Z.X.basicOpen_le f
  let ρ := (Z.X.presheaf.map (homOfLE hle₂).op).hom
  have hu : ∀ σ, IsUnit (ρ (M σ).det) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun σ => (M σ).det) (Finset.mem_univ σ)))
      (Z.X.toRingedSpace.isUnit_res_basicOpen f)
  let Mu : ∀ σ : E →+* ℂ, GL (Fin n) Γ(Z.X, Z.X.basicOpen f) := fun σ =>
    Matrix.nonsingInvUnit ((M σ).map ρ) (by show IsUnit (ρ.mapMatrix (M σ)).det; rw [← RingHom.map_det]; exact hu σ)
  let c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, Z.X.basicOpen f) := fun σ i l => ρ (M σ (Fin.castLE (hmn σ) i) l)
  have hext : ∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, Z.X.basicOpen f)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l :=
    fun σ => ⟨Mu σ, Fin.castLEEmb (hmn σ), fun i l => rfl⟩
  let a' : ∀ σ (r : Fin (Dw.mult σ + 1)), GL (Fin n) Γ(Z.X, Z.X.basicOpen f) := fun σ r =>
    Matrix.GeneralLinearGroup.map ρ (a σ r)
  have hst' : ∀ σ (r : Fin (Dw.mult σ + 1)), StepAt Z B g L σ r hU' m (a' σ r) := fun σ r =>
    stepAt_res E H Dw Xo p W Y i₀ Z B g L σ r U _ hU hU' hle₂ V n m (a σ r) (hst σ r)
  have hrow' : ∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧
      ∀ l, c σ i l = ((a' σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, Z.X.basicOpen f)) l j := by
    intro σ i
    obtain ⟨j, hj, e⟩ := hrow σ i
    refine ⟨j, hj, fun l => ?_⟩
    simp only [c, a', e, ← map_inv]
    rfl
  have hUV' : Z.X.basicOpen f ≤ g ⁻¹ᵁ V := hle₂.trans hUV
  refine ⟨⟨g, hg, _, hU', V, hUV', n, m, hm, c, hext, fun k _ y hy hyo =>
    GlobalTheory.T.lattice_frame_fiber_basis (GlobalTheory.T.lattice_frame_fiber_rank) E H Dw Xo p W hp hW Y i₀ Z B L g hg _ hU' V hUV' n m hm a' hst' c hext hrow' k y hy hyo⟩, ?_⟩
  show x ∈ Z.X.basicOpen f
  rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ x hx, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun σ _ => hM σ

end GlobalTheory.LocM.LatCover
