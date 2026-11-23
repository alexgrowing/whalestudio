import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.LastKerRep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂]

theorem hasVal_transport {Q : Pair k n} {R : Pair k n₂} (G : Matrix n₂ n k) (G' : Matrix n n₂ k) (hGG : G * G' = 1)
    {e : n₂ → k} (he : R.HasVal e 1) (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ R.ker) {s : 𝓀[k]ˣ}
    (hs : Q.HasVal (G' *ᵥ e) s) (y : n → k) (a : 𝓀[k]) :
    Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a) := by
  have hGe : ∀ (r : 𝒪[k]) (z : n → k), G *ᵥ (z - r • (G' *ᵥ e)) = G *ᵥ z - r • e := by
    intro r z
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  obtain ⟨r, hr⟩ := residue_surjective (R := 𝒪[k]) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)
  have hsr : residue 𝒪[k] r * (s : 𝓀[k]) = a := by
    rw [hr, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  constructor
  · intro hy
    have h1 := hy.sub (hs.smul r)
    rw [hsr, sub_self] at h1
    have h2 := Pair.mem_ker.1 ((hker _).1 (Pair.mem_ker.2 h1))
    rw [hGe] at h2
    have h3 := h2.add (he.smul r)
    rw [sub_add_cancel, zero_add, mul_one, hr] at h3
    exact h3
  · intro hy
    have h1 := hy.sub (he.smul r)
    rw [mul_one, hr, sub_self, ← hGe] at h1
    have h2 := Pair.mem_ker.1 ((hker _).2 (Pair.mem_ker.2 h1))
    have h3 := h2.add (hs.smul r)
    rw [sub_add_cancel, zero_add, hsr] at h3
    exact h3

theorem maps_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    Maps (s⁻¹ • P) R (G * x) ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal, inv_inv]
  constructor
  · intro H y a hy
    rw [hT, Matrix.mulVec_mulVec]
    apply H
    rwa [← mul_assoc, Units.mul_inv, one_mul]
  · intro H y a hy
    have := (hT _ _).1 (H y _ hy)
    rwa [← mul_assoc, Units.inv_mul, one_mul, Matrix.mulVec_mulVec] at this

theorem phiOne_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    phiOne (s⁻¹ • P) R (G * x) = phiOne P Q x := by
  classical
  unfold phiOne
  exact if_congr (maps_transport P G s hT x) rfl rfl

section Frames
variable {D : D7} {p : SplitPt D k} {S T : HSp D} {n' : Type} [Fintype n'] [DecidableEq n']

theorem extFun_eq_of (α : Frame p S n') (β : Frame p T n₂) (β' : Frame p T n) (Ψ : Matrix n₂ n' k → ℂ)
    (Ψ' : Matrix n n' k → ℂ) (hΨ : ∀ x, Ψ' ((β'.b' * β.b) * x) = Ψ x) : extFun α β Ψ = extFun α β' Ψ' := by
  funext t
  unfold extFun
  split_ifs
  · rw [← hΨ]
    congr 1
    unfold rd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
  · rfl

end Frames

section Lists
variable {D : D7} {ι : Type} {p : ι → SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem overAll_of_extFun_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n₂) (β' : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n₂ n' k → ℂ)
    (Ψ' : ι → Matrix n n' k → ℂ) (h : ∀ i, extFun (α i) (β i) (Ψ i) = extFun (α i) (β' i) (Ψ' i))
    (hSB : ∀ i, Ψ' i ∈ SB (Matrix n n' k)) :
    ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β' LS LT Ψ' l f f'
  | [], _, _, hf => hf
  | i :: l, f, f', hf => by
    obtain ⟨g, hg, hov⟩ : ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := hf
    obtain ⟨h1, h2, h3, -, h5⟩ := hov
    refine ⟨g, overAll_of_extFun_eq ψ α β β' LS LT Ψ Ψ' h hSB l f g hg, h1, h2, h3, hSB i, ?_⟩
    rw [← h i]
    exact h5

end Lists

theorem isLattice_of_lastKer {m : Type} [Fintype m] [DecidableEq m] {Q : Pair k n₂} (G : Matrix (m ⊕ Fin 1) n₂ k)
    (G' : Matrix n₂ (m ⊕ Fin 1) k) (hGG : G * G' = 1) (L : Submodule 𝒪[k] (m → k))
    (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) : L.IsLattice k := by
  let e : (m → k) →ₗ[k] (m ⊕ Fin 1 → k) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext (i | i) <;> simp
      map_smul' := by intro c x; ext (i | i) <;> simp }
  let f : (m → k) →ₗ[k] (n₂ → k) := (Matrix.mulVecLin G').comp e
  have hGf : ∀ x, G *ᵥ f x = Sum.elim x 0 := by
    intro x
    simp only [f, e, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (G *ᵥ ·) hxy
    simp only [hGf] at this
    funext i
    exact congrFun this (Sum.inl i)
  have hL : L = Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hker, hGf, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    simp
  rw [hL]
  exact GlobalTheory.GoodLat.isLattice_comap Q.ker Q.ker_isLat f hf

end GlobalTheory.LastKerRep

open GlobalTheory.LastKerRep in

theorem GlobalTheory.SeeSaw.lastKernel_reps : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have htop := fun i => (hS.pre.topT (j + 1 + 1) h i).2
  choose Λ s hLat hKer hVal using htop
  have hGG : ∀ i, ((o.γ₀ (j + 1 + 1) h i).b' * (o.β (j + 1 + 1) i).b) * ((o.β (j + 1 + 1) i).b' * (o.γ₀ (j + 1 + 1) h i).b) = 1 := by
    intro i
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (o.β (j + 1 + 1) i).b, (o.β (j + 1 + 1) i).bb', Matrix.one_mul, (o.γ₀ (j + 1 + 1) h i).b'b]
  have hΛ : ∀ i, (Λ i).IsLattice k := fun i => isLattice_of_lastKer _ _ (hGG i) (Λ i) (hKer i)
  refine ⟨Λ, hΛ, fun i => (s i)⁻¹, hLat, (hv.atT (j + 1)).1, fun f hf => ?_⟩
  refine overAll_of_extFun_eq c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (o.γ₀ (j + 1 + 1) h) _ _ _ _ (fun i => ?_) (fun i => ?_)
    o.I f _ (hS.rep (j + 1) (by omega) f hf)
  · haveI := hΛ i
    apply extFun_eq_of
    intro x
    exact phiOne_transport _ _ _ (hasVal_transport _ _ (hGG i)
      (glue_hasVal (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last o.q (Λ i)))
      (fun y => (hKer i y).trans (by rw [glue_ker])) (hVal i)) x
  · haveI := hΛ i
    exact GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _

end
