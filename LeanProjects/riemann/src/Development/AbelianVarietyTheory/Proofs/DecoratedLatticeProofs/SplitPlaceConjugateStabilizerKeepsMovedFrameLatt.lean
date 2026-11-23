import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.StMoves

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_mul {m n p : Type} [Fintype n] {A : Matrix m n k} {B : Matrix n p k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) : ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j =>
  Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem int_one_sub {m a b : Type} [DecidableEq m] (f : a → m) (g' : b → m) :
    ∀ i j, ((1 : Matrix m m k).submatrix f g') i j ∈ 𝒪[k] := fun i j => by
  rw [submatrix_apply, one_apply]
  split_ifs
  exacts [Subring.one_mem _, Subring.zero_mem _]

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by simp [Formalism.L2.Theta.mt]

theorem alg_frame {n : ℕ} {Y R A' : Type} [Fintype Y] [DecidableEq Y] [CommRing R] [CommRing A'] (pr : R →+* k) (toE : R →+* A')
    (π : A' →+* k) (hmap : ∀ x, π (toE x) = pr x) (mg mt' mh b : Matrix (Fin n) (Fin n) R) (βv I : Matrix (Fin n) (Fin n) A')
    (Fβ : Matrix (Fin n) Y k) (Fγ : Matrix Y (Fin n) k) (e : Y ≃ Fin n) (hγβ : Fγ * Fβ = 1) (hb : b.map toE = βv)
    (hmv : (mt' * b).map pr = Fβ.submatrix id e.symm) (hg1 : mg * mt' = mt' * mh) (hfin : mh.map toE * βv = βv * I) :
    Fγ * mg.map pr * Fβ = (1 : Matrix Y Y k).submatrix id e.symm * I.map π * (1 : Matrix Y Y k).submatrix e.symm id := by
  have hm : ∀ N : Matrix (Fin n) (Fin n) R, (N.map toE).map π = N.map pr := fun N => Matrix.ext fun _ _ => hmap _
  have eq2 : mg.map pr * Fβ.submatrix id e.symm = Fβ.submatrix id e.symm * I.map π := by
    rw [← hmv, ← Matrix.map_mul, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc, Matrix.map_mul, ← hm (mh * b), Matrix.map_mul,
      hb, hfin, Matrix.map_mul, ← hb, hm, ← Matrix.mul_assoc, ← Matrix.map_mul]
  have eq1 : Fβ = Fβ.submatrix id e.symm * (1 : Matrix Y Y k).submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]; rfl
  have eq3 : Fγ * Fβ.submatrix id e.symm = (1 : Matrix Y Y k).submatrix id e.symm := by
    rw [← hγβ]
    exact Matrix.submatrix_mul_equiv Fγ Fβ id (Equiv.refl _) e.symm
  conv_lhs => rw [eq1]
  rw [Matrix.mul_assoc Fγ, ← Matrix.mul_assoc _ (Fβ.submatrix id e.symm), eq2, ← eq3]
  simp only [Matrix.mul_assoc]

theorem int_of_mem_St (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y)
    (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank)
    (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm))
    (g : GA D S) (hg : Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    ∀ i j, (F.γ * (mt S g).map q.pr * F.β) i j ∈ 𝒪[k] := by
  obtain ⟨Y0, hY0⟩ := hg
  obtain ⟨π, h1, -, h3, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart q hq
  have hb' : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
    Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
  have hmv : (mt S t * β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map q.pr = F.β.submatrix id e.symm := hM _ hb'
  have hZi : ∀ i j, ((Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val.map π) i j ∈ 𝒪[k] := fun i j => h3 (Y0.val i j)
  have hmap : ∀ N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (N.map (toEAf D)).map π = N.map q.pr :=
    fun N => Matrix.ext fun _ _ => h1 _
  have hfin : Lev.finE S (t⁻¹ * g * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0 := by
    rw [← hY0]
    simp [Formalism.L2.DIV.frGL]
  have hfin' : (mt S (t⁻¹ * g * t)).map (toEAf D) * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val := by
    have := congrArg Units.val hfin
    rwa [Units.val_mul, Units.val_mul] at this
  have hg1 : mt S g * mt S t = mt S t * mt S (t⁻¹ * g * t) := by
    rw [← mt_mul, ← mt_mul]; congr 1; group
  rw [alg_frame q.pr (toEAf D) π h1 (mt S g) (mt S t) (mt S (t⁻¹ * g * t)) (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)) β.val
    (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val F.β F.γ e F.γβ hb' hmv hg1 hfin']
  exact int_mul (int_mul (int_one_sub _ _) hZi) (int_one_sub _ _)

open scoped Pointwise in

theorem moves_of_mem_St : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  intro D k _ _ _ _ q PP hq S L hL Y _ _ F hF t β e hM g hg
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q S Y F.β F.γ F.βγ F.γβ
  have hlat : (⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩ : GlobalTheory.FinPl.Frame q S Y).IsLat L (GlobalTheory.StepData.latOf 1) := fun x => by
    rw [GlobalTheory.StepData.mem_latOf_one]; exact hF x
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q S Y _ L _ hL hlat g).2 ?_
  have hA : ∀ i j, (GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g).val i j ∈ 𝒪[k] :=
    int_of_mem_St q hq S F t β e hM g hg
  have hAi : ∀ i j, ((GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g)⁻¹).val i j ∈ 𝒪[k] := by
    rw [← map_inv]
    refine int_of_mem_St q hq S F t β e hM g⁻¹ ?_
    have : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hg
  have hK : GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g ∈ GlobalTheory.StepData.stabLat 1 := by
    rw [GlobalTheory.StepData.mem_stabLat, inv_one, one_mul, mul_one]
    exact GlobalTheory.StepData.mem_KO.2 ⟨hA, hAi⟩
  have hs := GlobalTheory.StepData.mem_stabLat_iff.1 hK
  set A := GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g
  ext y
  conv_rhs => rw [← hs]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf 1 ∧ A • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf A).2 hx
  · intro hy
    refine ⟨A⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf A).1 ?_, smul_inv_smul _ _⟩
    have : A.val *ᵥ (A⁻¹ • y) = y := smul_inv_smul A y
    rwa [this]

end GlobalTheory.LocMod.StMoves
end
