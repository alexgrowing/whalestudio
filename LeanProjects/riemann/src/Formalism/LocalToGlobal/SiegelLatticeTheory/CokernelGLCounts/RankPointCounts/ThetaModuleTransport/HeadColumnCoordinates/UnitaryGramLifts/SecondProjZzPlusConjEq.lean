import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section LiftM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem lift_cj_mem_R (hs : M.split = some g) (x : M.R) : M.L.cj (x : E) ∈ M.R := by
  obtain ⟨h1, h2, c, hc⟩ := comp_of_mem_R hs x.2
  refine mem_R_of hs _ ⟨_, h2⟩ ⟨_, h1⟩ (-c) ?_ ?_
  · rw [g.e_cj]; rfl
  · show (g.e (x : E)).2 - (g.e (x : E)).1 = (g.q : F) * ((-c : 𝒪[F]) : F)
    push_cast; linear_combination -hc

def sigR (hs : M.split = some g) : M.R →+* M.R where
  toFun x := ⟨M.L.cj x, lift_cj_mem_R hs x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

theorem sigR_coe (hs : M.split = some g) (x : M.R) : ((sigR hs x : M.R) : E) = M.L.cj (x : E) := rfl

theorem lift_eps_mem {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : (T - T') / (g.q : F) ∈ 𝒪[F] := by
  obtain ⟨c, hc⟩ := h
  rw [hc, pow_two, mul_assoc, mul_div_cancel_left₀ _ (q_ne g)]
  exact mul_mem g.q.2 c.2

def epsR (hs : M.split = some g) {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : M.R :=
  dgR hs ⟨_, lift_eps_mem h⟩

theorem firstProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) = ph1 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [firstProj_apply, cor, h]
  · simp [firstProj_apply, cor, h]

theorem secondProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) = -(ph2 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [secondProj_apply, cor, h]
  · simp [secondProj_apply, cor, h]

theorem secondProj_zzPlus_conj_eq (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := secondProj_zzPlus_conj hs Zh T T' a b

theorem lift_zsig (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (hG : GHyp M g T T' TT Zh Z Zσ) :
    Zσ.Z = -lstar (sigR hs) Z.Z + epsR hs hG.2.1 • liftE r := by
  have hZ : ∀ a b, ((Z.Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.1 a) b; simpa using this
  have hZσ : ∀ a b, ((Zσ.Z a b : M.R) : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.2.1 a) b; simpa using this
  have hq := q_ne g
  ext a b
  rw [eq_iff_ph (g := g)]
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, lstar_apply, Subring.coe_add,
    Subring.coe_neg, Subring.coe_mul, sigR_coe, hZ, hZσ, liftE, Matrix.of_apply, epsR, dgR_coe, map_add, map_neg,
    map_mul, firstProj_algebraMap, ph2_algebraMap_eq]
  constructor
  · rw [firstProj_zzPlus_conj hs, firstProj_conj_apply, secondProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring
  · rw [secondProj_zzPlus_conj_eq hs, secondProj_conj_apply, firstProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring

theorem lift_cancel (Z : M.Mat (r + 1)) (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (h : Z.Z * A = Z.Z * B) :
    A = B := by
  have h1 := congrArg (fun X => X.map M.R.subtype) h
  simp only [Matrix.map_mul] at h1
  have h2 : A.map M.R.subtype = B.map M.R.subtype := by
    rw [← Matrix.one_mul (A.map M.R.subtype), ← Matrix.nonsing_inv_mul _ Z.unit, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mul]
  ext i j
  exact congrFun (congrFun h2 i) j

end LiftM

section LiftK

variable {R : Type} [CommRing R] {r : ℕ}

end LiftK

def LiftPQP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r : ℕ) (Z₁ Z₂ : M.Mat (r + 1)) (γ : IsoMbe Z₁.Z Z₂.Z),
    ∃ P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
      (∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)) ∧ P * Z₁.Z = Z₂.Z * Q ∧
      (∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) ∧
      (∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0)

def isoMbeSymm {R : Type} [CommRing R] {r : ℕ} {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (γ : IsoMbe Z₁ Z₂) :
    IsoMbe Z₂ Z₁ :=
  ⟨γ.1.symm, by rw [LinearEquiv.symm_apply_eq]; exact γ.2.1.symm,
    by rw [LinearEquiv.symm_apply_eq]; exact γ.2.2.symm⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
