import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CoordGHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L}

section Rtools

theorem mem_R_of (hs : M.split = some g) (x : E) (a b c : 𝒪[F]) (hx : g.e x = ((a : F), (b : F)))
    (h : (a : F) - b = (g.q : F) * c) : x ∈ M.R := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(a, b), ?_, ?_⟩
  · show (Ideal.Quotient.mk (Ideal.span {g.q})) a = (Ideal.Quotient.mk (Ideal.span {g.q})) b
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨c, Subtype.ext (by push_cast; exact h)⟩
  · show ((a : F), (b : F)) = g.e x
    rw [hx]

def dgR (hs : M.split = some g) : 𝒪[F] →+* M.R where
  toFun c := ⟨algebraMap F E c, mem_R_of hs _ c c 0 (by rw [AlgEquiv.commutes]; rfl) (by simp)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

theorem dgR_coe (hs : M.split = some g) (c : 𝒪[F]) : ((dgR hs c : M.R) : E) = algebraMap F E c := rfl

theorem e_dgR (hs : M.split = some g) (c : 𝒪[F]) : g.e ((dgR hs c : M.R) : E) = ((c : F), (c : F)) := by
  rw [dgR_coe, AlgEquiv.commutes]
  rfl

def trO (hs : M.split = some g) : M.R →+ 𝒪[F] where
  toFun x := ⟨((g.e x).1 - (g.e x).2) / (g.q : F), by
    obtain ⟨-, -, c, hc⟩ := comp_of_mem_R hs x.2
    rw [hc, mul_div_cancel_left₀ _ (q_ne g)]; exact c.2⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by
    apply Subtype.ext
    simp only [Subring.coe_add, map_add, Prod.fst_add, Prod.snd_add]
    push_cast
    ring

theorem trO_coe (hs : M.split = some g) (x : M.R) :
    ((trO hs x : 𝒪[F]) : F) = ((g.e x).1 - (g.e x).2) / (g.q : F) := rfl

def q2 (hs : M.split = some g) : M.R :=
  ⟨g.e.symm (0, (g.q : F)), mem_R_of hs _ 0 g.q (-1) (by simp) (by simp)⟩

theorem embedding_uniformizer (hs : M.split = some g) : g.e ((q2 hs : M.R) : E) = (0, (g.q : F)) := by
  show g.e (g.e.symm (0, (g.q : F))) = _
  exact g.e.apply_symm_apply _

theorem trO_one (hs : M.split = some g) : trO hs 1 = 0 := by
  apply Subtype.ext
  rw [trO_coe]
  simp

theorem trO_dgR_mul (hs : M.split = some g) (c : 𝒪[F]) (x : M.R) :
    trO hs (dgR hs c * x) = c * trO hs x := by
  apply Subtype.ext
  rw [trO_coe, MulMemClass.coe_mul, MulMemClass.coe_mul, trO_coe, map_mul, e_dgR, Prod.fst_mul, Prod.snd_mul]
  ring

theorem R_decomp (hs : M.split = some g) (s : M.R) :
    ∃ a b : 𝒪[F], s = dgR hs a + dgR hs b * q2 hs := by
  obtain ⟨h1, -, c, hc⟩ := comp_of_mem_R hs s.2
  refine ⟨⟨(g.e s).1, h1⟩, -c, ?_⟩
  apply Subtype.ext
  apply g.e.injective
  rw [AddMemClass.coe_add, MulMemClass.coe_mul, map_add, map_mul, e_dgR, e_dgR, embedding_uniformizer]
  ext
  · simp
  · simp only [Prod.snd_add, Prod.snd_mul]
    push_cast
    linear_combination (-1 : F) * hc

end Rtools

section DD1

variable (hs : M.split = some g) {r : ℕ}

abbrev eV (r : ℕ) : Fin (r + 1) → M.R := Pi.single (Fin.last r) 1

def llMap (Z : M.Mat (r + 1)) (TT : M.R) : (Fin (r + 1) → M.R) →+ (Fin (r + 1) → M.R) where
  toFun m := Z.Z.mulVec m - (TT * dgR hs (trO hs (m (Fin.last r)))) • eV r
  map_zero' := by simp
  map_add' x y := by
    simp only [Matrix.mulVec_add, Pi.add_apply, map_add, mul_add, add_smul]
    abel

def LL (Z : M.Mat (r + 1)) (TT : M.R) : AddSubgroup (Fin (r + 1) → M.R) := (llMap hs Z TT).range

abbrev DD1 (Z : M.Mat (r + 1)) (TT : M.R) : Type := (Fin (r + 1) → M.R) ⧸ LL hs Z TT

end DD1

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
