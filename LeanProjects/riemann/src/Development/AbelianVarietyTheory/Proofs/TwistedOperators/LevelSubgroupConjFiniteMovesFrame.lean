import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FrameConj

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {T : G} (hT : T ∈ H) (x : G) :
    T * x * T⁻¹ ∈ H ↔ x ∈ H := by
  rw [Subgroup.mul_mem_cancel_right H (H.inv_mem hT), Subgroup.mul_mem_cancel_left H hT]

theorem frGL_mul_left (T β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y) :
    frGL (T * β) y = T * frGL β y * T⁻¹ := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_mem_St_iff (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    T * x * T⁻¹ ∈ St (T * β) ↔ x ∈ St β := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [frGL_mul_left] at hy
    exact mul_left_cancel (mul_right_cancel hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, frGL_mul_left T β y⟩

theorem redFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (T * β) PP (T * x * T⁻¹) = redFn β PP x := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := hx
    rw [← frGL_mul_left, redFn_frGL, redFn_frGL]
  · have h' : T * x * T⁻¹ ∉ St (T * β) := fun h => hx ((conj_mem_St_iff T β x).1 h)
    unfold redFn ext1
    rw [dif_neg hx, dif_neg h']

variable {LL : Type} [CommRing LL]

theorem rTup_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    rTup (T * β) L (T * x * T⁻¹) = rTup β L x := by
  funext PP
  show upperLeftBlock L.hr (redFn (T * β) PP.1 (T * x * T⁻¹)) = upperLeftBlock L.hr (redFn β PP.1 x)
  rw [redFn_conj]

theorem levFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    levFn (T * β) L (T * x * T⁻¹) = levFn β L x := by
  unfold levFn
  simp only [rTup_conj, redFn_conj]

theorem conj_mem_lev_iff [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E}
    {T : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hT : T ∈ UA hc J) (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (L : LevDat E LL n) : T * x * T⁻¹ ∈ lev hc J (T * β) L ↔ x ∈ lev hc J β L := by
  rw [mem_lev, mem_lev, mem_parLev, mem_parLev, conj_mem_iff _ hT, conj_mem_St_iff, rTup_conj]
  simp only [redFn_conj]

end Gen

theorem levS_conj_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V),
    t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧
      levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  intro D V β L t ht k
  have hfin : finE V (t * k * t⁻¹) = finE V t * finE V k * (finE V t)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨?_, ?_⟩
  · show k ∈ levG V β L ↔ t * k * t⁻¹ ∈ levG V (finE V t * β) L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [conj_mem_iff _ ht, hfin, conj_mem_lev_iff (GlobalTheory.LevSplit.finE_mem_UA V t)]
  · unfold levChi
    rw [hfin, levFn_conj]

end GlobalTheory.FrameConj
