import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieAlgebraExpEqOfCommuteCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KInfLines

variable {D : D7}

theorem exists_log_of_cartan {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ} (hG : Gᴴ = G)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C) (hg : gᴴ * G * g = G) (hgC : Commute g C) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g :=
  GlobalTheory.T.exists_lieAlgebra_exp_eq_of_commute_cartanInvolution hG hC hg hgC

theorem emb_cases (t : D.what₂.Tau) (e : GlobalTheory.AdelicU.EmbOver D.host.E (GlobalTheory.AdelicU.placeOf D t)) :
    e.1 = tauE D t ∨ e.1 = (starRingEnd ℂ).comp (tauE D t) := by
  obtain ⟨t', h | h⟩ := GlobalTheory.DefLiftMult.exists_tauE D e.1
  · have e2 : t = t' := (GlobalTheory.AdelicU.placeOf_bijective D).1 (GlobalTheory.AdelicU.eq_placeOf e h)
    subst e2
    exact Or.inl h
  · have h4 : ((starRingEnd ℂ).comp (tauE D t')).comp (algebraMap D.host.F D.host.E) =
        (GlobalTheory.AdelicU.placeOf D t).embedding := h ▸ e.2
    have h5 : t = t' := by
      apply (GlobalTheory.AdelicU.placeOf_bijective D).1
      rw [← InfinitePlace.mk_embedding (GlobalTheory.AdelicU.placeOf D t), ← h4, GlobalTheory.AdelicU.placeOf]
      exact InfinitePlace.mk_conjugate_eq ((tauE D t').comp (algebraMap D.host.F D.host.E))
    subst h5
    exact Or.inr h

theorem piInf_eq_infProj {w : InfinitePlace D.host.F} (e : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf e y = GlobalTheory.AdelicU.infProj e (infPart D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  | tmul a x => rfl

theorem isInfFam_thetaC (D : D7) : IsInfFam (Eqv.thetaC D) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  exact Eqv.eq_thetaC D hθ ▸ hθ

theorem psiT_cA (t : D.what₂.Tau) (y : AE D) :
    Eqv.psiT D t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig y) = conj (Eqv.psiT D t y) := Eqv.psiT_sigR D t y

theorem piInf_cA_of_eq (t : D.what₂.Tau) (e : GlobalTheory.AdelicU.EmbOver D.host.E (GlobalTheory.AdelicU.placeOf D t))
    (h : e.1 = tauE D t) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig y) = conj (Eqv.psiT D t y) := by
  rw [piInf_eq_infProj, ← GlobalTheory.AdelicU.eq_infProj (isInfFam_thetaC D) e h, ← psiT_cA]
  rfl

theorem piInf_cA_of_eq_conj (t : D.what₂.Tau) (e : GlobalTheory.AdelicU.EmbOver D.host.E (GlobalTheory.AdelicU.placeOf D t))
    (h : e.1 = (starRingEnd ℂ).comp (tauE D t)) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig y) = Eqv.psiT D t y := by
  obtain ⟨σ, hσ⟩ := e
  simp only at h
  subst h
  rw [GlobalTheory.ConjInfExp.piInf_eq _ (isInfFam_thetaC D)]
  show conj (Eqv.psiT D t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig y)) = _
  rw [psiT_cA, Complex.conj_conj]

end GlobalTheory.KInfLines

namespace GlobalTheory.KInfLines

variable {D : D7}

theorem commute_map_conj_iff {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} :
    Commute (A.map conj) B ↔ Commute A (B.map conj) := by
  have key : ∀ {A B : Matrix (Fin n) (Fin n) ℂ}, Commute A B → Commute (A.map conj) (B.map conj) := fun h =>
    h.map (RingHom.mapMatrix (starRingEnd ℂ))
  have cc : ∀ A : Matrix (Fin n) (Fin n) ℂ, (A.map conj).map conj = A := fun A => by
    ext i j; simp
  constructor
  · intro h; simpa only [cc] using key h
  · intro h; simpa only [cc] using key h

theorem isCartan_conj {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (M.map conj) (θ.map conj) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · have := congrArg (fun X => X.map conj) h2
    simp only [Matrix.map_mul] at this
    have e1 : (θ.map conj)ᵀ = θᵀ.map conj := Matrix.transpose_map.symm
    have e2 : (θ.map conj).map star = (θ.map star).map conj := by ext i j; simp
    rw [e1, e2]; exact this
  · have e : ((θ.map conj) *ᵥ x) ⬝ᵥ (M.map conj) *ᵥ star x = conj ((θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x)) := by
      simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
    rw [e, Complex.conj_re]
    exact h3 _ (by simpa using hx)

theorem map_conj_of_herm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : Gᴴ = G) : G.map conj = Gᵀ := by
  ext i j
  have h := congrFun (congrFun hG j) i
  simpa [Matrix.conjTranspose_apply] using h

theorem commute_exp {n : ℕ} {Z C : Matrix (Fin n) (Fin n) ℂ} (h : Commute Z C) (s : ℝ) :
    Commute (NormedSpace.exp (s • Z)) C :=
  (h.smul_left s).exp_left

theorem at_of_finPart {y : AE D} (hy : finPart D y = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) y := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (by rw [map_zero]; exact hu)
  rw [Algebra.smul_def]
  apply Eqv.ae_ext D
  · rw [map_mul, map_zero, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hf : fstA D.host.F u = 0 := hu1
    simp only [infPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, hf,
      TensorProduct.zero_tmul, zero_mul]
  · rw [map_mul, hy, mul_zero, map_zero]

theorem mat_conjU (W : HSp D) {J : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (c : D.host.E) (hJ : J = c • W.gram)
    (g : GA D W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ g) =
      (Eqv.matA D W g).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) := rfl

theorem conjU_mul' (W : HSp D) {J : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (c : D.host.E) (hJ : J = c • W.gram)
    (g g' : GA D W) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ (g * g') =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ g' :=
  Subtype.ext (Units.ext (by
    show (Eqv.matA D W g * Eqv.matA D W g').map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = _
    exact Matrix.map_mul))

theorem conjU_one'' (W : HSp D) {J : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (c : D.host.E) (hJ : J = c • W.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ 1 = 1 :=
  Subtype.ext (Units.ext (by
    show (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)))

theorem conjU_prod (W : HSp D) {J : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (c : D.host.E) (hJ : J = c • W.gram)
    (L : List (GA D W)) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ L.prod = (L.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W c hJ)).prod := by
  induction L with
  | nil => exact conjU_one'' W c hJ
  | cons a L ih => rw [List.prod_cons, conjU_mul', ih, List.map_cons, List.prod_cons]

theorem prod_map_ite {M ι : Type} [Monoid M] [DecidableEq ι] (g : ι → M) (τ : ι) :
    ∀ L : List ι, L.Nodup → τ ∈ L → (L.map fun t => if τ = t then g t else 1).prod = g τ
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, hL, h => by
    rw [List.map_cons, List.prod_cons]
    obtain ⟨ha, hL'⟩ := List.nodup_cons.1 hL
    by_cases e : τ = a
    · subst e
      rw [if_pos rfl, List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      rw [if_neg]
      rintro rfl
      exact ha ht
    · rw [if_neg e, one_mul]
      exact prod_map_ite g τ L hL' ((List.mem_cons.1 h).resolve_left e)

end GlobalTheory.KInfLines

namespace GlobalTheory.KInfLines

variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}

def gsOf (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J) (t : D.what₂.Tau) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (Eqv.psiT D t)).map conj

theorem incM_psiT (hJ : V.J = (1 : D.host.E) • W.gram) (t : D.what₂.Tau) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F V.J).map (Eqv.psiT D t) = gramAt D W t := by
  ext i j; rw [hJ, one_smul]; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Eqv.psiT_inclR, gramAt]

theorem unitFam_gsOf (hJ : V.J = (1 : D.host.E) • W.gram) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J) :
    Eqv.IsUnitFam D W (gsOf k) := by
  have hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F V.J *
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F V.J := k.2
  intro t
  have h1 := congrArg (fun M => M.map (Eqv.psiT D t)) hk2
  simp only [Matrix.map_mul, incM_psiT hJ] at h1
  have e1 : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ).map (Eqv.psiT D t) = (gsOf k t)ᴴ := by
    ext i j; simp [gsOf, Matrix.conjTranspose_apply]
  have e2 : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)).map (Eqv.psiT D t) = gsOf k t := by
    ext i j; simp only [Matrix.map_apply, gsOf]; exact psiT_cA t _
  rw [e1, e2] at h1
  exact h1

theorem fin_one_of_mem {k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J}
    (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (finPart D) = 1 := by
  ext i j
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k i j - (1 : Matrix _ _ (AE D)) i j) :=
    fun u hu => congrFun (congrFun (hk u hu) i) j
  have h2 := GlobalTheory.ConjInfExp.finPart_eq_one (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k i j - (1 : Matrix _ _ (AE D)) i j + 1)
    (by rwa [add_sub_cancel_right])
  rw [RingHom.map_add, RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at h2
  rw [Matrix.map_apply, h2]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem finPart_cA (y : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig y) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D y) :=
  Eqv.finPart_sigR D y

theorem fin_cA_one {M : Matrix (Fin W.rank) (Fin W.rank) (AE D)} (h : M.map (finPart D) = 1) :
    (M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)).map (finPart D) = 1 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at this ⊢
  rw [finPart_cA, this]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem eq_conjU_famH (hJ : V.J = (1 : D.host.E) • W.gram) {k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J}
    (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)) :
    k = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (Eqv.famH D W (gsOf k) (unitFam_gsOf hJ k)) := by
  apply Subtype.ext; apply Units.ext
  show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = (Eqv.famM D W (gsOf k)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
  apply Eqv.mat_ext D
  · intro t
    ext i j
    have := congrFun (congrFun (Eqv.psi_famM D W (gsOf k) t) i) j
    simp only [Matrix.map_apply] at this ⊢
    rw [psiT_cA, this]
    simp [gsOf]
  · rw [fin_one_of_mem hk, fin_cA_one (Eqv.fin_famM D W (gsOf k))]

theorem mem_UAt (hJ : V.J = (1 : D.host.E) • W.gram) {x : GA D W} (hx : x ∈ GinfC W) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  have hf := fin_cA_one ((Eqv.mem_GinfC D W x).1 hx)
  intro u hu
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  apply at_of_finPart _ u hu
  have := congrFun (congrFun hf i) j
  rw [Matrix.map_apply] at this
  rw [Matrix.sub_apply, RingHom.map_sub, mat_conjU, this]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

end GlobalTheory.KInfLines

namespace GlobalTheory.KInfLines

variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}

theorem cartan_data (hJ : V.J = (1 : D.host.E) • W.gram) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) {r s : ℕ}
    (hV : V.IsHerm D.sp.cm.sig Bs r s) {k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J}
    (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) (t : D.what₂.Tau) :
    ∃ C : Matrix (Fin W.rank) (Fin W.rank) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (gramAt D W t)ᵀ C ∧
      Commute (gsOf k t) C ∧ ∀ (x : GA D W) (A : Matrix (Fin W.rank) (Fin W.rank) ℂ),
        (Eqv.matA D W x).map (Eqv.psiT D t) = A → Commute A C →
        Commute ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ x)).map
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb (GlobalTheory.AdelicU.placeOf D t)))) (V.θ (GlobalTheory.AdelicU.placeOf D t)) := by
  have hcom := hk.2 (GlobalTheory.AdelicU.placeOf D t)
  rw [eq_conjU_famH hJ hk.1] at hcom
  have hgsA : (Eqv.matA D W (Eqv.famH D W (gsOf k) (unitFam_gsOf hJ k))).map (Eqv.psiT D t) = gsOf k t :=
    Eqv.psi_famM D W (gsOf k) t
  have hV' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (W.gram.map (Bs.emb (GlobalTheory.AdelicU.placeOf D t)).1)
      (V.θ (GlobalTheory.AdelicU.placeOf D t)) := by
    have := hV.cartan (GlobalTheory.AdelicU.placeOf D t); rwa [hJ, one_smul] at this
  have hG : gramAt D W t = W.gram.map (tauE D t) := rfl
  rcases emb_cases t (Bs.emb (GlobalTheory.AdelicU.placeOf D t)) with he | he
  · have rd : ∀ x : GA D W, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ x)).map
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb (GlobalTheory.AdelicU.placeOf D t))) = ((Eqv.matA D W x).map (Eqv.psiT D t)).map conj := by
      intro x; ext i j
      simp only [mat_conjU, Matrix.map_apply]
      exact piInf_cA_of_eq t _ he _
    refine ⟨(V.θ (GlobalTheory.AdelicU.placeOf D t)).map conj, ?_, ?_, fun x A hA hc => ?_⟩
    · have := isCartan_conj hV'
      rwa [he, ← hG, map_conj_of_herm (GlobalTheory.SmoothForms.RealPts.gramAt_herm W t)] at this
    · rw [rd, hgsA] at hcom
      exact commute_map_conj_iff.1 hcom
    · rw [rd, hA]
      exact commute_map_conj_iff.2 hc
  · have rd : ∀ x : GA D W, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ x)).map
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb (GlobalTheory.AdelicU.placeOf D t))) = (Eqv.matA D W x).map (Eqv.psiT D t) := by
      intro x; ext i j
      simp only [mat_conjU, Matrix.map_apply]
      exact piInf_cA_of_eq_conj t _ he _
    refine ⟨V.θ (GlobalTheory.AdelicU.placeOf D t), ?_, ?_, fun x A hA hc => ?_⟩
    · have e : W.gram.map ((starRingEnd ℂ).comp (tauE D t)) = (gramAt D W t).map conj := by
        rw [hG, Matrix.map_map]; rfl
      have := hV'
      rwa [he, e, map_conj_of_herm (GlobalTheory.SmoothForms.RealPts.gramAt_herm W t)] at this
    · rw [rd, hgsA] at hcom
      exact hcom
    · rw [rd, hA]; exact hc

theorem line_mem (hJ : V.J = (1 : D.host.E) • W.gram) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (C : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hC : ∀ t (x : GA D W) (A : Matrix (Fin W.rank) (Fin W.rank) ℂ),
        (Eqv.matA D W x).map (Eqv.psiT D t) = A → Commute A (C t) →
        Commute ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ x)).map
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb (GlobalTheory.AdelicU.placeOf D t)))) (V.θ (GlobalTheory.AdelicU.placeOf D t)))
    {t : D.what₂.Tau} {Z : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hZ : Z ∈ lieAt W t) (hZC : Commute Z (C t)) (s' : ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP (Eqv.thetaC D) W t Z s') ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb := by
  have hat := GlobalTheory.Mem.Lift.isAtTau_oneP (isInfFam_thetaC D) hZ s'
  refine ⟨mem_UAt hJ hat.1, fun w => ?_⟩
  obtain ⟨t', rfl⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w
  by_cases e : t' = t
  · subst e
    exact hC t' _ _ (by rw [← Eqv.infMat_thetaC]; exact hat.2.1) (commute_exp hZC s')
  · exact hC t' _ 1 (by rw [← Eqv.infMat_thetaC]; exact hat.2.2 t' e) (Commute.one_left _)

theorem prod_eq (hJ : V.J = (1 : D.host.E) • W.gram) {k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J}
    (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F))
    (Z : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hZ : ∀ t, Z t ∈ lieAt W t ∧ NormedSpace.exp (Z t) = gsOf k t) :
    k = ((Finset.univ.toList.map fun t => (t, Z t)).map fun q =>
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP (Eqv.thetaC D) W q.1 q.2 1)).prod := by
  classical
  have hat : ∀ t (s' : ℝ), IsAtTau (Eqv.thetaC D) W t (NormedSpace.exp (s' • Z t)) (oneP (Eqv.thetaC D) W t (Z t) s') :=
    fun t s' => GlobalTheory.Mem.Lift.isAtTau_oneP (isInfFam_thetaC D) (hZ t).1 s'
  have e1 : ((Finset.univ.toList.map fun t => (t, Z t)).map fun q : D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ =>
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP (Eqv.thetaC D) W q.1 q.2 1)) =
      (Finset.univ.toList.map fun t => oneP (Eqv.thetaC D) W t (Z t) 1).map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ) := by
    rw [List.map_map, List.map_map]; rfl
  rw [e1, ← conjU_prod]
  refine (eq_conjU_famH hJ hk).trans (congrArg _ ?_)
  symm
  apply Eqv.famH_unique D W (gsOf k) (unitFam_gsOf hJ k)
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact (hat t 1).1
  · intro τ
    let φ : GA D W →* Matrix (Fin W.rank) (Fin W.rank) ℂ :=
      { toFun := fun h => (Eqv.matA D W h).map (Eqv.psiT D τ)
        map_one' := by rw [Eqv.matA_one]; exact Matrix.map_one _ (map_zero _) (map_one _)
        map_mul' := fun a b => by rw [Eqv.matA_mul]; exact Matrix.map_mul }
    have hterm : ∀ t, φ (oneP (Eqv.thetaC D) W t (Z t) 1) = if τ = t then gsOf k t else 1 := by
      intro t
      show (Eqv.matA D W _).map (Eqv.psiT D τ) = _
      rw [← Eqv.infMat_thetaC]
      by_cases e : τ = t
      · subst e; rw [if_pos rfl, (hat τ 1).2.1, one_smul, (hZ τ).2]
      · rw [if_neg e]; exact (hat t 1).2.2 τ e
    rw [Eqv.infMat_thetaC]
    show φ _ = gsOf k τ
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def, hterm]
    exact prod_map_ite (gsOf k) τ _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))

theorem prod_lines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  intro _ D θ W Bs V r s hJ hθ _ hV k hk
  obtain rfl := Eqv.eq_thetaC D hθ
  choose C hC using cartan_data hJ Bs hV hk
  choose Z hZ using fun t => exists_log_of_cartan (GlobalTheory.SmoothForms.RealPts.gramAt_herm W t) (hC t).1
    (unitFam_gsOf hJ k t) (hC t).2.1
  refine ⟨Finset.univ.toList.map fun t => (t, Z t), ?_, prod_eq hJ hk.1 Z fun t => ⟨(hZ t).1, (hZ t).2.2⟩⟩
  intro q hq
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
  exact ⟨(hZ t).1, line_mem hJ Bs C (fun t => (hC t).2.2) (hZ t).1 (hZ t).2.1⟩

end GlobalTheory.KInfLines
