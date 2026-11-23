import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInRat

variable {D : D7}

theorem toGf_injective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : Function.Injective (toGf P) := by
  intro a b h
  have h1 : finHom V (P.ψ a) = finHom V (P.ψ b) := congrArg Subtype.val h
  have h2 : Formalism.IndefR.Lev.finE V (P.ψ a) = Formalism.IndefR.Lev.finE V (P.ψ b) := by
    simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, h1]
  rw [hU, hU] at h2
  exact Subtype.ext h2

theorem toGf_surjective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Function.Surjective (toGf P) := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  obtain ⟨h, hh⟩ := P.onto k k1
  refine ⟨h, Subtype.ext ?_⟩
  show finHom V (P.ψ h) = finHom V x
  rw [hh, k2]

theorem af_nontrivial : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField (maximalRealSubfield D.host.E))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := ⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (ReciprocityTheory.Aut.evalAt D.host.E v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem inclL_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) := by
  haveI := af_nontrivial (D := D)
  haveI : Nontrivial (ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap (maximalRealSubfield D.host.E) (ReciprocityTheory.Aut.AFplus D.host.E)).injective
  exact (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E).injective

theorem inclA_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

def glL (n : ℕ) : GL (Fin n) D.host.E →* GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) :=
  Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom

theorem glL_injective (n : ℕ) : Function.Injective (glL (D := D) n) := fun a b h =>
  Units.ext (Matrix.map_injective inclL_injective (congrArg Units.val h))

theorem glL_mem (n : ℕ) (x : GL (Fin n) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E n) :
    glL n x ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  have h : (x : Matrix (Fin n) (Fin n) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  have h2 := congrArg (fun M => Matrix.map M
    (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  show (x : Matrix (Fin n) (Fin n) D.host.E).map _ * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
    ((x : Matrix (Fin n) (Fin n) D.host.E).map _) = 1
  rw [← h2]
  congr 1

def toStd (n : ℕ) : ReciprocityTheory.Aut.GQ0 D.host.E n →* ReciprocityTheory.Aut.GQ D.host.E n where
  toFun x := ⟨⟨glL n x.1, glL_mem n x.1 x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext1; ext1; exact map_one _
  map_mul' a b := by ext1; ext1; exact map_mul _ _ _

theorem toStd_bij (n : ℕ) : Function.Bijective (toStd (D := D) n) := by
  refine ⟨fun a b h => Subtype.ext (glL_injective n (congrArg (fun y => y.1.1) h)), fun γ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩

section V

variable {V : HSp D}

theorem cT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) M := rfl

theorem mem_UJ (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h : (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  show Formalism.UG.cT _ (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x = V.gram
  rw [hV, Matrix.mul_one, cT_eq]
  exact mul_eq_one_comm.1 h

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E)
    (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  rw [hV, Matrix.mul_one, cT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_HR (x : GL (Fin V.rank) D.host.E) (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  have h2 := GlobalTheory.UnitarySplit.map_cond (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (sigR (AF D.host.F) D.sp.cm.sig) (fun y => rfl) V.gram x.1
  rw [h] at h2
  exact h2.symm

def toV (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ0 D.host.E V.rank →* Formalism.L2.Theta.GQ V where
  toFun x := ⟨⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x.1, mem_HR x.1 (mem_UJ hV x.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 ⟨x.1, mem_UJ hV x.1 x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_mul _ _ _

theorem toV_bij (hV : V.gram = 1) : Function.Bijective (toV hV) := by
  refine ⟨fun a b h => Subtype.ext (Units.ext (Matrix.map_injective inclA_injective
    (congrArg (fun y : Formalism.L2.Theta.GQ V => Units.val (y.1 : HR (AF D.host.F) D.sp.cm.sig V.gram).1) h))), fun δ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 δ.2)
  exact ⟨⟨x, mem_rationalGL_of_unitaryGroupGram_unitGram hV x hx⟩, Subtype.ext (Subtype.ext he)⟩

def ratE (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V :=
  (MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm.trans (MulEquiv.ofBijective (toV hV) (toV_bij hV))

theorem ratE_toStd (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) : ratE hV (toStd V.rank x) = toV hV x :=
  congrArg (toV hV) ((MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm_apply_apply x)

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem finHom_eq_of_finE {g h : GA D V} (e : Formalism.IndefR.Lev.finE V g = Formalism.IndefR.Lev.finE V h) :
    finHom V g = finHom V h :=
  Units.ext (Matrix.map_injective swapAE_injective (congrArg Units.val e))

theorem finE_toV (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    Formalism.IndefR.Lev.finE V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = km D V.rank (toStd V.rank x).1 := by
  apply Units.ext
  ext i j
  show swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (x.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
  simp [Algebra.TensorProduct.map_tmul, swapAE, glL]
  rfl

theorem ratIso_ratE (hV : V.gram = 1) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : RatIso P (ratE hV) := by
  intro γ
  obtain ⟨x, rfl⟩ := (toStd_bij (D := D) V.rank).2 γ
  have hr := ratE_toStd hV x
  refine ⟨(congrArg (Bridge.ratF V) hr).trans (Subtype.ext ?_), fun γ₀ h => ?_⟩
  · exact finHom_eq_of_finE ((finE_toV hV x).trans (hU (toStd V.rank x).1).symm)
  · have hx : x.1 = γ₀ := glL_injective V.rank (Units.ext h)
    have key : Bridge.IsRatMat V (toV hV x) γ₀ := by
      show Formalism.L2.Theta.matHom V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = Formalism.UG.bc (incA D) γ₀
      rw [← hx]
      rfl
    exact hr ▸ key

end V

theorem toGf_bij_ratIso : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank), V.gram = 1 → UnitFr P →
    Function.Bijective (toGf P) ∧ ∃ e, RatIso P e := by
  intro D V P hV hU
  exact ⟨⟨toGf_injective P hU, toGf_surjective P⟩, ratE hV, ratIso_ratE hV P hU⟩

end GlobalTheory.MtInRat
