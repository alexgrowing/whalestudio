import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSpace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc HasSig)
open scoped Matrix

variable {D : D7}

def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)

instance surj_cO : RingHomSurjective (cO D) :=
  ⟨fun o => ⟨cO D o, by ext; simp [cO]⟩⟩

instance surj_star : RingHomSurjective (starRingEnd D.host.E) :=
  ⟨fun o => ⟨star o, by rw [starRingEnd_apply, star_star]⟩⟩

def cvO (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[cO D] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    ext i
    simp only [Pi.smul_apply, cO]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [smul_eq_mul, star_mul', mul_eq_mul_left_iff, map_mul, Pi.smul_apply]
    first
      | exact Or.inl rfl
      | (simp [mul_comm]; exact Or.inl rfl)

def cvE (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[starRingEnd D.host.E] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    funext i
    show star (o * z i) = star o * star (z i)
    exact star_mul' _ _

def conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  L.map (cvO D n)

theorem mem_conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (z : Fin n → D.host.E) :
    z ∈ conjLat L ↔ (fun i => star (z i)) ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : (fun i => star ((cvO D n) y i)) = y := by ext i; simp [cvO]
    rw [e]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    ext i; simp [cvO]

theorem isLattice_conjLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : L.IsLattice D.host.E) :
    (conjLat L).IsLattice D.host.E := by
  refine ⟨hL.fg.map _, ?_⟩
  have h1 : ((conjLat L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = cvE D n '' (L : Set _) := by
    rw [conjLat, Submodule.map_coe]; rfl
  rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro z
  exact ⟨fun i => star (z i), by ext i; simp [cvE]⟩

theorem isIntegral_star_iff (a : D.host.E) : IsIntegral ℤ (star a) ↔ IsIntegral ℤ a := by
  constructor
  · intro h
    have := map_isIntegral_int (starRingEnd D.host.E) h
    rwa [starRingEnd_apply, star_star] at this
  · intro h
    exact map_isIntegral_int (starRingEnd D.host.E) h

theorem form_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : ∀ i j, D.sp.cm.sig (J j i) = J i j)
    (a b : Fin n → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J (fun i => star (a i)) b =
      star (∑ i, ∑ j, star (star (b i)) * J i j * a j) := by
  have hs : ∀ i j, star (J i j) = J j i := fun i j => hJ j i
  have hσ : ∀ x, D.sp.cm.sig x = star x := fun _ => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hσ, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {B : Base D.host.F D.host.E} {n r s : ℕ} {V : Spc D.host.F D.host.E n}

theorem mem_conjLat_iff (hV : V.IsHerm D.sp.cm.sig B r s) (z : Fin n → D.host.E) :
    z ∈ conjLat V.L ↔ ∀ x ∈ conjLat V.L, IsIntegral ℤ (∑ i, ∑ j, star (x i) * V.J i j * z j) := by
  rw [mem_conjLat, hV.dual]
  constructor
  · intro h x hx
    rw [mem_conjLat] at hx
    have h1 := h _ hx
    rw [form_conj V.J hV.herm] at h1
    simpa only [star_star, isIntegral_star_iff] using h1
  · intro h y hy
    have hx : (fun i => star (y i)) ∈ conjLat V.L := by
      rw [mem_conjLat]; simpa only [star_star] using hy
    have h1 := h _ hx
    rw [form_conj V.J hV.herm, isIntegral_star_iff]
    exact h1

theorem sesq_herm (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).IsSymm := by
  have hs : ∀ i j, star (V.J i j) = V.J j i := fun i j => hV.herm j i
  refine ⟨fun x y => ?_⟩
  simp only [GlobalTheory.WeilSchrodingerHerm.sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
    star_star, Pi.star_apply, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_nondeg (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).Nondegenerate := by
  have hdet : V.J.det ≠ 0 := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D B V hV
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : star x ᵥ* V.J = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← GlobalTheory.WeilSchrodingerHerm.sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  · have h1 : V.J *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [GlobalTheory.WeilSchrodingerHerm.sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

theorem sesq_unimod (hV : V.IsHerm D.sp.cm.sig B r s) :
    Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D V.J) (conjLat V.L) := by
  show Formalism.E.hdual _ (conjLat V.L) = conjLat V.L
  ext x
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [mem_conjLat_iff hV x]
  refine forall₂_congr fun y _ => ?_
  rw [GlobalTheory.WeilSchrodingerHerm.sesq_apply, GlobalTheory.WeilSchrodingerHerm.mem_one_iff]
  have e : star y ⬝ᵥ (V.J *ᵥ x) = ∑ i, ∑ j, star (y i) * V.J i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [e]

theorem hasSig_map_conj {m a b : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : HasSig M a b) :
    HasSig (M.map (starRingEnd ℂ)) a b := by
  obtain ⟨hn, A, hA⟩ := h
  refine ⟨hn, A.map star, ?_⟩
  have e1 : (A.map star).map star = A := by ext i j; simp
  have e2 : (A.map star)ᵀ * M.map (starRingEnd ℂ) * A = (Aᵀ * M * A.map star).map (starRingEnd ℂ) := by
    simp only [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j; simp
  rw [e1, e2, hA, Matrix.fromBlocks_map]
  have e3 : (-1 : Matrix (Fin b) (Fin b) ℂ).map (starRingEnd ℂ) = -1 := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp [e3]

theorem hasSignature_all (hG : B.IsGood D.sp.cm.sig) {m a b : ℕ} (J : Matrix (Fin m) (Fin m) D.host.E)
    (hs : ∀ w, HasSig (J.map (B.emb w).1) a b) (φ : D.host.E →+* ℂ) : Formalism.UG.HasSignature (J.map φ) a b := by
  have h := hG.cm
  haveI := h.1
  set w := InfinitePlace.mk (φ.comp (algebraMap D.host.F D.host.E)) with hw
  have hreal : ComplexEmbedding.IsReal (φ.comp (algebraMap D.host.F D.host.E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have he : (B.emb w).1.comp (algebraMap D.host.F D.host.E) = φ.comp (algebraMap D.host.F D.host.E) := by
    rw [(B.emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  rcases GlobalTheory.IdxAll.eq_or_eq_comp _ h _ _ he with h1 | h1
  · rw [h1]; exact hasSig_map_conj (hs w)
  · have e : (J.map φ).map (starRingEnd ℂ) = J.map (B.emb w).1 := by
      ext i j; simp [h1]
    rw [e]; exact hs w

end GlobalTheory.ConjSpace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc) in

theorem GlobalTheory.ConjSpace.main : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  intro D Bs hG _ n r p V hV
  have hn : r + p = n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact (hV.sig w).1
  have hgram := GlobalTheory.WeilSchrodinger.gram_hspOf V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p))
  refine ⟨GlobalTheory.WeilSchrodinger.hspOf D V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p)), GlobalTheory.ConjSpace.conjLat V.L, ⟨GlobalTheory.ConjSpace.isLattice_conjLat hV.lat, fun y => ?_⟩,
    fun τ => ?_, ⟨rfl, ?_, fun y => ?_⟩⟩
  · rw [hgram]
    refine (GlobalTheory.ConjSpace.mem_conjLat_iff (n := n) hV y).trans ?_
    refine forall₂_congr fun x _ => ?_
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩
  · show Formalism.UG.HasSignature ((HSpace.gram _).map (tauE D τ)) _ p
    rw [hgram]
    have h := GlobalTheory.ConjSpace.hasSignature_all hG V.J hV.sig (tauE D τ)
    have hr : r = n - p := by omega
    rw [hr] at h
    exact h
  · rw [hgram, one_smul]
    rfl
  · refine Iff.symm ((GlobalTheory.ConjSpace.mem_conjLat (n := n) V.L _).trans ?_)
    simp only [star_star]
    exact Iff.rfl

end
