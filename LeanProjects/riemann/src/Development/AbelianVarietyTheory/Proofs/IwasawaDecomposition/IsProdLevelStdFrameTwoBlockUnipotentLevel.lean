import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtInProd

section Cut

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def cutMat (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem cutMat_one (e : R) : cutMat e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [cutMat, ← add_smul, add_sub_cancel, one_smul]

theorem cutMat_one_left (M : Matrix (Fin n) (Fin n) R) : cutMat 1 M = M := by
  rw [cutMat, one_smul, sub_self, zero_smul, add_zero]

theorem cutMat_zero_left (M : Matrix (Fin n) (Fin n) R) : cutMat 0 M = 1 := by
  rw [cutMat, zero_smul, sub_zero, one_smul, zero_add]

theorem cutMat_mul {e : R} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) R) :
    cutMat e (M * N) = cutMat e M * cutMat e N := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h2, h3, zero_smul, add_zero, zero_add]

theorem cutMat_mul_compl {e : R} (he : e * e = e) (M : Matrix (Fin n) (Fin n) R) :
    cutMat e M * cutMat (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem map_cutMat (f : R →+* S) (e : R) (M : Matrix (Fin n) (Fin n) R) :
    (cutMat e M).map f = cutMat (f e) (M.map f) := by
  ext i j
  by_cases h : i = j <;> simp [cutMat, Matrix.one_apply, h]

theorem conjT_cutMat (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    ReciprocityTheory.Aut.conjT σ (cutMat e M) = cutMat e (ReciprocityTheory.Aut.conjT σ M) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ReciprocityTheory.Aut.conjT, cutMat, hσ]
  · simp [ReciprocityTheory.Aut.conjT, cutMat, hσ, Matrix.one_apply, h, Ne.symm h]

def cutHom {e : R} (he : e * e = e) : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R where
  toFun := cutMat e
  map_one' := cutMat_one e
  map_mul' := cutMat_mul he

end Cut

section Adelic

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open Classical

def idemF (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AFplus L :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem idemF_apply (v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (idemF (L := L) v) w = if w = v then 1 else 0 := rfl

theorem idemF_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemF (L := L) v * idemF v = idemF v := by
  apply Subtype.ext
  funext w
  show (if w = v then (1 : w.adicCompletion (maximalRealSubfield L)) else 0) * (if w = v then 1 else 0) = (if w = v then 1 else 0)
  split_ifs <;> simp

variable (L) in

def eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] idemF v

theorem eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v * eA L v = eA L v := by
  rw [eA, Algebra.TensorProduct.tmul_mul_tmul, one_mul, idemF_mul]

theorem conj_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : conjAL L (eA L v) = eA L v := by
  simp [conjAL, eA, Algebra.TensorProduct.map_tmul]

theorem compAt_eA (w v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L w (eA L v) = if w = v then 1 else 0 := by
  have : compAt L w (eA L v) = (1 : L) ⊗ₜ[maximalRealSubfield L] ((idemF (L := L) v) w) := rfl
  rw [this, idemF_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem eA_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v ∈ ALint L :=
  Subring.subset_closure (Or.inr ⟨idemF v, fun w => by
    rw [idemF_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _, rfl⟩)

def cutGA {e : AL L} (he : e * e = e) (hc : conjAL L e = e) : GA L n →* GA L n :=
  ((Units.map (cutHom (n := n) he)).comp (GA L n).subtype).codRestrict _ (fun g => by
    have hg : (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) g.1 = 1 := g.2
    show cutMat e (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (cutMat e g.1) = 1
    rw [conjT_cutMat _ hc, ← cutMat_mul he, hg, cutMat_one])

theorem cutGA_val {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) = cutMat e g.1 := rfl

theorem cutGA_mem_Umax {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (heI : e ∈ ALint L) {g : GA L n}
    (hg : g ∈ Umax L n) : cutGA he hc g ∈ Umax L n := by
  have hg' : ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hg
  show ∀ i j, ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  intro i j
  rw [cutGA_val]
  simp only [cutMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine Subring.add_mem _ (Subring.mul_mem _ heI (hg' i j)) (Subring.mul_mem _ (Subring.sub_mem _ (Subring.one_mem _) heI) ?_)
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Adelic

section Adelic2

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cut_map_compAt {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) =
      cutMat (compAt L w e) ((g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w)) := by
  rw [cutGA_val, map_cutMat]

theorem one_sub_eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (1 - eA L v) * (1 - eA L v) = 1 - eA L v := by
  rw [mul_sub, mul_one, sub_mul, one_mul, eA_mul, sub_self, sub_zero]

theorem conj_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (1 - eA L v) = 1 - eA L v := by
  rw [map_sub, map_one, conj_eA]

theorem triv_cut_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v} (cutGA (eA_mul v) (conj_eA v) g) := by
  intro w hw
  rw [cut_map_compAt, compAt_eA, if_neg (fun h => hw (Set.mem_singleton_iff.2 h)), cutMat_zero_left]

theorem triv_cut_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v}ᶜ (cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g) := by
  intro w hw
  have hwv : w = v := by simpa using hw
  rw [cut_map_compAt, map_sub, map_one, compAt_eA, if_pos hwv, sub_self, cutMat_zero_left]

theorem cut_eA_at (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    ((cutGA (eA_mul v) (conj_eA v) g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [cut_map_compAt, compAt_eA, if_pos rfl, cutMat_one_left]

theorem cut_mul_cut (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    cutGA (eA_mul v) (conj_eA v) g * cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g = g :=
  Subtype.ext (Units.ext (cutMat_mul_compl (eA_mul v) _))

end Adelic2

theorem main : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  intro D n hr Pg Q ψ chi xi κ hκ v
  obtain ⟨hUA, hSt, hred, -⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  set κ1 := cutGA (eA_mul v) (conj_eA v) κ with hκ1
  set κ2 := cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) κ with hκ2
  have hκ' := Subgroup.mem_comap.1 hκ
  rw [mem_lev, mem_parLev] at hκ'
  obtain ⟨⟨-, hSκ, hPg, hQ⟩, hT⟩ := hκ'
  have hUm : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hSt κ).1 hSκ
  have hUm1 : κ1 ∈ ReciprocityTheory.Aut.Umax D.host.E n := cutGA_mem_Umax _ _ (eA_mem v) hUm
  have hUm2 : κ2 ∈ ReciprocityTheory.Aut.Umax D.host.E n :=
    cutGA_mem_Umax _ _ (Subring.sub_mem _ (Subring.one_mem _) (eA_mem v)) hUm
  have key : ∀ PP, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) ∨
      redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = 1 := by
    intro PP
    have hov : NG.OverPl PP (underPl (maximalRealSubfield D.host.E) PP) := (underPl_asIdeal (F := maximalRealSubfield D.host.E) PP).symm
    by_cases h : underPl (maximalRealSubfield D.host.E) PP = v
    · left
      rw [← cut_mul_cut v κ, map_mul, redFn_mul ((hSt _).2 hUm1) ((hSt _).2 hUm2),
        hred κ2 hUm2 {v}ᶜ _ PP (triv_cut_one_sub_eA v κ) (h ▸ hov) (by simp), mul_one]
    · right
      exact hred κ1 hUm1 {v} _ PP (triv_cut_eA v κ) hov h
  refine ⟨κ1, ?_, triv_cut_eA v κ, cut_eA_at v κ⟩
  apply Subgroup.mem_comap.2
  rw [mem_lev, mem_parLev]
  refine ⟨⟨hUA κ1, (hSt κ1).2 hUm1, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rcases key PP with h | h <;> rw [h]
    · exact hPg PP hP
    · exact Subgroup.one_mem _
  · rcases key PP with h | h <;> rw [h]
    · exact hQ PP hP
    · exact Subgroup.one_mem _
  · intro PP _
    have hT' := hT PP (Set.mem_univ _)
    show upperLeftBlock _ (redFn _ PP.1 (km D n κ1)) ∈ _
    rcases key PP.1 with h | h <;> rw [h]
    · exact hT'
    · have h2 : upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      show upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) ∈ unip (kP PP.1) D.R.r
      rw [h2]
      exact (unip (kP PP.1) D.R.r).one_mem

end GlobalTheory.MtInProd
