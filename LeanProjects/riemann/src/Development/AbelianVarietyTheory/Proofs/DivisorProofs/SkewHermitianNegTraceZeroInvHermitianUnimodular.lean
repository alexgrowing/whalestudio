import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerSkew

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

section Gen

variable {K : Type} [Field K] [StarRing K] {k : ℕ}

theorem star_smul_vec (e : K) (a : Fin k → K) : star (e • a) = star e • star a := by
  funext i
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']

theorem psi_smul (M : Matrix (Fin k) (Fin k) K) (e : K) (a : Fin k → K) :
    M *ᵥ star (e • a) = star e • (M *ᵥ star a) := by
  rw [star_smul_vec, Matrix.mulVec_smul]

theorem psiInv_smul (N : Matrix (Fin k) (Fin k) K) (e : K) (x : Fin k → K) :
    star (N *ᵥ (e • x)) = star e • star (N *ᵥ x) := by
  rw [Matrix.mulVec_smul, star_smul_vec]

end Gen

variable (D : D7) {k : ℕ}

def conjO (c : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨star (c : D.host.E), int_cc D c.isIntegral_coe⟩

theorem herm_eq (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ star y) := by
  have hc : ∀ z : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc z = star z := fun _ => rfl
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_eq (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y = x ⬝ᵥ (J *ᵥ star y) := rfl

theorem herm_smul (c : D.host.E) (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm (c • J) x y = c * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [herm_eq, form_eq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mem_Dinv_iff (w : D.host.E) :
    w ∈ Dinv D ↔ ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * w)) := by
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  rw [Dinv, FractionalIdeal.mem_dual h1]
  constructor
  · intro h o
    have h1 := h (o : D.host.E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨q, hq⟩ := h1
    rw [← hq]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.1 (h o)

theorem sesq_psi (G M : Matrix (Fin k) (Fin k) D.host.E) (a b : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G (M *ᵥ star b) (M *ᵥ star a) = b ⬝ᵥ ((Mᴴ * G * M) *ᵥ star a) := by
  rw [GlobalTheory.WeilSchrodingerHerm.sesq_apply, Matrix.star_mulVec, star_star, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

theorem herm_swap (G : Matrix (Fin k) (Fin k) D.host.E) (hG : ∀ i j, star (G i j) = G j i) (x y : Fin k → D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G y x = star (ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  rw [herm_eq, herm_eq]
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def latQ (N : Matrix (Fin k) (Fin k) D.host.E) (L' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin k → D.host.E) where
  carrier := {x | star (N *ᵥ x) ∈ L'}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Matrix.mulVec_add, star_add] at *
    exact L'.add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.mulVec_zero, star_zero]
    exact L'.zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [← algebraMap_smul D.host.E c x, psiInv_smul]
    have e : star (algebraMap (𝓞 D.host.E) D.host.E c) = algebraMap (𝓞 D.host.E) D.host.E (conjO D c) := rfl
    rw [e, algebraMap_smul]
    exact L'.smul_mem _ hx

theorem mem_latQ {N : Matrix (Fin k) (Fin k) D.host.E} {L' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {x : Fin k → D.host.E} : x ∈ latQ D N L' ↔ star (N *ᵥ x) ∈ L' := Iff.rfl

theorem psi_mem_iff {M N : Matrix (Fin k) (Fin k) D.host.E} (hNM : N * M = 1)
    {L' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (a : Fin k → D.host.E) :
    M *ᵥ star a ∈ latQ D N L' ↔ a ∈ L' := by
  rw [mem_latQ, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, star_star]

theorem latQ_isLattice {M N : Matrix (Fin k) (Fin k) D.host.E} (hMN : M * N = 1) (hNM : N * M = 1)
    (L' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL' : L'.IsLattice D.host.E) :
    (latQ D N L').IsLattice D.host.E := by
  classical
  have hback : ∀ x : Fin k → D.host.E, M *ᵥ star (star (N *ᵥ x)) = x := fun x => by
    rw [star_star, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := hL'.fg
    refine ⟨s.image (fun a => M *ᵥ star a), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact (psi_mem_iff D hNM a).2 (hs ▸ Submodule.subset_span ha)
    · intro x hx
      have hx' : star (N *ᵥ x) ∈ Submodule.span (𝓞 D.host.E) (s : Set (Fin k → D.host.E)) := hs.symm ▸ hx
      have key : ∀ a ∈ Submodule.span (𝓞 D.host.E) (s : Set (Fin k → D.host.E)),
          M *ᵥ star a ∈ Submodule.span (𝓞 D.host.E)
            ((s.image (fun a => M *ᵥ star a) : Finset (Fin k → D.host.E)) : Set (Fin k → D.host.E)) := by
        intro a ha
        induction ha using Submodule.span_induction with
        | mem a ha =>
          apply Submodule.subset_span
          rw [Finset.coe_image]
          exact ⟨a, ha, rfl⟩
        | zero => simp
        | add a b _ _ iha ihb =>
          rw [star_add, Matrix.mulVec_add]
          exact Submodule.add_mem _ iha ihb
        | smul c a _ ih =>
          rw [← algebraMap_smul D.host.E c a, psi_smul]
          have e : star (algebraMap (𝓞 D.host.E) D.host.E c) = algebraMap (𝓞 D.host.E) D.host.E (conjO D c) := rfl
          rw [e, algebraMap_smul]
          exact Submodule.smul_mem _ _ ih
      have := key _ hx'
      rwa [hback] at this
  · rw [eq_top_iff]
    intro x _
    have hx' : star (N *ᵥ x) ∈ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) := by
      rw [hL'.span_eq_top]; trivial
    have key : ∀ a ∈ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)),
        M *ᵥ star a ∈ Submodule.span D.host.E ((latQ D N L' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) :
          Set (Fin k → D.host.E)) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact Submodule.subset_span ((psi_mem_iff D hNM a).2 ha)
      | zero => simp
      | add a b _ _ iha ihb =>
        rw [star_add, Matrix.mulVec_add]
        exact Submodule.add_mem _ iha ihb
      | smul c a _ ih =>
        rw [psi_smul]
        exact Submodule.smul_mem _ _ ih
    have := key _ hx'
    rwa [hback] at this

theorem localLattice_isLattice (hP : FactPrincipalDatum) (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E))
    (hΛ : Λ.IsLattice D.host.E) : (lattice₂ D Λ).IsLattice D.host.E := by
  refine ⟨localLattice_fg D Λ hΛ.fg, ?_⟩
  have h0 : (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    inv_ne_zero (Formalism.L2.Pj.AA_ne_zero hP D)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h => h0 (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  rw [eq_top_iff]
  rintro v -
  have hv0 : v ∈ Submodule.span D.host.E (Λ : Set (Fin k → D.host.E)) := by rw [hΛ.span_eq_top]; trivial
  have hv : b • v ∈ Submodule.span D.host.E ((lattice₂ D Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) :
      Set (Fin k → D.host.E)) := by
    induction hv0 using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (smul_mem_latP hP hb hz)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ ih =>
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ih
  have := Submodule.smul_mem _ b⁻¹ hv
  rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this

variable (B : Base D.host.F D.host.E) {d : ℕ} (Y : Spc D.host.F D.host.E d) {r s : ℕ}

theorem det_J_ne_zero_skew (hY : Y.IsSkew D.sp.cm.sig B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hY.sig w)
  intro h0
  apply h
  have hm : (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]

theorem skew_to_herm (hY : Y.IsSkew D.sp.cm.sig B r s) :
    IsUnit Y.J.det ∧ ∃ L : Submodule (𝓞 D.host.E) (Fin d → D.host.E), L.IsLattice D.host.E ∧
      (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).IsSymm ∧
      (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)) L := by
  have hP : FactPrincipalDatum := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ : D.host.xi0 ≠ 0 := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero hP D
  have hsξ : star D.host.xi0 = -D.host.xi0 := Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg
  have hdet : Y.J.det ≠ 0 := det_J_ne_zero_skew D B Y hY
  have hu : IsUnit Y.J.det := isUnit_iff_ne_zero.2 hdet
  have hsk : ∀ i j, star (Y.J j i) = -Y.J i j := fun i j => hY.skew i j
  have hJ : Y.Jᴴ = -Y.J := Matrix.ext fun i j => by
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
    exact hsk i j
  refine ⟨hu, ?_⟩
  set ξ := D.host.xi0 with hξdef
  set G : Matrix (Fin d) (Fin d) D.host.E := -ξ • Y.J⁻¹ with hGdef
  set G' : Matrix (Fin d) (Fin d) D.host.E := ξ⁻¹ • Y.J with hG'def
  set M : Matrix (Fin d) (Fin d) D.host.E := (-ξ⁻¹) • Y.J with hMdef
  have hMN : M * G = 1 := by
    rw [hMdef, hGdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hu, neg_mul_neg,
      inv_mul_cancel₀ hξ, one_smul]
  have hNM : G * M = 1 := by
    rw [hMdef, hGdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hu, neg_mul_neg,
      mul_inv_cancel₀ hξ, one_smul]
  have hJinv : (Y.Jᴴ)⁻¹ = -Y.J⁻¹ := by
    rw [hJ]
    apply Matrix.inv_eq_left_inv
    rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_nonsing_inv, hJinv, star_neg, hsξ, neg_neg, smul_neg,
      neg_smul]
  have hsG : ∀ i j, star (G i j) = G j i := fun i j => by
    have := congrFun (congrFun hGh j) i
    rwa [Matrix.conjTranspose_apply] at this
  have hsG' : ∀ i j, star (G' i j) = G' j i := fun i j => by
    rw [hG'def, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul', star_inv₀, hsξ]
    have e : star (Y.J i j) = -Y.J j i := hsk j i
    rw [e, inv_neg, neg_mul_neg]
  have hMh : Mᴴ = -(ξ⁻¹ • Y.J) := by
    rw [hMdef, Matrix.conjTranspose_smul, hJ, star_neg, star_inv₀, hsξ, inv_neg, neg_neg, smul_neg]
  have hM : Mᴴ * G * M = -G' := by
    rw [hMh, hGdef, hMdef, hG'def]
    simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [neg_mul_neg, inv_mul_cancel₀ hξ, one_smul]
  have hkey : ∀ a b : Fin d → D.host.E,
      GlobalTheory.WeilSchrodinger.sesq D G (M *ᵥ star b) (M *ᵥ star a) = -ReciprocityTheory.ChartRestriction.G.FD.herm G' b a := by
    intro a b
    rw [sesq_psi, hM, Matrix.neg_mulVec, dotProduct_neg, herm_eq]
  have hF : ∀ y, y ∈ Y.L ↔ ∀ z ∈ Y.L, ξ * ReciprocityTheory.ChartRestriction.G.FD.herm G' y z ∈ Dinv D := by
    intro y
    rw [hY.dual y]
    refine forall₂_congr fun z _ => ?_
    rw [hG'def, herm_smul, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul, mem_Dinv_iff]
  have hdetG : G.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hMN
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at h1
    exact zero_ne_one h1
  refine ⟨latQ D G (lattice₂ D Y.L), latQ_isLattice D hMN hNM _ (localLattice_isLattice D hP Y.L hY.lat), ?_, ?_, ?_⟩
  ·
    refine ⟨fun x y => ?_⟩
    simp only [GlobalTheory.WeilSchrodingerHerm.sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
      star_star, Pi.star_apply, hsG, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h1 : star x ᵥ* G = 0 := by
        refine dotProduct_eq_zero _ fun v => ?_
        rw [← Matrix.dotProduct_mulVec, ← GlobalTheory.WeilSchrodingerHerm.sesq_apply]
        exact hx v
      have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdetG h1
      simpa using congrArg star h2
    · have h1 : G *ᵥ y = 0 := by
        refine dotProduct_eq_zero _ fun v => ?_
        rw [dotProduct_comm]
        have := hy (star v)
        rwa [GlobalTheory.WeilSchrodingerHerm.sesq_apply, star_star] at this
      exact Matrix.eq_zero_of_mulVec_eq_zero hdetG h1
  ·
    show Formalism.E.hdual _ _ = _
    have hback : ∀ x : Fin d → D.host.E, M *ᵥ star (star (G *ᵥ x)) = x := fun x => by
      rw [star_star, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      GlobalTheory.WeilSchrodingerHerm.mem_one_iff]
    obtain ⟨a, rfl⟩ : ∃ a, x = M *ᵥ star a := ⟨star (G *ᵥ x), (hback x).symm⟩
    rw [psi_mem_iff D hNM]
    constructor
    · intro h
      apply mem_dual_localLattice_of_forall hP G' Y.L hF
      intro b hb
      have h1 := h _ ((psi_mem_iff D hNM b).2 hb)
      rw [hkey] at h1
      have h2 : IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm G' b a) := by simpa using h1.neg
      rw [herm_swap D G' hsG' b a]
      exact int_cc D h2
    · intro ha y hy
      obtain ⟨b, rfl⟩ : ∃ b, y = M *ᵥ star b := ⟨star (G *ᵥ y), (hback y).symm⟩
      rw [psi_mem_iff D hNM] at hy
      rw [hkey]
      exact (localLattice_form_integral hP G' Y.L hF hy ha).neg

end GlobalTheory.WeilSchrodingerSkew

end

theorem GlobalTheory.WeilSchrodingerSkew.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (d : ℕ) (Y : Spc D.host.F D.host.E d) (r s : ℕ), Y.IsSkew D.sp.cm.sig B r s →
      IsUnit Y.J.det ∧ ∃ L : Submodule (𝓞 D.host.E) (Fin d → D.host.E), L.IsLattice D.host.E ∧
        (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).IsSymm ∧
        (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)) L :=
  fun D B _ _ Y _ _ hY => GlobalTheory.WeilSchrodingerSkew.skew_to_herm D B Y hY
