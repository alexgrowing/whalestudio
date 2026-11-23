import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfDecompGlob
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical IsDedekindDomain

theorem bwG_span_dualSet {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) :
    ((Submodule.span (𝓞 K) (dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = dualSet σ J L := by
  apply le_antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero =>
      intro x _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add y y' _ _ hy hy' =>
      intro x hx
      have e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
        simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem (hy x hx) (hy' x hx)
    | smul r y _ hy =>
      intro x hx
      have e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact mul_mem ⟨r, rfl⟩ (hy x hx)
  · exact Submodule.subset_span

variable (D : D7) (u : D.what₂.Word)

theorem bwG_Ld_coe (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (Ld D u i hi c : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c) :=
  bwG_span_dualSet _ _ _

theorem bwG_intSpan_smul (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) {Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    D.what₂.embLL r • Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  induction hQ using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * s, f, mul_mem hr hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem bwG_int_mem (w : D.what₂.places.Pl) (k : 𝓞 D.what₂.LL) :
    algebraMap (𝓞 D.what₂.LL) D.what₂.LL k ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one k)

theorem bwG_inv_mem (w : D.what₂.places.Pl) {r : 𝓞 D.what₂.LL} (hr : r ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ ∈ intW D.what₂.places w := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hr
  exact (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])

def BwBasisInd (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B₂ : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B₂ →
    ∀ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z,
      fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi).eY z) =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q₂ ((Tt.val i hi).eY z)

theorem bwLocGlob_of_ind (Tt : FormsTied D u) (hI : BwBasisInd D u Tt) : BwLocGlob D u Tt := by
  intro w hw i hi y hy
  show y ∈ locW D.what₂.places w ((D.fm u).lat i).L
  rw [D.mem_locW_iff]
  obtain ⟨-, -, hsp⟩ := (D.fm u).lat_good i
  obtain ⟨d, hd, hdy⟩ := Formalism.L2.DIV.lc_exists_smul_mem ((D.fm u).lat i).L (x := y) (by rw [hsp]; trivial)
  obtain ⟨t, ht, htw⟩ := Formalism.L2.DIV.lc_primeTo d hd (D.plEq w)
  refine ⟨t, ht, ?_⟩
  refine ((Tt.val i hi).lat _).2 fun w' c B hB => ?_
  by_cases hw' : w' = w
  · subst hw'
    obtain ⟨B₀, hB₀, Q, hQ, hyQ⟩ := hy c
    have hB' : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B := by
      rw [bwG_Ld_coe, ← hw]
      exact hB
    obtain ⟨Q₂, hQ₂, he⟩ := hI w' hw i hi c B₀ B hB₀ hB' Q hQ
    refine ⟨_, bwG_intSpan_smul D w' _ _ (bwG_int_mem D w' t) hQ₂, fun z => ?_⟩
    rw [← algebraMap_smul D.what₂.LL t y, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hyQ z, he z,
      LinearMap.map_smul]
    rfl
  · have hne : D.plEq w' ≠ D.plEq w := fun h => hw' (D.plEq.injective h)
    obtain ⟨r, hr, k, hk⟩ := htw _ hne
    obtain ⟨P, hP, hdP⟩ := ((Tt.val i hi).lat _).1 hdy w' c B hB
    have hr0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL r ≠ 0 := by
      intro h
      apply hr
      have : r = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [h, map_zero])
      rw [this]
      exact zero_mem _
    have e : t • y = ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ * algebraMap (𝓞 D.what₂.LL) D.what₂.LL k) • (d • y) := by
      rw [← algebraMap_smul D.what₂.LL t y, ← algebraMap_smul D.what₂.LL d y, smul_smul]
      congr 1
      have hk' := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) hk
      rw [map_mul, map_mul] at hk'
      field_simp
      rw [mul_comm, hk', mul_comm]
    refine ⟨_, bwG_intSpan_smul D w' _ _ (mul_mem (bwG_inv_mem D w' hr) (bwG_int_mem D w' k)) hP, fun z => ?_⟩
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hdP z, LinearMap.map_smul]
    rfl

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
