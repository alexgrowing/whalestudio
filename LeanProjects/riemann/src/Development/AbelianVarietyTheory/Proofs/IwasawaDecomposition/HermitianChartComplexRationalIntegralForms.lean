import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul

noncomputable section

namespace GlobalTheory.Mem.Col2.ValTie

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct

section Frames

variable {ι : Type} [Fintype ι] {n : ℕ}

def mulFr {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Frames G) : Frames G :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

omit [Fintype ι] in
theorem mulFr_val {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Frames G) (τ : ι) : (mulFr g hg y).1 τ = g τ * y.1 τ := rfl

theorem cspan_eq (lam : ι → DomWeight n) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  refine le_antisymm ((Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_) fun F hF => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    show MvPolynomial.map (RingHom.id ℂ) P ∈ _
    rw [MvPolynomial.map_id]
    exact hP
  · have h := Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam F hF
    rwa [MvPolynomial.map_id] at h

theorem valC_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Frames G → ℂ} (hv : v ∈ ValC G lam) :
    (fun z => v (mulFr g hg z)) ∈ ValC G lam := by
  unfold ValC at hv ⊢
  rw [cspan_eq] at hv ⊢
  obtain ⟨P, hP, rfl⟩ := hv
  refine ⟨(∏ τ, (g τ).det ^ shiftOf lam τ) • Formalism.GradedWeylDivisibility.blockAct ℂ g P,
    Submodule.smul_mem _ _ (Formalism.L2.DIV.ps_blockAct_mem_VV lam g hP), ?_⟩
  rw [← Formalism.L2.Col.fnOf_mul]
  funext z
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, mulFr_val, Pi.one_apply, Matrix.one_mul, Matrix.mul_one]

variable {E : Type} [Field E]

omit [Fintype ι] in
theorem atInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) :
    atInf emb (a * b) = atInf emb a * atInf emb b := by
  funext τ
  simp [atInf, Matrix.map_mul]

omit [Fintype ι] in
theorem isUnit_atInf (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  show IsUnit (((γ : Matrix (Fin n) (Fin n) E)).map (emb τ)).det
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units γ).map _

end Frames

section Pol

open Formalism.L2.Col Formalism.L2.DIV
open scoped Pointwise

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

def RatPol (lam : ι → DomWeight n) : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

theorem smul_mem_RatPol (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatPol s lam) : s r • p ∈ RatPol s lam := by
  unfold RatPol at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatPol_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatPol s (fun τ => Formalism.L2.Forms.shW (lam τ) (c τ)) = RatPol s lam := by
  unfold RatPol
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatPol (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatPol s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatPol at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatPol (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatPol s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatPol s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatPol s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatPol s lam c hx

end Pol

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem mem_fiC_iff (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) {c : Type}
    (y : c → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))) (φ : c → Frames (gramC J emb) → ℂ) :
    φ ∈ FiC S emb lam y ↔ ∀ c0, φ c0 ∈ ValC (gramC J emb) lam ∧ ∀ γ ∈ UJ (σ : E →+* E) J, ∀ κ : S.U,
      (y c0).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c0).1 * κ.1 →
      ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z → φ c0 z = (S.chi κ : ℂ) * φ c0 z' := by
  classical
  constructor
  · rintro ⟨g, hg, rfl⟩ c0
    exact ⟨(Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (y c0) (Set.mem_univ _),
      fun γ hγ κ e z z' hz => (Submodule.mem_inf.1 hg).1 γ hγ (y c0) (y c0) κ e z z' hz⟩
  intro hφ
  have hU : ∀ κ : S.U, (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    fun κ => ((S.U_eq _).1 κ.2).1
  have dec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ (c0 : c) (γ : UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 * (y c0).1 * κ.1 := by
    intro x
    obtain ⟨c0, hc0⟩ := hy.2 (Quotient.mk'' x)
    obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq _ _ (y c0) x).1 hc0
    have hh' : (h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈
        (UJ (σ : E →+* E) J).map (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) := Subgroup.mem_subgroupOf.1 hh
    have hk' : (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := Subgroup.mem_subgroupOf.1 hk
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 hh'
    refine ⟨c0, ⟨γ, hγ⟩, ⟨_, hk'⟩, ?_⟩
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]

  have uniq : ∀ (c1 c2 : c) (γ1 γ2 : UJ (σ : E →+* E) J) (κ1 κ2 : S.U),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1.1 * (y c1).1 * κ1.1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1 * (y c2).1 * κ2.1 →
      ∀ z1 z2 : Frames (gramC J emb), (∀ τ, atInf emb γ1.1.1 τ * z1.1 τ = atInf emb γ2.1.1 τ * z2.1 τ) →
        (S.chi κ1 : ℂ) * φ c1 z1 = (S.chi κ2 : ℂ) * φ c2 z2 := by
    intro c1 c2 γ1 γ2 κ1 κ2 e z1 z2 hz
    have hr : (y c2).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1).1 * (y c1).1 * (κ1 * κ2⁻¹).1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (y c2).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1)⁻¹ *
              (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1 * (y c2).1 * κ2.1) * (κ2.1)⁻¹ := by group
        _ = _ := by rw [← e]; group
    have hc : c1 = c2 := by
      let kk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨(κ1 * κ2⁻¹).1, hU _⟩
      let r : UPts σ J (FiniteAdeleRing (𝓞 F) F) := y c2 * kk⁻¹ * (y c1)⁻¹
      have hrR : r ∈ (ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_map.2 ⟨(γ2⁻¹ * γ1).1, (γ2⁻¹ * γ1).2, ?_⟩
        show _ = (y c2).1 * ((κ1 * κ2⁻¹).1)⁻¹ * ((y c1).1)⁻¹
        rw [hr]
        group
      have hkK : kk ∈ S.U.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
        rw [Subgroup.mem_subgroupOf]
        exact (κ1 * κ2⁻¹).2
      refine hy.1 (show (Quotient.mk'' (y c1) : Cls S) = Quotient.mk'' (y c2) from
        (DoubleCoset.eq _ _ (y c1) (y c2)).2 ⟨r, hrR, kk, hkK, ?_⟩)
      simp only [r]
      group
    subst hc
    have h := (hφ c1).2 (γ2⁻¹ * γ1).1 (γ2⁻¹ * γ1).2 (κ1 * κ2⁻¹) hr z2 z1 (fun τ => by
      have h1 : γ2.1.1 * (γ2⁻¹ * γ1).1.1 = γ1.1.1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
      have h2 := congrFun (atInf_mul emb γ2.1.1 (γ2⁻¹ * γ1).1.1) τ
      rw [h1, Pi.mul_apply] at h2
      have h3 := hz τ
      rw [h2, Matrix.mul_assoc] at h3
      exact (((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_atInf emb γ2.1 τ)).mul_left_cancel h3).symm)
    rw [h, ← mul_assoc, ← Units.val_mul, map_mul, map_inv, mul_comm (S.chi κ1), mul_inv_cancel_left]
  choose cc gam kap hdec using dec
  have htr : ∀ (γ : GL (Fin n) E) (z : Frames (gramC J emb)) τ,
      atInf emb γ.1 τ * (mulFr (atInf emb (γ⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z).1 τ = z.1 τ := by
    intro γ z τ
    have h2 := congrFun (atInf_mul emb γ.1 (γ⁻¹ : GL (Fin n) E).1) τ
    rw [Pi.mul_apply] at h2
    rw [mulFr_val, ← Matrix.mul_assoc, ← h2, Units.mul_inv]
    simp [atInf]
  let gf : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x z =>
    ((S.chi (kap x) : ℂˣ) : ℂ) * φ (cc x)
      (mulFr (atInf emb (((gam x).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z)
  have hAd : gf ∈ AdFun S emb := by
    intro γ hγ x x' κ hx z z' hz
    have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gam x').1 * (y (cc x')).1 * (kap x').1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) ((⟨γ, hγ⟩ : UJ (σ : E →+* E) J) * gam x).1 *
        (y (cc x)).1 * (kap x * κ).1 := by
      rw [← hdec x', hx, hdec x]
      simp only [Subgroup.coe_mul, map_mul, mul_assoc]
    refine (uniq _ _ _ _ _ _ e _
      (mulFr (atInf emb (((gam x).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z') fun τ => ?_).trans ?_
    · rw [htr, hz τ, Subgroup.coe_mul, Units.val_mul, atInf_mul, Pi.mul_apply, Matrix.mul_assoc, htr]
    · simp only [gf, map_mul, Units.val_mul]
      ring
  have hpi : ∀ x, gf x ∈ ValC (gramC J emb) lam := fun x =>
    Submodule.smul_mem _ ((S.chi (kap x) : ℂˣ) : ℂ) (valC_tr _ lam _ (isUnit_atInf emb _) (hφ (cc x)).1)
  refine Submodule.mem_map.2 ⟨gf, Submodule.mem_inf.2 ⟨hAd, Submodule.mem_pi.2 fun x _ => hpi x⟩, ?_⟩
  funext c0 z
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gam (y c0)).1 * (y (cc (y c0))).1 * (kap (y c0)).1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (1 : UJ (σ : E →+* E) J).1 * (y c0).1 * (1 : S.U).1 := by
    rw [← hdec (y c0)]
    simp
  refine (uniq _ _ _ _ _ _ e _ z fun τ => ?_).trans (by simp)
  rw [htr]
  simp [atInf]

end Adelic

section Step

open Formalism.L2.Col Formalism.L2.DIV

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem exists_embF_iff (h : (S.fam emb lam).Ok) (φ : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ) :
    (∃ x, S.embF emb σ lam h x = φ) ↔ φ ∈ S.Fi emb σ lam ∧ ∀ c, ∃ P ∈ RatPol σ lam, φ c = fnOf _ (shiftOf lam) 1 P := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Law.embF_mem S emb σ lam h x, fun c => ⟨_, map_mem_RatPol σ lam (x.1 c).2, rfl⟩⟩
  · rintro ⟨hφ, hv⟩
    have hv' : ∀ c, ∃ v : VV K lam, φ c = evV emb 1 lam σ v := fun c => by
      obtain ⟨P, hP, e⟩ := hv c
      obtain ⟨F, hF, rfl⟩ := exists_VV_of_mem_RatPol σ lam hP
      exact ⟨⟨F, hF⟩, e⟩
    choose v hv using hv'
    refine ⟨⟨v, fun c g => ?_⟩, funext fun c => (hv c).symm⟩
    have e : evV emb 1 lam σ (S.rho emb lam c.1 g.1 (v c)) = evV emb 1 lam σ (v c) := by
      rw [Law.evV_rho, ← hv c]
      exact (hφ c).2 g
    exact Subtype.ext (evFr_injective _ _ σ (stdFrC _) e)

variable {F : Type} [Field F] [NumberField F] [Algebra F E] {sg : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
  {bad : Set (HeightOneSpectrum (𝓞 F))}

omit [StarRing E] [NumberField K] [StarRing K] in

theorem stab_inv_iff (c : S.Cl) (lev : StepLevel F E sg J T f bad) {e : ι → E →+* ℂ} (he : e = embAt σ emb)
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (st : S.Stab c → UJ (sg : E →+* E) J)
    (hst : ∀ s, (st s).1 = S.gam c.1 s.1)
    (hr : ∀ γ : UJ (sg : E →+* E) J, (∃ s, st s = γ) ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj y).toMonoidHom)
    (hchi : ∀ (s : S.Stab c) (κ : lev.U), y = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (S.gam c.1 s.1) * y * κ.1 →
      (lev.chi κ : ℂ) = σ (S.chr c.1 s.1 : Kˣ))
    (v : GlobalTheory.Mem.Col2.Fr emb σ n → ℂ) (p : Frames (gramC J e) → GlobalTheory.Mem.Col2.Fr emb σ n) (hp : ∀ z, (p z).1 = z.1) :
    (∀ g : S.Stab c, S.tr emb σ c.1 g.1 v = v) ↔ ∀ γ ∈ UJ (sg : E →+* E) J, ∀ κ : lev.U,
      y = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y * κ.1 →
      ∀ z z' : Frames (gramC J e), IsTr (atInf e γ) z' z → v (p z) = (lev.chi κ : ℂ) * v (p z') := by
  subst he
  constructor
  · intro h γ hγ κ hy z z' hz
    obtain ⟨s, hs⟩ := (hr ⟨γ, hγ⟩).2 (Subgroup.mem_map.2 ⟨κ.1⁻¹, inv_mem κ.2, by
      show y * κ.1⁻¹ * y⁻¹ = bc _ γ
      rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
      exact hy⟩)
    obtain rfl : γ = S.gam c.1 s.1 := (congrArg Subtype.val hs).symm.trans (hst s)
    have e1 : p z = frMul emb σ (S.gam c.1 s.1) (p z') := Subtype.ext (funext fun τ => by
      rw [hp, hz τ, ← hp z']
      rfl)
    rw [hchi s κ hy, ← congrFun (h s) (p z), GStep.tr, trFr_apply, e1, ← frMul_mul, inv_mul_cancel, frMul_one]
  · intro h s
    obtain ⟨κ, hκ, hy⟩ := Subgroup.mem_map.1 ((hr (st s)).1 ⟨s, rfl⟩)
    have hy' : y = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (S.gam c.1 s.1) * y * (⟨κ, hκ⟩⁻¹ : lev.U).1 := by
      rw [← hst, ← hy]
      show y = y * κ * y⁻¹ * y * κ⁻¹
      group
    funext z
    have hpz : ∀ z : GlobalTheory.Mem.Col2.Fr emb σ n, p ⟨z.1, z.2⟩ = z := fun z => Subtype.ext (hp _)
    have h1 := h _ (hst s ▸ (st s).2) _ hy' ⟨z.1, z.2⟩
      ⟨(frMul emb σ (S.gam c.1 s.1)⁻¹ z).1, (frMul emb σ (S.gam c.1 s.1)⁻¹ z).2⟩ (fun τ => by
        have h2 : frMul emb σ (S.gam c.1 s.1) (frMul emb σ (S.gam c.1 s.1)⁻¹ z) = z := by
          rw [← frMul_mul, mul_inv_cancel, frMul_one]
        exact (congrFun (congrArg Subtype.val h2) τ).symm)
    rw [hpz, hpz, hchi s _ hy'] at h1
    rw [GStep.tr, trFr_apply, ← h1]

theorem mem_valC_comp {G G' : ι → Matrix (Fin n) (Fin n) ℂ} {l l' : ι → DomWeight n} (hl : l' = l) (v : Frames G → ℂ)
    (p : Frames G' → Frames G) (hp : ∀ z, (p z).1 = z.1) : (fun z => v (p z)) ∈ ValC G' l' ↔ v ∈ ValC G l := by
  subst hl
  have e : (fun z => v (p z)) = fun z : Frames G' => v ⟨z.1, z.2⟩ := funext fun z => congrArg v (Subtype.ext (hp z))
  rw [e]
  exact Iff.rfl

theorem dualSet_std (s : E →+* E) (hs : ∀ x, s x = star x) (L : Submodule (𝓞 E) (Sp E n)) :
    dualSet s (1 : Matrix (Fin n) (Fin n) E) L = (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set (Sp E n)) := by
  ext y
  rw [SetLike.mem_coe, mem_dual]
  refine forall₂_congr fun x _ => ?_
  have : Formalism.UG.hform s (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
    simp [Formalism.UG.hform, hStd_apply, Matrix.one_apply, hs]
  rw [this, Submodule.mem_one]
  rfl

end Step

section Lev

open Formalism.L2.Col

variable {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem lev_part_smul (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (s : FrmG Λ Θ) (p : DecoF X.E n ST SG Q)
    (h : FrmG.incl Λ Θ s • p = p) :
    FrmG.incl Λ Θ (1, s.2) • p = ((s.1⁻¹, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p := by
  have e : FrmG.incl Λ Θ (1, s.2) = ((s.1⁻¹, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) * FrmG.incl Λ Θ s :=
    Prod.ext (inv_mul_cancel s.1).symm (one_mul _).symm
  rw [e, mul_smul, h]

end Lev

end GlobalTheory.Mem.Col2.ValTie

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

set_option maxHeartbeats 2000000 in

theorem val_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → ValuationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY (fun _ => True) chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY hK hY
  obtain ⟨k, hR⟩ := hK
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL := (hc u a).1
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u a) i = GlobalTheory.Mem.Col2.lamT (B.hcW u) i := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) i) ((i * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) i) (-((i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : i * (B.R.t + 1) / 2 = i * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hYs : ∀ z, (eY.symm z).1 = z.1 := fun z => (hY (eY.symm z)).symm.trans (congrArg Subtype.val (eY.apply_symm_apply z))
  refine ⟨fun φ => ?_, fun φ => ?_, fun w _ x => ?_⟩
  · have hchi : ∀ (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U),
        (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1 →
        ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
      intro c s κ hy
      have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
      have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
      have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
      have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
      have h4 : ratAd B.host.F (s.1.1⁻¹ : UF B.host.E (B.R.N i)) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1))⁻¹ := by
        rw [ratAd, map_inv, map_inv]
        rfl
      rw [h4, h3 _ _ _ _ hy, ← h2] at h1
      exact hR.chr c κ (1, s.1.2) (map_one (ufGL B.fields.E (B.R.N i))) h1
    have key : ∀ c : (I.stp u a i).Cl,
        (φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ∧
          ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c) ↔ _ := fun c =>
      and_congr (mem_valC_comp (G' := gramC (gramN (I.rec7 l Z) i hi) (Formalism.L2.Forms.embT (I.rec7 l Z))) hlam (φ c) eY.symm hYs).symm
        (stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) i hi) (I.stp u a i) B.fields.emb B.embLL c
          (K (chOf c)).lev hemb ((K (chOf c)).y ⟨c, rfl⟩).1
          ((K (chOf c)).stabI ⟨c, rfl⟩) (hR.stab c) ((K (chOf c)).stabI_range ⟨c, rfl⟩) (hchi c) (φ c) eY.symm hYs)
    constructor
    · intro h β
      refine (mem_fiC_iff _ _ _ _ (K β).y_bij _).2 ?_
      rintro ⟨c, rfl⟩
      exact (key c).1 (h c)
    · intro h c
      exact (key c).2 ((mem_fiC_iff _ _ _ _ (K (chOf c)).y_bij _).1 (h (chOf c)) ⟨c, rfl⟩)
  · have hrat : RatPol B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) = RatSpan (I.rec7 l Z) ((I.fm l u a).lam i) := by
      rw [← hlam]
      exact RatPol_shW B.embLL ((I.fm l u a).lam i) fun _ => ((i * (B.R.t + 1) / 2 : ℕ) : ℤ)
    refine (exists_embF_iff (I.stp u a i) B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ((l.fmL u a).fam i) φ).trans
      (and_congr_right fun _ => forall_congr' fun c => ?_)
    rw [hrat]
    refine exists_congr fun P => and_congr_right fun _ => funext_iff.trans (forall_congr' fun z => ?_)
    exact Eq.congr_right (fnOf_eq (congrArg shiftOf hlam.symm) (fun _ => rfl) _ _ _ (hY z).symm)
  · change HeightOneSpectrum (𝓞 B.fields.K) at w
    have hp := (I.rec7 l Z).what₂.places.resChar_prime w
    have hd : ∀ c, dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)
        (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = SetLike.coe ((I.stp u a i).rep c).1.1.deco.1.Lsh := by
      intro c
      have h1 := dualSet_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
      exact (congrArg₂ (dualSet _) hG (hL c)).trans h1
    have hint : ∀ P, P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u a).lam i) ↔
        ∃ z₀ ∈ localization₂ w.asIdeal (delStd B.LL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i)), P = MvPolynomial.map B.embLL z₀ := by
      intro P
      have h := mem_closure_iff (I.rec7 l Z).what₂.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
        ((I.rec7 l Z).val_nonneg_iff w) (lamTG (D := I.rec7 l Z) (I.fm l u a) i) P
      simp only [lamTG, delSq_shW] at h
      rw [← hlam]
      exact h
    have hfin : Finite (I.stp u a i).Cl := by
      have := ((l.ch u a).step i).fin_orb
      exact Finite.instSigma
    have h1 : x ∈ (I.fm l u a).S i w ↔ ∀ c, x.1 c ∈ localization₂ w.asIdeal
        (delAtr B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ((I.stp u a i).rep c).1.1.deco.1.Lsh) :=
      ((I.rec7 l Z).mem_locW_iff w _ x).trans
        (mem_localization_latticeOf (I.stp u a i) B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ((l.fmL u a).fam i) _ w x)
    refine h1.trans (forall_congr' fun c => ?_)
    have l1 := ((I.stp u a i).rep c).1.1.deco.2.Lsh_lattice
    have hbel : ∀ τ, (((I.rec7 l Z).what₂.places.resChar w : ℕ) : 𝓞 B.fields.E) ∈ (bcBelow (B.fields.emb τ) w).asIdeal := fun τ => by
      show bcO (B.fields.emb τ) _ ∈ w.asIdeal
      rw [map_natCast]
      exact GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w
    have key : ∀ Bm : GL (Fin (B.R.N i)) B.host.E,
        Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set _) Bm →
        (x.1 c ∈ localization₂ w.asIdeal
          (delAtr B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ((I.stp u a i).rep c).1.1.deco.1.Lsh) ↔
        ∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u a).lam i), ∀ z, (I.fm l u a).emb i x c z =
          fnOf _ (shiftOf (lamTG (D := I.rec7 l Z) (I.fm l u a) i))
            (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin (B.R.N i)) B.host.E).1) P (eY z)) := by
      intro Bm hB
      refine (mem_localization_delAtr_fn B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) w l1 (fun _ => Bm)
        (fun τ => isBasisAt_of_isLocBasis hp _ (hbel τ) hB) (x.1 c)).trans ?_
      constructor
      · rintro ⟨z, hz, e⟩
        refine ⟨_, (hint _).2 ⟨z, hz, rfl⟩, fun y => (congrFun e y).trans ?_⟩
        exact fnOf_eq (congrArg shiftOf hlam.symm) (fun τ => congrArg (fun e => atInf e _ τ) hemb.symm) _ _ _ (hY y).symm
      · rintro ⟨P, hP, e⟩
        obtain ⟨z, hz, rfl⟩ := (hint P).1 hP
        refine ⟨z, hz, funext fun y => (e y).trans ?_⟩
        exact fnOf_eq (congrArg shiftOf hlam) (fun τ => congrArg (fun e => atInf e _ τ) hemb) _ _ _ (hY y)
    constructor
    · intro h Bm hB
      rw [hd c] at hB
      exact (key Bm hB).1 h
    · intro h
      have : Fact ((I.rec7 l Z).what₂.places.resChar w).Prime := ⟨hp⟩
      obtain ⟨Bm, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) B.host.E _ l1.fg l1.span_eq_top
      exact (key Bm hB).2 (h Bm (by rw [hd c]; exact hB))

end GlobalTheory.Mem.Col2.TC

end
