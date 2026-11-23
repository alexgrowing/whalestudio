import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_swap {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem form_add {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x v w : Fin n → E) :
    form σ J x (v + w) = form σ J x v + form σ J x w := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem form_smul {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x v : Fin n → E) (s : E) :
    form σ J x (s • v) = σ s * form σ J x v := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gram_col {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x) (c : E) (x v : Fin n → E)
    (i : Fin 1) :
    ((Formalism.UG.cT (σ : E →+* E) (Matrix.of fun k (_ : Fin 1) => x k) * (c • J.map σ)) *ᵥ v) i =
      c * σ (form σ J x v) := by
  simp only [Formalism.UG.cT, form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [RingHom.coe_coe]
  ring

end GlobalTheory.UnipCocompact

namespace GlobalTheory.UnipCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_decomp {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁} {i₀ i₁ : ℕ}
    (hL : Y.L.IsLattice E) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (v : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  let S : Submodule E (Fin n → E) :=
    { carrier := {v | ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y}
      add_mem' := by
        rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
        exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add, add_smul, add_smul]; abel⟩
      zero_mem' := ⟨0, 0, 0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨s, t, u, rfl⟩
        exact ⟨r * s, r * t, r • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]⟩ }
  have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ S := Submodule.span_le.2 fun z hz => by
    obtain ⟨s, t, u, -, -, -, e⟩ := hH.split z hz
    exact ⟨s, t, u, e⟩
  rw [hL.span_eq_top] at hle
  exact hle (Submodule.mem_top (x := v))

end GlobalTheory.UnipCocompact

namespace GlobalTheory.UnipCocompact

open GlobalTheory.ThK.SquareIntegrability in

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → GlobalTheory.Cusp.Cocompact (ratU σ G.W.J) (unip σ G.W H') := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c, hc0, hcσ⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hW := hT.geo.hW
  have hσinj : Function.Injective σ := fun p q h => by rw [← hσ p, ← hσ q, h]
  set J := G.W.J with hJdef
  set C : Matrix (Fin (a + a')) (Fin 1) E := Matrix.of fun k _ => H'.x k with hCdef
  have hJ' : IsHermND σ (c • J.map σ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hcσ]
      rw [show σ (J i j) = -J j i from hW.skew j i]; ring
    · rw [Matrix.det_smul]
      refine mul_ne_zero (pow_ne_zero _ hc0) ?_
      have := (RingHom.map_det (σ : E →+* E) J).symm
      rw [show J.map σ = (σ : E →+* E).mapMatrix J from rfl, this]
      exact (map_ne_zero _).2 (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B _ _ _ G.W hW)
  have hxy := hH.xy
  have hx0 : H'.x ≠ 0 := fun h => by
    rw [h] at hxy; simp [form] at hxy
  have hperp : ∀ v, (Formalism.UG.cT (σ : E →+* E) C * (c • J.map σ)) *ᵥ v = 0 ↔ form σ J H'.x v = 0 := fun v => by
    constructor
    · intro h
      have := congrFun h 0
      rw [gram_col J hσ c H'.x v 0] at this
      exact hσinj ((mul_eq_zero.1 this).resolve_left hc0 |>.trans (map_zero σ).symm)
    · intro h; funext i; rw [gram_col J hσ c H'.x v i, h, map_zero, mul_zero]; rfl
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • J.map σ) C := by
    refine ⟨?_, ?_⟩
    · exact linearIndependent_unique_iff.2 (fun h => hx0 (funext fun k => congrFun h k))
    · ext i j
      have := congrFun ((hperp H'.x).2 hH.xx) i
      rw [Matrix.mul_apply, Matrix.zero_apply]
      simp only [Matrix.mulVec, dotProduct] at this
      simpa only [hCdef, Matrix.of_apply, Pi.zero_apply] using this

  have hLat : G.W.L.IsLattice E := hW.lat
  have hxι : ∀ u, form σ J H'.x (H'.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap hσ hW.skew, (hH.orth u).1, map_zero, neg_zero]
  have hincV : ∀ (s : E) (u : Fin d₁ → E), (fun k => inclR (F := F) (AF F) ((s • H'.x + H'.ι *ᵥ u) k)) =
      inclR (F := F) (AF F) s • incV F H'.x + incM F H'.ι *ᵥ incV F u := fun s u => by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, incV, incM, Matrix.mulVec, dotProduct,
      map_sum, Matrix.map_apply]
  set e := toGAd hσ J hc0 with he
  have hfwd : ∀ u ∈ unip σ G.W H', e u ∈ GlobalTheory.UAut.unipFlag σ (c • J.map σ) C (fun _ => 0) := by
    intro u hu
    rw [GlobalTheory.UnipCT.unip_eq] at hu
    obtain ⟨hu1, hu2⟩ := hu
    refine Subgroup.subset_closure ⟨fun i => ⟨0, fun _ _ => rfl, ?_⟩, fun v hv => ?_⟩
    · rw [Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
      exact hu1
    · have hv0 := (hperp v).1 hv
      obtain ⟨s, t, w, rfl⟩ := exists_decomp hLat hH v
      have ht : t = 0 := by
        rw [form_add, form_add, form_smul, form_smul, hH.xx, hxι, hH.xy] at hv0
        simpa using hv0
      subst ht
      rw [zero_smul, add_zero] at *
      obtain ⟨b, hb⟩ := hu2 (incV F w)
      refine ⟨fun _ => b, ?_⟩
      rw [hincV]
      have hm : (((matHom (AF F) σ (c • J.map σ)) (e u) : GL (Fin (a + a')) (AF F ⊗[F] E)) :
          Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) = mat u := rfl
      rw [hm, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hu1, hb]
      funext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, SiegelSet.adMat, Matrix.mulVec, dotProduct,
        Matrix.map_apply, hCdef, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, incV]
      ring

  have hcol : ∀ j : Fin d₁, (Formalism.UG.cT (σ : E →+* E) C * (c • J.map σ)) *ᵥ (fun i => H'.ι i j) = 0 := fun j => by
    rw [hperp]
    have := hxι (Pi.single j 1)
    rwa [Matrix.mulVec_single_one] at this
  have hbwd : ∀ g ∈ GlobalTheory.UAut.unipFlag σ (c • J.map σ) C (fun _ => 0), e.symm g ∈ unip σ G.W H' := by
    have hle : GlobalTheory.UAut.unipFlag σ (c • J.map σ) C (fun _ => 0) ≤ (unip σ G.W H').comap e.symm.toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      obtain ⟨h1, h2⟩ := hg
      have hm : mat (e.symm g) = (((matHom (AF F) σ (c • J.map σ)) g : GL (Fin (a + a')) (AF F ⊗[F] E)) :
          Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) := rfl
      rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.UnipCT.unip_eq]
      obtain ⟨a₀, ha₀, e₀⟩ := h1 0
      have ha0 : a₀ = 0 := funext fun j => ha₀ j le_rfl
      subst ha0
      rw [Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e₀
      choose A hA using fun j => h2 _ (hcol j)
      refine ⟨?_, fun z => ⟨∑ j, z j * A j 0, ?_⟩⟩
      · show mat (e.symm g) *ᵥ incV F H'.x = incV F H'.x
        rw [hm]; exact e₀
      · show mat (e.symm g) *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + (∑ j, z j * A j 0) • incV F H'.x
        have hM : ((((matHom (AF F) σ (c • J.map σ)) g : GL (Fin (a + a')) (AF F ⊗[F] E)) :
            Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) - 1) * incM F H'.ι =
            Matrix.of fun i j => inclR (F := F) (AF F) (H'.x i) * A j 0 := by
          ext i j
          have := congrFun (hA j) i
          simp only [SiegelSet.adMat, Matrix.mulVec, dotProduct, Matrix.map_apply, hCdef, Matrix.of_apply,
            Finset.univ_unique, Finset.sum_singleton] at this
          rw [Matrix.mul_apply, Matrix.of_apply]
          exact this
        rw [hm, ← sub_eq_iff_eq_add']
        rw [show ∀ (P : Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) (v : Fin (a + a') → AF F ⊗[F] E),
          P *ᵥ v - v = (P - 1) *ᵥ v from fun P v => by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
        rw [Matrix.mulVec_mulVec, hM]
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, incV, Finset.sum_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    exact fun g hg => hle hg
  obtain ⟨K', hK', hKs⟩ := GlobalTheory.UAut.cocompact_unipFlag hJ' hσ hC (fun _ => 0)
  have hcont : Continuous e.symm := continuous_induced_rng.2 continuous_subtype_val
  let f : GlobalTheory.UAut.unipFlag σ (c • J.map σ) C (fun _ => 0) → unip σ G.W H' := fun g => ⟨e.symm g, hbwd g g.2⟩
  have hf : Continuous f := (hcont.comp continuous_subtype_val).subtype_mk _
  refine ⟨f '' K', hK'.image hf, fun n => ?_⟩
  let m : GlobalTheory.UAut.unipFlag σ (c • J.map σ) C (fun _ => 0) := ⟨e n, hfwd n n.2⟩
  obtain ⟨γ, hγ, hγK⟩ := hKs m
  refine ⟨f γ, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    obtain ⟨w, -, hw⟩ := Subgroup.mem_subgroupOf.1 hγ
    exact ⟨w, hw⟩
  · refine ⟨γ * m, hγK, ?_⟩
    apply Subtype.ext
    show e.symm (γ.1 * e n) = e.symm γ.1 * n.1
    rw [map_mul, MulEquiv.symm_apply_apply]

end GlobalTheory.UnipCocompact
