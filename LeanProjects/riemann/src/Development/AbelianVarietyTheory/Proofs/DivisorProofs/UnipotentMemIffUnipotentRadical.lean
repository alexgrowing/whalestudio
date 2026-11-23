import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.UnipMem

open GlobalTheory.LeviPlane Formalism.UG

theorem row_mulVec {R : Type} [CommRing R] {s : R →+* R} (hs : ∀ x, s (s x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) R)
    (a : R) (x v : Fin n → R) (k : Fin 1) :
    ((cT s (Matrix.of fun i (_ : Fin 1) => x i) * (a • J.map s)) *ᵥ v) k = a * s (fm s J x v) := by
  simp only [fm, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hs, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem fm_mulVec {R : Type} [CommRing R] {s : R →+* R} {n : ℕ} {J g : Matrix (Fin n) (Fin n) R}
    (hg : gᵀ * J * g.map s = J) (u v : Fin n → R) : fm s J (g *ᵥ u) (g *ᵥ v) = fm s J u v := by
  have e : (fun i => s ((g *ᵥ v) i)) = g.map s *ᵥ fun i => s (v i) := funext fun i => RingHom.map_mulVec s g v i
  conv_rhs => rw [← hg]
  simp only [fm, e, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (u : Fin n → E) :
    incV F (M *ᵥ u) = incM F M *ᵥ incV F u :=
  funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) M u i

theorem exists_split {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) {d₁ : ℕ}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → E) :
    ∃ (a t : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + t • H'.y := by
  have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
    rw [hW.lat.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨a, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, t, u, rfl⟩ := hp
    obtain ⟨a', t', u', rfl⟩ := hq
    exact ⟨a + a', t + t', u + u', by rw [Matrix.mulVec_add, add_smul, add_smul]; abel⟩
  | smul b p _ hp =>
    obtain ⟨a, t, u, rfl⟩ := hp
    exact ⟨b * a, b * t, b • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]⟩

theorem gen_iff {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s)
    (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {d₁ : ℕ}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (u : UA σ W.J) :
    (mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) ↔
    ((mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ∧
      adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) * (mat u - 1) = 0 ∧
      ∀ x : Fin d → E, (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ x = 0 →
        ∃ a : Fin 1 → AE F E, (mat u - 1) *ᵥ incV F x = adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a) := by
  have hcol : ∀ a : Fin 1 → AE F E, adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a = a 0 • incV F H'.x := fun a => by
    funext i; simp [Matrix.mulVec, dotProduct, incV, mul_comm]
  have h1 : (mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ↔ mat u *ᵥ incV F H'.x = incV F H'.x := by
    rw [← sub_eq_zero (a := mat u *ᵥ _), show mat u *ᵥ incV F H'.x - incV F H'.x = (mat u - 1) *ᵥ incV F H'.x by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    exact ⟨fun h => funext fun i => congrFun (congrFun h i) 0, fun h => Matrix.ext fun i _ => congrFun h i⟩
  have hrow : ∀ (v : Fin d → E) k, ((cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ v) k =
      c * σ (fm (σ : E →+* E) W.J H'.x v) := fun v k => row_mulVec (s := (σ : E →+* E)) hσ W.J c H'.x v k
  have hxι : ∀ w, fm (σ : E →+* E) W.J H'.x (H'.ι *ᵥ w) = 0 := fun w => by
    rw [fm_skew (σ : E →+* E) hσ W.J hW.skew, show fm (σ : E →+* E) W.J (H'.ι *ᵥ w) H'.x = 0 from (hH.orth w).1, map_zero,
      neg_zero]
  rw [h1]
  refine and_congr_right fun hx => ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h z => ?_⟩
  · have e : adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) =
        cT (cA σ).toRingHom (Matrix.of fun i (_ : Fin 1) => incV F H'.x i) *
          (inclR (F := F) (AF F) c • (incM F W.J).map (cA σ).toRingHom) := by
      ext k j
      simp only [adMat, cT, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, incV, incM, cAr_inclR, RingHom.coe_coe]
    have hu : (mat u)ᵀ * incM F W.J * (mat u).map (cA σ).toRingHom = incM F W.J := u.2
    rw [e]
    refine Matrix.ext_of_mulVec_single fun j => funext fun k => ?_
    rw [← Matrix.mulVec_mulVec, row_mulVec (cA_invol hσ), Matrix.sub_mulVec, Matrix.one_mulVec, fm_sub_right]
    conv_lhs => enter [2, 2, 1]; rw [← hx, fm_mulVec hu]
    simp
  · obtain ⟨a, t, w, rfl⟩ := exists_split hW hH v
    have ht := congrFun hv 0
    rw [hrow, fm_add_right, fm_add_right, fm_smul_right, fm_smul_right, hxι,
      show fm (σ : E →+* E) W.J H'.x H'.x = 0 from hH.xx, show fm (σ : E →+* E) W.J H'.x H'.y = 1 from hH.xy] at ht
    have ht0 : t = 0 := by simpa [hc] using ht
    obtain ⟨b, hb⟩ := h (incV F w)
    refine ⟨fun _ => b, ?_⟩
    have e : incV F (a • H'.x + H'.ι *ᵥ w + t • H'.y) = inclR (F := F) (AF F) a • incV F H'.x + incM F H'.ι *ᵥ incV F w := by
      rw [ht0, zero_smul, add_zero, ← incV_mulVec]; funext i; simp [incV]
    rw [hcol, e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hx, hb]
    abel
  · have h3 : ∀ j : Fin d₁, ∃ a : AE F E, (mat u - 1) *ᵥ (incM F H'.ι *ᵥ Pi.single j 1) = a • incV F H'.x := fun j => by
      obtain ⟨a, ha⟩ := h.2 (H'.ι *ᵥ Pi.single j 1) (funext fun k => by rw [hrow, hxι]; simp)
      refine ⟨a 0, ?_⟩
      rw [← hcol, ← ha, incV_mulVec]
      congr 2
      funext i; by_cases hij : i = j <;> simp [incV, Pi.single_apply, hij]
    choose a ha using h3
    refine ⟨∑ j, z j * a j, ?_⟩
    rw [← sub_eq_iff_eq_add', show mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z = (mat u - 1) *ᵥ (incM F H'.ι *ᵥ z) by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    conv_lhs => rw [show z = ∑ j, z j • Pi.single j 1 from by funext i; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ha, smul_smul, Finset.sum_smul]

end GlobalTheory.UnipMem

theorem GlobalTheory.UnipMem.mem_unip_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ g : UA σ W.J, g ∈ unip σ W H' ↔ toGAd hσ W.J hc g ∈ unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  intro F E _ _ _ _ _ σ B d r s W hW hσ c hc _ d₁ W₁ H' i₀ i₁ hH g
  have e : (unip σ W H').map (toGAd hσ W.J hc).toMonoidHom =
      unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
    rw [unip, MonoidHom.map_closure, unipRad]
    congr 1
    ext k
    obtain ⟨u, rfl⟩ := (toGAd hσ W.J hc).surjective k
    refine ((toGAd hσ W.J hc).injective.mem_set_image).trans ?_
    exact GlobalTheory.UnipMem.gen_iff hW hσ hc hH u
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (f := (toGAd hσ W.J hc).toMonoidHom) (toGAd hσ W.J hc).injective).symm
