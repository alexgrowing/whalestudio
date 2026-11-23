import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipRat

open Matrix GlobalTheory.LeviLine

variable {R : Type} [CommRing R] {n : ℕ}

def eich (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (x w : Fin n → R) (k : R) : Matrix (Fin n) (Fin n) R :=
  1 - vecMulVec x (J *ᵥ fun i => c (w i)) - vecMulVec w (J *ᵥ fun i => c (x i)) - k • vecMulVec x (J *ᵥ fun i => c (x i))

variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

theorem eich_mulVec (x w : Fin n → R) (k : R) (z : Fin n → R) :
    eich c J x w k *ᵥ z = z - sf c J z w • x - sf c J z x • w - (k * sf c J z x) • x := by
  simp only [eich, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul, sf, dotProduct_comm z]

theorem sf_neg_right (u v : Fin n → R) : sf c J u (-v) = -sf c J u v := by
  rw [show -v = (-1 : R) • v by simp, sf_smul_right, map_neg, map_one, neg_one_mul]

theorem sf_neg_left (u v : Fin n → R) : sf c J (-u) v = -sf c J u v := by
  rw [show -u = (-1 : R) • u by simp, sf_smul_left, neg_one_mul]

variable {c J}

theorem eich_neg_mul {x w : Fin n → R} {k : R} (hxx : sf c J x x = 0) (hxw : sf c J x w = 0) (hwx : sf c J w x = 0)
    (hk : 2 * k + sf c J w w = 0) (w' : Fin n → R) (hw' : w' = -w) :
    eich c J x w' k * eich c J x w k = 1 := by
  subst hw'
  refine ext_mulVec fun u => ?_
  rw [← mulVec_mulVec, eich_mulVec, eich_mulVec, one_mulVec]
  simp only [sf_sub_left, sf_smul_left, sf_neg_right, hxx, hxw, hwx]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (-(sf c J u x * x i)) * hk

theorem eich_mul_neg {x w : Fin n → R} {k : R} (hxx : sf c J x x = 0) (hxw : sf c J x w = 0) (hwx : sf c J w x = 0)
    (hk : 2 * k + sf c J w w = 0) (w' : Fin n → R) (hw' : w' = -w) :
    eich c J x w k * eich c J x w' k = 1 := by
  subst hw'
  refine ext_mulVec fun u => ?_
  rw [← mulVec_mulVec, eich_mulVec, eich_mulVec, one_mulVec]
  simp only [sf_sub_left, sf_smul_left, sf_neg_right, sf_neg_left, hxx, hxw, hwx]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (-(sf c J u x * x i)) * hk

theorem eich_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) {x w : Fin n → R} {k : R}
    (hxx : sf c J x x = 0) (hxw : sf c J x w = 0) (hk : k - c k + sf c J w w = 0) :
    (eich c J x w k)ᵀ * J * (eich c J x w k).map c = J := by
  have hwx : sf c J w x = 0 := by rw [sf_skew c J hc hJ, hxw, map_zero, neg_zero]
  refine ext_form fun u v => ?_
  set v' : Fin n → R := fun i => c (v i) with hv'
  have hv : v = fun i => c (v' i) := funext fun i => (hc (v i)).symm
  have key : (eich c J x w k).map c *ᵥ v = fun i => c ((eich c J x w k *ᵥ v') i) := by
    ext i
    rw [RingHom.map_mulVec, hv]
    rfl
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, key]
  change sf c J (eich c J x w k *ᵥ u) (eich c J x w k *ᵥ v') = u ⬝ᵥ J *ᵥ v
  rw [hv]
  change _ = sf c J u v'
  rw [eich_mulVec, eich_mulVec]
  simp only [sf_sub_left, sf_smul_left, sf_sub_right, sf_smul_right, map_mul, map_sub, hxx, hxw, hwx]
  rw [sf_skew c J hc hJ x v', sf_skew c J hc hJ w v']
  linear_combination (sf c J u x * c (sf c J v' x)) * hk

end GlobalTheory.ThK.UnipRat

namespace GlobalTheory.ThK.UnipRat

open Matrix GlobalTheory.LeviLine

variable {R : Type} [CommRing R] {n m : ℕ}

theorem sf_mulVec_mulVec (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) (u v : Fin m → R) :
    sf c J (A *ᵥ u) (A *ᵥ v) = sf c (Aᵀ * J * A.map c) u v := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := funext fun i => RingHom.map_mulVec _ _ _ _
  simp only [sf, h, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem vecMulVec_mulVec_rect (x : Fin n → R) (a z : Fin m → R) : vecMulVec x a *ᵥ z = (a ⬝ᵥ z) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.ThK.UnipRat

open Matrix GlobalTheory.LeviLine GlobalTheory.ThK.UnipRat GlobalTheory.ThK.UnipDom.Additive in

theorem GlobalTheory.ThK.UnipRat.exists_rat_unip_coA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ α : Fin n₁ → E, ∃ γ ∈ unip σ Y H, γ ∈ ratU σ Y.J ∧ coA σ Y.J H γ = fun j => inclR (F := F) (AF F) (α j) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H hcm hskew hP α
  obtain ⟨_, hxx, _, hxy, horth, hgram, _, hcart₁⟩ := hP
  set c : E →+* E := (σ : E →ₐ[F] E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := fun r => sigma_invol hcm r
  have hJ : ∀ i j, c (Y.J j i) = -Y.J i j := hskew
  have hsf : ∀ u v, sf c Y.J u v = form σ Y.J u v := fun _ _ => rfl

  have hdet : IsUnit Y₁.J.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    set τ : E →+* ℂ := (B.emb w).1
    have hx : (fun i => star (τ (v i))) ≠ 0 := by
      intro hx0
      apply hv0
      funext i
      have := congrFun hx0 i
      simpa using this
    have hpos := (hcart₁ w).2.2 _ hx
    have hz : (Complex.I • Y₁.J.map τ) *ᵥ star (fun i => star (τ (v i))) = 0 := by
      have hs : star (fun i => star (τ (v i))) = fun i => τ (v i) := funext fun i => by simp
      rw [hs, smul_mulVec]
      have : Y₁.J.map τ *ᵥ (fun i => τ (v i)) = fun i => τ ((Y₁.J *ᵥ v) i) :=
        funext fun i => (RingHom.map_mulVec _ _ _ _).symm
      rw [this, hv]
      funext i
      simp
    rw [hz, dotProduct_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

  set b' : Fin n₁ → E := Y₁.J⁻¹ *ᵥ (-α) with hb'def
  have hb' : Y₁.J *ᵥ b' = -α := by
    rw [hb'def, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  set b : Fin n₁ → E := fun i => σ (b' i) with hbdef
  have hσb : (fun i => c (b i)) = b' := funext fun i => hc (b' i)
  set w : Fin n → E := H.ι *ᵥ b with hwdef
  set k : E := -(sf c Y.J w w) / 2 with hkdef
  have hwx : sf c Y.J w H.x = 0 := (horth b).1
  have hxw : sf c Y.J H.x w = 0 := by rw [sf_skew c _ hc hJ, hwx, map_zero, neg_zero]
  have hxx' : sf c Y.J H.x H.x = 0 := hxx
  have hk2 : 2 * k + sf c Y.J w w = 0 := by rw [hkdef]; ring
  have hcs : c (sf c Y.J w w) = -sf c Y.J w w := by
    have := sf_skew c _ hc hJ w w
    linear_combination this
  have hku : k - c k + sf c Y.J w w = 0 := by
    have h2 : c 2 = 2 := map_ofNat c 2
    rw [hkdef, map_div₀, map_neg, hcs, h2]
    ring
  set U := eich c Y.J H.x w k with hUdef
  have hU : Uᵀ * Y.J * U.map c = Y.J := eich_unitary hc hJ hxx' hxw hku
  let g₀ : GL (Fin n) E := ⟨U, eich c Y.J H.x (-w) k, eich_mul_neg hxx' hxw hwx hk2 _ rfl,
    eich_neg_mul hxx' hxw hwx hk2 _ rfl⟩
  let g : GL (Fin n) (AE F E) := Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) g₀
  have hgmat : (g : Matrix (Fin n) (Fin n) (AE F E)) = incM F U := rfl
  have hmapc : (incM F U).map (cA σ) = incM F (U.map c) := by
    ext i j
    simp [incM, GlobalTheory.LeviLine.cA_inclR, hcdef]
  have hgU : g ∈ UG (cA σ) (incM F Y.J) := by
    show (incM F U)ᵀ * incM F Y.J * (incM F U).map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom = incM F Y.J
    have h1 : (incM F U).map (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom = incM F (U.map c) := hmapc
    rw [h1]
    simp only [incM]
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  let γ : UA σ Y.J := ⟨g, hgU⟩
  have hmat : mat γ = incM F U := rfl

  have hιx : ∀ u, sf c Y.J (H.ι *ᵥ u) H.x = 0 := fun u => (horth u).1
  set ρ : Fin n₁ → E := fun j => sf c Y.J (H.ι *ᵥ Pi.single j 1) w with hρdef
  have hUι : U * H.ι = H.ι - vecMulVec H.x ρ := by
    refine ext_mulVec_single fun j => ?_
    rw [← mulVec_mulVec, hUdef, eich_mulVec, sub_mulVec, vecMulVec_mulVec_rect, hιx]
    simp [hρdef, dotProduct_single]
  have hincvv : incM F (vecMulVec H.x ρ) = vecMulVec (incV F H.x) (incV F ρ) := by
    ext i j
    simp [incM, incV, vecMulVec_apply]
  refine ⟨γ, Subgroup.subset_closure ⟨?_, fun z => ⟨-(incV F ρ ⬝ᵥ z), ?_⟩⟩, ?_, ?_⟩
  · rw [hmat, incM_mulVec_incV, hUdef, eich_mulVec, hxw, hxx']
    simp
  · rw [hmat, mulVec_mulVec]
    simp only [incM] at hincvv ⊢
    rw [← Matrix.map_mul, hUι, Matrix.map_sub _ (map_sub _), hincvv, sub_mulVec, vecMulVec_mulVec_rect, neg_smul, sub_eq_add_neg]
  · rw [ratU, Subgroup.mem_subgroupOf]
    exact ⟨g₀, rfl⟩
  · funext j
    simp only [coA]
    rw [hmat, single_eq_incV, incM_mulVec_incV, incM_mulVec_incV, fA_incV]
    congr 1
    rw [← hsf, hUdef, eich_mulVec, hιx]
    have hy : sf c Y.J H.x H.y = 1 := hxy
    have hιy : sf c Y.J (H.ι *ᵥ Pi.single j 1) H.y = 0 := (horth _).2
    simp only [sf_sub_left, sf_smul_left, hy, hιy, zero_mul, mul_zero, sub_zero, mul_one, zero_sub]
    rw [hwdef, sf_mulVec_mulVec]
    have hg' : H.ιᵀ * Y.J * H.ι.map c = Y₁.J := hgram
    rw [hg']
    simp only [sf, hσb, hb', single_one_dotProduct, Pi.neg_apply, neg_neg]

end
