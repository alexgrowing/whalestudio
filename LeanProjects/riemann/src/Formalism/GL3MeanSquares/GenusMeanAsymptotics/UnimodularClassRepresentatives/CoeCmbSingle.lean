import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMatrixOfIsom

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c

theorem coe_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : (cmb b c : V) = ∑ l, c l • b l := by
  rw [cmb, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Submodule.coe_smul, bO_apply]

theorem crd_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : crd b (cmb b c) = c :=
  (bO b).equivFun.apply_symm_apply c

theorem cmb_crd (b : Basis κ K V) (y : spanO b) : cmb b (crd b y) = y :=
  (bO b).equivFun.symm_apply_apply y

def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))

theorem coe_inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) (y : spanO b) : (inA 𝔭 b y : V) = y := rfl

abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))

theorem mk_eq_iff {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) (k : ℕ) (x y : ↥(locF 𝔭 (spanO b))) :
    (Submodule.Quotient.mk x : QA 𝔭 b k) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem quotLocF_mk' {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (y : spanO b) : quotLocF h𝔭 (spanO b) k (Submodule.Quotient.mk y) = Submodule.Quotient.mk (inA 𝔭 b y) :=
  rfl

theorem exists_cmb {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩

theorem cmb_eq_sum (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]

theorem end_apply_cmb {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K))
    (hXY : ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
      Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i))) (c : κ → 𝓞 K) :
    X (Submodule.Quotient.mk (inA 𝔭 b (cmb b c))) = Submodule.Quotient.mk (inA 𝔭 b (cmb b (Y *ᵥ c))) := by
  have h1 : cmb b (Y *ᵥ c) = ∑ i, c i • cmb b fun l => Y l i := by
    apply (bO b).equivFun.injective
    show crd b _ = crd b _
    have : crd b (∑ i, c i • cmb b fun l => Y l i) = ∑ i, c i • crd b (cmb b fun l => Y l i) := by
      unfold crd
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    rw [this, crd_cmb]
    funext l
    simp [crd_cmb, mulVec, dotProduct, mul_comm]
  rw [h1, cmb_eq_sum b c]
  simp only [← Submodule.mkQ_apply] at hXY ⊢
  simp only [map_sum, map_smul, hXY]

theorem coe_cmb_single (b : Basis κ K V) (i : κ) : (cmb b (Pi.single i 1) : V) = b i := by
  rw [coe_cmb, Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

def eL {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (k : ℕ) :
    Module.End (𝓞 K) (QA 𝔭 b k) ≃ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (quotLocF h𝔭 (spanO b) k).symm.conj.toEquiv.trans (eM b (extP K 𝔭 ^ k))

theorem bO_eq_cmb (b : Basis κ K V) (i : κ) : bO b i = cmb b (Pi.single i 1) := by
  apply Subtype.ext
  rw [bO_apply, coe_cmb_single]

theorem eL_col {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (i : κ) :
    (fun l => eL h𝔭 b k X l i) = qE b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm
      (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) := by
  have h1 := eM_mulVec b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm.conj X)
    (Submodule.Quotient.mk (bO b i))
  rw [qE_bO, mulVec_single_one, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, bO_eq_cmb,
    quotLocF_mk'] at h1
  exact h1

theorem eL_eq_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K)) :
    eL h𝔭 b k X = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by
  have key : ∀ i, (fun l => Ideal.Quotient.mk (extP K 𝔭 ^ k) (Y l i)) =
      qE b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm
        (Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)))) := by
    intro i
    rw [← quotLocF_mk' h𝔭, LinearEquiv.symm_apply_apply, qE_mk, crd_cmb]
  constructor
  · intro h i
    have h1 := eL_col h𝔭 b k X i
    rw [h] at h1
    have h2 : (fun l => (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) l i) =
        fun l => Ideal.Quotient.mk (extP K 𝔭 ^ k) (Y l i) := rfl
    rw [h2, key i] at h1
    exact ((quotLocF h𝔭 (spanO b) k).symm.injective ((qE b (extP K 𝔭 ^ k)).injective h1)).symm
  · intro h
    ext l i
    have h1 := eL_col h𝔭 b k X i
    rw [h i, ← key i] at h1
    exact congrFun h1 l

end Formalism.HermitianLattices.Ext.L3.HU
