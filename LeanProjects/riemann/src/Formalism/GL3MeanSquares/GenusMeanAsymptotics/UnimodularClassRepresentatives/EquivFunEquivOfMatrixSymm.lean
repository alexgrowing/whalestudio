import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeZeroOfNotMem

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def gramK (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) : Matrix κ κ K := Matrix.of fun i j => h (b i) (b j)

theorem form_repr (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (x y : V) :
    h x y = star (b.equivFun x) ⬝ᵥ (gramK h b *ᵥ b.equivFun y) := by
  calc h x y = h (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
        rw [b.sum_equivFun x, b.sum_equivFun y]
    _ = ∑ i, ∑ j, star (b.equivFun x i) * (b.equivFun y j * h (b i) (b j)) := by
        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [dotProduct, mulVec, Pi.star_apply, gramK, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramK_conjTranspose {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (b : Basis κ K V) :
    (gramK h b)ᴴ = gramK h b := by
  ext i j
  exact hs.eq (b j) (b i)

theorem smul_basis_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) {a : K} (ha : a ∈ SP K 𝔭)
    (i : κ) : a • b i ∈ locF 𝔭 (spanO b) := by
  obtain ⟨t, ht, z, e⟩ := mem_SP.1 ha
  refine (mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩
  rw [← algebraMap_smul K (ι t), smul_smul, ← e, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (x : V) :
    x ∈ locF 𝔭 (spanO b) ↔ ∀ i, b.equivFun x i ∈ SP K 𝔭 := by
  constructor
  · intro hx i
    obtain ⟨t, ht, h1⟩ := (mem_locF 𝔭 _ _).1 hx
    have h2 : ι t • x = _ := coe_eq_sum b ⟨_, h1⟩
    generalize crd b ⟨_, h1⟩ = c at h2
    refine mem_SP.2 ⟨t, ht, c i, ?_⟩
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [← algebraMap_smul K (ι t), map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
      Basis.equivFun_self, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h3
    exact h3.symm
  · intro hx
    rw [← b.sum_equivFun x]
    exact Submodule.sum_mem _ fun i _ => smul_basis_mem b (hx i) i

theorem mem_smul_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ) (x : V) :
    x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) ↔ ∀ i, InP 𝔭 k (b.equivFun x i) := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y hy =>
      intro i
      rw [← algebraMap_smul K r, map_smul, Pi.smul_apply, smul_eq_mul]
      exact (inP_jK hr).mul (l := 0) ((mem_locF_iff_repr b y).1 hy i)
    | add y _ z _ hy hz =>
      intro i
      rw [map_add]
      exact (hy i).add (hz i)
  · intro hx
    rw [← b.sum_equivFun x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht, z, hz, e⟩ := hx i
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    have h1 : (jK (ι t))⁻¹ ∈ SP K 𝔭 := mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ ht0]⟩
    have h2 : b.equivFun x i • b i = z • ((jK (ι t))⁻¹ • b i) := by
      rw [← algebraMap_smul K z, smul_smul, e]
      congr 1
      field_simp
    rw [h2]
    exact Submodule.smul_mem_smul hz (smul_basis_mem b h1 i)

theorem equivFun_toLin (b : Basis κ K V) (G : Matrix κ κ K) (x : V) :
    b.equivFun (Matrix.toLin b b G x) = G *ᵥ b.equivFun x := by
  have := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b G) x
  rw [LinearMap.toMatrix_toLin] at this
  funext i
  exact (congrFun this i).symm

def equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin b b G) (Matrix.toLin b b G')
    (by rw [← Matrix.toLin_mul, hG, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, mul_eq_one_comm.1 hG, Matrix.toLin_one])

theorem equivFun_equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_toLin b G x

theorem equivFun_equivOfMatrix_symm (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun ((equivOfMatrix b G G' hG).symm x) = G' *ᵥ b.equivFun x := equivFun_toLin b G' x

theorem equivOfMatrix_mem_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (hU : Gᴴ * gramK h b * G = gramK h b) :
    equivOfMatrix b G G' hG ∈ Formalism.HermitianLatticesTheory.isom h := by
  intro x y
  rw [form_repr h b, form_repr h b x y, equivFun_equivOfMatrix, equivFun_equivOfMatrix, form_mulVec, hU]

theorem mulVec_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) {v : κ → K}
    (hv : ∀ i, v i ∈ SP K 𝔭) (i : κ) : (G *ᵥ v) i ∈ SP K 𝔭 :=
  (SP K 𝔭).sum_mem fun j _ => (SP K 𝔭).mul_mem (hG i j) (hv j)

theorem gmap_equivOfMatrix {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (h1 : Ent (SP K 𝔭) G) (h2 : Ent (SP K 𝔭) G') :
    Formalism.HermitianLatticesTheory.gmap (equivOfMatrix b G G' hG) (locF 𝔭 (spanO b)) = locF 𝔭 (spanO b) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_locF_iff_repr]
    intro i
    have : b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_equivOfMatrix b G G' hG x
    show b.equivFun (equivOfMatrix b G G' hG x) i ∈ _
    rw [this]
    exact mulVec_mem h1 ((mem_locF_iff_repr b x).1 hx) i
  · intro x hx
    refine ⟨(equivOfMatrix b G G' hG).symm x, ?_, (equivOfMatrix b G G' hG).apply_symm_apply x⟩
    show _ ∈ locF 𝔭 (spanO b)
    rw [mem_locF_iff_repr]
    intro i
    rw [equivFun_equivOfMatrix_symm]
    exact mulVec_mem h2 ((mem_locF_iff_repr b x).1 hx) i

end Formalism.HermitianLattices.Ext.L3.HU
