import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev spanO (b : Basis κ K V) : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)

def bO (b : Basis κ K V) : Basis κ (𝓞 K) (spanO b) :=
  Basis.span (b.linearIndependent.restrict_scalars' (𝓞 K))

theorem bO_apply (b : Basis κ K V) (i : κ) : (bO b i : V) = b i := Basis.coe_span_apply _ i

def crd (b : Basis κ K V) (y : spanO b) : κ → 𝓞 K := (bO b).equivFun y

theorem coe_eq_sum (b : Basis κ K V) (y : spanO b) :
    (y : V) = ∑ i, algebraMap (𝓞 K) K (crd b y i) • b i := by
  conv_lhs => rw [← (bO b).sum_equivFun y]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, bO_apply, algebraMap_smul]
  rfl

theorem form_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) (y y' : spanO b) :
    h (y : V) (y' : V) = algebraMap (𝓞 K) K (star (crd b y) ⬝ᵥ (H *ᵥ crd b y')) := by
  rw [coe_eq_sum b y, map_sum, LinearMap.sum_apply, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_eq_sum b y', map_smulₛₗ, LinearMap.smul_apply, map_sum, map_mul, mulVec, dotProduct, map_sum,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, hH, mul_comm]

theorem congrP_int {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a c : 𝓞 K) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K a) (algebraMap (𝓞 K) K c) ↔
      Ideal.Quotient.mk (extP K 𝔭 ^ k) a = Ideal.Quotient.mk (extP K 𝔭 ^ k) c := by
  rw [Ideal.Quotient.eq]
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have e' : z = ι t * (a - c) := by
      apply RingOfIntegers.coe_injective
      rw [e, map_mul, map_sub]
      rfl
    have ht' : t ∉ 𝔭 ^ (0 + 1) := by rwa [zero_add, pow_one]
    exact mem_of_mul_mem h𝔭 ht' (by rw [zero_add, ← e']; exact hz)
  · intro hm
    exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a - c, hm, by simp⟩

def redL (b : Basis κ K V) (J : Ideal (𝓞 K)) : spanO b →ₗ[𝓞 K] (κ → 𝓞 K ⧸ J) :=
  (J.mkQ.compLeft κ) ∘ₗ (bO b).equivFun.toLinearMap

theorem redL_apply (b : Basis κ K V) (J : Ideal (𝓞 K)) (y : spanO b) :
    redL b J y = fun i => Ideal.Quotient.mk J (crd b y i) := rfl

theorem redL_surjective (b : Basis κ K V) (J : Ideal (𝓞 K)) : Function.Surjective (redL b J) := by
  intro x
  choose c hc using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨(bO b).equivFun.symm c, ?_⟩
  rw [redL_apply]
  funext i
  rw [crd, LinearEquiv.apply_symm_apply, hc]

theorem ker_redL (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    LinearMap.ker (redL b J) = (J • ⊤ : Submodule (𝓞 K) (spanO b)) := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, redL_apply] at hy
    rw [← (bO b).sum_equivFun y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hy i)
  · rw [Submodule.smul_le]
    intro a ha y _
    rw [LinearMap.mem_ker, map_smul]
    funext i
    rw [Pi.smul_apply, redL_apply, Algebra.smul_def]
    have : algebraMap (𝓞 K) (𝓞 K ⧸ J) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
    rw [this, zero_mul]
    rfl

def qE (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b))) ≃ₗ[𝓞 K] (κ → 𝓞 K ⧸ J) :=
  (Submodule.quotEquivOfEq _ _ (ker_redL b J).symm).trans
    ((redL b J).quotKerEquivOfSurjective (redL_surjective b J))

theorem qE_mk (b : Basis κ K V) (J : Ideal (𝓞 K)) (y : spanO b) :
    qE b J (Submodule.Quotient.mk y) = fun i => Ideal.Quotient.mk J (crd b y i) := rfl

variable [Fact (IsFixF K F)]

theorem mk_form (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix κ κ (𝓞 K)) (c c' : κ → 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (star c ⬝ᵥ (H *ᵥ c')) =
      star (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (c i)) ⬝ᵥ
        (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (c' i)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec _ H c' i

theorem nkCount_free (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (n : 𝓞 F) :
    nkCount h (spanO b) 𝔭 k n = Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
      star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) = Ideal.Quotient.mk _ (ι n)} := by
  unfold nkCount
  refine Nat.card_congr ((qE b (extP K 𝔭 ^ k)).toEquiv.subtypeEquiv fun x => ?_)
  have key : ∀ y : spanO b, CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ↔
      star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y)) ⬝ᵥ
        (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y))) =
        Ideal.Quotient.mk _ (ι n) := by
    intro y
    rw [form_eq h b hH, ← MeanB.algebraMap_comp, congrP_int h𝔭, mk_form, qE_mk]
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact (key y).1 hy
  · intro hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨y, rfl, (key y).2 hx⟩

theorem form_mulVec {A : Type*} [CommRing A] [StarRing A] (M N : Matrix κ κ A) (u v : κ → A) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem form_single {A : Type*} [CommRing A] [StarRing A] (N : Matrix κ κ A) (i j : κ) :
    star (Pi.single i (1 : A)) ⬝ᵥ (N *ᵥ Pi.single j (1 : A)) = N i j := by
  have : star (Pi.single i (1 : A) : κ → A) = Pi.single i 1 := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl]
  rw [this, mulVec_single_one, single_one_dotProduct]
  rfl

theorem qE_bO (b : Basis κ K V) (J : Ideal (𝓞 K)) (i : κ) :
    qE b J (Submodule.Quotient.mk (bO b i)) = Pi.single i 1 := by
  rw [qE_mk]
  funext l
  rw [crd, Basis.equivFun_self]
  by_cases hl : i = l
  · subst hl; simp
  · rw [if_neg hl, map_zero, Pi.single_eq_of_ne (Ne.symm hl)]

def eM (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    Module.End (𝓞 K) (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b))) ≃ Matrix κ κ (𝓞 K ⧸ J) :=
  (qE b J).conj.toEquiv.trans
    ((LinearMap.extendScalarsOfSurjectiveEquiv (R := 𝓞 K) (S := 𝓞 K ⧸ J)
      Ideal.Quotient.mk_surjective).toEquiv.trans LinearMap.toMatrix'.toEquiv)

theorem eM_mulVec (b : Basis κ K V) (J : Ideal (𝓞 K))
    (X : Module.End (𝓞 K) (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b)))) (q) :
    eM b J X *ᵥ qE b J q = qE b J (X q) := by
  have : eM b J X = LinearMap.toMatrix' (LinearMap.extendScalarsOfSurjectiveEquiv (R := 𝓞 K)
      (S := 𝓞 K ⧸ J) Ideal.Quotient.mk_surjective ((qE b J).conj X)) := rfl
  rw [this, LinearMap.toMatrix'_mulVec]
  show (qE b J).conj X (qE b J q) = _
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

theorem akCount_free (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) :
    akCount h (spanO b) 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} := by
  unfold akCount
  refine Nat.card_congr ((eM b (extP K 𝔭 ^ k)).subtypeEquiv fun X => ?_)
  have key : ∀ x y x' y' : spanO b, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      (CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) ↔
        star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk x)) ⬝ᵥ
          (((eM b (extP K 𝔭 ^ k) X)ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *
            eM b (extP K 𝔭 ^ k) X) *ᵥ qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y)) =
        star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk x)) ⬝ᵥ
          (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ
            qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y))) := by
    intro x y x' y' hx hy
    rw [form_eq h b hH, form_eq h b hH, congrP_int h𝔭, mk_form, mk_form, ← qE_mk, ← qE_mk, ← qE_mk,
      ← qE_mk, hx, hy, ← eM_mulVec, ← eM_mulVec, form_mulVec]
  constructor
  · intro hX
    ext i j
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk (bO b i)))
    obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk (bO b j)))
    have := (key _ _ x' y' hx' hy').1 (hX _ _ x' y' hx' hy')
    rwa [qE_bO, qE_bO, form_single, form_single] at this
  · intro hX x y x' y' hx hy
    rw [key x y x' y' hx hy, hX]

theorem nkCount_eq (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (hb : locF 𝔭 (spanO b) = locF 𝔭 L) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) (k : ℕ) (n : 𝓞 F) :
    nkCount h L 𝔭 k n = Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
      star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) = Ideal.Quotient.mk _ (ι n)} := by
  have hF : IsFixF K F := Fact.out
  rw [← nkCount_free h b hH h𝔭, ← nkCount_locF hF h L 𝔭 h𝔭, ← hb, nkCount_locF hF h _ 𝔭 h𝔭]

theorem akCount_eq (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (hb : locF 𝔭 (spanO b) = locF 𝔭 L) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} := by
  have hF : IsFixF K F := Fact.out
  rw [← akCount_free h b hH h𝔭, ← akCount_locF hF h L 𝔭 h𝔭, ← hb, akCount_locF hF h _ 𝔭 h𝔭]

end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
