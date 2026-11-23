import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsAsmHformSmulRight
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegerDenominator

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG Formalism.UG.CS Formalism.UG.P

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem coe_algebraMap_int (d : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

theorem hcompl_norm (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (p : Ideal (𝓞 E)) [hp : p.IsPrime]
    (s : 𝓞 E) (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) :
    ∃ (t : 𝓞 E) (d : 𝓞 F), algebraMap (𝓞 F) (𝓞 E) d ∉ p ∧ algebraMap (𝓞 F) (𝓞 E) d = t * s := by
  have hstar : ∀ x : E, σ x = star x := fun x => RingHom.congr_fun hσ x
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    obtain ⟨hs1, hs2⟩ := hs
    have hint : IsIntegral ℤ (σ (s : E)) := map_isIntegral_int σ s.2
    let t : 𝓞 E := ⟨σ (s : E), hint⟩
    have htp : t ∉ p := hs2 t (hstar _)
    have hinv : σ (σ (s : E) * (s : E)) = σ (s : E) * (s : E) := by
      rw [map_mul, hstar (σ (s : E)), hstar (s : E), star_star, mul_comm]
    obtain ⟨a, ha⟩ := hfix _ hinv
    have haint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ha]
      exact hint.mul s.2
    refine ⟨t, ⟨a, haint⟩, ?_, ?_⟩
    · have e : algebraMap (𝓞 F) (𝓞 E) ⟨a, haint⟩ = t * s := by
        apply RingOfIntegers.ext
        exact ha
      rw [e]
      exact fun h => (hp.mem_or_mem h).elim htp hs1
    · apply RingOfIntegers.ext
      exact ha
  | one => exact ⟨1, 1, by rw [map_one]; exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, d, h1, h2⟩ := hx
    obtain ⟨t', d', h1', h2'⟩ := hy
    refine ⟨t * t', d * d', ?_, ?_⟩
    · rw [map_mul]
      exact fun h => (hp.mem_or_mem h).elim h1 h1'
    · rw [map_mul, h2, h2']; ring

theorem mem_loc_iff (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (p : Ideal (𝓞 E)) [hp : p.IsPrime]
    (v : Ideal (𝓞 F)) (hv : v = p.comap (algebraMap (𝓞 F) (𝓞 E)))
    (Λ : Submodule (𝓞 E) (n → E)) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p Λ ↔ ∃ d : 𝓞 F, d ∉ v ∧ (algebraMap F E (d : F)) • x ∈ Λ := by
  have hstar : ∀ x : E, σ x = star x := fun x => RingHom.congr_fun hσ x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, d, h1, h2⟩ := hcompl_norm σ hσ hfix p s hs
    refine ⟨d, by rw [hv]; exact h1, ?_⟩
    have : (algebraMap F E (d : F)) • x = t • (s • x) := by
      rw [← coe_algebraMap_int, h2, smul_smul]
      rfl
    rw [this]
    exact Λ.smul_mem t hx
  · rintro ⟨d, hd, hx⟩
    refine ⟨algebraMap (𝓞 F) (𝓞 E) d, Submonoid.subset_closure ⟨by rw [hv] at hd; exact hd, ?_⟩, hx⟩
    intro t ht
    have : t = algebraMap (𝓞 F) (𝓞 E) d := by
      apply RingOfIntegers.ext
      rw [coe_algebraMap_int]
      have h2 : (t : E) = star (algebraMap F E (d : F)) := ht
      rw [h2, ← hstar, AlgHom.commutes]
    rw [this]
    rw [hv] at hd; exact hd

end Loc

section Glue

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : Type} [Fintype n] [DecidableEq n]

def glueM (e : I → R) (A : I → Matrix n n R) : Matrix n n R := ∑ i, e i • A i

theorem glueM_mul {e : I → R} (he : OrthogonalIdempotents e) (A B : I → Matrix n n R) :
    glueM e A * glueM e B = glueM e (fun i => A i * B i) := by
  classical
  unfold glueM
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_smul_comm, he.ortho (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem glueM_const {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : Matrix n n R) :
    glueM e (fun _ => A) = A := by
  unfold glueM
  rw [← Finset.sum_smul, he.complete, one_smul]

theorem smul_glueM {e : I → R} (he : OrthogonalIdempotents e) (A : I → Matrix n n R) (i : I) :
    e i • glueM e A = e i • A i := by
  classical
  unfold glueM
  rw [Finset.smul_sum, Finset.sum_eq_single i]
  · rw [smul_smul, (he.idem i).eq]
  · intro j _ hj
    rw [smul_smul, he.ortho (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cT_glueM (τ : R →+* R) {e : I → R} (hτ : ∀ i, τ (e i) = e i) (A : I → Matrix n n R) :
    cT τ (glueM e A) = glueM e (fun i => cT τ (A i)) := by
  ext a b
  simp only [cT, glueM, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, hτ]

def glueGL {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : I → GL n R) : GL n R where
  val := glueM e (fun i => (A i : Matrix n n R))
  inv := glueM e (fun i => ((A i)⁻¹ : GL n R))
  val_inv := by
    rw [glueM_mul he.toOrthogonalIdempotents]
    simp only [Units.mul_inv]
    exact glueM_const he 1
  inv_val := by
    rw [glueM_mul he.toOrthogonalIdempotents]
    simp only [Units.inv_mul]
    exact glueM_const he 1

theorem glueGL_mem_UJ {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : I → GL n R)
    (τ : R →+* R) (hτ : ∀ i, τ (e i) = e i) (J : Matrix n n R) (hA : ∀ i, A i ∈ UJ τ J) :
    glueGL he A ∈ UJ τ J := by
  show cT τ (glueM e (fun i => (A i : Matrix n n R))) * J * glueM e (fun i => (A i : Matrix n n R)) = J
  rw [cT_glueM τ hτ]
  conv_lhs => rw [← glueM_const he J]
  rw [glueM_mul he.toOrthogonalIdempotents, glueM_mul he.toOrthogonalIdempotents]
  have : (fun i => cT τ (A i : Matrix n n R) * J * (A i : Matrix n n R)) = fun _ => J := by
    funext i; exact hA i
  rw [this]
  exact glueM_const he J

end Glue

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def inclAd : 𝔸 →+* 𝒜 := (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜).toRingHom

theorem inclAd_apply (a : 𝔸) : inclAd (E := E) a = (1 : E) ⊗ₜ[F] a := rfl

theorem sigR_inclAd (σ : E →ₐ[F] E) (a : 𝔸) : sigR σ 𝔸 (inclAd (E := E) a) = inclAd a := by
  show Algebra.TensorProduct.map σ (AlgHom.id F 𝔸) ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

def Near (a : 𝔸) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) : Prop :=
  ∃ d : 𝓞 F, ∃ c ∈ intAd F, a = algebraMap F 𝔸 (d : F) * c ∧ (algebraMap F E (d : F)) • y ∈ Λ

theorem near_mem {a : 𝔸} {Λ : Submodule (𝓞 E) (n → E)} {y : n → E} (h : Near a Λ y) :
    inclAd (E := E) a • (fun i => ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  obtain ⟨d, c, hc, rfl, hy⟩ := h
  have hcS : inclAd (E := E) c ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)
  have e : inclAd (E := E) (algebraMap F 𝔸 (d : F) * c) • (fun i => ιA (y i)) =
      (⟨inclAd (E := E) c, hcS⟩ : 𝒮) • (fun i => ιA (((algebraMap F E (d : F)) • y) i)) := by
    funext i
    show ((1 : E) ⊗ₜ[F] (algebraMap F 𝔸 (d : F) * c)) * ((y i) ⊗ₜ[F] (1 : 𝔸)) =
      ((1 : E) ⊗ₜ[F] c) * ((algebraMap F E (d : F) * y i) ⊗ₜ[F] (1 : 𝔸))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
      mul_one, mul_one, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

theorem sum_smul_eq {I : Type} [Fintype I] {e : I → 𝒜} (he : CompleteOrthogonalIdempotents e)
    (u : n → 𝒜) : u = ∑ i, e i • u := by
  rw [← Finset.sum_smul, he.complete, one_smul]

theorem bc_mulVec_incl (γ : GL n E) (x : n → E) :
    ((bc ιA γ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) =
      fun i => ιA (((γ : Matrix n n E) *ᵥ x) i) := csEquiv_bc_mulVec γ x

theorem glue_globLat (σ : E →ₐ[F] E) (J : Matrix n n E) {I : Type} [Fintype I] (a : I → 𝔸)
    (ha : CompleteOrthogonalIdempotents a) (γ : I → GL n E) (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J)
    (L M : Submodule (𝓞 E) (n → E)) (hMfin : Module.Finite (𝓞 E) M)
    (hMspan : Submodule.span E (M : Set (n → E)) = ⊤)
    (H1 : ∀ i, ∀ x ∈ M, Near (a i) L ((((γ i)⁻¹ : GL n E) : Matrix n n E) *ᵥ x))
    (H2 : ∀ i, ∀ l ∈ L, Near (a i) M ((γ i : Matrix n n E) *ᵥ l)) :
    ∃ g ∈ UPts σ J 𝔸, globLat g L = M := by
  have he : CompleteOrthogonalIdempotents (fun i => inclAd (E := E) (a i)) := ha.map inclAd
  refine ⟨glueGL he (fun i => bc ιA (γ i)), ?_, ?_⟩
  · refine glueGL_mem_UJ he _ _ (fun i => sigR_inclAd σ (a i)) _ fun i => ?_
    exact Formalism.UG.Final.RatPtsLe F E n σ J 𝔸 ⟨γ i, hγ i, rfl⟩
  · ext x
    constructor
    · intro hx
      have hx' : glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) ∈
          latS (F := F) 𝔸 𝒮 L := hx
      set u := glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) with hu
      have hgu : (fun i => ιA (x i)) = glueM (fun i => inclAd (E := E) (a i))
          (fun i => ((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ u := by
        rw [hu, Matrix.mulVec_mulVec]
        have := (glueGL he (fun i => bc ιA (γ i))).val_inv
        change glueM _ _ * glueM _ _ = 1 at this
        rw [this, Matrix.one_mulVec]
      have key : ∀ i, ∀ w ∈ latS (F := F) 𝔸 𝒮 L,
          inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w) ∈
            latS (F := F) 𝔸 𝒮 M := by
        intro i w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨l, hl, rfl⟩ := hw
          rw [bc_mulVec_incl]
          exact near_mem (H2 i l hl)
        | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
        | add w w' _ _ h h' => rw [Matrix.mulVec_add, smul_add]; exact add_mem h h'
        | smul s w _ h =>
          have : inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (s • w)) =
              s • (inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w)) := by
            rw [Subring.smul_def, Matrix.mulVec_smul, Subring.smul_def, smul_comm]
          rw [this]
          exact Submodule.smul_mem _ _ h
      have hmem : (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 M := by
        rw [sum_smul_eq he (fun i => ιA (x i))]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [hgu, ← Matrix.smul_mulVec, smul_glueM he.toOrthogonalIdempotents, Matrix.smul_mulVec]
        exact key i u hx'
      have h1 := Formalism.UG.P.global_lattice_one_holds F E n M hMfin hMspan
      rw [← h1]
      show (((1 : GL n 𝒜)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 M
      rw [inv_one, Units.val_one, Matrix.one_mulVec]
      exact hmem
    · intro hx
      show glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) ∈
          latS (F := F) 𝔸 𝒮 L
      rw [sum_smul_eq he (glueM _ _ *ᵥ _)]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Matrix.smul_mulVec, smul_glueM he.toOrthogonalIdempotents, Matrix.smul_mulVec, ← map_inv,
        bc_mulVec_incl]
      exact near_mem (H1 i x hx)

end Main

section Ind

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open Classical in

def indA (T : Set (HeightOneSpectrum (𝓞 F))) : 𝔸 :=
  ⟨fun w => if w ∈ T then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem indA_mem {T : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 F)} (h : w ∈ T) :
    indA T w = 1 := by
  classical
  exact if_pos h

theorem indA_notMem {T : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 F)} (h : w ∉ T) :
    indA T w = 0 := by
  classical
  exact if_neg h

theorem indA_complete {I : Type} [Fintype I] (T : I → Set (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ w, ∃! i, w ∈ T i) : CompleteOrthogonalIdempotents (fun i => indA (T i)) := by
  classical
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro i j hij
    refine DFunLike.ext _ _ fun w => ?_
    show indA (T i) w * indA (T j) w = 0
    by_cases h : w ∈ T i
    · have : w ∉ T j := fun h' => hij ((hT w).unique h h')
      rw [indA_notMem this, mul_zero]
    · rw [indA_notMem h, zero_mul]
  · refine DFunLike.ext _ _ fun w => ?_
    have e : (∑ i, indA (T i)) w = ∑ i, indA (T i) w := map_sum (evalV F w) _ _
    show (∑ i, indA (T i)) w = 1
    obtain ⟨i0, h0, hu⟩ := hT w
    rw [e, Finset.sum_eq_single i0, indA_mem h0]
    · intro j _ hj
      exact indA_notMem fun h => hj (hu j h)
    · intro h; exact absurd (Finset.mem_univ i0) h

theorem indA_div (T : Set (HeightOneSpectrum (𝓞 F))) (d : 𝓞 F) (hd : ∀ w ∈ T, d ∉ w.asIdeal) :
    ∃ c ∈ intAd F, indA T = algebraMap F 𝔸 (d : F) * c := by
  classical
  have hint : ∀ w : HeightOneSpectrum (𝓞 F),
      (if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0) ∈
        w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, levelaf_valued_algebraMap,
        show ((d : F)) = algebraMap (𝓞 F) F d from rfl,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (hd w h), inv_one]
    · exact zero_mem _
  refine ⟨⟨fun w => if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0,
    Filter.Eventually.of_forall hint⟩, hint, ?_⟩
  refine DFunLike.ext _ _ fun w => ?_
  show indA T w = algebraMap F (w.adicCompletion F) (d : F) *
    (if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0)
  by_cases h : w ∈ T
  · rw [indA_mem h, if_pos h, mul_inv_cancel₀]
    have hd0 : d ≠ 0 := fun h0 => hd w h (h0 ▸ zero_mem _)
    exact levelaf_algebraMap_ne_zero w d hd0
  · rw [indA_notMem h, if_neg h, mul_zero]

end Ind

section Denom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem algebraMap_coe_mul (a b : 𝓞 F) :
    algebraMap F E ((a * b : 𝓞 F) : F) = algebraMap F E (a : F) * algebraMap F E (b : F) := by
  rw [← map_mul]; rfl

theorem smul_int_mem (L : Submodule (𝓞 E) (n → E)) (d : 𝓞 F) {x : n → E} (hx : x ∈ L) :
    (algebraMap F E (d : F)) • x ∈ L := L.smul_mem (algebraMap (𝓞 F) (𝓞 E) d) hx

theorem exists_denom_pt (L : Submodule (𝓞 E) (n → E))
    (hL : Submodule.span E (L : Set (n → E)) = ⊤) (x : n → E) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (algebraMap F E (D : F)) • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt L hL x

theorem exists_denom (L M : Submodule (𝓞 E) (n → E))
    (hL : Submodule.span E (L : Set (n → E)) = ⊤) (hM : M.FG) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ x ∈ M, (algebraMap F E (D : F)) • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose D hD0 hD using exists_denom_pt (F := F) L hL
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.2 fun s _ => hD0 s, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' : x ∈ S := hx
    rw [← Finset.mul_prod_erase S D hx', mul_comm, algebraMap_coe_mul, ← smul_smul]
    exact smul_int_mem L _ (hD x)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul a x _ h =>
    rw [smul_comm]
    exact L.smul_mem a h

end Denom

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem finite_places_of_mem (D : 𝓞 F) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite := by
  have := Ideal.finite_factors (I := Ideal.span {D}) (by simpa using hD)
  simpa only [Ideal.dvd_span_singleton] using this

theorem exists_prime_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : Ideal (𝓞 E), p.IsMaximal ∧ v.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) := by
  have hv : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  exact ⟨Q, hQ, hQv.symm⟩

theorem genus_local (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (L M : Submodule (𝓞 E) (n → E))
    (hgen : Formalism.HermitianLatticesTheory.SameGenus h L M) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : GL n E, γ ∈ UJ (σ : E →+* E) (gram h) ∧
      (∀ x ∈ M, ∃ d : 𝓞 F, d ∉ v.asIdeal ∧
        (algebraMap F E (d : F)) • (((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) ∈ L) ∧
      (∀ l ∈ L, ∃ d : 𝓞 F, d ∉ v.asIdeal ∧
        (algebraMap F E (d : F)) • ((γ : Matrix n n E) *ᵥ l) ∈ M) := by
  obtain ⟨p, hp, hpv⟩ := exists_prime_over (E := E) v
  have hpp : p.IsPrime := hp.isPrime
  obtain ⟨u, hu, hLM⟩ := hgen p hp
  obtain ⟨γ, rfl⟩ := Formalism.UG.Final.HermBridgeSurj E n h u hu
  have hle : ∀ (N : Submodule (𝓞 E) (n → E)), ∀ x ∈ N, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p N := by
    intro N x hx
    rw [mem_loc_iff σ hσ hfix p v.asIdeal hpv]
    refine ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
    simpa using hx
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [hσ]
    exact (Formalism.UG.Final.HermBridge E n h γ).2 hu
  · intro x hx
    have hx' := hle M x hx
    rw [← hLM] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : (γ : Matrix n n E) *ᵥ y = x := by
      rw [← Formalism.UG.Final.GlEquivApply E n γ y]; exact hyx
    rw [← hyx', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact (mem_loc_iff σ hσ hfix p v.asIdeal hpv L y).1 hy
  · intro l hl
    have : (γ : Matrix n n E) *ᵥ l ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
      rw [← hLM, ← Formalism.UG.Final.GlEquivApply E n γ l]
      exact ⟨l, hle L l hl, rfl⟩
    exact (mem_loc_iff σ hσ hfix p v.asIdeal hpv M _).1 this

theorem genus_surj (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (L M : Submodule (𝓞 E) (n → E))
    (hLfin : Module.Finite (𝓞 E) L) (hLspan : Submodule.span E (L : Set (n → E)) = ⊤)
    (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    ∃ g ∈ UPts σ (gram h) 𝔸, globLat g L = M := by
  classical
  obtain ⟨hMlat, hgen⟩ := hM
  have hMfg : M.FG := hMlat.fg
  have hMspan : Submodule.span E (M : Set (n → E)) = ⊤ := hMlat.span_eq_top
  obtain ⟨D1, hD1, h1⟩ := exists_denom (F := F) L M hLspan hMfg
  obtain ⟨D2, hD2, h2⟩ := exists_denom (F := F) M L hMspan (Module.Finite.iff_fg.1 hLfin)
  have hD : D1 * D2 ≠ 0 := mul_ne_zero hD1 hD2
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (finite_places_of_mem (D1 * D2) hD).toFinset with hS
  have hSmem : ∀ w, w ∉ S → D1 * D2 ∉ w.asIdeal := by
    intro w hw hmem
    exact hw ((Set.Finite.mem_toFinset _).2 hmem)
  choose γ hγU hγ1 hγ2 using genus_local σ hσ hfix h L M hgen
  let T : Option S → Set (HeightOneSpectrum (𝓞 F)) := fun i => i.elim {w | w ∉ S} (fun v => {v.1})
  let γ' : Option S → GL n E := fun i => i.elim 1 (fun v => γ v.1)
  have hT : ∀ w, ∃! i, w ∈ T i := by
    intro w
    by_cases hw : w ∈ S
    · refine ⟨some ⟨w, hw⟩, rfl, ?_⟩
      rintro (_ | ⟨v, hv⟩) hi
      · exact absurd hw hi
      · have : w = v := hi
        subst this; rfl
    · refine ⟨none, hw, ?_⟩
      rintro (_ | ⟨v, hv⟩) hi
      · rfl
      · have : w = v := hi
        subst this; exact absurd hv hw
  refine glue_globLat σ (gram h) (fun i => indA (T i)) (indA_complete T hT) γ' ?_ L M
    (Module.Finite.iff_fg.2 hMfg) hMspan ?_ ?_
  · rintro (_ | v)
    · exact one_mem _
    · exact hγU v.1
  · rintro (_ | v) x hx
    · obtain ⟨c, hc, hc'⟩ := indA_div (T none) (D1 * D2) hSmem
      refine ⟨D1 * D2, c, hc, hc', ?_⟩
      show (algebraMap F E ((D1 * D2 : 𝓞 F) : F)) • ((((1 : GL n E)⁻¹ : GL n E) : Matrix n n E) *ᵥ x) ∈ L
      rw [inv_one, Units.val_one, Matrix.one_mulVec, mul_comm, algebraMap_coe_mul, ← smul_smul]
      exact smul_int_mem L D2 (h1 x hx)
    · obtain ⟨d, hd, hdx⟩ := hγ1 v.1 x hx
      obtain ⟨c, hc, hc'⟩ := indA_div (T (some v)) d (by
        intro w hw
        have : w = v.1 := hw
        rw [this]; exact hd)
      exact ⟨d, c, hc, hc', hdx⟩
  · rintro (_ | v) l hl
    · obtain ⟨c, hc, hc'⟩ := indA_div (T none) (D1 * D2) hSmem
      refine ⟨D1 * D2, c, hc, hc', ?_⟩
      show (algebraMap F E ((D1 * D2 : 𝓞 F) : F)) • (((1 : GL n E) : Matrix n n E) *ᵥ l) ∈ M
      rw [Units.val_one, Matrix.one_mulVec, algebraMap_coe_mul, ← smul_smul]
      exact smul_int_mem M D1 (h2 l hl)
    · obtain ⟨d, hd, hdx⟩ := hγ2 v.1 l hl
      obtain ⟨c, hc, hc'⟩ := indA_div (T (some v)) d (by
        intro w hw
        have : w = v.1 := hw
        rw [this]; exact hd)
      exact ⟨d, c, hc, hc', hdx⟩

end Surj

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {k : ℕ}

theorem gram_stdForm : gram (Formalism.MainNotions.StandardLattice.stdForm E k) = 1 := by
  ext i j
  show ∑ a, star ((Pi.single i 1 : Fin k → E) a) * (Pi.single j 1 : Fin k → E) a = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, star_one, one_mul, Matrix.one_apply, Pi.single_apply]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem stdLat_fg : (Formalism.MainNotions.StandardLattice.stdLat E k).FG := Submodule.fg_span (Set.finite_range _)

theorem stdLat_finite : Module.Finite (𝓞 E) (Formalism.MainNotions.StandardLattice.stdLat E k) := Module.Finite.iff_fg.2 stdLat_fg

theorem stdLat_span : Submodule.span E ((Formalism.MainNotions.StandardLattice.stdLat E k : Submodule (𝓞 E) (Fin k → E)) :
    Set (Fin k → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin k)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem sig_eq_star (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e) : (σ : E →+* E) = starRingEnd E :=
  RingHom.ext hσ

theorem genusSurj (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) :
    GenusSurj σ (1 : Matrix (Fin k) (Fin k) E) := by
  intro M hM
  have := genus_surj σ (sig_eq_star σ hσ) hfix (Formalism.MainNotions.StandardLattice.stdForm E k) (Formalism.MainNotions.StandardLattice.stdLat E k) M
    stdLat_finite stdLat_span hM
  rwa [gram_stdForm] at this

end Std

end Formalism.MainNotions.Gaps.CC.Surj
