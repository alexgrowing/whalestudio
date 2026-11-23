import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChartStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulOfTwCoord
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemSpanOfSaturatingOfLe

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory

theorem exists_X_pow_smul_mem_span_of_dehomogenisation {ι : Type} {R : Type} [CommRing R]
    {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (i : ι) {B N : Type} [CommRing B] [AddCommGroup N] [Module B N]
    {π : MvPolynomial ι R →+* B} (hπ : Function.Surjective π) (hi : π (MvPolynomial.X i) = 1)
    (ε : G →ₛₗ[π] N)
    (hker : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    {g : G} (hg : g ∈ 𝒢 0) (hgen : ∀ z : N, ∃ b : B, z = b • ε g)
    (K : Submodule (MvPolynomial ι R) G) (hK : g ∈ K) (y : G) :
    ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y ∈ K := by
  induction y using Decomposition.inductionOn 𝒢 with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    refine ⟨p + q, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hp
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hq
  | @homogeneous n y =>
    obtain ⟨b, hb⟩ := hgen (ε y)
    obtain ⟨F, rfl⟩ := hπ b
    obtain ⟨n₀, hn₀⟩ := exists_homogeneous_add_X_sub_one_smul (polyGrading ι R) i F
    obtain ⟨F', hF', w, e⟩ := hn₀ (n + ((n₀ - n).toNat : ℕ)) (by omega)
    have hX : (MvPolynomial.X i : MvPolynomial ι R) ^ (n₀ - n).toNat ∈
        polyGrading ι R ((n₀ - n).toNat : ℕ) :=
      mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow i _)
    have h₁ := grSMul_mem 𝒢 hX y.2
    have h₂ := grSMul_mem 𝒢 hF' hg
    rw [zero_add] at h₂
    have hFF : π F = π F' := by
      rw [e, map_add, smul_eq_mul, map_mul, map_sub, hi, map_one, sub_self, zero_mul, add_zero]
    obtain ⟨k, hk⟩ := hker _ _ (sub_mem h₁ h₂) (by
      rw [map_sub, map_smulₛₗ, map_smulₛₗ, map_pow, hi, one_pow, one_smul, hb, hFF, sub_self])
    refine ⟨k + (n₀ - n).toNat, ?_⟩
    rw [smul_sub, sub_eq_zero] at hk
    rw [pow_add, mul_smul, hk]
    exact K.smul_mem _ (K.smul_mem _ hK)

namespace AbLaw

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {H : LB Y}
  {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (M : LB Y)

theorem operatorsCommute_mulSec (V : Y.Opens) :
    OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V :=
  fun i j _ a => SecOn.mulSec_comm (s i) (s j) a

theorem restrict_eq_zero_of_X_pow_smul (i : Fin (m + 1)) (k : ℕ) : ∀ (n : ℤ)
    (a : SecOnR f (tw M H n) ⊤), (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k •
      GrSum.of (operatorsCommute_mulSec f s M ⊤) n a = 0 →
    SecOnR.restrict f _ (le_top : nonzeroLocus (s i) ≤ ⊤) a = 0 := by
  induction k with
  | zero =>
    intro n a h
    rw [pow_zero, one_smul, map_eq_zero_iff _ (GrSum.of_injective _ n)] at h
    rw [h, map_zero]
  | succ k ih =>
    intro n a h
    rw [pow_succ, mul_smul, GrSum.X_smul_of] at h
    have e := ih _ _ h
    refine (map_eq_zero_iff _ (SecOnR.mulSec_bijective f (M := M) n (s i) le_rfl).1).1 ?_
    exact (SecOn.mulSec_restrict (s i) le_top a).trans e

theorem grSum_eq_zero_of_X_pow_smul (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (y : GrSum (operatorsCommute_mulSec f s M ⊤))
    (h : ∀ i, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) : y = 0 := by
  obtain ⟨T, hT⟩ := exists_sum_grProj (GrSum.grading _) y
  rw [← hT]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [GrSum.proj_grading, map_eq_zero_iff _ (GrSum.of_injective _ n)]
  refine SecOnR.ext_of_cover f (fun i => nonzeroLocus (s i)) (fun _ => le_top) hs.ge fun i => ?_
  obtain ⟨k, hk⟩ := h i
  rw [map_zero]
  refine restrict_eq_zero_of_X_pow_smul f s M i k n _ ?_
  have hX : (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k ∈ polyGrading _ R (k : ℕ) :=
    mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow i _)
  rw [← GrSum.proj_grading, ← proj_smul_of_mem (GrSum.grading _) hX, hk, map_zero]

def twZeroTrivEquiv (hH : H.IsLB) (V : Y.Opens) :
    Γ(Y, V) ≃ₗ[Γ(Y, V)] SecOn (tw (Inh.trivLB Y) H 0) V :=
  (secOnTrivEquiv V).symm ≪≫ₗ SecOn.twZeroEquiv (Inh.trivLB_isLB Y) hH V

theorem twCoord_twZeroTrivEquiv_one (hH : H.IsLB) (V : Y.Opens) (p : (Inh.trivLB Y).ι) (k : H.ι) :
    SecOn.twCoord (twZeroTrivEquiv hH V 1) p k = 1 := by
  refine (SecOn.twCoord_twZeroEquiv (Inh.trivLB_isLB Y) hH _ p k).trans ?_
  have e := SecOn.coord_chart_symm (Inh.trivLB_isLB Y) PUnit.unit p (le_top : V ≤ ⊤) 1
  have e₂ : rs Y (inf_le_left : V ⊓ ⊤ ≤ V) 1 *
      rs Y (le_inf le_top le_top : V ⊓ ⊤ ≤ ⊤ ⊓ ⊤) 1 = 1 := by
    rw [map_one, map_one, _root_.one_mul]
  exact (congrArg _ (e.trans e₂)).trans (map_one _)

theorem exists_eq_smul_restrict_one (hH : H.IsLB) (V : Y.Opens)
    (z : SecOn (tw (Inh.trivLB Y) H 0) V) :
    ∃ b : Γ(Y, V), z = b • SecOn.restrict _ (le_top : V ≤ ⊤) (twZeroTrivEquiv hH ⊤ 1) := by
  have e : SecOn.restrict _ (le_top : V ≤ ⊤) (twZeroTrivEquiv hH ⊤ 1) = twZeroTrivEquiv hH V 1 :=
    SecOn.tw_ext fun p k => by
      rw [SecOn.twCoord_restrict, twCoord_twZeroTrivEquiv_one, twCoord_twZeroTrivEquiv_one, map_one]
  obtain ⟨b, rfl⟩ := (twZeroTrivEquiv hH V).surjective z
  exact ⟨b, by rw [e, ← map_smul, smul_eq_mul, _root_.mul_one]⟩

def twTrivOfSec {t : ℤ} (σ : LB.Sec (pw H t)) : SecOn (tw (Inh.trivLB Y) H t) ⊤ :=
  SecOn.twMk t (fun _ k => rs Y (inf_le_right.trans inf_le_right) (σ.f k))
    fun p q k l O hp hq hM hH => by
      have e := (congrArg (rs Y hH) (σ.compat k l)).trans (map_mul (rs Y hH) _ _)
      have e₁ : res hM ((Inh.trivLB Y).g p q) = 1 := map_one _
      rw [e₁, _root_.one_mul, ← map_zpow]
      exact ((rs_rs _ _ _).trans (rs_rs _ _ _).symm).trans
        (e.trans (congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)))

theorem exists_form_eq_sec_pw : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F := by
  intro R _ Y f _ H m s hH hs
  let hx := operatorsCommute_mulSec f s (Inh.trivLB Y)
  let g : GrSum (hx ⊤) := GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ (twZeroTrivEquiv hH ⊤ 1))
  have hg : g ∈ GrSum.grading (hx ⊤) 0 := GrSum.of_mem_grading _ _ _
  obtain ⟨n₀, hn₀⟩ := mem_span_of_saturating_of_le (Fin (m + 1)) R (GrSum (hx ⊤))
    (GrSum.grading (hx ⊤)) 1 (fun _ => 0) (fun _ => g) (fun _ => hg)
    (fun i y => by
      obtain ⟨-, r, hr, hπ⟩ := hs.2 i
      obtain ⟨hi, ε, -, hker, hε⟩ :=
        GlobalTheory.T.exists_dehomogenisation_twisted_chart R Y f H m s _ hH (Inh.trivLB_isLB Y) hs hx i r hr
      exact exists_X_pow_smul_mem_span_of_dehomogenisation (GrSum.grading (hx ⊤)) i hπ
        ((MvPolynomial.eval₂Hom_X' _ _ i).trans hi) ε hker hg
        (fun z => by rw [hε]; exact exists_eq_smul_restrict_one hH _ z) _
        (Submodule.subset_span (Set.mem_range_self (f := fun _ : Fin 1 => g) 0)) y)
    (grSum_eq_zero_of_X_pow_smul f s _ hs.1)
  refine ⟨n₀.toNat, fun t ht σ => ?_⟩
  have hσ := GrSum.of_mem_grading (hx ⊤) t (SecOnR.of f _ ⊤ (twTrivOfSec σ))
  have hm := hn₀ t (by omega) _ hσ
  rw [Set.range_const, LinearMap.span_singleton_eq_range] at hm
  have hgr : IsGradedMap (polyGrading (Fin (m + 1)) R) (GrSum.grading (hx ⊤))
      (LinearMap.toSpanSingleton (MvPolynomial (Fin (m + 1)) R) _ g) := fun n p hp => by
    have := grSMul_mem (GrSum.grading (hx ⊤)) hp hg
    rwa [zero_add] at this
  obtain ⟨F, hF, e⟩ := hgr.exists_mem_of_mem_range hσ hm
  refine ⟨F, mem_polyGrading_natCast.1 hF, fun k => ?_⟩
  obtain ⟨y', hy', hc⟩ := exists_smul_of_twCoord R Y f H m s _ hx ⊤ F t 0 t
    (twZeroTrivEquiv hH ⊤ 1) hF (zero_add _).symm
  have hyy : twTrivOfSec σ = y' := GrSum.of_injective (hx ⊤) t (e.symm.trans hy')
  have h := hc PUnit.unit k
  rw [← hyy, twCoord_twZeroTrivEquiv_one hH ⊤ PUnit.unit k, _root_.mul_one] at h
  have h' := congrArg (rs Y (le_inf le_top (le_inf le_top le_rfl) : H.U k ≤ ⊤ ⊓ (⊤ ⊓ H.U k))) h
  exact ((rs_rs _ _ _).trans (rs_self _ _)).symm.trans (h'.trans ((rs_rs _ _ _).trans (rs_self _ _)))

end AbLaw

end GlobalTheory
