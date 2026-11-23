import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StandardLattice

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB

open NumberField
open scoped Matrix

def pZ (l : ℕ) : Ideal ℤ := Ideal.span {(l : ℤ)}

variable (l : ℕ) [hl : Fact l.Prime]

instance pZ_isPrime : (pZ l).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)

theorem pZ_ne_bot : pZ l ≠ ⊥ := by
  unfold pZ
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hl.out.ne_zero

theorem mem_pZ_iff (z : ℤ) : z ∈ pZ l ↔ (l : ℤ) ∣ z := Ideal.mem_span_singleton

variable (K : Type) [Field K] [NumberField K]

abbrev Ml : Submonoid (𝓞 K) := Algebra.algebraMapSubmonoid (𝓞 K) (pZ l).primeCompl

abbrev Rl : Type := Localization (Ml l K)

variable {l K}

theorem mem_Ml_iff (s : 𝓞 K) : s ∈ Ml l K ↔ ∃ z : ℤ, ¬ (l : ℤ) ∣ z ∧ algebraMap ℤ (𝓞 K) z = s := by
  unfold Ml Algebra.algebraMapSubmonoid
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, fun h => hz ((mem_pZ_iff l z).2 h), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, fun h => hz ((mem_pZ_iff l z).1 h), rfl⟩

theorem natCast_mem_Ml {s : ℕ} (hs : ¬ l ∣ s) : (s : 𝓞 K) ∈ Ml l K :=
  (mem_Ml_iff _).2 ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩

theorem zero_notMem_Ml : (0 : 𝓞 K) ∉ Ml l K := by
  intro h
  obtain ⟨z, hz, h0⟩ := (mem_Ml_iff _).1 h
  have : z = 0 := (algebraMap ℤ (𝓞 K)).injective_int (h0.trans (map_zero _).symm)
  exact hz (this ▸ dvd_zero _)

variable (l K)

theorem Ml_le : Ml l K ≤ nonZeroDivisors (𝓞 K) := le_nonZeroDivisors_of_noZeroDivisors zero_notMem_Ml

instance Rl_isDomain : IsDomain (Rl l K) := IsLocalization.isDomain_localization (Ml_le l K)

def rlToK : Rl l K →+* K :=
  IsLocalization.lift (M := Ml l K) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ ?_
    intro h
    have h0 : (y : 𝓞 K) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [h, map_zero]
    exact zero_notMem_Ml (h0 ▸ y.2))

instance rlAlgebra : Algebra (Rl l K) K := (rlToK l K).toAlgebra

instance rlTower : IsScalarTower (𝓞 K) (Rl l K) K :=
  IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq _ x).symm)

instance rlFrac : IsFractionRing (Rl l K) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ml l K) (Rl l K) K

instance rlDedekind : IsDedekindDomain (Rl l K) :=
  IsLocalization.isDedekindDomain (𝓞 K) (Ml_le l K) (Rl l K)

theorem rl_pid : IsPrincipalIdealRing (Rl l K) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) (pZ l) (pZ_ne_bot l)

theorem algebraMap_rl_injective : Function.Injective (algebraMap (Rl l K) K) :=
  IsFractionRing.injective (Rl l K) K

theorem mem_range_rl_iff (y : K) :
    y ∈ (algebraMap (Rl l K) K).range ↔ ∃ s : ℕ, ¬ l ∣ s ∧ (s : K) * y ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨a, ⟨m, hm⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Ml l K) r
    obtain ⟨z, hz, rfl⟩ := (mem_Ml_iff _).1 hm
    have key : (z : K) * algebraMap (Rl l K) K (IsLocalization.mk' (Rl l K) a ⟨_, hm⟩) = algebraMap (𝓞 K) K a := by
      have h1 := IsLocalization.mk'_spec (Rl l K) a ⟨_, hm⟩
      have h2 := congrArg (algebraMap (Rl l K) K) h1
      rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K a,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K] at h2
      have h5 : algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) z) = (z : K) := by simp
      rw [← h2, mul_comm]
      congr 1
    refine ⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq z with h | h
    · have e : ((z.natAbs : ℕ) : K) = (z : K) := by
        have e' : ((z.natAbs : ℕ) : ℤ) = z := by omega
        rw [← Int.cast_natCast, e']
      rw [e, key]
      exact ⟨a, rfl⟩
    · have e : ((z.natAbs : ℕ) : K) = -(z : K) := by
        have e' : ((z.natAbs : ℕ) : ℤ) = -z := by omega
        rw [← Int.cast_natCast, e', Int.cast_neg]
      rw [e, neg_mul, key]
      exact ⟨-a, by simp⟩
  · rintro ⟨s, hs, a, ha⟩
    have hs0 : (s : K) ≠ 0 := by
      have : s ≠ 0 := fun h => hs (h ▸ dvd_zero l)
      exact_mod_cast this
    refine ⟨IsLocalization.mk' (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩, ?_⟩
    have h1 := IsLocalization.mk'_spec (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩
    have h2 := congrArg (algebraMap (Rl l K) K) h1
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at h2
    simp only [map_natCast] at h2
    apply mul_left_cancel₀ hs0
    rw [← h2, mul_comm]

section Mod

variable (V : Type) [AddCommGroup V] [Module K V]

@[reducible] def rlModule : Module (Rl l K) V := Module.compHom V (algebraMap (Rl l K) K)

attribute [local instance] rlModule

instance rlTowerK : IsScalarTower (Rl l K) K V :=
  ⟨fun r a x => by
    show (r • a) • x = algebraMap (Rl l K) K r • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩

instance rlTowerO [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : IsScalarTower (𝓞 K) (Rl l K) V :=
  ⟨fun r s x => by
    show algebraMap (Rl l K) K (r • s) • x = r • (algebraMap (Rl l K) K s • x)
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply, algebraMap_smul]⟩

instance rlTorsionFree : Module.IsTorsionFree (Rl l K) V :=
  Module.IsTorsionFree.of_smul_eq_zero (fun r x h => by
    change algebraMap (Rl l K) K r • x = 0 at h
    rcases smul_eq_zero.1 h with h | h
    · left
      exact algebraMap_rl_injective l K (by rw [h, map_zero])
    · exact Or.inr h)

variable {V} [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def atL (L : Submodule (𝓞 K) V) : Submodule (Rl l K) V := Submodule.span (Rl l K) (L : Set V)

theorem mem_atL_iff {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atL l K L ↔ ∃ s ∈ Ml l K, s • x ∈ L := by
  first | exact UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff .. | (apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (intros; apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› L x | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› L | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l

theorem atL_fg {L : Submodule (𝓞 K) V} (h : L.FG) : (atL l K L).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  unfold atL
  rw [← hS, Submodule.span_span_of_tower]

theorem le_atL (L : Submodule (𝓞 K) V) : (L : Set V) ⊆ atL l K L := Submodule.subset_span

theorem span_atL (L : Submodule (𝓞 K) V) :
    Submodule.span K (atL l K L : Set V) = Submodule.span K (L : Set V) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    have : atL l K L ≤ (Submodule.span K (L : Set V)).restrictScalars (Rl l K) :=
      Submodule.span_le.2 Submodule.subset_span
    exact this
  · exact Submodule.span_mono (le_atL l K L)

theorem exists_basis_atL {A : Submodule (𝓞 K) V} (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι (Rl l K) (atL l K A)) (bK : Module.Basis ι K V),
      ∀ i, bK i = (b i : V) := by
  have := rl_pid l K
  have : Module.Finite (Rl l K) (atL l K A) := Module.Finite.iff_fg.2 (atL_fg l K hfg)
  have : Module.Free (Rl l K) (atL l K A) := inferInstance
  let b := Module.Free.chooseBasis (Rl l K) (atL l K A)
  have hli : LinearIndependent (Rl l K) (fun i => ((b i : atL l K A) : V)) :=
    b.linearIndependent.map' (atL l K A).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atL l K A) : V)) :=
    (LinearIndependent.iff_fractionRing (Rl l K) K).1 hli
  have hs : Submodule.span (Rl l K) (Set.range fun i => ((b i : atL l K A) : V)) = atL l K A := by
    have h1 : (Set.range fun i => ((b i : atL l K A) : V)) = (atL l K A).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have key : ∀ S : Set V, Submodule.span (Rl l K) S = atL l K A → Submodule.span K S = ⊤ := fun S hS => by
    rw [← hsp, ← span_atL l K A, ← hS, Submodule.span_span_of_tower]
  exact ⟨_, inferInstance, b, Module.Basis.mk hliK (key _ hs).ge, fun i => Module.Basis.mk_apply _ _ i⟩

theorem mem_atL_iff_repr {A : Submodule (𝓞 K) V} {ι : Type} [Fintype ι] (b : Module.Basis ι (Rl l K) (atL l K A))
    (bK : Module.Basis ι K V) (hb : ∀ i, bK i = (b i : V)) (x : V) :
    x ∈ atL l K A ↔ ∀ i, bK.repr x i ∈ (algebraMap (Rl l K) K).range := by
  classical
  constructor
  · intro hx i
    have e : x = ∑ j, algebraMap (Rl l K) K (b.repr ⟨x, hx⟩ j) • bK j := by
      have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j]
      rfl
    rw [e, bK.repr_sum_self]
    exact ⟨_, rfl⟩
  · intro h
    choose r hr using h
    have e : x = ∑ j, r j • (b j : V) := by
      conv_lhs => rw [← bK.sum_repr x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hr j, hb j]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2

theorem mem_atL_iff_nat {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atL l K L ↔ ∃ s : ℕ, ¬ l ∣ s ∧ s • x ∈ L := by
  rw [mem_atL_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨z, hz, rfl⟩ := (mem_Ml_iff _).1 hs
    have e0 : algebraMap ℤ (𝓞 K) z • x = z • x := by
      rw [algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]
    rw [e0] at hx
    refine ⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq z with h | h
    · have e : z.natAbs • x = z • x := by
        conv_rhs => rw [h]
        rw [natCast_zsmul]
      rwa [e]
    · have e : z.natAbs • x = -(z • x) := by
        conv_rhs => rw [h]
        rw [neg_zsmul, natCast_zsmul, neg_neg]
      rw [e]
      exact L.neg_mem hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨(s : 𝓞 K), natCast_mem_Ml hs, ?_⟩
    rwa [Nat.cast_smul_eq_nsmul]

end Mod

section Vec

variable {n : ℕ}

theorem exists_isLocBasis (A : Submodule (𝓞 K) (Fin n → K)) (hfg : A.FG)
    (hsp : Submodule.span K (A : Set (Fin n → K)) = ⊤) :
    ∃ B : GL (Fin n) K, Formalism.L2.Forms.IsLocBasis l (A : Set (Fin n → K)) B := by
  classical
  let _ := rlModule l K (Fin n → K)
  obtain ⟨ι, hι, b, bK, hb⟩ := exists_basis_atL l K hfg hsp
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin n) K (Fin n → K) := bK.reindex e
  let b'' := b.reindex e
  have hb' : ∀ i, b' i = (b'' i : Fin n → K) := fun i => by
    simp only [b', b'', Module.Basis.reindex_apply]
    exact hb _
  let B : GL (Fin n) K :=
    ⟨(Pi.basisFun K (Fin n)).toMatrix b', b'.toMatrix (Pi.basisFun K (Fin n)),
      Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have key : ∀ x, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = b'.repr x := fun x => by
    show b'.toMatrix (Pi.basisFun K (Fin n)) *ᵥ x = _
    have hx : ((Pi.basisFun K (Fin n)).repr x : Fin n → K) = x := funext fun a => by simp
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun K (Fin n)) b' x
    rw [hx] at h
    exact h
  refine ⟨B, fun x => ?_⟩
  have h1 : (∃ s : ℕ, ¬ l ∣ s ∧ (s : K) • x ∈ A) ↔ x ∈ atL l K A := by
    rw [mem_atL_iff_nat]
    simp only [Nat.cast_smul_eq_nsmul]
  simp only [SetLike.mem_coe]
  rw [h1, mem_atL_iff_repr l K b'' b' hb']
  simp only [key]
  constructor
  · intro h
    choose s hs hy using fun a => (mem_range_rl_iff l K (b'.repr x a)).1 (h a)
    refine ⟨∏ a, s a, fun hd => ?_, fun a => ?_⟩
    · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hl.out.prime _).1 hd
      exact hs a ha
    · rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ a), mul_comm (s a), Nat.cast_mul, mul_assoc]
      obtain ⟨r, hr⟩ := hy a
      rw [← hr]
      exact ⟨((∏ b ∈ Finset.univ.erase a, s b : ℕ) : 𝓞 K) * r, by rw [map_mul, map_natCast]⟩
  · rintro ⟨s, hs, h⟩ a
    exact (mem_range_rl_iff l K _).2 ⟨s, hs, h a⟩

end Vec

section Bound

open Formalism.L2.DIV Formalism.L2.Col

variable {K} {n : ℕ}

def bnd (d : 𝓞 K) : Submodule (𝓞 K) (Fin n → K) := (colLat (1 : GL (Fin n) K)).comap (d • LinearMap.id)

theorem mem_bnd (d : 𝓞 K) (x : Fin n → K) :
    x ∈ bnd d ↔ ∀ a, algebraMap (𝓞 K) K d * x a ∈ (algebraMap (𝓞 K) K).range := by
  unfold bnd
  rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, lc_mem_colLat_one]
  refine forall_congr' fun a => ?_
  rw [lc_mem_one_iff, Pi.smul_apply, Algebra.smul_def, RingHom.mem_range]

theorem algebraMap_ne_zero {d : 𝓞 K} (hd : d ≠ 0) : algebraMap (𝓞 K) K d ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hd

theorem fg_of_le_bnd {L : Submodule (𝓞 K) (Fin n → K)} {d : 𝓞 K} (hd : d ≠ 0) (h : L ≤ bnd d) : L.FG := by
  have : IsNoetherian (𝓞 K) (colLat (1 : GL (Fin n) K)) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  let φ : L →ₗ[𝓞 K] colLat (1 : GL (Fin n) K) :=
    { toFun := fun x => ⟨d • (x : Fin n → K), h x.2⟩
      map_add' := fun x y => by ext1; simp [smul_add]
      map_smul' := fun a x => by ext1; simp [smul_comm d a] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : d • (x : Fin n → K) = d • (y : Fin n → K) := congrArg Subtype.val hxy
    rw [← algebraMap_smul K d (x : Fin n → K), ← algebraMap_smul K d (y : Fin n → K)] at h1
    exact Subtype.ext (smul_right_injective _ (algebraMap_ne_zero hd) h1)
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_injective φ hinj
  exact (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)

theorem bnd_mono (d e : 𝓞 K) : (bnd d : Submodule (𝓞 K) (Fin n → K)) ≤ bnd (e * d) := by
  intro x hx
  rw [mem_bnd] at hx ⊢
  intro a
  obtain ⟨r, hr⟩ := hx a
  exact ⟨e * r, by rw [map_mul, hr, map_mul, mul_assoc]⟩

theorem exists_le_bnd (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ L ≤ bnd d := by
  obtain ⟨d, hd, h1, -⟩ := lc_sandwich L hL
  exact ⟨d, hd, fun x hx => h1 x hx⟩

theorem sig_int (σ : K →+* K) (r : 𝓞 K) : ∃ r' : 𝓞 K, algebraMap (𝓞 K) K r' = σ (algebraMap (𝓞 K) K r) :=
  IsIntegralClosure.isIntegral_iff.1 ((NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom)

theorem sig_ne_zero (σ : K →+* K) {d : 𝓞 K} (hd : d ≠ 0) : σ (algebraMap (𝓞 K) K d) ≠ 0 :=
  (map_ne_zero_iff σ σ.injective).2 (algebraMap_ne_zero hd)

theorem dual_le_bnd (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (hJ : IsUnit J.det)
    (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ Submodule.span (𝓞 K) (Formalism.BasicNotions.dualSet σ J L) ≤ bnd d := by
  classical
  obtain ⟨d0, hd0, -, h2⟩ := lc_sandwich L hL
  obtain ⟨d0', hd0'⟩ := sig_int σ d0
  obtain ⟨d1, hd1⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin n × Fin n => J⁻¹ p.1 p.2)
  have hd0'0 : d0' ≠ 0 := by
    intro h
    apply sig_ne_zero σ hd0
    rw [← hd0', h, map_zero]
  refine ⟨(d1 : 𝓞 K) * d0', mul_ne_zero (nonZeroDivisors.ne_zero d1.2) hd0'0, Submodule.span_le.2 fun y hy => ?_⟩
  have hJy : ∀ a, σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a ∈ (algebraMap (𝓞 K) K).range := by
    intro a
    have hx : d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a) ∈ L :=
      h2 _ (lc_col_mem_colLat 1 a)
    have h3 := hy _ hx
    have e : Formalism.UG.hform σ J (d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a)) y =
        σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a := by
      unfold Formalism.UG.hform
      rw [Finset.sum_eq_single a]
      · simp only [Pi.smul_apply, Units.val_one, Matrix.one_apply_eq, Algebra.smul_def, mul_one, Matrix.mulVec,
          dotProduct, Finset.mul_sum, mul_assoc]
      · intro b _ hb
        simp [Matrix.one_apply, hb]
      · simp
    rw [← e]
    exact h3
  rw [SetLike.mem_coe, mem_bnd]
  intro a
  have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
  rw [ey, map_mul, hd0', Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun c _ => ?_
  obtain ⟨r, hr⟩ := hd1 (J⁻¹ a c) (Finset.mem_image.2 ⟨(a, c), Finset.mem_univ _, rfl⟩)
  obtain ⟨q, hq⟩ := hJy c
  refine ⟨r * q, ?_⟩
  rw [map_mul, hr, hq, Algebra.smul_def]
  ring

theorem dual_span (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    Submodule.span K ((Submodule.span (𝓞 K) (Formalism.BasicNotions.dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) :
      Set (Fin n → K)) = ⊤ := by
  classical
  obtain ⟨d0, hd0, h1, -⟩ := lc_sandwich L hL
  obtain ⟨d0', hd0'⟩ := sig_int σ d0
  have hd0'0 : d0' ≠ 0 := by
    intro h
    apply sig_ne_zero σ hd0
    rw [← hd0', h, map_zero]
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨e, he⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin n × Fin n => J p.1 p.2 * z p.2)
  set c : K := algebraMap (𝓞 K) K d0' * algebraMap (𝓞 K) K (e : 𝓞 K) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (algebraMap_ne_zero hd0'0) (algebraMap_ne_zero (nonZeroDivisors.ne_zero e.2))
  have hmem : c • z ∈ Formalism.BasicNotions.dualSet σ J L := by
    intro x hx
    have hx' := (lc_mem_colLat_one _).1 (h1 x hx)
    unfold Formalism.UG.hform
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := (lc_mem_one_iff _).1 (hx' i)
    obtain ⟨r', hr'⟩ := sig_int σ r
    obtain ⟨q, hq⟩ := he (J i j * z j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    refine ⟨r' * q, ?_⟩
    rw [map_mul, hr', hq, hr, Pi.smul_apply, Algebra.smul_def, map_mul, ← hd0', Pi.smul_apply, smul_eq_mul,
      Algebra.smul_def, hc]
    ring
  have e2 : z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hmem))

end Bound

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB
