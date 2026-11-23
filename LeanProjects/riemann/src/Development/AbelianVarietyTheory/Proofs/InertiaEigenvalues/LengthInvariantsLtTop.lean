import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLen
import Formalism.LocalRingCardinality.Lemmas

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem length_quot_ne_top [IsDiscreteValuationRing O] (a : O) (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  exact ENat.coe_ne_top n

theorem fix_frac_zero {Γ : Type} {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) O)
    (hker : ∀ v : Fin r → O, (∀ g, (M g).mulVec v = v) → v = 0)
    (x : Fin r → FractionRing O) (hx : ∀ g, ((M g).map (algebraMap O (FractionRing O))).mulVec x = x) :
    x = 0 := by
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose u hu using hbi
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hu' : (fun j => algebraMap O (FractionRing O) (u j)) = algebraMap O (FractionRing O) b • x := by
    funext j; rw [hu j]; simp [Algebra.smul_def]
  have h0 : u = 0 := by
    refine hker u fun g => ?_
    funext j
    apply hinj
    rw [RingHom.map_mulVec]
    show ((M g).map (algebraMap O (FractionRing O))).mulVec (fun j => algebraMap O (FractionRing O) (u j)) j = _
    rw [hu', Matrix.mulVec_smul, hx g]
    exact (congrFun hu' j).symm
  have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => nonZeroDivisors.ne_zero hb (hinj h)
  have : algebraMap O (FractionRing O) b • x = 0 := by
    rw [← hu', h0]; funext j; simp
  exact (smul_eq_zero.mp this).resolve_left hb0

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem exists_finset_ker {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Γ → V →ₗ[K] V) (h : ∀ x, (∀ g, f g x = 0) → x = 0) :
    ∃ s : Finset Γ, ∀ x, (∀ g ∈ s, f g x = 0) → x = 0 := by
  classical
  let S : Set (Submodule K V) := Set.range fun s : Finset Γ => ⨅ g ∈ s, LinearMap.ker (f g)
  obtain ⟨p, ⟨s, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min S ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨s, fun x hx => h x fun g => ?_⟩
  have hle : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) ≤ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    rw [Finset.iInf_insert]; exact inf_le_right
  have heq : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) = ⨅ g' ∈ s, LinearMap.ker (f g') := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hxs : x ∈ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]; exact hx
  rw [← heq] at hxs
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hxs
  exact hxs g (Finset.mem_insert_self g s)

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_killer {ι : Type} [Fintype ι] {r : ℕ} (A : ι → Matrix (Fin r) (Fin r) O)
    (h : ∀ x : Fin r → FractionRing O, (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x = 0) → x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ x : Fin r → FractionRing O,
      (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x ∈ stdG O (FractionRing O) r) →
        c • x ∈ stdG O (FractionRing O) r := by
  classical
  set K := FractionRing O
  have hinj := IsFractionRing.injective O K
  let B : Matrix (ι × Fin r) (Fin r) K := fun p j => algebraMap O K (A p.1 p.2 j)
  have hB : ∀ x p, (B.mulVec x) p = (((A p.1).map (algebraMap O K)).mulVec x) p.2 := fun _ _ => rfl
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    refine h x fun q => ?_
    funext i
    rw [← hB x (q, i), hx]; rfl
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set P' := LinearMap.toMatrix' P
  have hPB : P' * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hP, LinearMap.toMatrix'_id]
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin r × (ι × Fin r) => P' p.1 p.2)
  choose Q hQ using hbi
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  choose y hy using hx
  let Y : ι × Fin r → O := fun p => y p.1 p.2
  have hY : (fun p => algebraMap O K (Y p)) = B.mulVec x := by
    funext p
    rw [hB]
    exact congrFun (hy p.1) p.2
  refine ⟨(Matrix.of fun j p => Q (j, p)).mulVec Y, ?_⟩
  funext j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
  rw [RingHom.map_mulVec]
  have hQ' : (Matrix.of fun j p => Q (j, p)).map (algebraMap O K) = algebraMap O K b • P' := by
    ext j p
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ (j, p), Algebra.smul_def]
  have hYf : (⇑(algebraMap O K) ∘ Y) = B.mulVec x := hY
  rw [hQ', hYf, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec, Pi.smul_apply,
    Pi.smul_apply, algebraMap_smul]

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem stdG_eq_span (r : ℕ) :
    stdG O (FractionRing O) r = Submodule.span O (Set.range fun j : Fin r => (Pi.single j 1 : Fin r → FractionRing O)) := by
  ext x
  rw [Submodule.mem_span_range_iff_exists_fun]
  show x ∈ LinearMap.range _ ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem WKG_mk {Γ : Type} [Group Γ] {r : ℕ} (M : Γ →* Matrix (Fin r) (Fin r) O) (g : Γ) (x : Fin r → FractionRing O) :
    WKG M g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((M g).map (algebraMap O (FractionRing O))).mulVec x) := rfl

theorem length_invariants_lt_top [IsDiscreteValuationRing O] {Γ Γ' : Type} [Group Γ] [Group Γ'] {r : ℕ}
    (M : Γ →* Matrix (Fin r) (Fin r) O) (f : Γ' →* Γ)
    (hker : ∀ v : Fin r → O, (∀ g, (M (f g)).mulVec v = v) → v = 0) :
    Module.length O ↥(Representation.invariants ((WKG M).comp f)) < ⊤ := by
  classical
  set K := FractionRing O
  let A : Γ' → Matrix (Fin r) (Fin r) O := fun g => M (f g) - 1
  have hAm : ∀ g, (A g).map (algebraMap O K) = (M (f g)).map (algebraMap O K) - 1 := by
    intro g
    show (algebraMap O K).mapMatrix (M (f g) - 1) = _
    rw [map_sub, map_one]; rfl
  have hK : ∀ x : Fin r → K, (∀ g, ((A g).map (algebraMap O K)).mulVec x = 0) → x = 0 := by
    intro x hx
    refine fix_frac_zero (fun g => M (f g)) hker x fun g => ?_
    have := hx g
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  obtain ⟨s, hs⟩ := exists_finset_ker (fun g => Matrix.toLin' ((A g).map (algebraMap O K)))
    (fun x hx => hK x fun g => by simpa [Matrix.toLin'_apply] using hx g)
  obtain ⟨c, hc0, hc⟩ := exists_killer (fun q : s => A q.1)
    (fun x hx => hs x fun g hg => by simpa [Matrix.toLin'_apply] using hx ⟨g, hg⟩)
  have hinj := IsFractionRing.injective O K
  have ha : algebraMap O K c ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K)]
    exact fun h => hc0 (hinj h)
  have hW : ∀ x ∈ Representation.invariants ((WKG M).comp f), c ^ 1 • x = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine hc x fun q => ?_
    have h1 := hx q.1
    rw [MonoidHom.comp_apply, WKG_mk, Submodule.Quotient.eq] at h1
    show ((A q.1).map (algebraMap O K)).mulVec x ∈ _
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hle := length_le_of_killed (LL := K) (stdG O K r) _ (stdG_eq_span r) c ha 1 _ hW
  have hL := length_quot_ne_top c hc0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hL
  refine lt_of_le_of_lt hle ?_
  rw [← hm]
  norm_cast
  exact ENat.coe_lt_top _

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG2 i r ρ π → ∀ w ∈ placesOver D.host.E (D.nd.l i), Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))) < ⊤ := by
  intro D i r ρ π hG2 w hw
  have hH0 := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.2.2.2.2.1
  show Module.length _ ↥(Representation.invariants ((WKG (WpO D.nd i ρ π)).comp (decS D.nd w))) < ⊤
  refine length_invariants_lt_top (WpO D.nd i ρ π) (decS D.nd w) fun v hv => ?_
  set C := TruncatedSeriesCountingIdentities.CoefExt.self i w hw
  set Bw := D.nbr i w hw
  let φ : D.nd.O i →+* ↥C.LL.1 :=
    (TruncatedSeriesCountingIdentities.CoefExt.inc C).comp ((algebraMap (Br.Ow Bw) (Br.LLw Bw)).comp Bw.eO.toRingHom)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := (TruncatedSeriesCountingIdentities.CoefExt.inc C).injective hab
    exact Br.toLL_inj Bw h1
  have hloc : ∀ gK, TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) gK = (WpO D.nd i ρ π (decS D.nd w (Br.ι Bw gK))).map φ := fun _ => rfl
  have hmem : (fun j => φ (v j)) ∈ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    intro gK
    rw [sub_eq_zero]
    show Matrix.toLinAlgEquiv' _ _ = _
    rw [Matrix.toLinAlgEquiv'_apply, hloc]
    funext j
    rw [show (fun j => φ (v j)) = ⇑φ ∘ v from rfl, ← RingHom.map_mulVec, hv]
  rw [hH0, Submodule.mem_bot] at hmem
  funext j
  exact hφ (by simpa using congrFun hmem j)

end GlobalTheory.FiniteTwistInvariants
