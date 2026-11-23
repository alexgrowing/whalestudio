import Mathlib

namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

variable {R₀ B K : Type} [CommRing R₀] [CommRing B] [Field K] [Algebra R₀ B]
  [Algebra B K] [Algebra R₀ K] [IsScalarTower R₀ B K]

def derOf (h : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0) : Derivation R₀ B K :=
  Derivation.mk'
    { toFun := fun b => (h b).snd
      map_add' := fun x y => by simp
      map_smul' := fun a b => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, snd_mul, hc, hfst, smul_zero, add_zero, smul_eq_mul,
          ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, snd_mul, hfst, Algebra.smul_def,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, Algebra.algebraMap_self,
        RingHom.id_apply]
      ring)

@[simp] lemma derOf_apply (h : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0) (b : B) :
    derOf h hfst hc b = (h b).snd := rfl

lemma derOf_injective (h h' : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0)
    (hfst' : ∀ b, (h' b).fst = algebraMap B K b)
    (hc' : ∀ a : R₀, (h' (algebraMap R₀ B a)).snd = 0)
    (e : derOf h hfst hc = derOf h' hfst' hc') : h = h' := by
  ext b
  · rw [hfst, hfst']
  · have := congrArg (fun D : Derivation R₀ B K => D b) e
    simpa using this

lemma derivation_eq_of_basis {ι : Type} (e : Module.Basis ι B Ω[B⁄R₀]) (D D' : Derivation R₀ B K)
    (h : ∀ j, D.liftKaehlerDifferential (e j) = D'.liftKaehlerDifferential (e j)) : D = D' := by
  have : D.liftKaehlerDifferential = D'.liftKaehlerDifferential := e.ext h
  rw [← Derivation.liftKaehlerDifferential_comp D, ← Derivation.liftKaehlerDifferential_comp D', this]

lemma liftKaehler_eq_sum {ι : Type} [Fintype ι] (D : Derivation R₀ B K) (Ds : ι → Derivation R₀ B K)
    (c : ι → K) (h : ∀ x, D x = ∑ i, c i * Ds i x) (ω : Ω[B⁄R₀]) :
    D.liftKaehlerDifferential ω = ∑ i, c i * (Ds i).liftKaehlerDifferential ω := by
  let φ : Ω[B⁄R₀] →ₗ[B] K :=
    { toFun := fun ω => ∑ i, c i * (Ds i).liftKaehlerDifferential ω
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun b x => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have : D.liftKaehlerDifferential = φ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [φ, Derivation.liftKaehlerDifferential_comp_D, h]
  rw [this]; rfl

end FirstOrderPoints

end GlobalTheory

namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

theorem exists_linearCombination_eq :
    ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  intro R₀ B K _ _ _ _ n hsm ι _ hcard R hR hinj g hgfst hg
  classical
  haveI : Algebra.IsStandardSmooth R₀ B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let ρ : B →+* K := (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R
  letI : Algebra B K := ρ.toAlgebra
  letI : Algebra R₀ K := (ρ.comp (algebraMap R₀ B)).toAlgebra
  haveI : IsScalarTower R₀ B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := ρ.domain_nontrivial
  have hfin : Module.finrank B Ω[B⁄R₀] = n := by
    have := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R₀) (S := B) n
    rw [← Module.finrank_eq_rank] at this
    exact_mod_cast this
  let e := Module.finBasisOfFinrankEq B Ω[B⁄R₀] hfin
  let hM : (ι → K) → B →+* DualNumber K := fun M =>
    (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R
  have hMfst : ∀ M b, (hM M b).fst = algebraMap B K b := fun M b => by
    simp [hM, ρ, RingHom.algebraMap_toAlgebra]
  have hR0 : ∀ a : R₀, (R (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hR a)
    simpa using this
  have hMc : ∀ M (a : R₀), (hM M (algebraMap R₀ B a)).snd = 0 := fun M a => by
    simp [hM, hR0 a]
  let D : (ι → K) → Derivation R₀ B K := fun M => derOf (hM M) (hMfst M) (hMc M)
  have hD : ∀ M x, D M x = ∑ i, M i * D (Pi.single i 1) x := by
    intro M x
    simp [D, hM, Fintype.linearCombination_apply, Pi.single_apply, mul_comm]
  let w : ι → (Fin n → K) := fun i j => (D (Pi.single i 1)).liftKaehlerDifferential (e j)
  let L := Fintype.linearCombination K w
  have hL : ∀ M, L M = fun j => (D M).liftKaehlerDifferential (e j) := by
    intro M
    funext j
    rw [liftKaehler_eq_sum (D M) (fun i => D (Pi.single i 1)) M (hD M)]
    simp [L, w, Fintype.linearCombination_apply, Finset.sum_apply]
  have Linj : Function.Injective L := by
    intro M M' hMM
    apply hinj
    apply derOf_injective (hM M) (hM M') (hMfst M) (hMc M) (hMfst M') (hMc M')
    apply derivation_eq_of_basis e
    intro j
    rw [hL, hL] at hMM
    exact congrFun hMM j
  have Lsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hcard])).mp Linj
  have hgfst' : ∀ b, (g b).fst = algebraMap B K b := fun b => hgfst b
  have hgc : ∀ a : R₀, (g (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hg a)
    simpa using this
  obtain ⟨M, hMeq⟩ := Lsurj (fun j => (derOf g hgfst' hgc).liftKaehlerDifferential (e j))
  refine ⟨M, ?_⟩
  refine derOf_injective g (hM M) hgfst' hgc (hMfst M) (hMc M) ?_
  apply derivation_eq_of_basis e
  intro j
  rw [hL] at hMeq
  exact (congrFun hMeq j).symm

end FirstOrderPoints

end GlobalTheory
