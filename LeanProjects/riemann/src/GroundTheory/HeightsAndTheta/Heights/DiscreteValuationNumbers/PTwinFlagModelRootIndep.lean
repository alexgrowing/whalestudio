import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModelRootIndep

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

theorem monoList_eq_flatten {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) :
    monoList deg μ = (List.ofFn fun s => List.replicate (μ s) (deg s)).flatten := by
  simp [monoList, List.flatMap, List.ofFn_eq_map]

theorem monoList_mapDomain {m : ℕ} {A : Type*} (deg : Fin ((m + 1) + (m + 1)) → A) (ν : Fin m →₀ ℕ) :
    monoList deg (Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν) =
      monoList (deg ∘ fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν := by
  have he : Function.Injective (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) :=
    fun i j h => Fin.castSucc_injective m ((Fin.natAdd_inj (m + 1)).mp h)
  have h1 : ∀ i : Fin (m + 1), Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν
      (Fin.castLE (Nat.le_add_right (m + 1) (m + 1)) i) = 0 :=
    fun i => Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp at this
      omega)
  have h2 : Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν
      (Fin.natAdd (m + 1) (Fin.last m)) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp at this
      omega)
  have h3 : ∀ i : Fin m, Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν
      (Fin.natAdd (m + 1) i.castSucc) = ν i :=
    fun i => Finsupp.mapDomain_apply he ν i
  have hA : (List.ofFn fun i : Fin (m + 1) =>
      List.replicate (Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν
        (Fin.castLE (Nat.le_add_right (m + 1) (m + 1)) i))
        (deg (Fin.castLE (Nat.le_add_right (m + 1) (m + 1)) i))).flatten = [] := by
    simp only [h1, List.replicate_zero]
    simp
  have hB : (List.ofFn fun i : Fin (m + 1) =>
      List.replicate (Finsupp.mapDomain (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) ν (Fin.natAdd (m + 1) i))
        (deg (Fin.natAdd (m + 1) i))).flatten =
      (List.ofFn fun s => List.replicate (ν s) ((deg ∘ fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) s)).flatten := by
    rw [List.ofFn_succ']
    simp only [h2, h3, List.replicate_zero, List.concat_eq_append, List.flatten_append, Function.comp]
    simp
  rw [monoList_eq_flatten, monoList_eq_flatten, List.ofFn_add, List.flatten_append, hA, hB, List.nil_append]

theorem polyNum_rename {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : IFamily F κ) (W : Ideal (MRingOver F κ)) (n : ℕ) {m r : ℕ} (deg : Fin r → K → ℤ)
    (e : Fin m → Fin r) (he : Function.Injective e)
    (hl : ∀ ν, monoList deg (Finsupp.mapDomain e ν) = monoList (deg ∘ e) ν) (P : MvPolynomial (Fin m) ℤ) :
    polyNum I W n deg (rename e P) = polyNum I W n (deg ∘ e) P := by
  classical
  unfold polyNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 1
  exact congrArg (fun l : List (K → ℤ) => if h : l.length = n then I W n (fun j => l.get (Fin.cast h.symm j))
    else 0) (hl ν)

theorem divDiff_last {m : ℕ} (P : MvPolynomial (Fin m) ℤ) :
    divDiff (Fin.last m) (rename Fin.castSucc P * X (Fin.last m)) =
      rename (fun i : Fin m => Fin.natAdd (m + 1) i.castSucc) P := by
  classical
  have hcs : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) := Fin.castSucc_injective m
  unfold divDiff
  rw [support_mul_X, support_rename_of_injective hcs, Finset.sum_map,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hcs h]
  conv_rhs => rw [P.as_sum, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hl : Finsupp.mapDomain Fin.castSucc ν (Fin.last m) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨j, hj⟩
      exact (Fin.castSucc_lt_last j).ne hj)
  have hc : ∀ i : Fin m, Finsupp.mapDomain Fin.castSucc ν i.castSucc = ν i :=
    fun i => Finsupp.mapDomain_apply hcs ν i
  have hs : ∀ i : Fin m, Finsupp.single (Fin.last m) 1 i.castSucc = 0 := fun i => by
    rw [Finsupp.single_apply, if_neg (Fin.castSucc_lt_last i).ne']
  have hemp : (Finset.univ.filter fun j : Fin (m + 1) => Fin.last m < j) = ∅ :=
    Finset.filter_false_of_mem fun j _ => not_lt.mpr (Fin.le_last j)
  simp only [addRightEmbedding_apply, coeff_mul_X, coeff_rename_mapDomain _ hcs, Finsupp.add_apply,
    Finsupp.single_eq_same, hl, zero_add, hemp, Finset.prod_empty, mul_one, Finset.range_one,
    Finset.sum_singleton, pow_zero, Nat.sub_self, Nat.zero_sub]
  rw [Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_last, if_true, lt_irrefl, if_false, mul_one, hc, hs, add_zero]
  rw [monomial_eq, map_mul, rename_C, Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
  simp only [map_pow, rename_X]

theorem divCycle_one {R : Type*} [CommRing R] [IsNoetherianRing R] {K : Type} [Fintype K] {κ : K → Type}
    [∀ k, Fintype (κ k)] (P : Ideal (MRingOver R κ)) : divCycle P 1 = 0 := by
  classical
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
  rw [if_neg]
  rintro ⟨h, -⟩
  rw [Ideal.span_singleton_one, sup_top_eq, Ideal.minimalPrimes_top] at h
  exact h

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem isVertDiv_C {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    {P : Ideal (MRingOver O κ)} (hP : P.IsPrime) (hflat : P.comap (C : O →+* MRingOver O κ) = ⊥)
    {c : O} (hc : c ≠ 0) : IsVertDiv O P 0 (C c) 1 := by
  have h1 : IsMultiHomog (1 : MRingOver O κ) 0 := by simpa using isMultiHomog_C O (ι := κ) (1 : O)
  have hnot : ∀ Q : Ideal (MRingOver O κ), Q.comap (C : O →+* MRingOver O κ) = ⊥ → C c ∉ Q := by
    intro Q hQ h
    have : c ∈ Q.comap (C : O →+* MRingOver O κ) := h
    rw [hQ, Ideal.mem_bot] at this
    exact hc this
  refine ⟨⟨0, 0, isMultiHomog_C O c, h1, by simp⟩, hnot P hflat,
    fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h), fun Q hQ _ hQf =>
      ⟨1, C c, ⟨0, h1⟩, ⟨0, isMultiHomog_C O c⟩,
        fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h), hnot Q hQf, by simp⟩⟩

variable {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def selfPair {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (φ : FlagPair O x E E') (hP : (mcIdeal O x).IsPrime)
    (hflat : (mcIdeal O x).comap (C : O →+* MRingOver O ι) = ⊥) : FlagPair O x E E :=
  { φ.toFullFlag with
    deg' := φ.deg
    gen' := φ.gen
    gen'_mem := φ.gen_mem
    frame' := φ.frame
    f := fun _ => 1
    g := fun _ => 1
    rel := fun i => by simp
    vert := fun i => by
      rw [sub_self]
      simpa using isVertDiv_C hP hflat (one_ne_zero : (1 : O) ≠ 0) }

def selfModel {x : (Σ k, ι k) → Ω} {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (F : FlagModel O x d N E E') : FlagModel O x d N E E where
  K' := F.K'
  ι' := F.ι'
  z := F.z
  model := F.model
  birat := F.birat
  EB := F.EB
  E'B := F.EB
  pull := F.pull
  pull' := F.pull
  flag := selfPair F.flag F.model.2.1.1 F.model.2.2.1

theorem append_snoc_castSucc {N q : ℕ} {K₁ K' : Type} (u : Fin N → K₁ ⊕ K' → ℤ) (L : Fin q → K₁ → ℤ)
    (s : Fin (N + q)) :
    Fin.append u (fun l => pullDeg (K' := K') (Fin.snoc (α := fun _ => K₁ → ℤ) L 0 l)) s.castSucc =
      Fin.append u (fun l => pullDeg (K' := K') (L l)) s := by
  induction s using Fin.addCases with
  | left i =>
    rw [show (Fin.castAdd q i).castSucc = Fin.castAdd (q + 1) i from Fin.ext rfl, Fin.append_left,
      Fin.append_left]
  | right j =>
    rw [show (Fin.natAdd N j).castSucc = Fin.natAdd N j.castSucc from Fin.ext rfl, Fin.append_right,
      Fin.append_right, Fin.snoc_castSucc]

theorem polyNum_divDiff_last {F : Type*} [Field F] {K₀ : Type} [Fintype K₀] {κ : K₀ → Type}
    [∀ k, Fintype (κ k)] (I : IFamily F κ) (W : Ideal (MRingOver F κ)) (n : ℕ) {N q : ℕ}
    (A : Fin (N + (q + 1)) → K₀ → ℤ) (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) :
    polyNum I W n (Fin.append A A) (divDiff (Fin.natAdd N (Fin.last q))
        (rename (Fin.castAdd (q + 1)) G * rename (Fin.natAdd N) (rename Fin.castSucc Q * X (Fin.last q)))) =
      polyNum I W n (fun s => A s.castSucc) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) := by
  have hH : (rename (Fin.castAdd (q + 1)) G * rename (Fin.natAdd N) (rename Fin.castSucc Q * X (Fin.last q)) :
      MvPolynomial (Fin (N + (q + 1))) ℤ) =
      rename Fin.castSucc (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) * X (Fin.last (N + q)) := by
    have e1 : (Fin.castSucc ∘ Fin.castAdd q : Fin N → Fin (N + q + 1)) = Fin.castAdd (q + 1) :=
      funext fun i => Fin.ext rfl
    have e2 : (Fin.castSucc ∘ Fin.natAdd N : Fin q → Fin (N + q + 1)) = Fin.natAdd N ∘ Fin.castSucc :=
      funext fun i => Fin.ext rfl
    have e3 : (Fin.natAdd N (Fin.last q) : Fin (N + q + 1)) = Fin.last (N + q) := Fin.ext rfl
    rw [map_mul, map_mul, rename_X, rename_rename, rename_rename, rename_rename, e1, e2, e3, mul_assoc]
  have hD : divDiff (Fin.natAdd N (Fin.last q))
      (rename (Fin.castAdd (q + 1)) G * rename (Fin.natAdd N) (rename Fin.castSucc Q * X (Fin.last q))) =
      rename (fun i : Fin (N + q) => Fin.natAdd (N + (q + 1)) i.castSucc)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) := by
    rw [hH]
    exact divDiff_last _
  rw [hD]
  refine (polyNum_rename I W n (Fin.append A A) (fun i : Fin (N + q) => Fin.natAdd (N + (q + 1)) i.castSucc)
    (fun i j h => Fin.castSucc_injective _ ((Fin.natAdd_inj _).mp h))
    (fun ν => monoList_mapDomain (m := N + q) (Fin.append A A) ν) _).trans ?_
  congr 1
  funext s
  exact Fin.append_right A A s.castSucc

theorem value_self {x : (Σ k, ι k) → Ω} {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (F : FlagModel O x d N E E')
    (I : IFamily (kap O) (Sum.elim ι F.ι')) (G : MvPolynomial (Fin N) ℤ) {q : ℕ} (L : Fin q → K → ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (a : O) :
    (selfModel F).value O I G (Fin.snoc (α := fun _ => K → ℤ) L 0) (Fin.snoc (α := fun _ => K → ℤ) L 0)
        (fun l => C (Fin.snoc (α := fun _ => O) (fun _ => 1) a l)) (fun _ => 1)
        (rename Fin.castSucc Q * X (Fin.last q)) =
      vEval O (fun W => polyNum I W d (Fin.append F.flag.deg fun l => pullDeg (K' := F.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle (mcIdeal O (joinCoord x F.z)) (C a))) := by
  have h0 : ∀ (J : Ideal (MRingOver (kap O) (Sum.elim ι F.ι')) → ℤ)
      (h : MRingOver O (Sum.elim ι F.ι')), vEval O J (ratCyc O (mcIdeal O (joinCoord x F.z)) h h) = 0 := by
    intro J h
    rw [ratCyc, sub_self, vEval, Finsupp.sum_zero_index]
  simp only [FlagModel.value, pairNum, selfModel, selfPair]
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last]
  have e : ∀ u v w t : ℤ, u = 0 → v = 0 → w = t → u + (v + w) = t := by
    intro u v w t hu hv hw
    rw [hu, hv, hw, zero_add, zero_add]
  have hr : ratCyc O (mcIdeal O (joinCoord x F.z)) (rename (liftVar F.ι') (C a)) (rename (liftVar F.ι') 1) =
      Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle (mcIdeal O (joinCoord x F.z)) (C a)) := by
    rw [ratCyc, rename_C, map_one, divCycle_one, Finsupp.mapRange_zero, sub_zero]
  refine e _ _ _ _ (Finset.sum_eq_zero fun i _ => h0 _ _) (Finset.sum_eq_zero fun j _ => h0 _ _) ?_
  refine (congrArg (vEval O _) hr).trans (congrArg (fun J => vEval O J _) (funext fun W => ?_))
  refine (polyNum_divDiff_last I W d _ G Q).trans ?_
  congr 1
  funext s
  exact append_snoc_castSucc _ _ s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModelRootIndep

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModelRootIndep (selfModel value_self isVertDiv_C)

theorem FlagModelRootIndependence.proof (h : FlagModelValueIndependence.Statement) :
    FlagModelRootIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW _ F₁ F₂ I₁ I₂ hI₁ hI₂ c G hsym hG hcd q L Q hQ a ha
  have hsame : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have hvert : ∀ l : Fin (q + 1), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x)
      (Fin.snoc (α := fun _ => K → ℤ) L 0 l - Fin.snoc (α := fun _ => K → ℤ) L 0 l)
      (C (Fin.snoc (α := fun _ => O) (fun _ => 1) a l)) 1 := by
    intro l
    rw [sub_self]
    refine isVertDiv_C hW.2.1.1 hW.2.2.1 ?_
    induction l using Fin.lastCases with
    | last => simpa using ha
    | cast j => simp
  have hQ' : (rename Fin.castSucc Q * X (Fin.last q) : MvPolynomial (Fin (q + 1)) ℤ).IsHomogeneous
      (d + 1 - c) := by
    rw [show d + 1 - c = d - c + 1 by omega]
    exact (hQ.rename_isHomogeneous).mul (isHomogeneous_X ℤ (Fin.last q))
  have key := h O Ω K ι x d N V E E hW hsame (selfModel F₁) (selfModel F₂) I₁ I₂ hI₁ hI₂ G hsym (q + 1)
    (Fin.snoc (α := fun _ => K → ℤ) L 0) (Fin.snoc (α := fun _ => K → ℤ) L 0)
    (fun l => C (Fin.snoc (α := fun _ => O) (fun _ => 1) a l)) (fun _ => 1) hvert c
    (rename Fin.castSucc Q * X (Fin.last q)) (by omega) hG hQ'
  exact (value_self F₁ I₁ G L Q a).symm.trans (key.trans (value_self F₂ I₂ G L Q a))

end GroundTheory.Heights₂.Heights.NumbersDVR
