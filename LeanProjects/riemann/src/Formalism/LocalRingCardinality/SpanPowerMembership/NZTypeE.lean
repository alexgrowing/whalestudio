import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain

theorem monicOf_injective {K : Type} [Field K] {N : ℕ} : Function.Injective (monicOf (K := K) (N := N)) := by
  intro a b h
  funext i
  have h2 := congrArg (fun p => Polynomial.coeff p i) h
  simpa [monicOf, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Fin.val_inj,
    (Fin.is_lt i).ne] using h2

variable {R : Ranks} {H : Host R}

theorem neZero_g (k : Fin 2) : NeZero (H.g k) := by
  exact ⟨(H.g_prime k).ne_zero⟩

theorem fact_g (k : Fin 2) : Fact (H.g k).Prime := by
  exact ⟨H.g_prime k⟩

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {what₂ : Rows.Data R} (N : NData R H what₂)

abbrev Ix : Type := Σ k : Fin 2, N.PlG k

def GoodT (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (fun v j => (N.chiT k v j)⁻¹)

variable {K : Type} [Field K]

def e0F (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k)))) :
    MonoidAlgebra K (G0g N) :=
  eSum (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (monicOf a))
    (fun a => GoodT N fun k v => monicOf (a ⟨k, v⟩))

variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)

include hcen in
theorem seriesIdempotent_central (a : MonoidAlgebra K (G0g N)) : e0F N es * a = a * e0F N es := by
  unfold e0F
  apply eSum_central
  intro i x b
  exact hcen i.1 (monicOf x) b

include hidem horth in
theorem seriesIdempotent_idem : e0F N es * e0F N es = e0F N es := by
  unfold e0F
  apply eSum_idem
  · intro i x
    exact hidem i.1 (monicOf x)
  · intro i x y hxy
    exact horth i.1 _ _ (fun h => hxy (monicOf_injective h))

include hidem horth in
theorem seriesIdempotent_ne_zero (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) (hf : GoodT N f) (hne : ∀ k v, es k (f k v) ≠ 0) :
    e0F N es ≠ 0 := by
  have e : (fun k v => monicOf (fun i : Fin R.r => (f k v).coeff i)) = f := by
    funext k v
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hf k).1.1 v).1 ((hf k).1.1 v).2.1
  unfold e0F
  apply eSum_ne_zero (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (E := fun kv a => es kv.1 (monicOf a))
    (S := fun a => GoodT N fun k v => monicOf (a ⟨k, v⟩)) (b := fun kv : Ix N => fun i : Fin R.r => (f kv.1 kv.2).coeff i)
  · intro i l
    exact hidem i.1 (monicOf l)
  · intro i x y hxy
    exact horth i.1 _ _ (fun h => hxy (monicOf_injective h))
  · show GoodT N fun k v => monicOf (fun i : Fin R.r => (f k v).coeff i)
    rw [e]
    exact hf
  · intro kv
    show es kv.1 (monicOf fun i : Fin R.r => (f kv.1 kv.2).coeff i) ≠ 0
    rw [Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hf kv.1).1.1 kv.2).1 ((hf kv.1).1.1 kv.2).2.1]
    exact hne kv.1 kv.2

variable {N}

theorem e0_eq {A : NAut N} (X : NTypes A) : X.e0 = e0F N X.eSer := by
  apply MonoidAlgebra.ext
  ext g
  rw [e0F, eSum_coeff]
  simp only [Formalism.BasicNotions.NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  rfl

theorem idempotent_mem_center {A : NAut N} (X : NTypes A) :
    X.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  rw [e0_eq X, Subalgebra.mem_center_iff]
  intro b
  exact (seriesIdempotent_central N X.eSer X.eSer_central b).symm

theorem idempotent_sum {A : NAut N} (X : NTypes A) : X.e0 * X.e0 = X.e0 := by
  rw [e0_eq X]
  exact seriesIdempotent_idem N X.eSer X.eSer_idem X.eSer_orth

theorem ambientAction_idempotent {A : NAut N} (X : NTypes A) (μ) : X.onAmb μ X.e0 = X.cenAmb μ ⟨X.e0, idempotent_mem_center X⟩ := by
  unfold Formalism.BasicNotions.NTypes.onAmb
  rw [dif_pos (idempotent_mem_center X)]

theorem matrixAction_idempotent {A : NAut N} (X : NTypes A) (μ j) : X.onMt μ j X.e0 = X.cenMt μ j ⟨X.e0, idempotent_mem_center X⟩ := by
  unfold Formalism.BasicNotions.NTypes.onMt
  rw [dif_pos (idempotent_mem_center X)]

end Formalism.BasicNotions.Examples₂.NZ
