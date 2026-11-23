import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
import GroundTheory.GlobalFields.IdeleGroups.StandardOpenEquiv

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace AdeleBaseChange

omit [NumberField K] in

theorem finiteCompletionMap_eq_galHom (σ : L ≃ₐ[K] L) (w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • comapPrime (σ : L ≃+* L) w') :
    finiteCompletionMap (σ : L ≃+* L) w' = galHom σ (comapPrime (σ : L ≃+* L) w') w' h := by
  have := (HeightOneSpectrum.denseRange_algebraMap L (comapPrime (σ : L ≃+* L) w')).equalizer
    (continuous_finiteCompletionMap _ w') (continuous_galHom σ _ w' h)
    (funext fun l ↦ by
      simp only [Function.comp_apply, finiteCompletionMap_algebraMap, galHom_algebraMap]
      rfl)
  exact RingHom.ext (congrFun this)

omit [NumberField K] in

theorem smul_snd_eq_galHom (σ : L ≃ₐ[K] L) (a : 𝔸[L]) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) : (σ • a).2 w' = galHom σ w w' h (a.2 w) := by
  obtain rfl : w = comapPrime (σ : L ≃+* L) w' := by
    rw [comapPrime_eq_inv_smul, h, inv_smul_smul]
  rw [smul_snd, finiteCompletionMap_eq_galHom σ w' h]

end AdeleBaseChange

namespace IdeleGroup

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

theorem finite_setOf_liesOver :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite :=
  (Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
    fun w hw ↦ ⟨⟨w, hw⟩, rfl⟩

open Classical in

def finiteAdeleAboveFun (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if h : w.asIdeal.LiesOver v.asIdeal then a ⟨w, h⟩ else 1

omit [NumberField K] in
theorem finiteAdeleAboveFun_apply (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : PlacesOver L v) : finiteAdeleAboveFun v a w.1 = a w := by
  rw [finiteAdeleAboveFun, dif_pos w.2]

omit [NumberField K] in
theorem finiteAdeleAboveFun_apply_of_not (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    finiteAdeleAboveFun v a w = 1 := by
  rw [finiteAdeleAboveFun, dif_neg h]

theorem finiteAdeleAboveFun_eventually (a : (w : PlacesOver L v) → w.1.adicCompletion L) :
    ∀ᶠ w in Filter.cofinite, finiteAdeleAboveFun v a w ∈ w.adicCompletionIntegers L := by
  refine Filter.eventually_cofinite.2 ((finite_setOf_liesOver (L := L) v).subset fun w hw ↦ ?_)
  by_contra h
  apply hw
  rw [finiteAdeleAboveFun_apply_of_not v a h]
  exact (w.adicCompletionIntegers L).one_mem

omit [NumberField K] in
theorem finiteAdeleAboveFun_one :
    finiteAdeleAboveFun v (1 : (w : PlacesOver L v) → w.1.adicCompletion L) = 1 := by
  funext w
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · exact finiteAdeleAboveFun_apply v 1 ⟨w, h⟩
  · exact finiteAdeleAboveFun_apply_of_not v 1 h

omit [NumberField K] in
theorem finiteAdeleAboveFun_mul (a b : (w : PlacesOver L v) → w.1.adicCompletion L) :
    finiteAdeleAboveFun v (a * b) = finiteAdeleAboveFun v a * finiteAdeleAboveFun v b := by
  funext w
  rw [Pi.mul_apply]
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · rw [finiteAdeleAboveFun_apply v _ ⟨w, h⟩, finiteAdeleAboveFun_apply v _ ⟨w, h⟩,
      finiteAdeleAboveFun_apply v _ ⟨w, h⟩, Pi.mul_apply]
  · rw [finiteAdeleAboveFun_apply_of_not v _ h, finiteAdeleAboveFun_apply_of_not v _ h,
      finiteAdeleAboveFun_apply_of_not v _ h, mul_one]

def finiteAdeleAbove : ((w : PlacesOver L v) → w.1.adicCompletion L) →* FiniteAdeleRing (𝓞 L) L where
  toFun a := (⟨finiteAdeleAboveFun v a, finiteAdeleAboveFun_eventually v a⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L])
  map_one' := Subtype.ext (finiteAdeleAboveFun_one v)
  map_mul' a b := Subtype.ext (finiteAdeleAboveFun_mul v a b)

theorem finiteAdeleAbove_apply (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : PlacesOver L v) : finiteAdeleAbove v a w.1 = a w :=
  finiteAdeleAboveFun_apply v a w

theorem finiteAdeleAbove_apply_of_not (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    finiteAdeleAbove v a w = 1 :=
  finiteAdeleAboveFun_apply_of_not v a h

theorem adele_ext {a b : 𝔸[L]} (h₁ : a.1 = b.1) (h₂ : ∀ w : HeightOneSpectrum (𝓞 L), a.2 w = b.2 w) :
    a = b :=
  Prod.ext h₁ (Subtype.ext (funext h₂))

def finiteEmbedAbove : ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) →* IdeleGroup L :=
  (Units.map (MonoidHom.prod 1 (finiteAdeleAbove v) :
      ((w : PlacesOver L v) → w.1.adicCompletion L) →*
        InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)).comp
    (MulEquiv.piUnits (M := fun w : PlacesOver L v ↦ w.1.adicCompletion L)).symm.toMonoidHom

theorem coe_finiteEmbedAbove_fst (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 = 1 :=
  rfl

theorem coe_finiteEmbedAbove_snd (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (w : PlacesOver L v) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 w.1 = y w :=
  finiteAdeleAbove_apply v _ w

theorem coe_finiteEmbedAbove_snd_of_not (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 w = 1 :=
  finiteAdeleAbove_apply_of_not v _ h

def finiteProjAbove : IdeleGroup L →* ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  MonoidHom.pi fun w ↦ finiteProj w.1

omit [NumberField K] in
@[simp]
theorem coe_finiteProjAbove_apply (x : IdeleGroup L) (w : PlacesOver L v) :
    ((finiteProjAbove v x w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      (x : 𝔸[L]).2 w.1 :=
  rfl

theorem finiteProjAbove_finiteEmbedAbove (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteProjAbove v (finiteEmbedAbove v y) = y :=
  funext fun w ↦ Units.ext (coe_finiteEmbedAbove_snd v y w)

omit [NumberField K] [NumberField L] in
theorem comapPrime_liesOver (σ : L ≃ₐ[K] L) (w : PlacesOver L v) :
    (comapPrime (σ : L ≃+* L) w.1).asIdeal.LiesOver v.asIdeal := by
  rw [comapPrime_eq_inv_smul]
  exact (σ⁻¹ • w).2

omit [NumberField K] in

theorem finiteProjAbove_smul_congr (σ : L ≃ₐ[K] L) {x y : IdeleGroup L}
    (h : finiteProjAbove v x = finiteProjAbove v y) :
    finiteProjAbove v (σ • x) = finiteProjAbove v (σ • y) := by
  funext u
  refine Units.ext ?_
  rw [coe_finiteProjAbove_apply, coe_finiteProjAbove_apply, coe_smul_idele, coe_smul_idele,
    smul_snd, smul_snd]
  congr 1
  have := congrArg (fun f : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ ↦
    ((f ⟨comapPrime (σ : L ≃+* L) u.1, comapPrime_liesOver v σ u⟩ : _) :
      (comapPrime (σ : L ≃+* L) u.1).adicCompletion L)) h
  exact this

instance finiteUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) where
  smul σ y := finiteProjAbove v (σ • finiteEmbedAbove v y)
  one_smul y := by
    change finiteProjAbove v ((1 : L ≃ₐ[K] L) • finiteEmbedAbove v y) = y
    rw [one_smul, finiteProjAbove_finiteEmbedAbove]
  mul_smul σ τ y := by
    change finiteProjAbove v ((σ * τ) • finiteEmbedAbove v y) =
      finiteProjAbove v (σ • finiteEmbedAbove v (finiteProjAbove v (τ • finiteEmbedAbove v y)))
    rw [mul_smul]
    exact finiteProjAbove_smul_congr v σ (finiteProjAbove_finiteEmbedAbove v _).symm
  smul_mul σ y z := by
    change finiteProjAbove v (σ • finiteEmbedAbove v (y * z)) =
      finiteProjAbove v (σ • finiteEmbedAbove v y) * finiteProjAbove v (σ • finiteEmbedAbove v z)
    rw [map_mul, smul_mul', map_mul]
  smul_one σ := by
    change finiteProjAbove v (σ • finiteEmbedAbove v 1) = 1
    rw [map_one, smul_one, map_one]

theorem finiteUnitsAbove_smul_def (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    σ • y = finiteProjAbove v (σ • finiteEmbedAbove v y) :=
  rfl

theorem finiteProjAbove_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    finiteProjAbove v (σ • x) = σ • finiteProjAbove v x :=
  finiteProjAbove_smul_congr v σ (finiteProjAbove_finiteEmbedAbove v _).symm

omit [NumberField K] [NumberField L] in
theorem liesOver_of_smul_liesOver (σ : L ≃ₐ[K] L) {w : HeightOneSpectrum (𝓞 L)}
    (h : (σ • w).asIdeal.LiesOver v.asIdeal) : w.asIdeal.LiesOver v.asIdeal := by
  have := (σ⁻¹ • (⟨σ • w, h⟩ : PlacesOver L v)).2
  rwa [coe_smul_placesOver, inv_smul_smul] at this

theorem finiteEmbedAbove_smul (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteEmbedAbove v (σ • y) = σ • finiteEmbedAbove v y := by
  refine Units.ext (adele_ext ?_ fun u ↦ ?_)
  · funext u
    rw [coe_finiteEmbedAbove_fst, coe_smul_idele, smul_fst, coe_finiteEmbedAbove_fst]
    exact (map_one (infiniteCompletionMap _ u)).symm
  · by_cases h : u.asIdeal.LiesOver v.asIdeal
    · rw [coe_finiteEmbedAbove_snd v _ ⟨u, h⟩, finiteUnitsAbove_smul_def,
        coe_finiteProjAbove_apply]
    · rw [coe_finiteEmbedAbove_snd_of_not v _ h, coe_smul_idele, smul_snd,
        coe_finiteEmbedAbove_snd_of_not v _ ?_, map_one]
      rw [comapPrime_eq_inv_smul]
      intro h'
      exact h (liesOver_of_smul_liesOver v σ⁻¹ h')

theorem finiteProjAbove_finiteEmbedAbove_of_ne {v v' : HeightOneSpectrum (𝓞 K)} (h : v' ≠ v)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteProjAbove v' (finiteEmbedAbove v y) = 1 := by
  funext u
  refine Units.ext ?_
  rw [coe_finiteProjAbove_apply, coe_finiteEmbedAbove_snd_of_not v y]
  · rfl
  · intro hu
    exact h ((below_eq_iff u.1 v').2 u.2 ▸ (below_eq_iff u.1 v).2 hu)

theorem finiteUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) :
    (((σ • y) (σ • w) : ((σ • w).1.adicCompletion L)ˣ) : (σ • w).1.adicCompletion L) =
      galEquiv v σ w.1 (σ • w).1 rfl (y w) := by
  rw [finiteUnitsAbove_smul_def, coe_finiteProjAbove_apply, coe_smul_idele,
    smul_snd_eq_galHom σ _ w.1 (σ • w).1 rfl, coe_finiteEmbedAbove_snd, galEquiv_apply]

end Finite

end IdeleGroup

end

end GroundTheory.Global
