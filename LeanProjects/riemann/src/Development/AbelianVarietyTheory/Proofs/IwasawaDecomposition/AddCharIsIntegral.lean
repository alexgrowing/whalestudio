import Mathlib
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

namespace GlobalTheory.Mem.AwayChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
open scoped TensorProduct

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adelic_ext {n : ℕ} (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g = bc (prV (E := E) v) h) : g = h := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub]
  have h1 := congrArg Units.val (H w)
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV] at h1
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  rw [this, sub_self]

theorem exists_trivial_on {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ s, bc (prV (E := E) v) k = 1) ∧
      ∀ v ∉ s, bc (prV (E := E) v) k = bc (prV (E := E) v) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have hne : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 k) = bc (prV (E := E) w) k := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      rfl
    refine ⟨Formalism.UG.P.afsplitU v 1 k, Formalism.UG.P.afsplitU_mem v σ J 1 k (one_mem _) hk, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h; exact Formalism.UG.P.afsplit_right1 w 1 k
      · rw [hne w h]; exact h1 w ((Finset.mem_insert.1 hw).resolve_left h)
    · rw [Finset.mem_insert, not_or] at hw
      rw [hne w hw.1]; exact h2 w hw.2

theorem finite_over (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_away_mem (S : StepLevel F E σ J T f bad) (p : ℕ) (hp : p ≠ 0)
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) g ∈ S.Uloc w) :
    ∃ κ : S.U, (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) g := by
  obtain ⟨k, hk, h1, h2⟩ := exists_trivial_on σ J (finite_over (F := F) p hp).toFinset g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
  refine ⟨⟨k, (S.U_eq k).2 ⟨hk, fun v => ?_⟩⟩, h1, h2⟩
  by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v hv]; exact one_mem _
  · rw [h2 v hv]; exact hw v hv

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A ℂ) (x : A) : IsIntegral ℤ (ψ x) := by
  have h : ψ x ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact IsIntegral.of_pow Nat.card_pos (by rw [h]; exact isIntegral_one)

theorem chi_isIntegral {gp : Fin 2 → ℕ} {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t 0 skip fc zl) (κ : S.U) : IsIntegral ℤ ((S.chi κ : ℂˣ) : ℂ) := by
  rw [X.chi_eq κ]
  refine IsIntegral.prod _ fun i _ => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun h => ?_
  haveI : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one, ← AddChar.map_neg_eq_inv]
  exact addChar_isIntegral _ _

end Adelic

theorem exists_inv_char {U LL O Kf : Type} [Group U] [Field LL] [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (χ : U →* ℂˣ) (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ c : U →* Oˣ, ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ algebraMap O Kf ((c κ : Oˣ) : O) * e r = 1 := by
  choose r hr o ho using h
  have r1 : r 1 = 1 := embLL.injective (by rw [hr]; simp)
  have rm : ∀ a b, r (a * b) = r a * r b := fun a b => embLL.injective (by rw [map_mul, hr, hr, hr]; simp)
  let o' : U →* O :=
    { toFun := o
      map_one' := hinj (by rw [ho, r1, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, ho, ho, ho, rm, map_mul]) }
  refine ⟨o'.toHomUnits⁻¹, fun κ => ⟨r κ, hr κ, ?_⟩⟩
  rw [← ho κ, ← map_mul]
  have : o κ = ((o'.toHomUnits κ : Oˣ) : O) := rfl
  rw [this, MonoidHom.inv_apply, Units.inv_mul, map_one]

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem exists_psiTied {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E sp.cm.sig J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hp : p ≠ 0) (hk : R.k = n)
    (hJ : ∀ x y, J x y = sp.gram0 (Fin.cast hk.symm x) (Fin.cast hk.symm y))
    (hU : ∀ v, S.Uloc v = (L.Uloc v).map (reGL hk _).toMonoidHom)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ, PsiTied S L p hk embLL e ψ := by
  obtain ⟨c, hc⟩ := exists_inv_char hinj S.chi embLL e h
  have hex : ∀ a : Formalism.L2.Herm.awayFrom₂ L p, ∃ κ : S.U,
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1) := by
    intro a
    obtain ⟨h2, h3⟩ := (mem_awayP_iff L p a.1).1 a.2
    refine exists_away_mem S p hp _ (reGL_mem_UPts hk sp.cm.sig sp.gram0 J hJ _ _ h2) fun w hw => ?_
    rw [bc_reGL, hU w]
    exact Subgroup.mem_map.2 ⟨_, h3 w hw, rfl⟩
  choose κ h1 h2 using hex
  have huniq : ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (k : S.U),
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k.1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) k.1 = bc (prV (E := E) w) (reGL hk _ a.1)) → κ a = k := by
    intro a k k1 k2
    refine Subtype.ext (adelic_ext _ _ fun v => ?_)
    by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [h1 a v hv, k1 v hv]
    · rw [h2 a v hv, k2 v hv]
  let K : Formalism.L2.Herm.awayFrom₂ L p →* S.U := MonoidHom.mk' κ fun a b => by
    refine huniq _ _ (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.coe_mul, map_mul, h1 a v hv, h1 b v hv, mul_one]
    · rw [Subgroup.coe_mul, map_mul, h2 a v hv, h2 b v hv, Subgroup.coe_mul, map_mul, map_mul]
  refine ⟨c.comp K, fun a k k1 k2 => ?_⟩
  obtain rfl := huniq a k k1 k2
  exact hc (κ a)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

set_option maxHeartbeats 4000000 in

theorem exists_psi : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) → (∀ u, LevelZeroCharacterRational T u) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))ˣ,
      PsiTied (LL := D.what₂.LL) (O := ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
        (Kf := KfRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ((T u).cls0).lev (L0 u)
        (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ψ := by
  intro D L0 T hJ hψ u w _
  refine exists_psiTied ((T u).cls0).lev (L0 u) _ (D.what₂.places.resChar_prime w).ne_zero (rank_eq_first_level D.R) (Formalism.L2.G.Cmp.gramN_zero D)
    (hJ u).Uloc_eq Subtype.val_injective _ _ fun κ => ?_
  obtain ⟨r, hr⟩ := chiRatAll_rec T u (hψ u) κ
  refine ⟨r, hr, (embRec_int D w _ r).1 ((val_nonneg_iff D w r).2 ?_)⟩
  have h1 : IsIntegral ℤ (D.what₂.embLL r) := hr ▸ chi_isIntegral ((T u).glev0) κ
  have h2 : IsIntegral ℤ r := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 h1
  exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (⟨r, h2⟩ : 𝓞 D.what₂.LL)

end GlobalTheory.Mem.AwayChar
