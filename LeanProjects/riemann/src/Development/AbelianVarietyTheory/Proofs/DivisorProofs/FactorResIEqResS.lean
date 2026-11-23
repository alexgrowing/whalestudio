import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    ∃ a : 𝓞 E, s - oToS F E a ∈ idS F I := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resI F I hI s)
  exact ⟨a, (resI_eq_zero_iff I hI _).1 (by rw [map_sub, resI_oToS, ha, sub_self])⟩

theorem resI_eq_mk_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) (a : 𝓞 E) :
    resI F I hI s = Ideal.Quotient.mk I a ↔ s - oToS F E a ∈ idS F I := by
  rw [← resI_eq_zero_iff I hI, map_sub, resI_oToS, sub_eq_zero]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

theorem factor_resI {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I ≤ J) (s : Formalism.L2.Herm.intAf F E) :
    Ideal.Quotient.factor h (resI F I hI s) = resI F J hJ s := by
  obtain ⟨a, ha⟩ := exists_sub_mem I hI s
  rw [(resI_eq_mk_iff I hI s a).2 ha, (resI_eq_mk_iff J hJ s a).2 (Ideal.map_mono h ha)]
  rfl

theorem factor_resI_eq_resS {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (w : Pl E) (h : I ≤ w.asIdeal)
    (s : Formalism.L2.Herm.intAf F E) : Ideal.Quotient.factor h (resI F I hI s) = resS F w s :=
  factor_resI hI w.ne_bot h s

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

def crtHom (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : 𝓞 E ⧸ I →+* ∀ w : ↥Pg, kP w.1 :=
  RingHom.pi fun w => Ideal.Quotient.factor (hle w)

theorem crtHom_bijective (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) :
    Function.Bijective (crtHom hle) := by
  classical
  have hc : Pairwise (fun v w : ↥Pg => IsCoprime v.1.asIdeal w.1.asIdeal) := fun v w h =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun e => h (Subtype.ext e))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hP, ← Finset.prod_coe_sort Pg,
      Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun v _ w _ h => hc h)]
    simp only [Finset.mem_univ, iInf_pos, Ideal.mem_iInf]
    intro w
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx w)
  · intro x
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hc x
    exact ⟨Ideal.Quotient.mk I a, funext fun w => ha w⟩

def crt (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : (𝓞 E ⧸ I) ≃+* ∀ w : ↥Pg, kP w.1 :=
  RingEquiv.ofBijective (crtHom hle) (crtHom_bijective hP hle)

theorem crt_apply (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (x : 𝓞 E ⧸ I) (w : ↥Pg) :
    crt hP hle x w = Ideal.Quotient.factor (hle w) x := rfl

def chiProd {K : Type} [Field K] (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (kP w.1)ˣ →* Kˣ) :
    (𝓞 E ⧸ I)ˣ →* Kˣ :=
  ∏ w : ↥Pg, (χ w).comp (Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom)

theorem chiProd_apply {K : Type} [Field K] (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (kP w.1)ˣ →* Kˣ)
    (u : (𝓞 E ⧸ I)ˣ) : chiProd hle χ u = ∏ w : ↥Pg, χ w (Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom u) := by
  simp [chiProd]

theorem exists_chiProd_eq {K : Type} [Field K] (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal)
    (χ' : (𝓞 E ⧸ I)ˣ →* Kˣ) : ∃ χ, chiProd hle χ = χ' := by
  classical
  let e : (𝓞 E ⧸ I)ˣ ≃* ∀ w : ↥Pg, (kP w.1)ˣ := (Units.mapEquiv (crt hP hle).toMulEquiv).trans MulEquiv.piUnits
  refine ⟨fun w => (χ'.comp e.symm.toMonoidHom).comp (MonoidHom.mulSingle (fun w : ↥Pg => (kP w.1)ˣ) w), ?_⟩
  ext1 u
  rw [chiProd_apply]
  have h : ∀ w, Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom u = e u w := fun w => Units.ext rfl
  simp only [h, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
  rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
  simp

end CRT

end GlobalTheory.GeoActCompare
