import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.proj_unique (h : IsOpp D Z Z') {a b b' : D.La} (hb : b ∈ Z') (hb' : b' ∈ Z')
    (h1 : a - b ∈ perp D Z) (h2 : a - b' ∈ perp D Z) : b = b' := by
  have := h.eq_zero (sub_mem hb hb') (by
    have := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at this)
  exact sub_eq_zero.1 this

def IsOpp.proj (h : IsOpp D Z Z') : D.La →ₗ[𝓞 E] Z' where
  toFun a := ⟨(h.exists_sub_mem_perp a).choose, (h.exists_sub_mem_perp a).choose_spec.1⟩
  map_add' a b := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hb := (h.exists_sub_mem_perp b).choose_spec
    have hab := (h.exists_sub_mem_perp (a + b)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hab.1 (add_mem ha.1 hb.1) hab.2 ?_
    have := add_mem ha.2 hb.2
    simpa [sub_add_sub_comm] using this
  map_smul' c a := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hca := (h.exists_sub_mem_perp (c • a)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hca.1 (Z'.smul_mem c ha.1) hca.2 ?_
    have := (perp D Z).smul_mem c ha.2
    simpa [smul_sub] using this

theorem IsOpp.sub_proj_mem (h : IsOpp D Z Z') (a : D.La) : a - h.proj a ∈ perp D Z :=
  (h.exists_sub_mem_perp a).choose_spec.2

theorem IsOpp.proj_eq (h : IsOpp D Z Z') {a b : D.La} (hb : b ∈ Z') (hab : a - b ∈ perp D Z) : (h.proj a : D.La) = b :=
  h.proj_unique (h.proj a).2 hb (h.sub_proj_mem a) hab

theorem IsOpp.proj_of_mem (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') : (h.proj b : D.La) = b :=
  h.proj_eq hb (by simp)

theorem IsOpp.proj_of_perp (h : IsOpp D Z Z') {a : D.La} (ha : a ∈ perp D Z) : (h.proj a : D.La) = 0 :=
  h.proj_eq Z'.zero_mem (by simpa using ha)

variable (D)

theorem exists_adjoint (σ : D.La →ₗ[𝓞 E] D.La) : ∃ w : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (w a) b = D.EF a (σ b) := by
  choose w hw using fun a => D.unimod.2 ((D.EF a).comp (σ.restrictScalars ℤ))
  refine ⟨{ toFun := w, map_add' := fun a b => D.unimod.1 ?_, map_smul' := fun c a => D.unimod.1 ?_ }, fun a b => ?_⟩
  · ext x; simp [hw]
  · ext x
    simp only [hw, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, RingHom.id_apply, D.adj]
    rw [← σ.map_smul]
  · exact congrArg (fun f => f b) (hw a)

theorem bijective_of_isometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) :
    Function.Bijective g := by
  obtain ⟨w, hw⟩ := exists_adjoint D g
  have hwg : ∀ a, w (g a) = a := fun a => D.unimod.1 (LinearMap.ext fun b => by rw [hw, hg])
  have hws : Function.Surjective w := fun a => ⟨g a, hwg a⟩
  haveI := D.fin
  have hwi : Function.Injective w := OrzechProperty.injective_of_surjective_endomorphism w hws
  refine ⟨fun a b hab => by rw [← hwg a, ← hwg b, hab], fun a => ⟨w a, hwi (by rw [hwg])⟩⟩

def equivOfIsometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) : D.La ≃ₗ[𝓞 E] D.La :=
  LinearEquiv.ofBijective g (bijective_of_isometry D g hg)

@[simp] theorem equivOfIsometry_apply (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) (a : D.La) :
    equivOfIsometry D g hg a = g a := rfl

end GlobalTheory.LowFilt
