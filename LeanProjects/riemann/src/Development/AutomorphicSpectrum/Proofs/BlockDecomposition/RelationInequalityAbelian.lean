import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst
open LocalGlobalAboveLAlt
open scoped commutatorElement

namespace GlobalTheory.CompanionTheory.RelIneAbProof

theorem eq_one_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have h1 : (f - 1) ^ Module.finrank ℂ V = 0 := by
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have h2 : (f - 1).IsSemisimple :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _) hs Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ h2)

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_commute {Γ : Type*} [Group Γ] (R : ↥(Weil h) →* Γ) (hR : IsSmooth R)
    (φ : ↥(Weil h)) :
    ∃ f : ℕ, 0 < f ∧ ∀ i : ↥(Ine (F := E) A), Commute (R φ ^ f) (R (ineIncl h i)) := by
  let S : Set Γ := Set.range fun σ : ↥(Ine (F := E) A) => R (ineIncl h σ)
  have hfin : S.Finite := hR.finite_range
  haveI : Finite S := hfin
  have hmem : ∀ s ∈ S, R φ * s * (R φ)⁻¹ ∈ S := by
    rintro _ ⟨σ, rfl⟩
    have h0 : deg (φ * ineIncl h σ * φ⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    have e : ineIncl h ⟨_, deg_eq_zero_iff.mp h0⟩ = φ * ineIncl h σ * φ⁻¹ := Subtype.ext rfl
    simp only [e, map_mul, map_inv]
  let c : S → S := fun s => ⟨R φ * s * (R φ)⁻¹, hmem s s.2⟩
  have hc : Function.Injective c := fun s t hst => by
    have := congrArg Subtype.val hst
    exact Subtype.ext (by simpa [c] using this)
  let π : Equiv.Perm S := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc)
  have hπ : ∀ s : S, ((π s : S) : Γ) = R φ * s * (R φ)⁻¹ := fun s => rfl
  have hpow : ∀ (k : ℕ) (s : S), (((π ^ k) s : S) : Γ) = R φ ^ k * s * (R φ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ', Equiv.Perm.mul_apply, hπ, ih, pow_succ']
      group
  refine ⟨orderOf π, orderOf_pos π, fun i => ?_⟩
  have h1 := hpow (orderOf π) ⟨_, i, rfl⟩
  rw [pow_orderOf_eq_one] at h1
  have h2 : R (ineIncl h i) = R φ ^ orderOf π * R (ineIncl h i) * (R φ ^ orderOf π)⁻¹ := h1
  exact (eq_mul_inv_iff_mul_eq.mp h2).symm

variable (h) in

def degSub (f : ℕ) : Subgroup ↥(Weil h) :=
  ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod f))).comp (degHom h)).ker

theorem mem_degSub {f : ℕ} {g : ↥(Weil h)} : g ∈ degSub h f ↔ (f : ℤ) ∣ deg g := by
  rw [degSub, MonoidHom.mem_ker]
  show Multiplicative.ofAdd ((deg g : ℤ) : ZMod f) = 1 ↔ _
  rw [ofAdd_eq_one]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem sub_degSub {f : ℕ} (hf : 0 < f) : LocalGlobalAboveLAlt.Sub (degSub h f) := by
  haveI : NeZero f := ⟨hf.ne'⟩
  refine LocalGlobalAboveLAlt.Sub.step LocalGlobalAboveLAlt.Sub.top le_top ?_ ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a _ b _
    rw [mem_degSub, commutatorElement_def]
    simp
  · rw [Subgroup.relIndex_top_right]
    have : (degSub h f).FiniteIndex := by
      unfold degSub
      infer_instance
    exact Subgroup.FiniteIndex.index_ne_zero
  · have : {s : ↥(Ine (F := E) A) | ineIncl h s ∈ degSub h f} = Set.univ :=
      Set.eq_univ_of_forall fun s => by simp [mem_degSub]
    rw [this]
    exact isOpen_univ

theorem charPol_eq (x y : WD h) (hxy : Rel x y)
    (hab : ∀ g : ↥(Weil h), (g : G E _) ∈ ⁅Ine (F := E) A, Ine (F := E) A⁆ → Triv y g)
    (g : ↥(Weil h)) (hg : deg g = 0) : x.charPol g = y.charPol g := by
  obtain ⟨n, b, rfl⟩ := WD.exists_rep y
  let R : ↥(Weil h) →* (Module.End ℂ (Fin n → ℂ))ˣ := MonoidHom.toHomUnits b.ρ
  have hRv : ∀ a, ((R a : (Module.End ℂ (Fin n → ℂ))ˣ) : Module.End ℂ (Fin n → ℂ)) = b.ρ a :=
    fun a => rfl
  have hR1 : ∀ a, R a = 1 ↔ b.ρ a = 1 := fun a => by rw [Units.ext_iff, hRv, Units.val_one]
  have hRs : IsSmooth R := b.smooth.of_le fun σ hσ => (hR1 σ).mpr hσ

  have hI : ∀ i j : ↥(Ine (F := E) A), Commute (R (ineIncl h i)) (R (ineIncl h j)) := by
    intro i j
    have hm : ((⁅ineIncl h i, ineIncl h j⁆ : ↥(Weil h)) : G E _) ∈
        ⁅Ine (F := E) A, Ine (F := E) A⁆ :=
      Subgroup.commutator_mem_commutator i.2 j.2
    have ht := hab _ hm
    rw [Triv, WD.charPol_mk, WD.lpDim_mk] at ht
    have h1 := (hR1 _).mpr (eq_one_of_charpoly _ (b.semisimple _) ht)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
    exact h1
  obtain ⟨f, hf, hΦ⟩ := exists_commute R hRs (frob h)

  have hdec : ∀ a ∈ degSub h f, ∃ (k : ℤ) (i : ↥(Ine (F := E) A)),
      R a = (R (frob h) ^ f) ^ k * R (ineIncl h i) := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_degSub.mp ha
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) a
    refine ⟨k, τ, ?_⟩
    conv_lhs => rw [hτ]
    rw [map_mul, map_zpow, hk, zpow_mul, zpow_natCast]
  have hcomm : ∀ a ∈ degSub h f, ∀ c ∈ degSub h f, Commute (R a) (R c) := by
    intro a ha c hc
    obtain ⟨k, i, hi⟩ := hdec a ha
    obtain ⟨l, j, hj⟩ := hdec c hc
    rw [hi, hj]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact (Commute.refl _).zpow_zpow _ _
    · exact (hΦ j).zpow_left _
    · exact ((hΦ i).zpow_left _).symm
    · exact hI i j
  have hker : ⁅degSub h f, degSub h f⁆ ≤ R.ker := by
    rw [Subgroup.commutator_le]
    intro a ha c hc
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm a ha c hc
  refine hxy.2.2 _ (sub_degSub hf) (fun a ha => ?_) g (mem_degSub.mpr (by simp [hg]))
  have h1 : b.ρ a = 1 := (hR1 a).mp (hker ha)
  rw [Triv, WD.charPol_mk, WD.lpDim_mk, h1, LinearMap.charpoly_one]

end

theorem relIneAb : RelIneAb := by
  intro E Ω _ _ _ _ _ A w h x y hxy hab g hg
  exact charPol_eq x y hxy hab g hg

end GlobalTheory.CompanionTheory.RelIneAbProof
