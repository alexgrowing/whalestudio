import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.LcIndicator
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiCosets
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ValLeOneOfNabsLt

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem comp_mem {e : Sp k n ≃ₜ Sp k n} (he : ∀ p, (e p).2 ≠ 0 → p.2 ≠ 0) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact he p (hsu hp)

theorem comp_mem_univ {e : Sp k n ≃ₜ Sp k n} {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, -⟩ := hf
  exact ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, Set.subset_univ _⟩

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n := Homeomorph.addRight ((c, 0) : Sp k n)

theorem trH_apply (c : Matrix (Fin n) (Fin n) k) (p : Sp k n) : trH c p = tr c p :=
  Prod.ext rfl (add_zero p.2)

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n :=
  Homeomorph.prodCongr (Homeomorph.smulOfNeZero (t : k) t.ne_zero) (Homeomorph.refl _)

def actH (g : GL (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun := act g
  invFun := act g⁻¹
  left_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  right_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  continuous_toFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  continuous_invFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)

theorem tr_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (c : Matrix (Fin n) (Fin n) k) :
    (fun p => f (tr c p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  have key := comp_mem (e := trH c) (fun p hp => by simpa [trH_apply, tr] using hp) hf
  simpa [trH_apply] using key

theorem hom_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (t : kˣ) :
    (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) :=
  comp_mem (e := homH t) (fun p hp => hp) hf

theorem act_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (g : GL (Fin n) k) :
    (fun p => f (act g p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  refine comp_mem (e := actH g) (fun p hp h0 => hp ?_) hf
  show g.val *ᵥ p.2 = 0
  rw [h0, Matrix.mulVec_zero]

def Good (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  TranslInv Z ζ ∧ SuppU ζ (CC Z ×ˢ Set.univ)

theorem agree {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hs : SuppU ζ (CC Z ×ˢ Set.univ)) {f f' : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (h : ∀ p ∈ OO Z, f p = f' p) : ζ f = ζ f' := by
  have hsub : f - f' ∈ supportedIn (UU : Set (Sp k n)) := Submodule.sub_mem _ hf hf'
  have hz := hs (f - f') hsub (by
    rintro p ⟨hp1, -⟩
    by_cases hp2 : p.2 = 0
    · have h1 : f p = 0 := by
        by_contra hne
        exact hf.2 hne hp2
      have h2 : f' p = 0 := by
        by_contra hne
        exact hf'.2 hne hp2
      simp [h1, h2]
    · simp [h ⟨p.1, p.2⟩ ⟨hp1, hp2⟩])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem good_tr {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) : ζ (fun p => f (tr c p)) = ζ f := by
  exact hg.1 c hc f ⟨hf.1, Set.subset_univ _⟩

theorem coset_ok {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) :
    (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) ⊆ Z ∧
      IsCompact ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) ∧
      ∀ a ∈ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)), ∃ U : Set (Matrix (Fin n) (Fin n) k),
        IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) := by
  refine ⟨?_, hM.cpt.image (continuous_add_right c), ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact Z.add_mem (hM.sub hm) hc
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨U0, hU0, h0, hU0Z⟩ := hM.nhd
    have hmZ : m + c ∈ Z := Z.add_mem (hM.sub hm) hc
    refine ⟨(fun x => x - (m + c)) ⁻¹' U0, hU0.preimage (continuous_sub_right _), by simpa using h0, ?_⟩
    rintro x ⟨hxU, hxZ⟩
    have hxM : x - (m + c) ∈ M := hU0Z ⟨hxU, Z.sub_mem hxZ hmZ⟩
    refine ⟨x - (m + c) + m, M.add_mem hxM hm, ?_⟩
    show x - (m + c) + m + c = x
    abel

theorem lift_ex (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p := by
  obtain ⟨h1, h2, h3⟩ := coset_ok hM hc
  exact psi_lift hZ h1 h2 h3 hh

theorem image_add_zero (M : Set (Matrix (Fin n) (Fin n) k)) : (fun a => a + (0 : Matrix (Fin n) (Fin n) k)) '' M = M := by
  simp

theorem exists_lift_of_lattice_average (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {h : Sp k n → ℂ}
    (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p := by
  have key := lift_ex hZ hM (c := 0) Z.zero_mem hh
  rwa [image_add_zero] at key

theorem tr_OO (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) {p : Sp k n} (hp : p ∈ OO Z) : tr c p ∈ OO Z :=
  ⟨(cc_add hZ hc).1.2 hp.1, hp.2⟩

theorem ind (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {fL fM : Sp k n → ℂ} (hfL : fL ∈ supportedIn (UU : Set (Sp k n))) (hfM : fM ∈ supportedIn (UU : Set (Sp k n)))
    (eL : ∀ p ∈ OO Z, fL p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (eM : ∀ p ∈ OO Z, fM p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p) :
    ζ fL = (M.relIndex L : ℂ) * ζ fM := by
  obtain ⟨D, hcard, hDL, hpsi⟩ := psi_cosets hL hM hML
  have hlift : ∀ d ∈ D, ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p :=
    fun d hd => lift_ex hZ hM (hL.sub (hDL d hd)) hh
  choose! F hFmem hFeq using hlift
  have hsum : ζ fL = ζ (∑ d ∈ D, F d) := by
    refine agree hg.2 hfL (Submodule.sum_mem _ fun d hd => hFmem d hd) ?_
    intro p hp
    rw [eL p hp, hpsi h, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d hd => (hFeq d hd p hp).symm
  have hterm : ∀ d ∈ D, ζ (F d) = ζ fM := by
    intro d hd
    have hcZ : d ∈ Z := hL.sub (hDL d hd)
    have e1 : ∀ p, psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p =
        psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h (tr d p) := by
      intro p
      have key := congrFun (psi_tr hZ ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h hcZ) p
      rw [key, Set.image_image]
      simp only [add_sub_cancel_right, Set.image_id']
    have e2 : ζ fM = ζ (fun p => F d (tr d p)) := by
      refine agree hg.2 hfM (tr_mem (hFmem d hd) d) ?_
      intro p hp
      rw [eM p hp, hFeq d hd _ (tr_OO hZ hcZ hp), e1]
    rw [e2, good_tr hg hcZ (hFmem d hd)]
  rw [hsum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]

theorem scale (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {f f' : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (e : ∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (e' : ∀ p ∈ OO Z, f' p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) (fun q => h (hom t q)) p) :
    ζ (fun p => f (hom t p)) = (((nabs k t)⁻¹ ^ Module.finrank k Z : ℝ) : ℂ) * ζ f' := by
  have hL' : IsLat Z (t⁻¹.val • L) := isLat_smul hL t⁻¹
  have hle : L ≤ t⁻¹.val • L := lat_le_inv hL ht
  have hh' : (fun q => h (hom t q)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hh t
  have hg' : (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hf t
  have eg : ∀ p ∈ OO Z, (fun p => f (hom t p)) p =
      psi Z ((t⁻¹.val • L : AddSubgroup (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k))
        (fun q => h (hom t q)) p := by
    intro p hp
    have hp' : hom t p ∈ OO Z := ⟨(cc_smul hZ (t : k) hp.1).1, hp.2⟩
    have key := congrFun (psi_hom hZ (L : Set (Matrix (Fin n) (Fin n) k)) h t) p
    simp only at key ⊢
    rw [e _ hp', key, AddSubgroup.coe_pointwise_smul]
  have main := ind hZ hg hL' hL hle hh' hg' hf' eg e'
  rw [main]
  congr 1
  rw [← lat_index_smul hL t ht]
  push_cast
  rfl

end PositivityTheory.RgUd.TP.Nil.Fib2

end
