import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.BaseComp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem star_int (r : 𝓞 E) : ∃ s : 𝓞 E, (s : E) = star (r : E) :=
  ⟨⟨star (r : E), r.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem mem_dual_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem fg_of_int (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) : L.FG := by
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  have hle : L ≤ LinearMap.range f := by
    intro x hx
    choose r hr using h x hx
    exact ⟨r, funext fun j => (hr j).symm⟩
  haveI : IsNoetherian (𝓞 E) (LinearMap.range f) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have := (isNoetherian_submodule.1 (inferInstance : IsNoetherian (𝓞 E) (LinearMap.range f))) L hle
  exact this

theorem sup_dual_eq_std (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E))
    (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    Lb ⊔ Ideal.span {c} • Formalism.HermitianLatticesTheory.dual (hStd E n) Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  have hst : star (t : E) ≠ 0 := by
    rw [star_ne_zero]; exact_mod_cast ht
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.smul_le]
      intro a ha y hy
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      have hx : (Pi.single j (t : E) : Fin n → E) ∈ Lb := by
        rw [hLb]
        intro k
        by_cases hk : k = j
        · subst hk; exact ⟨t, by simp, fun _ => dvd_refl t⟩
        · exact ⟨0, by simp [hk], fun _ => dvd_zero t⟩
      obtain ⟨r, hr⟩ := (mem_dual_iff Lb y).1 hy _ hx
      have hsum : ∑ k, star ((Pi.single j (t : E) : Fin n → E) k) * y k = star (t : E) * y j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hsum] at hr
      refine ⟨s * r, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hr]
      rw [show algebraMap (𝓞 E) E c = (c : E) from rfl, hc, mul_assoc]
  · intro x hx
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one] at hx
    choose r hr using hx
    let x' : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let w : Fin n → E := fun j => if j.1 + 1 = n then x j / star (t : E) else 0
    have hx' : x' ∈ Lb := by
      rw [hLb]
      intro j
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x', hj], fun _ => dvd_zero t⟩
      · exact ⟨r j, by simp [x', hj, hr j], fun h => absurd h hj⟩
    have hw : w ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) Lb := by
      rw [mem_dual_iff]
      intro z hz
      refine Subring.sum_mem _ fun k _ => ?_
      by_cases hk : k.1 + 1 = n
      · obtain ⟨q, hq, hdiv⟩ := (hLb z).1 hz k
        obtain ⟨d, rfl⟩ := hdiv hk
        obtain ⟨s, hs⟩ := star_int d
        refine ⟨s * r k, ?_⟩
        simp only [w, hk, if_true, hq]
        rw [map_mul, hr k, show algebraMap (𝓞 E) E s = (s : E) from rfl, hs]
        push_cast
        rw [star_mul', ← hr k]
        field_simp
      · exact ⟨0, by simp [w, hk]⟩
    have hxe : x = x' + c • w := by
      funext j
      by_cases hj : j.1 + 1 = n
      · simp only [x', w, hj, if_true, Pi.add_apply, Pi.smul_apply, zero_add]
        rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl, hc]
        field_simp
      · simp [x', w, hj]
    rw [hxe]
    exact Submodule.add_mem_sup hx' (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hw)

end GlobalTheory.TwU.BaseComp

open scoped TensorProduct

namespace GlobalTheory.TwU.BaseComp

theorem latCo_one_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (sp : Spaces R F E) (hσ : ∀ x, (sp.cm.sig : E →+* E) x = star x) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E)) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    GlobalTheory.TwU.latCo sp J 1 c 1 Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  subst hJ
  have hfg : Lb.FG := fg_of_int Lb fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have hA : Formalism.L2.PairingIndexBounds.F.latAd (F := F) (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb :=
    GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ Lb Lb (Module.Finite.iff_fg.2 hfg) (fun x => by simp)
  unfold GlobalTheory.TwU.latCo
  rw [hA]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual ((sp.cm.sig : E →+* E)) hσ Lb
  unfold dualL at key
  erw [key]
  exact sup_dual_eq_std t c ht hc Lb hLb

end GlobalTheory.TwU.BaseComp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.TwU.latCo_base_eq_stdL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), (∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N i) (X.piT u)) → GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) 1 Lb = StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i) := by
  intro B X I hI hP l Z u i hi Lb hLb
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have ht : X.piT u ≠ 0 := by
    intro h0
    have hc := l.pr.piT_cop u
    have h0' : (B.primes X).piT u = 0 := h0
    rw [h0', map_zero] at hc
    exact not_isCoprime_zero_zero hc
  exact GlobalTheory.TwU.BaseComp.latCo_one_base _ (fun x => rfl) _ hG (X.piT u) (B.fields.conjO (X.piT u)) ht rfl Lb hLb
