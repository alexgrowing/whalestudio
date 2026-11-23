import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankFrac
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

namespace SemilocResidueFrac

section Eval

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_iff (W : Ideal (MRing ι)) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {f : MRing ι} : aeval x f = 0 ↔ f ∈ W := by
  rw [← hx, RingHom.mem_ker]

def den (P W : Ideal (MRing ι)) [W.IsPrime] : Submonoid (MRing ι ⧸ P) :=
  W.primeCompl.map (Ideal.Quotient.mk P)

theorem den_le (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    den P W ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  rintro _ ⟨w, hw, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    Ideal.mem_primeCompl_iff.1 hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

abbrev locAt (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra (FractionRing (MRing ι ⧸ P)) (den P W) (den_le P W hPW)

def quotEv (P W : Ideal (MRing ι)) (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : MRing ι ⧸ P →+* Ω :=
  Ideal.Quotient.lift P (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom fun _ hf =>
    (aeval_eq_zero_iff W x hx).2 (hPW hf)

theorem quotEv_den (P W : Ideal (MRing ι)) [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) (t : den P W) : IsUnit (quotEv P W hPW x hx t) := by
  obtain ⟨_, w, hw, rfl⟩ := t
  exact isUnit_iff_ne_zero.2 fun h => Ideal.mem_primeCompl_iff.1 hw ((aeval_eq_zero_iff W x hx).1 h)

def evAt (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : locAt P W hPW →+* Ω :=
  IsLocalization.lift (M := den P W) (quotEv_den P W hPW x hx)

theorem evAt_algebraMap (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) (f : MRing ι) :
    evAt P W hPW x hx (algebraMap _ _ (Ideal.Quotient.mk P f)) = aeval x f :=
  IsLocalization.lift_eq _ _

theorem locRing_le (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    locRing P W ≤ (locAt P W hPW).toSubring := by
  rw [locRing, Subring.closure_le]
  rintro _ ⟨u, w, a, hw, hwW, -, -, rfl⟩
  exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P w, ⟨w, hwW, rfl⟩, rfl⟩

def evLoc (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : locRing P W →+* Ω :=
  (evAt P W hPW x hx).comp
    { toFun := fun z => ⟨z, locRing_le P W hPW z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem evLoc_spec (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} {u w : MRing ι}
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) :
    evLoc P W hPW x hx z * aeval x w = aeval x u := by
  have e' : (⟨z, locRing_le P W hPW z.2⟩ : locAt P W hPW) * algebraMap _ _ (Ideal.Quotient.mk P w) =
      algebraMap _ _ (Ideal.Quotient.mk P u) := Subtype.ext e
  have h := congrArg (evAt P W hPW x hx) e'
  rw [map_mul, evAt_algebraMap, evAt_algebraMap] at h
  exact (congrArg (· * aeval x w) (rfl : evLoc P W hPW x hx z = evAt P W hPW x hx ⟨z, locRing_le P W hPW z.2⟩)).trans h

theorem isUnit_of_rep (P W : Ideal (MRing ι)) [P.IsPrime] (hPW : P ≤ W) {z : locRing P W} {u w : MRing ι}
    {a : K → ℕ} (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) (huW : u ∉ W)
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) : IsUnit z := by
  have hu0 : regularityLocalResidue_holds.frHom P u ≠ 0 := fun h => huW (hPW (regularityLocalResidue_holds.frHom_eq_zero_iff.1 h))
  refine IsUnit.of_mul_eq_one (⟨_, regularityLocalResidue_holds.mem_locRing_of_form hPW hw hu huW⟩ : locRing P W) (Subtype.ext ?_)
  show (z : FractionRing (MRing ι ⧸ P)) * (regularityLocalResidue_holds.frHom P w * (regularityLocalResidue_holds.frHom P u)⁻¹) = 1
  rw [← mul_assoc, e, mul_inv_cancel₀ hu0]

theorem evLoc_ne_zero_iff (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} :
    evLoc P W hPW x hx z ≠ 0 ↔ IsUnit z := by
  refine ⟨fun hz => ?_, fun hz => (hz.map (evLoc P W hPW x hx)).ne_zero⟩
  obtain ⟨u, w, a, hu, hw, hwW, e⟩ := regularityLocalResidue_holds.exists_rep ‹W.IsPrime› z.2
  have h := evLoc_spec P W hPW x hx e
  refine isUnit_of_rep P W hPW hu hw (fun huW => hz ?_) e
  rw [(aeval_eq_zero_iff W x hx).2 huW] at h
  exact (mul_eq_zero.1 h).resolve_right (mt (aeval_eq_zero_iff W x hx).1 hwW)

theorem aeval_memI {F : Type} [Field F] [Algebra F Ω] (L : IntermediateField F Ω) {y : (Σ k, ι k) → Ω}
    (hy : ∀ p, y p ∈ L) (u : MRing ι) : aeval y u ∈ L := by
  induction u using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ a
  | add f g hf hg =>
    rw [map_add]
    exact add_mem hf hg
  | mul_X f p hf =>
    rw [map_mul, aeval_X]
    exact mul_mem hf (hy p)

end Eval

section Field

variable {Ω : Type} [Field Ω]

def rangeSubfield {R : Type*} [CommRing R] (ρ : R →+* Ω) (hinv : ∀ r, ρ r ≠ 0 → ∃ r', ρ r' * ρ r = 1) :
    Subfield Ω :=
  { ρ.range with
    inv_mem' := by
      rintro _ ⟨r, rfl⟩
      by_cases h : ρ r = 0
      · rw [h, inv_zero]
        exact ⟨0, map_zero ρ⟩
      · obtain ⟨r', e⟩ := hinv r h
        exact ⟨r', eq_inv_of_mul_eq_one_left e⟩ }

theorem mem_rangeSubfield {R : Type*} [CommRing R] (ρ : R →+* Ω) (hinv : ∀ r, ρ r ≠ 0 → ∃ r', ρ r' * ρ r = 1)
    (r : R) : ρ r ∈ rangeSubfield ρ hinv :=
  ⟨r, rfl⟩

theorem algebraMap_mem_of_int {F : Type} [Field F] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (S : Subfield Ω) (c : F) : algebraMap F Ω c ∈ S := by
  obtain ⟨a, b, -, rfl⟩ := hF c
  rw [map_div₀, map_intCast, map_intCast]
  exact div_mem (intCast_mem S a) (intCast_mem S b)

theorem mem_of_atPrime {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] (𝔪 : Ideal B) [𝔪.IsPrime]
    [IsLocalization.AtPrime C 𝔪] (ρ : C →+* Ω) (hker : ∀ b, ρ (algebraMap B C b) = 0 ↔ b ∈ 𝔪) (S : Subfield Ω)
    (hS : ∀ b, ρ (algebraMap B C b) ∈ S) (z : C) : ρ z ∈ S := by
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl z
  have e := congrArg ρ (IsLocalization.mk'_spec C b t)
  rw [map_mul] at e
  have ht : ρ (algebraMap B C t) ≠ 0 := fun h => t.2 ((hker t).1 h)
  rw [eq_div_of_mul_eq ht e]
  exact div_mem (hS b) (hS t)

theorem length_quot_eq_relfinrank {F : Type} [Field F] [Algebra F Ω] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔪 : Ideal B) (ρ : B →+* Ω) (hker : ∀ b, ρ b = 0 ↔ b ∈ 𝔪)
    (L₀ L : IntermediateField F Ω) (hle : L₀ ≤ L) (hB : ∀ b, ρ b ∈ L) (hBs : ∀ y ∈ L, ∃ b, ρ b = y)
    (hA : ∀ a, ρ (algebraMap A B a) ∈ L₀) (hAs : ∀ y ∈ L₀, ∃ a, ρ (algebraMap A B a) = y) :
    Module.length A (B ⧸ 𝔪) = (IntermediateField.relfinrank L₀ L : ℕ∞) := by
  set E := IntermediateField.extendScalars hle with hE
  let ψA : A →+* L₀ := (ρ.comp (algebraMap A B)).codRestrict L₀ hA
  let ψB : B →+* E := ρ.codRestrict E hB
  have hψA : Function.Surjective ψA := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hAs y hy
    exact ⟨a, Subtype.ext ha⟩
  have hψB : Function.Surjective ψB := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hBs y hy
    exact ⟨b, Subtype.ext hb⟩
  let _ : Algebra A L₀ := ψA.toAlgebra
  let _ : Algebra A E := ((algebraMap L₀ E).comp ψA).toAlgebra
  have : IsScalarTower A L₀ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hkerψ : RingHom.ker ψB = 𝔪 := by
    ext b
    rw [RingHom.mem_ker, ← hker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hH : ∀ b ∈ 𝔪, ψB b = 0 := fun b hb => by
    rw [← hkerψ] at hb
    exact hb
  let φ := Ideal.Quotient.lift 𝔪 ψB hH
  let φl : (B ⧸ 𝔪) →ₗ[A] E :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := by
        intro a m
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, RingHom.id_apply, Algebra.smul_def]
        apply Subtype.ext
        show ρ (algebraMap A B a * b) = ρ (algebraMap A B a) * ρ b
        exact map_mul ρ _ _ }
  have hφ : Function.Bijective φl :=
    ⟨(Ideal.injective_lift_iff hH).2 hkerψ, fun y => by
      obtain ⟨b, hb⟩ := hψB y
      exact ⟨Ideal.Quotient.mk 𝔪 b, hb⟩⟩
  let φe := LinearEquiv.ofBijective φl hφ
  have : Module.Finite A (B ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite A E := Module.Finite.equiv φe
  have : Module.Finite L₀ E := Module.Finite.of_restrictScalars_finite A L₀ E
  rw [φe.length_eq, Module.length_eq_of_surjective (R := L₀) hψA, Module.length_eq_finrank,
    IntermediateField.relfinrank_eq_finrank_of_le hle]

end Field

end SemilocResidueFrac

open SemilocResidueFrac SemilocRankFrac regularityLocalResidue_holds in

theorem SemilocResidueFrac.proof (hFin : SemilocFinite.Statement) (hMax : SemilocMaxIdeals.Statement) :
    SemilocResidueFrac.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW W' hW' _ G' i' hi' F _ _ hF
  classical
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hW'p : W'.IsPrime := hW'.1.1
  have hPW' : P' ≤ W' := hW'.2.1
  have hWW : imageZ v W' = W := hW'.2.2
  have hWp : W.IsPrime := hW.1.1.1
  have hQW : imageZ v P' ≤ W := le_sup_left.trans hW.1.1.2
  have hFinAB := (hFin K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW).1
  obtain ⟨h𝔪, hloc⟩ := (hMax K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW).1 W' hW'
  let y' : (Σ k', ι' k') → G'.Φ' := fun q => G'.x' q / G'.x' ⟨q.1, i' q.1⟩
  have hx0 : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h =>
    hi' k' ((aeval_eq_zero_iff W' G'.x' G'.genericFibre_ker_target).1 (by rw [aeval_X]; exact h))
  let ρ' := evLoc P' W' hPW' G'.x' G'.genericFibre_ker_target
  let ρB := ρ'.comp (semiToLoc P' (fibreOver v P' W) W' hW')
  have hkerB : ∀ b, ρB b = 0 ↔ b ∈ semiMaxIdeal P' (fibreOver v P' W) W' hW' := fun b => by
    rw [semiMaxIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← not_iff_not, not_not,
      ← Ne, RingHom.comp_apply, evLoc_ne_zero_iff]
  have hnz : ∀ f : MRing ι, aeval (G'.x' ∘ v) f = 0 ↔ f ∈ W := fun f => by
    rw [← aeval_rename, aeval_eq_zero_iff W' G'.x' G'.genericFibre_ker_target, ← hWW]
    rfl
  have hA : ∀ (a : locRing (imageZ v P') W) (u w : MRing ι),
      (a : FractionRing (MRing ι ⧸ imageZ v P')) * frHom (imageZ v P') w = frHom (imageZ v P') u →
      ρB (algebraMap _ _ a) * aeval (G'.x' ∘ v) w = aeval (G'.x' ∘ v) u := by
    intro a u w e
    have hfr : ∀ f : MRing ι, fracMapZ v P' (frHom (imageZ v P') f) = frHom P' (rename v f) :=
      fun f => fracMapZ_algebraMap v P' f
    have e' := congrArg (fracMapZ v P') e
    rw [map_mul, hfr, hfr] at e'
    rw [← aeval_rename, ← aeval_rename]
    exact evLoc_spec P' W' hPW' G'.x' G'.genericFibre_ker_target
      (z := semiToLoc P' (fibreOver v P' W) W' hW' (locToSemiloc hv P' W a)) e'
  have hAunit : ∀ a : locRing (imageZ v P') W, ρB (algebraMap _ _ a) ≠ 0 → IsUnit a := fun a ha => by
    obtain ⟨u, w, c, hu, hw, hwW, e⟩ := exists_rep hWp a.2
    have h := hA a u w e
    refine isUnit_of_rep (imageZ v P') W hQW hu hw (fun huW => ha ?_) e
    rw [(hnz u).2 huW] at h
    exact (mul_eq_zero.1 h).resolve_right (mt (hnz w).1 hwW)
  have hch : ∀ {a b : K'}, a = b → G'.x' ⟨a, i' a⟩ = G'.x' ⟨b, i' b⟩ := by
    rintro a b rfl
    rfl
  have hsc : G'.x' = fun q => y' q * G'.x' ⟨q.1, i' q.1⟩ :=
    funext fun q => (div_mul_cancel₀ _ (hx0 q.1)).symm
  have hscv : G'.x' ∘ v = fun p => (y' ∘ v) p * G'.x' ⟨κ p.1, i' (κ p.1)⟩ := funext fun p => by
    show G'.x' (v p) = G'.x' (v p) / G'.x' ⟨(v p).1, i' (v p).1⟩ * G'.x' ⟨κ p.1, i' (κ p.1)⟩
    rw [hch (hv.2.2.1 p), div_mul_cancel₀ _ (hx0 _)]

  have hρ'L : ∀ z, ρ' z ∈ IntermediateField.adjoin F (Set.range y') := fun z => by
    obtain ⟨u, w, c, hu, hw, hwW, e⟩ := exists_rep hW'p z.2
    have h := evLoc_spec P' W' hPW' G'.x' G'.genericFibre_ker_target e
    have e2 := aeval_scale_div y' hx0 hu hw
    rw [← hsc] at e2
    rw [eq_div_of_mul_eq (mt (aeval_eq_zero_iff W' G'.x' G'.genericFibre_ker_target).1 hwW) h, e2]
    exact div_mem (aeval_memI (IntermediateField.adjoin F (Set.range y'))
        (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) u)
      (aeval_memI (IntermediateField.adjoin F (Set.range y')) (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) w)
  have hρAL₀ : ∀ a : locRing (imageZ v P') W, ρB (algebraMap _ _ a) ∈ IntermediateField.adjoin F (Set.range (y' ∘ v)) := fun a => by
    obtain ⟨u, w, c, hu, hw, hwW, e⟩ := exists_rep hWp a.2
    have h := hA a u w e
    have e2 := aeval_scale_div (y' ∘ v) (c := fun k => G'.x' ⟨κ k, i' (κ k)⟩) (fun k => hx0 _) hu hw
    rw [← hscv] at e2
    rw [eq_div_of_mul_eq (mt (hnz w).1 hwW) h, e2]
    exact div_mem (aeval_memI (IntermediateField.adjoin F (Set.range (y' ∘ v)))
        (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) u)
      (aeval_memI (IntermediateField.adjoin F (Set.range (y' ∘ v))) (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) w)

  have hinvB : ∀ b, ρB b ≠ 0 → ∃ c, ρB c * ρB b = 1 := fun b hb => by
    obtain ⟨c, i, hi, e⟩ := h𝔪.exists_inv fun h => hb ((hkerB b).2 h)
    refine ⟨c, ?_⟩
    have h := congrArg ρB e
    rwa [map_add, map_mul, (hkerB i).2 hi, add_zero, map_one] at h
  have hinvA : ∀ a : locRing (imageZ v P') W, ρB (algebraMap _ (semiLocRing P' (fibreOver v P' W)) a) ≠ 0 →
      ∃ c, ρB (algebraMap _ (semiLocRing P' (fibreOver v P' W)) c) * ρB (algebraMap _ _ a) = 1 :=
    fun a ha => by
      obtain ⟨u, rfl⟩ := hAunit a ha
      refine ⟨(↑(u⁻¹) : locRing (imageZ v P') W), ?_⟩
      rw [← map_mul ρB, ← map_mul (algebraMap _ _), Units.inv_mul, map_one, map_one]
  let SB := rangeSubfield ρB hinvB
  let SA := rangeSubfield (ρB.comp (algebraMap (locRing (imageZ v P') W) _)) hinvA
  have hLB : IntermediateField.adjoin F (Set.range y') ≤
      SB.toIntermediateField (algebraMap_mem_of_int hF SB) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    have hz := mem_locRing_of_form hPW' (AvoidRing.isMultiHomog_X q.1 q.2)
      (AvoidRing.isMultiHomog_X q.1 (i' q.1)) (hi' q.1)
    have e := evLoc_spec P' W' hPW' G'.x' G'.genericFibre_ker_target (z := ⟨_, hz⟩) (u := X q) (w := X ⟨q.1, i' q.1⟩)
      (by rw [mul_assoc, inv_mul_cancel₀ (frHom_X_ne_zero hPW' hi' q.1), mul_one])
    rw [aeval_X, aeval_X] at e
    show y' q ∈ SB
    rw [show y' q = ρ' ⟨_, hz⟩ from (eq_div_of_mul_eq (hx0 q.1) e).symm]
    let _ := (semiToLoc P' (fibreOver v P' W) W' hW').toAlgebra
    exact mem_of_atPrime (semiMaxIdeal P' (fibreOver v P' W) W' hW') ρ' hkerB SB
      (mem_rangeSubfield ρB hinvB) _
  have hL₀A : IntermediateField.adjoin F (Set.range (y' ∘ v)) ≤
      SA.toIntermediateField (algebraMap_mem_of_int hF SA) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨j, hj⟩ := hW.2 k
    obtain ⟨⟨k0, i0⟩, hp0⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    obtain rfl : k0 = k := hv.1 ((hv.2.2.1 ⟨k0, i0⟩).symm.trans (congrArg Sigma.fst hp0))
    have mem : ∀ i₁ : ι k0, frHom (imageZ v P') (X ⟨k0, i₁⟩) * (frHom (imageZ v P') (X ⟨k0, j⟩))⁻¹ ∈
        locRing (imageZ v P') W := fun i₁ =>
      mem_locRing_of_form hQW (AvoidRing.isMultiHomog_X k0 i₁) (AvoidRing.isMultiHomog_X k0 j) hj
    have hj0 : frHom (imageZ v P') (X ⟨k0, j⟩) ≠ 0 := fun h => hj (hQW (frHom_eq_zero_iff.1 h))
    have val : ∀ i₁ : ι k0, ρB (algebraMap _ _ (⟨_, mem i₁⟩ : locRing (imageZ v P') W)) * G'.x' (v ⟨k0, j⟩) =
        G'.x' (v ⟨k0, i₁⟩) := fun i₁ => by
      have := hA ⟨_, mem i₁⟩ (X ⟨k0, i₁⟩) (X ⟨k0, j⟩)
        (by rw [mul_assoc, inv_mul_cancel₀ hj0, mul_one])
      rwa [aeval_X, aeval_X] at this
    have hxj : G'.x' (v ⟨k0, j⟩) ≠ 0 := fun h => hj ((hnz _).1 (by rw [aeval_X]; exact h))
    have e : (y' ∘ v) ⟨k0, i⟩ = ρB (algebraMap _ _ (⟨_, mem i⟩ : locRing (imageZ v P') W)) /
        ρB (algebraMap _ _ (⟨_, mem i0⟩ : locRing (imageZ v P') W)) := by
      rw [eq_div_of_mul_eq hxj (val i), eq_div_of_mul_eq hxj (val i0), div_div_div_cancel_right₀ hxj, hp0]
      show G'.x' (v ⟨k0, i⟩) / G'.x' ⟨(v ⟨k0, i⟩).1, i' (v ⟨k0, i⟩).1⟩ = _
      rw [hch (hv.2.2.1 _)]
    show (y' ∘ v) ⟨k0, i⟩ ∈ SA
    rw [e]
    exact div_mem (mem_rangeSubfield _ hinvA _) (mem_rangeSubfield _ hinvA _)
  have hle : IntermediateField.adjoin F (Set.range (y' ∘ v)) ≤ IntermediateField.adjoin F (Set.range y') :=
    IntermediateField.adjoin_le_iff.2 (by
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨v p, rfl⟩)
  exact length_quot_eq_relfinrank (semiMaxIdeal P' (fibreOver v P' W) W' hW') ρB hkerB _ _ hle
    (fun b => hρ'L _) (fun y hy => hLB hy) hρAL₀ (fun y hy => hL₀A hy)

end GroundTheory.Heights₂.Heights.Inter
