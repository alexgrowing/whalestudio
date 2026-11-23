import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpanFrame

open GlobalTheory.AmpleSpan

theorem secScal_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (a : ℤ)
    {T T' : Over S} (k : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (k ▷ A) (whiskerRight_snd k A) s s') :
    GeneratorPullback.SecScal L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) s' (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s
      (k ▷ A).left 1 := by
  have e : (k ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  refine (secScal_const_iff hL e).2 fun i Z r z hz => ?_
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
  have le := chart_le_res A L (k ▷ A) (whiskerRight_snd k A) a (fun _ => i)
  refine Eq.symm ((congrArg (gs r z _) (H fun _ => i)).trans ?_)
  exact (gs_res r z le hm _).trans (gs_pull r (k ▷ A).left z _ (le (x := r z) hm) _)

theorem valR_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}
    {ε' : K' → ℤ} {χ : Y ⟶ X} {χ' : Y' ⟶ X} {h : Y' ⟶ Y} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)}
    (H : GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1) {R : Type} [CommRing R] (x : Sp R ⟶ Y') (j : L.ι)
    (hx : ⊤ ≤ (x ≫ χ') ⁻¹ᵁ L.U j) :
    valR (x ≫ h) (LB.wchart L (fun _ : K => χ) (fun _ => j)) (s.f fun _ => j) =
      valR x (LB.wchart L (fun _ : K' => χ') (fun _ => j)) (s'.f fun _ => j) := by
  subst e
  have E := H (fun _ => j) (fun _ => j) (by rintro (a | a) (b | b) _ <;> rfl)
  have hm : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K' => h ≫ χ) (fun _ => j) ⊓ LB.wchart L (fun _ : K => h ≫ χ) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hx hz, Set.mem_iInter.2 fun _ => hx hz⟩
  have E' := congrArg (valR x _) E
  rw [HolHom.valR_res _ _ _ hm, resTop, map_one, one_mul] at E'
  exact (HolHom.valR_comp _ _ _ _).trans (E'.trans (HolHom.valR_res _ _ _ hm))

theorem exists_span_powOver (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ}
    (hN : 1 ≤ N) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ (m : ℕ) (b : Fin m → LB.Sec (powOver P.A P.L U N)), ∀ (X' Y' : Scheme.{0}) [IsAffine Y']
      (h : X' ⟶ (P.A.hom ⁻¹ᵁ U).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ U.toScheme), IsPullback h f' (P.A.hom ∣_ U) g →
      ∀ (K : Type) [Fintype K] (ε : K → ℤ) (φ : X' ⟶ P.A.left), h ≫ (P.A.hom ⁻¹ᵁ U).ι = φ → ∑ k, ε k = N →
      ∀ b' : Fin m → LB.Sec (LB.LinComb P.L (fun _ : K => φ) ε),
        (∀ i, GeneratorPullback.SecScal P.L _ _ (b' i) (fun _ : Fin N => (P.A.hom ⁻¹ᵁ U).ι) (fun _ => 1) (b i) h 1) →
        ∀ s, InSpan f' b' s := by
  obtain ⟨m, b₀, hb₀⟩ := exists_sections_span_affine hS S P N hN U hU
  obtain ⟨h₀, e₀, -, -, hE⟩ := translate_powOver_LPow P.A P.isLB N (U := U) (overRes (T := baseOver S) U)
    (𝟙 U.toScheme) (by simp)
  obtain ⟨E, hE⟩ := hE (IsIso.id _)
  refine ⟨m + 1, fun i => E.symm (b₀ i), fun X' Y' _ h f' g sq K _ ε φ e hε b' hb' s => ?_⟩
  let T' : Over S := Over.mk (g ≫ U.ι)
  have : IsAffine T'.left := ‹IsAffine Y'›
  let k : T' ⟶ overRes (T := baseOver S) U := Over.homMk g (by simp [T'])
  obtain ⟨h', e', sq', -, -⟩ := translate_powOver_LPow P.A P.isLB N (U := U) T' g rfl
  let b'' : Fin (m + 1) → LB.Sec (LPow P.A P.L N T') := fun i =>
    SecM.toSec P.A (SecAff.pull P.A P.L N k (SecM.ofSec P.A (b₀ i)))
  have hb'' : ∀ i, IsPullSec P.A P.L N (k ▷ P.A) (whiskerRight_snd k P.A) (b₀ i) (b'' i) := fun i =>
    (SecAff.isPullSec_iff P.A P.L N _ _ _).2 rfl
  have hsp := hb₀ T' k b'' hb''
  let θ := sq.isoIsPullback _ _ sq'
  have θ₁ : θ.hom ≫ h' = h := sq.isoIsPullback_hom_fst _ _ sq'
  have θ₂ : θ.hom ≫ (fst T' P.A).left = f' := sq.isoIsPullback_hom_snd _ _ sq'
  have θ₃ : θ.hom ≫ (snd T' P.A).left = φ := by rw [← e', ← Category.assoc, θ₁, e]
  obtain ⟨F, hF⟩ := exists_equiv_secScal P.isLB (h := θ.hom) (formEq_const (K := Fin 1) (K' := K)
    (ε := fun _ => (N : ℤ)) (ε' := ε) θ₃ (by simp [hε]))
  have θ₄ : θ.hom ≫ (k ▷ P.A).left ≫ h₀ = h := by
    rw [← cancel_mono (P.A.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, e₀, ← Over.comp_left, whiskerRight_snd, θ₃, e]
  refine InSpan.secScal P.isLB (h := θ.hom) (f := (fst T' P.A).left) (g := 𝟙 Y') (θ₂.trans (Category.comp_id _).symm)
    (t := b'') (s := F.symm s) ((inSpan_iff_mem_span P.A b'' _).2 (by rw [hsp]; trivial)) (fun i => ?_)
    ((hF _ _).2 (F.apply_symm_apply s))
  refine (secScal_iff_sval P.isLB).2 fun Z r z J hJ => ?_
  rw [← SectionScalarValuation.secScal_sval (hb' i) r z hJ, ← SectionScalarValuation.secScal_sval (secScal_of_isPullSec P.A P.isLB N k (hb'' i)) _ z hJ,
    ← SectionScalarValuation.secScal_sval ((hE _ _).2 (E.apply_symm_apply (b₀ i))) _ z hJ, Category.assoc, Category.assoc, θ₄]

end GlobalTheory.SpanFrame
