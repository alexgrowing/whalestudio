import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem exists_linear_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → A) (hr : Algebra.adjoin ℂ (Set.range r) = ⊤) (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (a : A) (ha : e a = 0) :
    ∃ c : ι → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
  have hK : ∀ x : A, x - algebraMap ℂ A (e x) ∈ RingHom.ker e := fun x => by
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  have hP : ∀ x, ∃ c : ι → ℂ,
      x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
    intro x
    have hx : x ∈ Algebra.adjoin ℂ (Set.range r) := hr ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      refine ⟨Pi.single l 1, ?_⟩
      have hs : ∑ l', (Pi.single l 1 : ι → ℂ) l' • (r l' - algebraMap ℂ A (e (r l'))) =
          r l - algebraMap ℂ A (e (r l)) := by
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      rw [hs, sub_self]
      exact zero_mem _
    | algebraMap c =>
      refine ⟨0, ?_⟩
      simp [he]
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c + d, ?_⟩
      have h : x + y - algebraMap ℂ A (e (x + y)) - ∑ l, (c + d) l • (r l - algebraMap ℂ A (e (r l))) =
          (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) := by
        simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        ring
      rw [h]
      exact add_mem hc hd
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨e x • d + e y • c, ?_⟩
      have h : x * y - algebraMap ℂ A (e (x * y)) -
            ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
          algebraMap ℂ A (e x) * (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) +
          algebraMap ℂ A (e y) * (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) := by
        have hsum : ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
            e x • ∑ l, d l • (r l - algebraMap ℂ A (e (r l))) +
              e y • ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, add_smul, smul_eq_mul, smul_eq_mul, mul_smul,
            mul_smul]
        rw [hsum, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
        ring
      have hxy : (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) ∈ RingHom.ker e ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hK x) (hK y)
      rw [h]
      exact add_mem (add_mem (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)) hxy
  obtain ⟨c, hc⟩ := hP a
  rw [ha, map_zero, sub_zero] at hc
  exact ⟨c, hc⟩

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem algebraMap_basicOpen {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (c : ℂ) :
    algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) c =
      (Proj.awayToSection (grading ℂ N) g).hom
        (HomogeneousLocalization.fromZeroRingHom (grading ℂ N) _ (algebraMap ℂ (grading ℂ N 0) c)) := by
  have h := GlobalTheory.QCoh.Qcqs.baseRingHom_comp_SpecMap (Proj.toSpecZero (grading ℂ N))
    (CommRingCat.ofHom (algebraMap ℂ (grading ℂ N 0))) (Proj.basicOpen (grading ℂ N) g)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading ℂ N) hg one_pos
  rw [GlobalTheory.QCoh.Qcqs.baseRingHom.eq_1 (Proj.toSpecZero _), h'] at h
  exact congrArg (fun φ => φ.hom c) h

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem frac_eq_aeval {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) ℂ) (hf : f ∈ grading ℂ N (n • 1)) :
    frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) f (g ^ n) hf (SetLike.pow_mem_graded n hg)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) =
      MvPolynomial.aeval (fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) f := by
  refine ext fun x hx => ?_
  let t : Localization.AtPrime x.asHomogeneousIdeal.toIdeal := Localization.mk 1 ⟨g, hx⟩
  have hC : (ev (grading ℂ N) _ x hx).comp (algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) =
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ) _).comp MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply]
    rw [algebraMap_basicOpen hg, awayToSection_fromZero, ev_frac, ← Localization.mk_one_eq_algebraMap]
    rfl
  have hX : ∀ l, ev (grading ℂ N) _ x hx (frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) = algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := by
    intro l
    rw [ev_frac, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    congr 1
    · simp
    · ext1; simp
  have hf' : f.IsHomogeneous n := by simpa using hf
  erw [ev_frac]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hC]
  have hfun : (ev (grading ℂ N) _ x hx ∘ fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) =
      fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := funext hX
  rw [hfun, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf']
  have h3 : MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)).comp MvPolynomial.C)
      (fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l)) f = algebraMap _ _ f := by
    have := MvPolynomial.eval₂_comp_left (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
      (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) MvPolynomial.C MvPolynomial.X f
    rw [MvPolynomial.eval₂_eta] at this
    exact this.symm
  rw [h3, Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  · simp
  · ext1; simp

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem mem_adjoin_frac {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1)
    (s : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) :
    s ∈ Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) := by
  obtain ⟨y, rfl⟩ := (Proj.basicOpenIsoAway (grading ℂ N) g hg one_pos).commRingCatIsoToRingEquiv.surjective s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hg y
  change (Proj.awayToSection (grading ℂ N) g).hom _ ∈ _
  rw [awayToSection_mk, frac_eq_aeval hg n f hf, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_fRatio_eq_top {S : Scheme.{0}} (p : S ⟶ Sp ℂ) (ι : S ⟶ PSpace ℂ N) [IsClosedImmersion ι]
    (hp : ι ≫ PSpace.str ℂ N = p) {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) :
    Algebra.adjoin (A := Sec p (fOpen ι g)) ℂ
      (Set.range fun l => fRatio ι (MvPolynomial.X l) g (X_mem ℂ N l) hg) = ⊤ := by
  subst hp
  let ψ : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) →ₐ[ℂ] Sec (ι ≫ PSpace.str ℂ N) (fOpen ι g) :=
    { (ι.app (Proj.basicOpen (grading ℂ N) g)).hom with
      commutes' := fun c => GlobalTheory.QCoh.Qcqs.app_baseRingHom ι (PSpace.str ℂ N) _ c }
  have hsurj : Function.Surjective ψ :=
    ι.app_surjective _ (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg one_pos)
  rw [eq_top_iff]
  intro a _
  obtain ⟨s, rfl⟩ := hsurj a
  have h1 : ψ s ∈ (Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl)).map ψ := Subalgebra.mem_map.2 ⟨s, mem_adjoin_frac hg s, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h1
  exact h1

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

theorem ratio_span_cotangent : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι g)), let U := GlobalTheory.EtProj.fOpen ι g; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; let e : Sec p U →+* ℂ := CxPts.evHom hy; ∀ a : Sec p U, e a = 0 → ∃ c : Fin (N + 1) → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ (Sec p U) (e (r l))) ∈ RingHom.ker e ^ 2 := by
  intro X p N ι hι hp g hg y hy U r e a ha
  have hr : Algebra.adjoin ℂ (Set.range r) = ⊤ := adjoin_fRatio_eq_top p ι hp hg
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c =>
    (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  exact exists_linear_mod_sq r hr e he a ha

end GlobalTheory.EtProj.RatSpan
