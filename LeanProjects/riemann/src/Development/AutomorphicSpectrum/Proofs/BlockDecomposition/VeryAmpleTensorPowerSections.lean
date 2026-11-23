import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem mem_basicOpen_prod {X : Scheme.{0}} {U : X.Opens} {ι : Type} (s : Finset ι) (g : ι → Γ(X, U)) {y : X}
    (hy : y ∈ U) : y ∈ X.basicOpen (∏ l ∈ s, g l) ↔ ∀ l ∈ s, y ∈ X.basicOpen (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact hy
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_nonzeroLocus_secMono {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (hk : 1 ≤ k) (y : X) :
    y ∈ nonzeroLocus (secMono h a w) ↔ ∀ l, y ∈ nonzeroLocus (a (w l)) := by
  constructor
  · intro hy l
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus hy
    have h1 := (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).1 hy
    exact (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).2
      ((mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).1 h1 l (Finset.mem_univ l))
  · intro hy
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus (hy ⟨0, hk⟩)
    refine (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).2 ?_
    exact (mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).2 fun l _ =>
      (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).1 (hy l)

theorem prod_update_eq_mul {B τ : Type} [CommMonoid B] {k : ℕ} (φ : τ → B) (w : Fin k → τ) (l : Fin k) (c : τ)
    (ρ : B) (h : φ c = ρ * φ (w l)) :
    ∏ l', φ (Function.update w l c l') = ρ * ∏ l', φ (w l') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun l' => φ (w l')) (Finset.mem_univ l), Function.update_self, h, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun l' hl' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl')]

theorem secRatio_secMono_update {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (l : Fin k) (c : τ)
    (hl : nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l))) :
    secRatio (secMono h a w) (secMono h a (Function.update w l c)) = resG X hl (secRatio (a (w l)) (a c)) := by
  refine (eq_secRatio _ _ fun κ => ?_).symm
  have key := secRatio_on (a (w l)) (a c) κ
    (W := nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ) (inf_le_left.trans hl) inf_le_right
  have := prod_update_eq_mul (fun t => resG X (inf_le_right : nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ ≤ L.U κ)
    (chartFn (a t) κ)) w l c _ key
  change resG X _ (∏ l', chartFn (a (Function.update w l c l')) κ) = _ * resG X _ (∏ l', chartFn (a (w l')) κ)
  rw [map_prod, map_prod, resG_resG]
  exact this

theorem mem_of_basicOpen {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (F : Γ(X, U))
    (hV : V = X.basicOpen F) (hle : V ≤ U) (S : Subring Γ(X, V)) (h1 : ∀ x, resG X hle x ∈ S)
    (g : Γ(X, V)) (hg : g ∈ S) (hgF : g * resG X hle F = 1) (z : Γ(X, V)) : z ∈ S := by
  subst hV
  have := hU.isLocalization_basicOpen F
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers F) z
  have hx' : z * resG X hle F ^ n = resG X hle x := by
    have e : ∀ t, algebraMap Γ(X, U) Γ(X, X.basicOpen F) t = resG X hle t := fun _ => rfl
    simpa only [e, map_pow] using hx
  have : z = resG X hle x * g ^ n := by
    rw [← hx', mul_assoc, ← mul_pow, mul_comm (resG X hle F), hgF, one_pow, mul_one]
  rw [this]
  exact S.mul_mem (h1 x) (S.pow_mem hg n)

theorem veryAmpleBy_secMono : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  intro R _ X f L d D k h p a hL hk hva m e
  obtain ⟨hcov, hch⟩ := hva
  refine ⟨?_, fun j => ?_⟩
  · refine top_unique ?_
    rw [← hcov]
    refine iSup_le fun i => ?_
    rw [← nonzeroLocus_secMono_const h a i hk]
    refine le_trans ?_ (le_iSup _ (e.symm fun _ => i))
    simp only [Equiv.apply_symm_apply, le_refl]
  · beta_reduce
    let w : Fin k → Fin (p + 1) := e j
    let l₀ : Fin k := ⟨0, hk⟩
    obtain ⟨hU, r, hr, hsurj⟩ := hch (w l₀)
    obtain rfl : r = fun t => secRatio (a (w l₀)) (a t) := funext fun t => eq_secRatio _ _ (hr t)
    have hN : ∀ l, nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l)) := fun l y hy =>
      (mem_nonzeroLocus_secMono h a w hk y).1 hy l
    have hV : nonzeroLocus (secMono h a w) = X.basicOpen (∏ l, secRatio (a (w l₀)) (a (w l))) := by
      ext y
      constructor
      · intro hy
        refine (mem_basicOpen_prod Finset.univ _ (hN l₀ hy)).2 fun l _ => ?_
        rw [basicOpen_secRatio]
        exact ⟨hN l₀ hy, hN l hy⟩
      · intro hy
        have hy₀ := X.basicOpen_le _ hy
        refine (mem_nonzeroLocus_secMono h a w hk y).2 fun l => ?_
        have := (mem_basicOpen_prod Finset.univ _ hy₀).1 hy l (Finset.mem_univ l)
        rw [basicOpen_secRatio] at this
        exact this.2
    refine ⟨hV ▸ hU.basicOpen _, fun t => secRatio (secMono h a w) (secMono h a (e t)),
      fun t κ => secRatio_spec _ _ κ, fun z => ?_⟩
    let S := (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (secMono h a w)))
      fun t => secRatio (secMono h a w) (secMono h a (e t))).range
    have hρ : ∀ v, secRatio (secMono h a w) (secMono h a v) ∈ S := fun v =>
      ⟨MvPolynomial.X (e.symm v), by simp⟩
    have hC : ∀ c : R, cst f (nonzeroLocus (secMono h a w)) c ∈ S := fun c =>
      ⟨MvPolynomial.C c, by simp⟩
    have h1 : ∀ x, resG X (hN l₀) x ∈ S := fun x => by
      obtain ⟨P, rfl⟩ := hsurj x
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (rs_cst f (hN l₀) c).symm ▸ hC c
      | add P Q hP hQ =>
        rw [map_add, map_add]
        exact S.add_mem hP hQ
      | mul_X P t hP =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        refine S.mul_mem hP ?_
        rw [← secRatio_secMono_update h a w l₀ t (hN l₀)]
        exact hρ _
    obtain ⟨P, hP⟩ : z ∈ S := mem_of_basicOpen hU _ hV (hN l₀) S h1
      (∏ l, secRatio (secMono h a w) (secMono h a (Function.update w l (w l₀))))
      (S.prod_mem fun l _ => hρ _) (by
        rw [map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun l _ => ?_
        rw [secRatio_secMono_update h a w l (w l₀) (hN l), mul_comm,
          secRatio_mul_secRatio _ _ _ (hN l₀) (hN l), secRatio_self, map_one]) z
    exact ⟨P, hP⟩

end GlobalTheory.CompanionTheory.FormalAlg
