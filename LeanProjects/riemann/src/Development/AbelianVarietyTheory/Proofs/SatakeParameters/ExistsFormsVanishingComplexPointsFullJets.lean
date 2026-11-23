import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenericForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioLinear
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominator
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoi
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.Jets

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem ev_ratio_eq_zero_iff {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {N n : ℕ} (ι : X ⟶ PSpace ℂ N)
    {f g : MvPolynomial (Fin (N + 1)) ℂ} (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {z : CxPts p (RingHom.id ℂ)} (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g)) :
    CxPts.evHom hz (fRatio ι f g hf hg) = 0 ↔ z ∉ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f) := by
  have e : X.basicOpen (fRatio ι f g hf hg) = fOpen ι g ⊓ fOpen ι f := by
    have e0 : X.basicOpen (fRatio ι f g hf hg) =
        ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ f g hf hg le_rfl) :=
      (Scheme.preimage_basicOpen ι _).symm
    rw [e0, basicOpen_frac]
    rfl
  have h1 := CxPts.mem_ptsIn_basicOpen hz (fRatio ι f g hf hg)
  rw [e, CxPts.mem_ptsIn_inf, CxPts.ev_eq hz] at h1
  constructor
  · intro h0 hf'
    exact (h1.1 ⟨hz, hf'⟩) h0
  · intro hn
    by_contra h0
    exact hn (h1.2 h0).2

theorem frac_smul_n {N n : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N n) :
    frac (grading ℂ N) V (c • f) g hcf hg hV = algebraMap ℂ Γ(PSpace ℂ N, V) c * frac (grading ℂ N) V f g hf hg hV := by
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [MvPolynomial.smul_eq_C_mul]
  ring

theorem fRatio_add_n {X : Scheme.{0}} {N n : ℕ} (ι : X ⟶ PSpace ℂ N) {f₁ f₂ g : MvPolynomial (Fin (N + 1)) ℂ}
    (h₁ : f₁ ∈ grading ℂ N n) (h₂ : f₂ ∈ grading ℂ N n) (h : f₁ + f₂ ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) :
    fRatio ι (f₁ + f₂) g h hg = fRatio ι f₁ g h₁ hg + fRatio ι f₂ g h₂ hg := by
  unfold fRatio
  rw [frac_add (ha := h₁) (ha₂ := h₂)]
  exact map_add _ _ _

theorem fRatio_smul_n {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N n : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) {f g : MvPolynomial (Fin (N + 1)) ℂ} (c : ℂ)
    (hf : f ∈ grading ℂ N n) (h : c • f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) :
    (show Sec p (fOpen ι g) from fRatio ι (c • f) g h hg) = c • (show Sec p (fOpen ι g) from fRatio ι f g hf hg) := by
  have e := RatLin.app_const p ι hι (Proj.basicOpen (grading ℂ N) g) c
  refine Eq.trans ?_ (Algebra.smul_def (A := Sec p (fOpen ι g)) c _).symm
  refine Eq.trans ?_ (congrArg (· * (show Sec p (fOpen ι g) from fRatio ι f g hf hg)) e)
  unfold fRatio
  rw [frac_smul_n _ f g hf hg le_rfl c h, map_mul, algebraMap_sections_eq]
  rfl

def rat {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N n : ℕ} (ι : X ⟶ PSpace ℂ N) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) : Sec p (fOpen ι g) := fRatio ι f g hf hg

theorem rat_sub_const {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N n : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) {f g : MvPolynomial (Fin (N + 1)) ℂ} (c : ℂ)
    (hf : f ∈ grading ℂ N n) (h : f + (-c) • g ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n) :
    rat p ι (f + (-c) • g) g h hg = rat p ι f g hf hg - algebraMap ℂ (Sec p (fOpen ι g)) c := by
  have hc : (-c) • g ∈ grading ℂ N n := Submodule.smul_mem _ _ hg
  have e1 : rat p ι (f + (-c) • g) g h hg = rat p ι f g hf hg + rat p ι ((-c) • g) g hc hg :=
    fRatio_add_n ι hf hc h hg
  have e2 : rat p ι ((-c) • g) g hc hg = (-c) • rat p ι g g hg hg := fRatio_smul_n p ι hι (-c) hg hc hg
  have e3 : rat p ι g g hg hg = 1 := fRatio_self ι g hg
  rw [e1, e2, e3, Algebra.algebraMap_eq_smul_one, neg_smul, sub_eq_add_neg]

theorem basicOpen_app_frac {X : Scheme.{0}} {N n : ℕ} (ι : X ⟶ PSpace ℂ N) (V : (PSpace ℂ N).Opens)
    {f g : MvPolynomial (Fin (N + 1)) ℂ} (hf : f ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    (hV : V ≤ Proj.basicOpen (grading ℂ N) g) :
    X.basicOpen ((ι.app V).hom (frac (grading ℂ N) V f g hf hg hV)) = ι ⁻¹ᵁ V ⊓ fOpen ι f := by
  have e0 : X.basicOpen ((ι.app V).hom (frac (grading ℂ N) V f g hf hg hV)) =
      ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) V f g hf hg hV) :=
    (Scheme.preimage_basicOpen ι _).symm
  rw [e0, basicOpen_frac]
  rfl

theorem ratio_sq_mem {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {N : ℕ} (ι : X ⟶ PSpace ℂ N) {m : ℕ}
    {q f₀ : MvPolynomial (Fin (N + 1)) ℂ} (hq : q ∈ grading ℂ N m)
    (hh : q * q ∈ grading ℂ N (m + m)) (hf₀ : f₀ ∈ grading ℂ N (m + m))
    {y : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι f₀))
    (hyq : q ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal) :
    fRatio ι (q * q) f₀ hh hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 := by
  have hle : f₀ ∈ grading ℂ N m * grading ℂ N m := by
    have e : ∀ k, grading ℂ N k = grading ℂ N 1 ^ k := fun k =>
      (MvPolynomial.homogeneousSubmodule_one_pow _ k).symm
    rw [e m, ← pow_add, ← e]
    exact hf₀
  have hK : ∀ b (hb : b ∈ grading ℂ N m),
      fRatio ι (q * b) f₀ (SetLike.mul_mem_graded hq hb) hf₀ ∈ RingHom.ker (CxPts.evHom hy) := by
    intro b hb
    refine (ev_ratio_eq_zero_iff ι _ hf₀ hy).2 fun h => ?_
    exact (mem_fOpen ι _ _).1 (CxPts.mem_ptsIn.1 h) (Ideal.mul_mem_right b _ hyq)
  have key : ∀ f ∈ grading ℂ N m * grading ℂ N m, ∃ hf : f ∈ grading ℂ N (m + m),
      fRatio ι (q * q) f₀ hh hf₀ * fRatio ι f f₀ hf hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 := by
    intro f hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro b hb c hc
      refine ⟨SetLike.mul_mem_graded hb hc, ?_⟩
      have e : fRatio ι (q * q) f₀ hh hf₀ * fRatio ι (b * c) f₀ (SetLike.mul_mem_graded hb hc) hf₀ =
          fRatio ι (q * b) f₀ (SetLike.mul_mem_graded hq hb) hf₀ *
            fRatio ι (q * c) f₀ (SetLike.mul_mem_graded hq hc) hf₀ := by
        unfold fRatio
        refine (map_mul _ _ _).symm.trans (Eq.trans (congrArg _ ?_) (map_mul _ _ _))
        exact frac_mul.trans ((frac_eq (by ring)).trans frac_mul.symm)
      rw [e, pow_two]
      exact Ideal.mul_mem_mul (hK b hb) (hK c hc)
    · rintro b c ⟨hb, hb'⟩ ⟨hc, hc'⟩
      refine ⟨add_mem hb hc, ?_⟩
      rw [fRatio_add_n ι hb hc, mul_add]
      exact add_mem hb' hc'
  obtain ⟨_, h⟩ := key f₀ hle
  rwa [fRatio_self, mul_one] at h

end GlobalTheory.EtProj.Jets

namespace GlobalTheory.EtProj.Jets
open GlobalTheory.ProjSpace

theorem eq_of_specializes {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (y : CxPts p (RingHom.id ℂ)) {x : X}
    (h : y.1 (IsLocalRing.closedPoint ℂ) ⤳ x) : x = y.1 (IsLocalRing.closedPoint ℂ) := by
  haveI : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hid : y.1 ≫ p = 𝟙 _ := y.2.trans (Spec.map_id _)
  haveI := isClosedImmersion_of_comp_eq_id p y.1 hid
  have hc : IsClosed ({y.1 (IsLocalRing.closedPoint ℂ)} : Set X) := by
    have := y.1.isClosedEmbedding.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint ℂ)
    exact (Set.image_singleton (f := ⇑y.1) (a := IsLocalRing.closedPoint ℂ)) ▸ this
  exact h.mem_closed hc rfl

theorem eq_zero_of_generic {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} {U : X.Opens}
    {y : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hg : y.1 (IsLocalRing.closedPoint ℂ) = genericPoint X) (u : Γ(X, U)) (hu : CxPts.evHom hy u = 0) :
    u = 0 := by
  have hyU : y.1 (IsLocalRing.closedPoint ℂ) ∈ U := CxPts.mem_ptsIn.1 hy
  have hgU : genericPoint X ∈ U := hg ▸ hyU
  have h1 : genericPoint X ∉ X.basicOpen u := by
    intro h
    rw [← hg] at h
    exact (CxPts.mem_ptsIn_basicOpen hy u).1 (CxPts.mem_ptsIn.2 h) (by rw [CxPts.ev_eq hy]; exact hu)
  rw [Scheme.mem_basicOpen _ _ _ hgU] at h1
  have h3 : X.presheaf.germ U (genericPoint X) hgU u = 0 := by
    by_contra h
    exact h1 (isUnit_iff_ne_zero.2 (show (X.presheaf.germ U (genericPoint X) hgU u : X.functionField) ≠ 0 from h))
  exact germ_injective_of_isIntegral X (genericPoint X) hgU (h3.trans (map_zero _).symm)

theorem pt_inj {X : Scheme.{0}} {p : X ⟶ Sp ℂ} [LocallyOfFiniteType p] {y z : CxPts p (RingHom.id ℂ)}
    (h : y.1 (IsLocalRing.closedPoint ℂ) = z.1 (IsLocalRing.closedPoint ℂ)) : y = z :=
  Subtype.ext (ext_of_apply_closedPoint_eq (K := ℂ) p (y.2.trans (Spec.map_id _)) (z.2.trans (Spec.map_id _)) h)

theorem exists_lin_sep {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) [IsClosedImmersion ι]
    (hp : ι ≫ PSpace.str ℂ N = p) (y : CxPts p (RingHom.id ℂ)) (x : X)
    (hx : x ≠ y.1 (IsLocalRing.closedPoint ℂ)) :
    ∃ l ∈ grading ℂ N 1, l ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal ∧
      l ∉ (ι.base x).asHomogeneousIdeal := by
  by_contra! H
  obtain ⟨i, hi⟩ := Generic.exists_X_notMem (ι.base (y.1 (IsLocalRing.closedPoint ℂ)))
  have hg := X_mem ℂ N i
  have hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (MvPolynomial.X i)) := CxPts.mem_ptsIn.2 hi
  let e : Sec p (fOpen ι (MvPolynomial.X i)) →+* ℂ := CxPts.evHom hy
  have he : ∀ c : ℂ, e (algebraMap ℂ _ c) = c := fun c => (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  let r : Fin (N + 1) → Sec p (fOpen ι (MvPolynomial.X i)) := fun l =>
    rat p ι (MvPolynomial.X l) (MvPolynomial.X i) (X_mem ℂ N l) hg
  have hL : ∀ l, (MvPolynomial.X l + (-e (r l)) • MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈ grading ℂ N 1 :=
    fun l => add_mem (X_mem ℂ N l) (Submodule.smul_mem _ _ hg)
  have hr : ∀ l, rat p ι _ _ (hL l) hg = r l - algebraMap ℂ _ (e (r l)) :=
    fun l => rat_sub_const p ι hp _ (X_mem ℂ N l) (hL l) hg
  have hLx : ∀ l, (MvPolynomial.X l + (-e (r l)) • MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      (ι.base x).asHomogeneousIdeal := by
    intro l
    refine H _ (hL l) ?_
    have h0 : e (rat p ι _ _ (hL l) hg) = 0 := by rw [hr, map_sub, he, sub_self]
    by_contra hn
    exact (ev_ratio_eq_zero_iff ι (hL l) hg hy).1 h0 (CxPts.mem_ptsIn.2 hn)
  have hxU : x ∈ fOpen ι (MvPolynomial.X i) := by
    intro h
    obtain ⟨l, hl⟩ := Generic.exists_X_notMem (ι.base x)
    have := Ideal.sub_mem _ (hLx l) (Ideal.mul_mem_left _ (MvPolynomial.C (-e (r l))) h)
    rw [← MvPolynomial.smul_eq_C_mul, add_sub_cancel_right] at this
    exact hl this
  let φ : Sec p (fOpen ι (MvPolynomial.X i)) →+* X.presheaf.stalk x := (X.presheaf.germ _ x hxU).hom
  let I : Ideal (Sec p (fOpen ι (MvPolynomial.X i))) := (IsLocalRing.maximalIdeal _).comap φ
  have hI : ∀ u : Sec p (fOpen ι (MvPolynomial.X i)), u ∈ I ↔ x ∉ X.basicOpen (U := fOpen ι (MvPolynomial.X i)) u :=
    fun u => (not_congr (Scheme.mem_basicOpen X (U := fOpen ι (MvPolynomial.X i)) u x hxU)).symm
  have key : ∀ u, u - algebraMap ℂ _ (e u) ∈ I := by
    intro u
    have hr' : Algebra.adjoin ℂ (Set.range r) = ⊤ := RatSpan.adjoin_fRatio_eq_top p ι hp hg
    have hu : u ∈ Algebra.adjoin ℂ (Set.range r) := hr' ▸ Algebra.mem_top
    induction hu using Algebra.adjoin_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [← hr, hI]
      intro h
      exact ((basicOpen_app_frac ι _ (hL l) hg le_rfl).le h).2 (hLx l)
    | algebraMap c => rw [he, sub_self]; exact I.zero_mem
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      convert I.add_mem ha hb using 1
      ring
    | mul a b _ _ ha hb =>
      rw [map_mul, map_mul]
      convert I.add_mem (I.mul_mem_right b ha) (I.mul_mem_left (algebraMap ℂ _ (e a)) hb) using 1
      ring
  have hU : IsAffineOpen (fOpen ι (MvPolynomial.X i)) :=
    (Proj.isAffineOpen_basicOpen (grading ℂ N) _ hg one_pos).preimage ι
  refine hx (eq_of_specializes y (specializes_iff_forall_open.2 fun s hs hxs => ?_))
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨x, hxs⟩ hxU
  refine hf (CxPts.mem_ptsIn.1 ((CxPts.mem_ptsIn_basicOpen hy f).2 fun h0 => ?_))
  have h1 : e f = 0 := (CxPts.ev_eq hy f).symm.trans h0
  have h2 : ∀ u, e u = 0 → u ∈ I := fun u hu => by simpa only [hu, map_zero, sub_zero] using key u
  exact (hI f).1 (h2 f h1) hxf

theorem exists_sep {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) [IsClosedImmersion ι]
    (hp : ι ≫ PSpace.str ℂ N = p) (S : Finset (CxPts p (RingHom.id ℂ))) (m : ℕ) (hm : S.card ≤ m) (x : X)
    (hx : ∀ y ∈ S, x ≠ y.1 (IsLocalRing.closedPoint ℂ)) :
    ∃ f ∈ grading ℂ N m, (∀ y ∈ S, f ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal) ∧
      f ∉ (ι.base x).asHomogeneousIdeal := by
  classical
  choose l hl1 hl2 hl3 using fun y : S => exists_lin_sep p ι hp y.1 x (hx y.1 y.2)
  obtain ⟨i, hi⟩ := Generic.exists_X_notMem (ι.base x)
  have hprod := SetLike.prod_mem_graded (grading ℂ N) (fun _ : S => 1) l (F := Finset.univ) (fun y _ => hl1 y)
  have hpow := SetLike.pow_mem_graded (m - S.card) (X_mem ℂ N i)
  have hdeg : (m - S.card) • 1 + ∑ _y ∈ (Finset.univ : Finset S), 1 = m := by
    simp only [smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
    omega
  refine ⟨MvPolynomial.X i ^ (m - S.card) * ∏ y, l y, hdeg ▸ SetLike.mul_mem_graded hpow hprod, ?_, ?_⟩
  · intro y hy
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem l (Finset.mem_univ ⟨y, hy⟩)) (hl2 ⟨y, hy⟩)
  · intro hmem
    have hP := (ι.base x).isPrime
    rcases hP.mem_or_mem hmem with h | h
    · exact hi (hP.mem_of_pow_mem _ h)
    · obtain ⟨y, -, hy⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
      exact hl3 y hy

end GlobalTheory.EtProj.Jets

namespace GlobalTheory.EtProj.Jets
open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem exists_lin_mul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) (hι : IsClosedImmersion ι)
    (hp : ι ≫ PSpace.str ℂ N = p) {k : ℕ} {g₀ w : MvPolynomial (Fin (N + 1)) ℂ} (hg₀ : g₀ ∈ grading ℂ N 1)
    (hw : w ∈ grading ℂ N k) {y : CxPts p (RingHom.id ℂ)}
    (hyw : w ∉ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal)
    (V : (PSpace ℂ N).Opens) (hV : V = Proj.basicOpen (grading ℂ N) g₀) (ha : g₀ * g₀ ^ k ∈ grading ℂ N (1 + k))
    (hVa : V ≤ Proj.basicOpen (grading ℂ N) (g₀ * g₀ ^ k))
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (ι ⁻¹ᵁ V)) (u : Γ(X, ι ⁻¹ᵁ V)) (hu : CxPts.evHom hy u = 0) :
    ∃ (l : MvPolynomial (Fin (N + 1)) ℂ) (hg : l * w ∈ grading ℂ N (1 + k)),
      l ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal ∧
      u - (ι.app V).hom (frac (grading ℂ N) V (l * w) (g₀ * g₀ ^ k) hg ha hVa) ∈ RingHom.ker (CxPts.evHom hy) ^ 2 := by
  subst hV
  have hy' : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀) := hy
  let e : Sec p (fOpen ι g₀) →+* ℂ := Generic.ev₀ ι g₀ hy'
  have he : ∀ c : ℂ, e (algebraMap ℂ _ c) = c := Generic.ev₀_algebraMap ι g₀ hy'
  let u' : Sec p (fOpen ι g₀) := u
  obtain ⟨c, hc⟩ := RatSpan.ratio_span_cotangent X p N ι hι hp g₀ hg₀ y hy' u' hu
  have h1 : u' - (Generic.fr ι g₀ hg₀ c - algebraMap ℂ _ (e (Generic.fr ι g₀ hg₀ c))) ∈ RingHom.ker e ^ 2 :=
    (Generic.mkQ_eq_mkQ ι g₀ hy' _ _).1 (((Generic.mkQ_eq_mkQ ι g₀ hy' _ _).2 hc).trans
      ((Generic.Lm_apply' ι g₀ hg₀ hy' c).symm.trans (Generic.Lm_apply ι g₀ hg₀ hy' hp c)))
  have hl₁ : Generic.lin c + (-e (Generic.fr ι g₀ hg₀ c)) • g₀ ∈ grading ℂ N 1 :=
    add_mem (Generic.lin_mem c) (Submodule.smul_mem _ _ hg₀)
  have hs : rat p ι _ g₀ hl₁ hg₀ = Generic.fr ι g₀ hg₀ c - algebraMap ℂ _ (e (Generic.fr ι g₀ hg₀ c)) :=
    rat_sub_const p ι hp _ (Generic.lin_mem c) hl₁ hg₀
  have hs0 : e (rat p ι _ g₀ hl₁ hg₀) = 0 := by rw [hs, map_sub, he, sub_self]
  rw [← hs] at h1
  generalize Generic.lin c + (-e (Generic.fr ι g₀ hg₀ c)) • g₀ = l₁ at hl₁ hs0 h1
  have hgk : g₀ ^ k ∈ grading ℂ N k := by simpa using SetLike.pow_mem_graded k hg₀
  have hVk : Proj.basicOpen (grading ℂ N) g₀ ≤ Proj.basicOpen (grading ℂ N) (g₀ ^ k) :=
    fun x hx h => hx (x.isPrime.mem_of_pow_mem k h)
  let t : Sec p (fOpen ι g₀) := (ι.app _).hom (frac (grading ℂ N) _ w (g₀ ^ k) hw hgk hVk)
  have ht : e t ≠ 0 := by
    have h2 := (CxPts.mem_ptsIn_basicOpen hy' t).1 (CxPts.mem_ptsIn.2
      ((basicOpen_app_frac ι _ hw hgk hVk).ge ⟨CxPts.mem_ptsIn.1 hy', hyw⟩))
    exact fun h => h2 ((CxPts.ev_eq hy' t).trans h)
  have hl : (e t)⁻¹ • l₁ ∈ grading ℂ N 1 := Submodule.smul_mem _ _ hl₁
  have hly : l₁ ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
    by_contra hn
    exact (ev_ratio_eq_zero_iff ι hl₁ hg₀ hy').1 hs0 (CxPts.mem_ptsIn.2 hn)
  refine ⟨(e t)⁻¹ • l₁, SetLike.mul_mem_graded hl hw, ?_, ?_⟩
  · rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ hly
  · let v : Sec p (fOpen ι g₀) := (ι.app _).hom (frac (grading ℂ N) _ ((e t)⁻¹ • l₁ * w) (g₀ * g₀ ^ k)
      (SetLike.mul_mem_graded hl hw) ha hVa)
    have e1 : v = rat p ι _ g₀ hl hg₀ * t :=
      Eq.trans (congrArg (ι.app _).hom (frac_mul_eq rfl).symm) (map_mul _ _ _)
    have e2 : rat p ι _ g₀ hl hg₀ = (e t)⁻¹ • rat p ι l₁ g₀ hl₁ hg₀ := fRatio_smul_n p ι hp _ hl₁ hl hg₀
    have h3 : 1 - algebraMap ℂ _ (e t)⁻¹ * t ∈ RingHom.ker e := by
      rw [RingHom.mem_ker, map_sub, map_mul, he, map_one, inv_mul_cancel₀ ht, sub_self]
    have h4 : u' - v ∈ RingHom.ker e ^ 2 := by
      have h5 := Ideal.mul_mem_mul (RingHom.mem_ker.2 hs0) h3
      rw [← pow_two] at h5
      convert add_mem h1 h5 using 1
      rw [e1, e2, Algebra.smul_def]
      ring
    exact h4

theorem exists_form_jet {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (hp : ι ≫ PSpace.str ℂ N = p) (S : Finset (CxPts p (RingHom.id ℂ))) {k n : ℕ}
    (hn : n = 1 + k) (hk : S.card ≤ k) {g₀ : MvPolynomial (Fin (N + 1)) ℂ} (hg₀ : g₀ ∈ grading ℂ N 1)
    (ha : g₀ * g₀ ^ k ∈ grading ℂ N n) {y : CxPts p (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (g₀ * g₀ ^ k))) (u : Γ(X, fOpen ι (g₀ * g₀ ^ k)))
    (hu : CxPts.evHom hy u = 0) :
    ∃ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ grading ℂ N n),
      (∀ z ∈ S, g ∈ (ι.base (z.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal) ∧
      u - fRatio ι g (g₀ * g₀ ^ k) hg ha ∈ RingHom.ker (CxPts.evHom hy) ^ 2 := by
  classical
  subst hn
  obtain ⟨w, hw, hwS, hwy⟩ := exists_sep p ι hp (S.erase y) k (Finset.card_erase_le.trans hk)
    (y.1 (IsLocalRing.closedPoint ℂ)) (fun z hz e => (Finset.mem_erase.1 hz).1 (pt_inj e).symm)
  have hV : Proj.basicOpen (grading ℂ N) (g₀ * g₀ ^ k) = Proj.basicOpen (grading ℂ N) g₀ := by
    rw [← pow_succ', Proj.basicOpen_pow _ _ _ (Nat.succ_pos k)]
  obtain ⟨l, hg, hl, h⟩ := exists_lin_mul p ι hι hp hg₀ hw hwy _ hV ha le_rfl hy u hu
  refine ⟨l * w, hg, fun z hz => ?_, h⟩
  by_cases e : z = y
  · subst e
    exact Ideal.mul_mem_right w _ hl
  · exact Ideal.mul_mem_left _ l (hwS z (Finset.mem_erase.2 ⟨e, hz⟩))

end GlobalTheory.EtProj.Jets

namespace GlobalTheory.EtProj.Jets
open GlobalTheory.ProjSpace

section Defs

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (S : Finset (CxPts p (RingHom.id ℂ)))

def vanS (k : ℕ) : Submodule ℂ (MvPolynomial (Fin (N + 1)) ℂ) :=
  grading ℂ N k ⊓ ⨅ y ∈ S, (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal.toIdeal.restrictScalars ℂ

theorem mem_vanS {k : ℕ} {f : MvPolynomial (Fin (N + 1)) ℂ} :
    f ∈ vanS ι S k ↔ f ∈ grading ℂ N k ∧ ∀ y ∈ S, f ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
  simp only [vanS, Submodule.mem_inf, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  rfl

def vanAt (k : ℕ) (x : X) : Submodule ℂ (vanS ι S k) :=
  ((ι.base x).asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap (vanS ι S k).subtype

variable (p) in

abbrev evS {U : X.Opens} {y : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U) : Sec p U →+* ℂ :=
  CxPts.evHom hy

variable (p) in

def sqI {U : X.Opens} {y : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U) : Submodule ℂ (Sec p U) :=
  ((RingHom.ker (evS p hy)) ^ 2).restrictScalars ℂ

def jet (hp : ι ≫ PSpace.str ℂ N = p) (k : ℕ) {a : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N k)
    {y : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι a)) :
    vanS ι S k →ₗ[ℂ] Sec p (fOpen ι a) ⧸ sqI p hy where
  toFun f := (sqI p hy).mkQ (fRatio ι f.1 a ((mem_vanS ι S).1 f.2).1 ha)
  map_add' f g := (congrArg (sqI p hy).mkQ
    (fRatio_add_n ι ((mem_vanS ι S).1 f.2).1 ((mem_vanS ι S).1 g.2).1 _ ha)).trans (map_add _ _ _)
  map_smul' c f := (congrArg (sqI p hy).mkQ
    (fRatio_smul_n p ι hp c ((mem_vanS ι S).1 f.2).1 _ ha)).trans (map_smul _ _ _)

theorem jet_range (hp : ι ≫ PSpace.str ℂ N = p) (d : ℕ) [SmoothOfRelativeDimension d p]
    (k : ℕ) {a : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N k)
    (hU : IsAffineOpen (fOpen ι a)) {y : CxPts p (RingHom.id ℂ)} (hyS : y ∈ S)
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι a))
    (honto : ∀ u : Γ(X, fOpen ι a), CxPts.evHom hy u = 0 →
      ∃ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ grading ℂ N k),
        (∀ z ∈ S, g ∈ (ι.base (z.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal) ∧
        u - fRatio ι g a hg ha ∈ RingHom.ker (CxPts.evHom hy) ^ 2) :
    FiniteDimensional ℂ (LinearMap.range (jet ι S hp k ha hy)) ∧
      Module.finrank ℂ (LinearMap.range (jet ι S hp k ha hy)) = d ∧
      ∀ u : Sec p (fOpen ι a), CxPts.evHom hy u = 0 → (sqI p hy).mkQ u ∈ LinearMap.range (jet ι S hp k ha hy) := by
  obtain ⟨g, hg0, hgs, hgi⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d (fOpen ι a) hU y hy
  have hq : ∀ u v : Sec p (fOpen ι a), (sqI p hy).mkQ u = (sqI p hy).mkQ v ↔
      u - v ∈ RingHom.ker (evS p hy) ^ 2 := by
    intro u v
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Iff.rfl
  have hmem : ∀ u : Sec p (fOpen ι a), CxPts.evHom hy u = 0 →
      (sqI p hy).mkQ u ∈ LinearMap.range (jet ι S hp k ha hy) := by
    intro u hu
    obtain ⟨f, hf, hfS, hfu⟩ := honto u hu
    have hfv : f ∈ vanS ι S k := (mem_vanS ι S).2 ⟨hf, hfS⟩
    exact ⟨⟨f, hfv⟩, ((hq _ _).2 hfu).symm⟩
  have hspan : LinearMap.range (jet ι S hp k ha hy) =
      Submodule.span ℂ (Set.range fun j => (sqI p hy).mkQ (g j)) := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      have hf0 : CxPts.evHom hy (fRatio ι f.1 a ((mem_vanS ι S).1 f.2).1 ha) = 0 := by
        rw [ev_ratio_eq_zero_iff, CxPts.mem_ptsIn, mem_fOpen, not_not]
        exact ((mem_vanS ι S).1 f.2).2 y hyS
      obtain ⟨b, hb⟩ := hgs _ hf0
      change (sqI p hy).mkQ _ ∈ _
      rw [(hq _ _).2 hb, map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmem _ (hg0 j)
  have hli : LinearIndependent ℂ (fun j => (sqI p hy).mkQ (g j)) := by
    rw [Fintype.linearIndependent_iff]
    intro b hb
    refine congrFun (hgi b ?_)
    have : (sqI p hy).mkQ (∑ j, b j • g j) = (sqI p hy).mkQ 0 := by
      rw [map_sum]
      simpa only [map_smul, map_zero] using hb
    have h2 := (hq _ _).1 this
    rw [sub_zero] at h2
    exact h2
  refine ⟨?_, ?_, hmem⟩
  · rw [hspan]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  · rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Defs

end GlobalTheory.EtProj.Jets

namespace GlobalTheory.EtProj.Jets
open GlobalTheory.ProjSpace

theorem exists_jet_forms : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (h : MvPolynomial (Fin (N + 1)) ℂ) (g : Fin d → MvPolynomial (Fin (N + 1)) ℂ)
      (hh : h ∈ GlobalTheory.ProjSpace.grading ℂ N n) (hg : ∀ j, g j ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (∀ j, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (g j)) ∧
      (∀ y ∈ S, ∀ j, y ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) ∧
      (∀ z : CxPts p (RingHom.id ℂ), z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι h) →
        (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) → z ∈ S) ∧
      ∀ y ∈ S, ∀ (f₀ : MvPolynomial (Fin (N + 1)) ℂ) (hf₀ : f₀ ∈ GlobalTheory.ProjSpace.grading ℂ N n)
        (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f₀)),
        GlobalTheory.EtProj.fRatio ι h f₀ hh hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 ∧
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (g j) f₀ (hg j) hf₀) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  intro X _ p d _ N ι hι hp S
  classical
  haveI : IsClosedImmersion ι := hι
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI := isProper_str ℂ N
  haveI : CompactSpace (PSpace ℂ N) := QuasiCompact.compactSpace_of_compactSpace (PSpace.str ℂ N)
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace ι
  haveI : IsNoetherian X := {}
  have hcoh : ∀ x : X, Order.coheight x ≤ d := fun x => GlobalTheory.AffineCover.coheight_le_of_smooth p inferInstance x
  set m := S.card + 1 with hm
  set n := m + m with hn
  have hn0 : 0 < n := by omega
  let Simg : Set X := {x | ∃ y ∈ S, x = y.1 (IsLocalRing.closedPoint ℂ)}
  have hsep : ∀ x : X, x ∉ Simg → ∃ f ∈ grading ℂ N m,
      (∀ y ∈ S, f ∈ (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal) ∧
        f ∉ (ι.base x).asHomogeneousIdeal :=
    fun x hx => exists_sep p ι hp S m (by omega) x (fun y hy e => hx ⟨y, hy, e⟩)
  have hvanm : ∀ x : X, x ∉ Simg → vanAt ι S m x ≠ ⊤ := by
    intro x hx htop
    obtain ⟨f, hf, hfS, hfx⟩ := hsep x hx
    have : (⟨f, (mem_vanS ι S).2 ⟨hf, hfS⟩⟩ : vanS ι S m) ∈ vanAt ι S m x := htop ▸ Submodule.mem_top
    exact hfx this
  have hvann : ∀ x : X, x ∉ Simg → vanAt ι S n x ≠ ⊤ := by
    intro x hx htop
    obtain ⟨f, hf, hfS, hfx⟩ := hsep x hx
    have hff : f * f ∈ vanS ι S n :=
      (mem_vanS ι S).2 ⟨SetLike.mul_mem_graded hf hf, fun y hy => Ideal.mul_mem_left _ _ (hfS y hy)⟩
    have : (⟨f * f, hff⟩ : vanS ι S n) ∈ vanAt ι S n x := htop ▸ Submodule.mem_top
    exact hfx (((ι.base x).isPrime.mem_or_mem this).elim id id)
  obtain ⟨g₀, hg₀, -, hg₀S⟩ := GlobalTheory.EtProj.exists_form_genericPoint_cxPts X p N ι 1 S
  have hnk : n = 1 + (n - 1) := by omega
  have ha : g₀ * g₀ ^ (n - 1) ∈ grading ℂ N n := by
    have h0 : g₀ ^ (n - 1) ∈ grading ℂ N (n - 1) := by simpa using SetLike.pow_mem_graded (n - 1) hg₀
    have h1 := SetLike.mul_mem_graded hg₀ h0
    rwa [← hnk] at h1
  have haS : ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι (g₀ * g₀ ^ (n - 1))) := by
    intro y hy
    have h0 := (mem_fOpen ι _ _).1 (CxPts.mem_ptsIn.1 (hg₀S y hy))
    have hP := (ι.base (y.1 (IsLocalRing.closedPoint ℂ))).isPrime
    exact CxPts.mem_ptsIn.2 fun h => (hP.mem_or_mem h).elim h0 fun h' => h0 (hP.mem_of_pow_mem _ h')
  have honto := fun (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ S) =>
    exists_form_jet p ι hι hp S hnk (by omega) hg₀ ha (haS y hy)
  generalize g₀ * g₀ ^ (n - 1) = a at ha haS honto
  have hU : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen (grading ℂ N) a ha hn0).preimage ι
  have hR := fun y : (S : Set (CxPts p (RingHom.id ℂ))) =>
    jet_range ι S hp d n ha hU y.2 (haS y.1 y.2) (honto y.1 y.2)
  let J := fun y : (S : Set (CxPts p (RingHom.id ℂ))) => jet ι S hp n ha (haS y.1 y.2)
  have hgenS : 0 < d → genericPoint X ∉ Simg := by
    rintro hd ⟨y, hy, e⟩
    obtain ⟨b, hb0, -, hbi⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d (fOpen ι a) hU y (haS y hy)
    have hz : b ⟨0, hd⟩ = 0 := eq_zero_of_generic (haS y hy) e.symm _ (hb0 _)
    have hsum : (∑ j, (Pi.single ⟨0, hd⟩ (1 : ℂ) : Fin d → ℂ) j • b j) = b ⟨0, hd⟩ := by
      simp [Pi.single_apply]
    have h1 := congrFun (hbi (Pi.single ⟨0, hd⟩ 1) (by rw [hsum, hz]; exact zero_mem _)) ⟨0, hd⟩
    simp at h1
  have key : ∀ k, k ≤ d → ∃ c : Fin k → vanS ι S n,
      (∀ i, genericPoint X ∈ fOpen ι (c i).1) ∧
      (∀ x : X, x ∉ Simg → (∀ i, x ∉ fOpen ι (c i).1) → (k : ℕ∞) ≤ Order.coheight x) ∧
      ∀ y : (S : Set (CxPts p (RingHom.id ℂ))), LinearIndependent ℂ (J y ∘ c) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun i => i.elim0, fun x _ _ => by simp, fun y => linearIndependent_empty_type⟩
    | succ k ih =>
      intro hk
      obtain ⟨c, hgen, hZ, hli⟩ := ih (Nat.le_of_succ_le hk)
      let Z : Set X := ⋂ i, (↑(fOpen ι (c i).1) : Set X)ᶜ
      have hZc : IsClosed Z := isClosed_iInter fun i => (fOpen ι (c i).1).isOpen.isClosed_compl
      obtain ⟨T, hTf, hTZ, hT⟩ := Generic.exists_finite_gen Z hZc
      let T' : Set X := T \ Simg
      have := (hTf.diff (t := Simg)).to_subtype
      let W : Option (T' ⊕ (S : Set (CxPts p (RingHom.id ℂ)))) → Submodule ℂ (vanS ι S n) := fun o =>
        o.elim (vanAt ι S n (genericPoint X)) (Sum.elim (fun t => vanAt ι S n t.1)
          (fun y => (Submodule.span ℂ (Set.range (J y ∘ c))).comap (J y)))
      have hW : ∀ o, W o ≠ ⊤ := by
        rintro (_ | t | y)
        · exact hvann _ (hgenS (by omega))
        · exact hvann _ t.2.2
        · intro htop
          obtain ⟨hfd, hrk, -⟩ := hR y
          have hle : LinearMap.range (J y) ≤ Submodule.span ℂ (Set.range (J y ∘ c)) := by
            rintro _ ⟨v, rfl⟩
            have : v ∈ W (some (Sum.inr y)) := htop ▸ Submodule.mem_top
            exact this
          haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range (J y ∘ c))
          have h1 := (Submodule.finrank_mono hle).trans (finrank_range_le_card _)
          rw [hrk, Fintype.card_fin] at h1
          omega
      obtain ⟨c', hc'⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
      refine ⟨Fin.snoc c c', fun i => ?_, fun x hx hxi => ?_, fun y => ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact (mem_fOpen ι _ _).2 (hc' none)
        · rw [Fin.snoc_castSucc]
          exact hgen i
      · have hxZ : x ∈ Z := Set.mem_iInter.2 fun i => by
          have := hxi i.castSucc
          rw [Fin.snoc_castSucc] at this
          exact this
        have hx' : x ∉ fOpen ι c'.1 := by
          have := hxi (Fin.last k)
          rwa [Fin.snoc_last] at this
        obtain ⟨t, ht, htx⟩ := hT x hxZ
        by_cases htS : t ∈ Simg
        · obtain ⟨y, hy, rfl⟩ := htS
          exact absurd ⟨y, hy, eq_of_specializes y htx⟩ hx
        have htZ := hTZ ht
        have h1 := hZ t htS (fun i => Set.mem_iInter.1 htZ i)
        have h2 := Generic.coheight_step htx _ (fOpen ι c'.1).isOpen
          ((mem_fOpen ι _ _).2 (hc' (some (Sum.inl ⟨t, ht, htS⟩)))) hx'
        calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; ring
          _ ≤ Order.coheight t + 1 := by gcongr
          _ ≤ Order.coheight x := h2
      · rw [Fin.comp_snoc, linearIndependent_fin_snoc]
        exact ⟨hli y, hc' (some (Sum.inr y))⟩
  obtain ⟨c, hgen, hZ, hli⟩ := key d le_rfl
  let Z : Set X := ⋂ i, (↑(fOpen ι (c i).1) : Set X)ᶜ
  have hZc : IsClosed Z := isClosed_iInter fun i => (fOpen ι (c i).1).isOpen.isClosed_compl
  obtain ⟨T, hTf, hTZ, hT⟩ := Generic.exists_finite_gen Z hZc
  let T' : Set X := T \ Simg
  have := (hTf.diff (t := Simg)).to_subtype
  obtain ⟨q, hq⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (fun t : T' => vanAt ι S m t.1)
    (fun t => hvanm _ t.2.2)
  obtain ⟨hqm, hqS⟩ := (mem_vanS ι S).1 q.2
  have hh : q.1 * q.1 ∈ grading ℂ N n := SetLike.mul_mem_graded hqm hqm
  let g : Fin d → MvPolynomial (Fin (N + 1)) ℂ := fun j => (c j).1
  have hg : ∀ j, g j ∈ grading ℂ N n := fun j => ((mem_vanS ι S).1 (c j).2).1
  refine ⟨n, q.1 * q.1, g, hh, hg, hn0, hgen, ?_, ?_, ?_⟩
  · intro y hy j hyj
    exact ((mem_fOpen ι _ _).1 (CxPts.mem_ptsIn.1 hyj)) (((mem_vanS ι S).1 (c j).2).2 y hy)
  · intro z hzh hzg
    have hx : z.1 (IsLocalRing.closedPoint ℂ) ∈ Simg := by
      by_contra hx
      have hxg : ∀ i, z.1 (IsLocalRing.closedPoint ℂ) ∉ fOpen ι (c i).1 :=
        fun i h => hzg i (CxPts.mem_ptsIn.2 h)
      have hxZ : z.1 (IsLocalRing.closedPoint ℂ) ∈ Z := Set.mem_iInter.2 hxg
      obtain ⟨t, ht, htx⟩ := hT _ hxZ
      by_cases htS : t ∈ Simg
      · obtain ⟨y, hy, rfl⟩ := htS
        exact hx ⟨y, hy, eq_of_specializes y htx⟩
      have htq : t ∈ fOpen ι (q.1 * q.1) := by
        intro hmem
        exact hq ⟨t, ht, htS⟩ (((ι.base t).isPrime.mem_or_mem hmem).elim id id)
      have hxh : z.1 (IsLocalRing.closedPoint ℂ) ∉ fOpen ι (q.1 * q.1) := fun h => hzh (CxPts.mem_ptsIn.2 h)
      have h2 := Generic.coheight_step htx _ (fOpen ι (q.1 * q.1)).isOpen htq hxh
      have h3 := hZ t htS (fun i => Set.mem_iInter.1 (hTZ ht) i)
      have h4 : (d : ℕ∞) + 1 ≤ Order.coheight t + 1 := by gcongr
      have := h4.trans (h2.trans (hcoh _))
      norm_cast at this
      omega
    obtain ⟨y, hy, e⟩ := hx
    rw [pt_inj e]
    exact hy
  · intro y hy f₀ hf₀ hyf
    refine ⟨ratio_sq_mem ι hqm hh hf₀ hyf (hqS y hy), ?_⟩
    · have hya := haS y hy
      obtain ⟨hfd, hrk, hmem⟩ := hR ⟨y, hy⟩
      refine GlobalTheory.EtProj.span_ratio_of_span_ratio X p N ι hι n hn0 d g a f₀ hg ha hf₀ y hya hyf ?_
      let r : Fin d → Sec p (fOpen ι a) := fun j => fRatio ι (g j) a (hg j) ha
      suffices H : ∀ u : Sec p (fOpen ι a), evS p hya u = 0 →
          u ∈ Ideal.span (Set.range r) ⊔ RingHom.ker (evS p hya) ^ 2 from fun u hu => H u hu
      intro u hu
      have hsp : Submodule.span ℂ (Set.range (J ⟨y, hy⟩ ∘ c)) = LinearMap.range (J ⟨y, hy⟩) :=
        Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ⟨c j, rfl⟩))
          (by rw [finrank_span_eq_card (hli ⟨y, hy⟩), Fintype.card_fin, hrk])
      have h1 := hmem u hu
      rw [← hsp] at h1
      obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
      have h2 : u - ∑ j, b j • r j ∈ RingHom.ker (evS p hya) ^ 2 := by
        have e1 : (sqI p hya).mkQ (∑ j, b j • r j) = (sqI p hya).mkQ u := by
          rw [← hb, map_sum]
          simp only [map_smul]
          rfl
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at e1
        have e2 := neg_mem e1
        rw [neg_sub] at e2
        exact e2
      have e : u = (u - ∑ j, b j • r j) + ∑ j, b j • r j := (sub_add_cancel _ _).symm
      rw [e]
      refine Ideal.add_mem _ (Ideal.mem_sup_right h2) (Ideal.mem_sup_left ?_)
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.EtProj.Jets
