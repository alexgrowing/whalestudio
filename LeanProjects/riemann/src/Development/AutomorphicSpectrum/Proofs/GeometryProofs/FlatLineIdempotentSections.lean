import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem glue_rel (R : Type) [CommRing R] [IsReduced R]
    (Rel : ∀ (F : Type) [Field F], (R →+* F) → F → Prop)
    (huniq : ∀ (F : Type) [Field F] (ψ : R →+* F) (r r' : F), Rel F ψ r → Rel F ψ r' → r = r')
    (hcov : ∀ q : PrimeSpectrum R, ∃ g a : R, g ∉ q.asIdeal ∧
      ∀ (F : Type) [Field F] (ψ : R →+* F), ψ g ≠ 0 → Rel F ψ (ψ a / ψ g)) :
    ∃ s : R, ∀ (F : Type) [Field F] (ψ : R →+* F), Rel F ψ (ψ s) := by
  classical

  let P : R → R → Prop := fun g a => ∀ (F : Type) [Field F] (ψ : R →+* F),
    (ψ g = 0 → ψ a = 0) ∧ (ψ g ≠ 0 → Rel F ψ (ψ a / ψ g))
  have hP : ∀ q : PrimeSpectrum R, ∃ g a : R, g ∉ q.asIdeal ∧ P g a := fun q => by
    obtain ⟨g, a, hg, h⟩ := hcov q
    refine ⟨g * g, a * g, fun hm => hg ((q.2.mem_or_mem hm).elim id id), fun F _ ψ => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
    · have : ψ g = 0 := by simpa [map_mul] using h0
      simp [this]
    · have h1 : ψ g ≠ 0 := fun h => h0 (by simp [h])
      have e : ψ (a * g) / ψ (g * g) = ψ a / ψ g := by
        rw [map_mul, map_mul]; field_simp
      rw [e]; exact h F ψ h1
  have hc : ∀ g a g' a', P g a → P g' a' → a * g' = a' * g := fun g a g' a' h h' => by
    have hz : a * g' - a' * g ∈ nilradical R := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro I hI
      haveI : I.IsPrime := hI
      let ψ : R →+* I.ResidueField := algebraMap R I.ResidueField
      have key : ψ (a * g' - a' * g) = 0 := by
        rw [map_sub, map_mul, map_mul]
        by_cases h1 : ψ g = 0
        · rw [(h _ ψ).1 h1, h1]; simp
        by_cases h2 : ψ g' = 0
        · rw [(h' _ ψ).1 h2, h2]; simp
        have := huniq _ ψ _ _ ((h _ ψ).2 h1) ((h' _ ψ).2 h2)
        field_simp at this
        linear_combination this
      have : a * g' - a' * g ∈ RingHom.ker ψ := key
      rwa [Ideal.ker_algebraMap_residueField] at this
    have : a * g' - a' * g = 0 := by
      rw [nilradical_eq_zero] at hz
      exact hz
    exact sub_eq_zero.1 this
  have htop : Ideal.span {g | ∃ a, P g a} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, a, hg, h⟩ := hP ⟨m, hm.isPrime⟩
    exact hg (hle (Ideal.subset_span ⟨a, h⟩))
  have h1 : (1 : R) ∈ Ideal.span {g | ∃ a, P g a} := by rw [htop]; trivial

  have gen : ∀ x ∈ Ideal.span {g | ∃ a, P g a}, ∃ s : R, ∀ g a, P g a → s * g = x * a := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨a', h'⟩ := hg'
      exact ⟨a', fun g a h => by
        have := hc g a g' a' h h'
        linear_combination -this⟩
    | zero => exact ⟨0, fun _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, fun g a h => by rw [add_mul, add_mul, hs g a h, ht g a h]⟩
    | smul r x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨r * s, fun g a h => by
        rw [smul_eq_mul, mul_assoc, hs g a h, mul_assoc]⟩
  obtain ⟨s, hs⟩ := gen 1 h1
  refine ⟨s, fun F _ ψ => ?_⟩
  let q : PrimeSpectrum R := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  obtain ⟨g, a, hg, h⟩ := hP q
  have hg' : ψ g ≠ 0 := hg
  have e : ψ s = ψ a / ψ g := by
    have := congrArg ψ (hs g a h)
    rw [map_mul, map_mul, map_one, _root_.one_mul] at this
    rw [← this]; field_simp
  rw [e]
  exact (h F ψ).2 hg'

theorem exists_basic {R : Type} [CommRing R] (A : Set (PrimeSpectrum R)) (hA : IsOpen A) (q : PrimeSpectrum R)
    (hq : q ∈ A) : ∃ g : R, g ∉ q.asIdeal ∧ ∀ t : PrimeSpectrum R, g ∉ t.asIdeal → t ∈ A := by
  obtain ⟨_, ⟨g, rfl⟩, hg, hs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq hA
  exact ⟨g, hg, fun t ht => hs ht⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (Formalism.L2.Pj.dualMap g) ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap (Formalism.L2.Pj.dualMap (g.comp f)) := by
  rw [← spMap_comp']
  congr 1
  ext a <;> simp [Formalism.L2.Pj.dualMap]

def frPtF {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift z.x (spMap (algebraMap c.F S)) (by
    rw [z.x_over]
    unfold Formalism.L2.Pj.sOf
    rw [spMap_comp'])

abbrev fpt {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F] (ψ : S →+* F) :
    Sp F ⟶ Xo.XF c := spMap ψ ≫ frPtF z

theorem fpt_under {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) : under (fpt z ψ) = spMap ψ ≫ z.x := by
  rw [under, fpt, frPtF, Category.assoc, pullback.lift_fst]

theorem fpt_snd {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) : fpt z ψ ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) := by
  rw [fpt, frPtF, Category.assoc, pullback.lift_snd, spMap_comp']

theorem eq_fpt {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) {y : Sp F ⟶ Xo.XF c} (h1 : under y = spMap ψ ≫ z.x)
    (h2 : y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S))) : y = fpt z ψ :=
  pullback.hom_ext (h1.trans (fpt_under z ψ).symm) (h2.trans (fpt_snd z ψ).symm)

def kerPt {R F : Type} [CommRing R] [Field F] (ψ : R →+* F) : PrimeSpectrum R :=
  ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩

theorem spMap_apply_eq {R F : Type} [CommRing R] [Field F] (ψ : R →+* F) (t : Sp F) :
    (show PrimeSpectrum R from (spMap ψ) t) = kerPt ψ := by
  have ht : (show PrimeSpectrum F from t).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  apply PrimeSpectrum.ext
  show Ideal.comap ψ (show PrimeSpectrum F from t).asIdeal = RingHom.ker ψ
  rw [ht]
  rfl

theorem range_fpt_subset_iff {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) (U : Set (Xo.XF c)) :
    Set.range (fpt z ψ) ⊆ U ↔ (frPtF z) (show Sp S from kerPt ψ) ∈ U := by
  have key : ∀ t : Sp F, (fpt z ψ) t = (frPtF z) (show Sp S from kerPt ψ) := fun t => by
    rw [fpt, Scheme.Hom.comp_apply]
    exact congrArg (frPtF z) (spMap_apply_eq ψ t)
  constructor
  · intro h
    obtain ⟨t⟩ : Nonempty (Sp F) := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩
    rw [← key t]
    exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    rw [key t]
    exact h

theorem kerPt_residue {R : Type} [CommRing R] (q : PrimeSpectrum R) :
    kerPt (algebraMap R q.asIdeal.ResidueField) = q :=
  PrimeSpectrum.ext (Ideal.ker_algebraMap_residueField _)

theorem eq_zero_of_fields {R : Type} [CommRing R] [IsReduced R] (x : R)
    (h : ∀ (F : Type) [Field F] (ψ : R →+* F), ψ x = 0) : x = 0 := by
  have hz : x ∈ nilradical R := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro I hI
    haveI : I.IsPrime := hI
    have : x ∈ RingHom.ker (algebraMap R I.ResidueField) := h _ _
    rwa [Ideal.ker_algebraMap_residueField] at this
  rw [nilradical_eq_zero] at hz
  exact hz

theorem pointRule {U : Set (Xo.XF c)} {τ : E →+* ℂ} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {Z : CptOver Y U} {φ : FrameFn Xo c} (hτ : τ (H.rt : E) = H.rt0) (hU : IsClopen U) (hl : IsLineFn U τ φ)
    (hf : FlatOnModel Z τ φ) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q)
    (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) :
    ∃ s e : p.R, ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x →
      y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) →
      (¬ Set.range y ⊆ U → ψ e = 0 ∧ ψ s = 0) ∧ (Set.range y ⊆ U → ψ e = 1 ∧
        ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
          (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
          (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
          ψ s = φ F y v w) := by
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hopen : IsOpen ((frPtF z) ⁻¹' U : Set (Sp p.R)) := hU.isOpen.preimage (frPtF z).continuous
  have hclosed : IsOpen ((frPtF z) ⁻¹' Uᶜ : Set (Sp p.R)) :=
    hU.isClosed.isOpen_compl.preimage (frPtF z).continuous

  obtain ⟨e, he⟩ := glue_rel p.R (fun F _ ψ r => (¬ Set.range (fpt z ψ) ⊆ U → r = 0) ∧ (Set.range (fpt z ψ) ⊆ U → r = 1))
    (fun F _ ψ r r' h h' => by
      by_cases hr : Set.range (fpt z ψ) ⊆ U
      · rw [h.2 hr, h'.2 hr]
      · rw [h.1 hr, h'.1 hr])
    (fun q => by
      by_cases hx : (frPtF z) (show Sp p.R from q) ∈ U
      · obtain ⟨g, hg, h⟩ := exists_basic _ hopen q hx
        refine ⟨g, g, hg, fun F _ ψ h0 => ⟨fun hr => ?_, fun _ => div_self h0⟩⟩
        exact absurd ((range_fpt_subset_iff z ψ U).2 (h _ h0)) hr
      · obtain ⟨g, hg, h⟩ := exists_basic _ hclosed q hx
        refine ⟨g, 0, hg, fun F _ ψ h0 => ⟨fun _ => by simp, fun hr => ?_⟩⟩
        exact absurd ((range_fpt_subset_iff z ψ U).1 hr) (h _ h0))
  obtain ⟨s, hs⟩ := glue_rel p.R (fun F _ ψ r => (¬ Set.range (fpt z ψ) ⊆ U → r = 0) ∧
      (Set.range (fpt z ψ) ⊆ U → ∀ (v : Vecs (fpt z ψ) D.p) (w : Vecs (fpt z ψ) D.q),
        (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
        (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
        r = φ F (fpt z ψ) v w))
    (fun F _ ψ r r' h h' => by
      by_cases hr : Set.range (fpt z ψ) ⊆ U
      · obtain ⟨v, w, ev, ew, -⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ p.R z F ψ (fpt z ψ) hp hq (fpt_under z ψ) (fpt_snd z ψ)
        rw [h.2 hr v w ev ew, h'.2 hr v w ev ew]
      · rw [h.1 hr, h'.1 hr])
    (fun q => by
      by_cases hx : (frPtF z) (show Sp p.R from q) ∈ U
      · have hr₀ : Set.range (fpt z (algebraMap p.R q.asIdeal.ResidueField)) ⊆ U := by
          rw [range_fpt_subset_iff, kerPt_residue]; exact hx
        obtain ⟨g, a, h0, h⟩ := GlobalTheory.T.flat_model_torus_ring E H D l Xo c U τ O β Y Z φ hτ hU hl hf p z q.asIdeal.ResidueField
          (algebraMap p.R _) _ (fpt_under z _) (fpt_snd z _) hr₀
        refine ⟨g, a, fun hg => h0 ?_, fun F _ ψ hg => ?_⟩
        · have : g ∈ RingHom.ker (algebraMap p.R q.asIdeal.ResidueField) := by
            rwa [Ideal.ker_algebraMap_residueField]
          exact this
        · obtain ⟨hr, hv⟩ := h F ψ (fpt z ψ) (fpt_under z ψ) (fpt_snd z ψ) hg
          refine ⟨fun hn => absurd hr hn, fun _ v w ev ew => ?_⟩
          rw [hv v w hp hq ev ew]
          field_simp
      · obtain ⟨g, hg, h⟩ := exists_basic _ hclosed q hx
        refine ⟨g, 0, hg, fun F _ ψ h0 => ⟨fun _ => by simp, fun hr => ?_⟩⟩
        exact absurd ((range_fpt_subset_iff z ψ U).1 hr) (h _ h0))
  refine ⟨s, e, fun F _ ψ y h1 h2 => ?_⟩
  obtain rfl := eq_fpt z ψ h1 h2
  refine ⟨fun hr => ⟨(he F ψ).1 hr, (hs F ψ).1 hr⟩, fun hr => ⟨(he F ψ).2 hr, fun v w hp' hq' ev ew => ?_⟩⟩
  exact (hs F ψ).2 hr v w ev ew

theorem conj_mult {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) : D.mult (ComplexEmbedding.conjugate τ) = D.q := by
  have hne : (ComplexEmbedding.conjugate τ) (H.rt : E) ≠ H.rt0 := by
    intro h
    have h1 : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have : (ComplexEmbedding.conjugate τ) (H.rt : E) = (starRingEnd ℂ) (τ (H.rt : E)) := rfl
      rw [this, hτ] at h
      exact h
    have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
    have h3 := H.sqrt_neg_disc_sq
    have h5 : H.rt0.re ^ 2 = -(H.d : ℝ) := by
      have := congrArg Complex.re h3
      simpa [pow_two, h2] using this
    have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg H.rt0.re]
  rw [Datum.mult, if_neg hne]

def detE (D : Datum H) (τ : E →+* ℂ) : Formalism.L2.Pj.Ix D → ℕ :=
  open Classical in Formalism.L2.Pj.ex D (fun x => if x.1 = τ then 1 else 0) 0

theorem wchar_add' {S : Type} [CommRing S] (e e' : Formalism.L2.Pj.Ix D → ℕ) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    Formalism.L2.Pj.wchar (e + e') t = Formalism.L2.Pj.wchar e t * Formalism.L2.Pj.wchar e' t := by
  simp only [Formalism.L2.Pj.wchar, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem wchar_detE {S : Type} [CommRing S] (τ : E →+* ℂ) {m : ℕ} (h : D.mult τ = m) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    Formalism.L2.Pj.wchar (detE D τ) t = ∏ i : Fin m, ((t (some ⟨τ, i.cast h.symm⟩) : Sˣ) : S) := by
  classical
  subst h
  unfold Formalism.L2.Pj.wchar detE
  rw [Fintype.prod_option]
  simp only [Formalism.L2.Pj.ex, pow_zero, _root_.one_mul]
  rw [Fintype.prod_sigma, Finset.prod_eq_single τ]
  · simp
  · intro σ _ hσ
    exact Finset.prod_eq_one fun i _ => by simp [hσ]
  · simp

end GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue

set_option maxHeartbeats 1600000 in

theorem exists_flat_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∃ s s' e : Formalism.L2.Pj.Rul Xo c, e ∈ Formalism.L2.Pj.sec Xo c 0 0 ∧ s * s' = e ∧ s * e = s ∧ s' * e = s' ∧ (∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Formalism.L2.Pj.Rul Xo c), (∀ x : (E →+* ℂ) × ℕ, x.2 < D.mult x.1 → (a' x : ℤ) = a x + Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = ComplexEmbedding.conjugate τ} 1 x - Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = τ} 1 x) → (f ∈ Formalism.L2.Pj.sec Xo c a n → f * s ∈ Formalism.L2.Pj.sec Xo c a' n) ∧ (f ∈ Formalism.L2.Pj.sec Xo c a' n → f * s' ∈ Formalism.L2.Pj.sec Xo c a n)) ∧ ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → (¬ Set.range y ⊆ U → ψ (e p z) = 0) ∧ (Set.range y ⊆ U → ψ (e p z) = 1 ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ hτ hU hl hf
  have hp : D.mult τ = D.p := by rw [Datum.mult, if_pos hτ]
  have hq : D.mult (ComplexEmbedding.conjugate τ) = D.q := conj_mult hτ
  have red : ∀ p : Formalism.L2.Pj.TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hex := fun (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) =>
    pointRule (Z := Z) (φ := φ) hτ hU hl hf hp hq p z
  choose s e hse using hex

  have C := fun (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) =>
    hse p z F ψ (fpt z ψ) (fpt_under z ψ) (fpt_snd z ψ)
  have FS : ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F),
      Set.range (fpt z ψ) ⊆ U → ψ (s p z) ≠ 0 := fun p z F _ ψ h => by
    obtain ⟨v, w, ev, ew, hfr⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ p.R z F ψ (fpt z ψ) hp hq (fpt_under z ψ) (fpt_snd z ψ)
    rw [((C p z F ψ).2 h).2 v w hp hq ev ew]
    exact hl.ne F _ _ v w (hfr U h)
  have zero : ∀ (p : Formalism.L2.Pj.TRing c.F) (x : p.R), (∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ x = 0) → x = 0 :=
    fun p x h => by
      haveI := red p
      exact eq_zero_of_fields x h
  have hee : ∀ p z, e p z * e p z = e p z := fun p z => sub_eq_zero.1 (zero p _ fun F _ ψ => by
    rw [map_sub, map_mul]
    by_cases hr : Set.range (fpt z ψ) ⊆ U
    · rw [((C p z F ψ).2 hr).1]; simp
    · rw [((C p z F ψ).1 hr).1]; simp)
  have hsE : ∀ p z, s p z * e p z = s p z := fun p z => sub_eq_zero.1 (zero p _ fun F _ ψ => by
    rw [map_sub, map_mul]
    by_cases hr : Set.range (fpt z ψ) ⊆ U
    · rw [((C p z F ψ).2 hr).1]; simp
    · rw [((C p z F ψ).1 hr).2]; simp)
  have hunit : ∀ p z, IsUnit (s p z + 1 - e p z) := fun p z => by
    by_contra hn
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
    haveI := hm.isPrime
    let ψ : p.R →+* m.ResidueField := algebraMap p.R m.ResidueField
    have h0 : ψ (s p z + 1 - e p z) = 0 := by
      have : s p z + 1 - e p z ∈ RingHom.ker ψ := by
        show _ ∈ RingHom.ker (algebraMap p.R m.ResidueField)
        rwa [Ideal.ker_algebraMap_residueField]
      exact this
    rw [map_sub, map_add, map_one] at h0
    by_cases hr : Set.range (fpt z ψ) ⊆ U
    · rw [((C p z _ ψ).2 hr).1] at h0
      exact FS p z _ ψ hr (by simpa using h0)
    · rw [((C p z _ ψ).1 hr).1, ((C p z _ ψ).1 hr).2] at h0
      simp at h0
  let s' : Formalism.L2.Pj.Rul Xo c := fun p z => e p z * Ring.inverse (s p z + 1 - e p z)
  have hss : ∀ p z, s p z * s' p z = e p z := fun p z => by
    have h1 := Ring.mul_inverse_cancel _ (hunit p z)
    have h2 := hee p z
    have h3 := hsE p z
    show s p z * (e p z * Ring.inverse (s p z + 1 - e p z)) = e p z
    set i := Ring.inverse (s p z + 1 - e p z)
    linear_combination (e p z) * h1 + i * h2
  have hs'E : ∀ p z, s' p z * e p z = s' p z := fun p z => by
    show e p z * _ * e p z = e p z * _
    linear_combination (Ring.inverse (s p z + 1 - e p z)) * hee p z

  have hnat : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → e q z = f (e p y) ∧ s q z = f (s p y) := fun p q f y z h => by
    have key : ∀ (F : Type) [Field F] (ψ : q.R →+* F), ψ (e q z) = ψ (f (e p y)) ∧ ψ (s q z) = ψ (f (s p y)) := by
      intro F _ ψ
      let ψ' : p.R →+* F := ψ.comp f.toRingHom
      have h1 : under (fpt z ψ) = spMap ψ' ≫ y.x := by
        rw [fpt_under, h.1, ← Category.assoc, ← spMap_comp']
      have h2 : fpt z ψ ≫ pullback.snd _ _ = spMap (ψ'.comp (algebraMap c.F p.R)) := by
        rw [fpt_snd]
        congr 1
        ext a
        simp [ψ']
      have D2 := hse p y F ψ' (fpt z ψ) h1 h2
      have D1 := C q z F ψ
      have e1 : ∀ x : p.R, ψ (f x) = ψ' x := fun _ => rfl
      rw [e1, e1]
      by_cases hr : Set.range (fpt z ψ) ⊆ U
      · obtain ⟨v, w, ev, ew, -⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ q.R z F ψ (fpt z ψ) hp hq (fpt_under z ψ) (fpt_snd z ψ)
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v w hp hq (fun i => ?_) (fun j => ?_)]
        · rw [ev i, h.2.1, ← Category.assoc, dualMap_spMap_comp]
        · rw [ew j, h.2.1, ← Category.assoc, dualMap_spMap_comp]
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        exact ⟨rfl, rfl⟩
    exact ⟨sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [map_sub, (key F ψ).1, sub_self]),
      sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [map_sub, (key F ψ).2, sub_self])⟩
  have hnat' : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → s' q z = f (s' p y) := fun p q f y z h => by
    obtain ⟨h1, h2⟩ := hnat p q f y z h
    have h3 := hss q z
    have h4 := congrArg f (hss p y)
    have h5 := hs'E q z
    have h6 := congrArg f (hs'E p y)
    rw [map_mul] at h4 h6
    rw [← h2] at h4
    rw [← h1] at h4 h6
    linear_combination (f (s' p y)) * h3 - (s' q z) * h4 - h5 + h6
  have hwt : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' → e p y' = e p y ∧
        s p y' * Formalism.L2.Pj.wchar (detE D τ) t = s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t := fun p t y y' h => by
    have key : ∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ (e p y') = ψ (e p y) ∧
        ψ (s p y' * Formalism.L2.Pj.wchar (detE D τ) t) = ψ (s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t) := by
      intro F _ ψ
      have h1 : under (fpt y ψ) = spMap ψ ≫ y'.x := by rw [fpt_under, h.1]
      have D2 := hse p y' F ψ (fpt y ψ) h1 (fpt_snd y ψ)
      have D1 := C p y F ψ
      rw [map_mul, map_mul]
      by_cases hr : Set.range (fpt y ψ) ⊆ U
      · obtain ⟨v, w, ev, ew, hfr⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ p.R y F ψ (fpt y ψ) hp hq (fpt_under y ψ) (fpt_snd y ψ)
        obtain ⟨v', w', ev', ew', hfr'⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ p.R y' F ψ (fpt y ψ) hp hq h1 (fpt_snd y ψ)
        obtain ⟨A, B, hA, hB, dA, dB⟩ := GlobalTheory.T.frame_borel_change_vectors E H D l Xo c τ p.R t y y' h F ψ (fpt y ψ) hp hq v v' w w' (fpt_under y ψ) ev ew ev' ew'
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v' w' hp hq ev' ew', wchar_detE τ hp, wchar_detE _ hq, map_prod, map_prod,
          ← dA, ← dB]
        exact hl.chg F _ _ v w v' w' A B (hfr U hr) (hfr' U hr) hA hB
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        simp
    have k1 : e p y' - e p y = 0 := zero p _ fun F _ ψ => by rw [map_sub, (key F ψ).1, sub_self]
    have k2 : s p y' * Formalism.L2.Pj.wchar (detE D τ) t - s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t = 0 :=
      zero p _ fun F _ ψ => by
        have := (key F ψ).2
        exact (map_sub ψ _ _).trans (sub_eq_zero.2 this)
    exact ⟨sub_eq_zero.1 k1, sub_eq_zero.1 k2⟩
  have hwt' : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' →
        s' p y' * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t = s' p y * Formalism.L2.Pj.wchar (detE D τ) t := fun p t y y' h => by
    obtain ⟨h1, h2⟩ := hwt p t y y' h
    have h3 := hss p y
    have h4 := hss p y'
    have h5 := hs'E p y
    have h6 := hs'E p y'
    rw [h1] at h4 h6
    set W := Formalism.L2.Pj.wchar (detE D τ) t
    set W' := Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t
    linear_combination (-(s' p y' * W')) * h3 + (s' p y * W) * h4 + (-(s' p y') * s' p y) * h2 - (W') * h6 + W * h5
  have hunitW : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (b : Formalism.L2.Pj.Ix D → ℕ),
      IsUnit (Formalism.L2.Pj.wchar b t) := fun p t b => IsUnit.prod_univ_iff.2 fun i => (t i).isUnit.pow _
  refine ⟨s, s', e, ⟨fun p q f y z h => (hnat p q f y z h).1, fun p t y y' h => ?_⟩, funext fun p => funext fun z => hss p z,
    funext fun p => funext fun z => hsE p z, funext fun p => funext fun z => hs'E p z, ?_, fun p z F _ ψ y h1 h2 => ?_⟩
  · have h0 : Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> simp [Formalism.L2.Pj.ex]
    rw [h0, _root_.one_mul]
    exact (hwt p t y y' h).1
  · intro a a' n f ha
    have hE : Formalism.L2.Pj.ex D a' n + detE D τ = Formalism.L2.Pj.ex D a n + detE D (ComplexEmbedding.conjugate τ) := by
      classical
      funext i
      rcases i with _ | ⟨σ, i⟩
      · simp [Formalism.L2.Pj.ex, detE]
      · have := ha (σ, i) i.2
        simp only [Pi.add_apply, Formalism.L2.Pj.ex, detE]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] at this
        split_ifs at this ⊢ <;> omega
    have hC : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ),
        Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a' n) t * Formalism.L2.Pj.wchar (detE D τ) t =
          Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a n) t * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ)) t := fun p t => by
      rw [← wchar_add', ← wchar_add', hE]
    refine ⟨fun hf => ⟨fun p q g y z h => ?_, fun p t y y' h => ?_⟩, fun hf => ⟨fun p q g y z h => ?_, fun p t y y' h => ?_⟩⟩
    · show f q z * s q z = g (f p y * s p y)
      rw [hf.1 p q g y z h, (hnat p q g y z h).2, map_mul]
    · show f p y' * s p y' = Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a' n) t * (f p y * s p y)
      have h1 := hf.2 p t y y' h
      have h2 := (hwt p t y y' h).2
      have h3 := hC p t
      refine (hunitW p t (detE D τ)).mul_left_cancel ?_
      rw [h1]
      linear_combination (Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a n) t * f p y) * h2 - (f p y * s p y) * h3
    · show f q z * s' q z = g (f p y * s' p y)
      have a1 : f q z = g (f p y) := hf.1 p q g y z h
      have a2 := hnat' p q g y z h
      exact (congrArg₂ (· * ·) a1 a2).trans (map_mul g _ _).symm
    · show f p y' * s' p y' = Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a n) t * (f p y * s' p y)
      have h1 := hf.2 p t y y' h
      have h2 := hwt' p t y y' h
      have h3 := hC p t
      refine (hunitW p t (detE D (ComplexEmbedding.conjugate τ))).mul_left_cancel ?_
      rw [h1]
      linear_combination (Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex D a' n) t * f p y) * h2 + (f p y * s' p y) * h3
  · have D1 := hse p z F ψ y h1 h2
    exact ⟨fun hr => (D1.1 hr).1, D1.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat
