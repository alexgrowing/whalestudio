import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeft

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HcptPull

noncomputable section

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

omit [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] in

theorem emb_eq (A : HodgeCpt Y S y) (B : HodgeCpt Y S y') (h : B.X ⟶ A.X) (i : Ω →+* Ω')
    (hdom : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i) (hf : B.f = h ≫ A.f) :
    B.emb = fun s => (i.comp A.cst).comp (labelEmb c s) := by
  have e1 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) = spMap ((i.comp A.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
    have e : B.ξ ≫ h = spMap i ≫ A.ξ := hdom
    rw [← B.cst_over, hf, Category.assoc, ← Category.assoc, e, Category.assoc, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e2 : B.cst.comp (algebraMap (𝓞 c.F) c.F) = (i.comp A.cst).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
  funext s
  refine RingHom.ext fun a => ?_
  exact RingHom.congr_fun e2
    ⟨labelEmb c s a, (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom⟩

set_option maxHeartbeats 1000000 in

theorem exists_pull (A : HodgeCpt Y S y) (B : HodgeCpt Y S y') (h : B.X ⟶ A.X) (i : Ω →+* Ω') (x : Sp Ω ⟶ Xo.XF c)
    (hx : A.ξ ≫ A.f = x ≫ Y.j) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q}
      (labelRk D s) ⊤)
    (hdom : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i) (hf : B.f = h ≫ A.f) (hR : B.R = A.R) :
    ∃ j : A.Li →+ B.Li, IsExtOver i j ∧ ∀ s, B.V s = (A.V s).pull B.ξ h j := by
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := B.tie.gen
  obtain ⟨mh, -⟩ := GlobalTheory.CompanionTheory.Ar.CoverLie.cancel hf A.m B.m
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M j (𝓞 E) A.t.act.act B.t.act.act A.ρ B.ρ
    hdom mh.cart hj A.act B.act (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li B.Li j hext hspan
  have hW : ∀ s, eigSp B.ρ ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li B.Li j A.ρ B.ρ (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ B.X Ω' B.ξ h i hdom
  have hsp : ∀ p' : Cpt B.ξ, genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt B.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt B.ξ p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt B.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt B.ξ p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt B.ξ), InFibre B.ξ p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian B.X Ω' B.ξ ℤ _ _ B.tie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt B.ξ, IsIntegrallyClosed (B.X.presheaf.stalk q.1) := fun q => (B.normal q.1).2
  have htors : ∀ p ∈ S, FullTorsion B.t.G B.ξ (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt B.ξ, 0 < D.p + D.q → B.M.htOm B.t.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt B.ξ p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y B.X B.f B.t B.m Ω' B.ξ (spMap i ≫ x) (by
      rw [hf, ← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) B.X Ω' B.ξ s0' o' B.t m0' B.Li B.M (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := GlobalTheory.T.omega_lattice_dominant_compat A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq B.ξ h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt B.ξ, InFibre B.ξ p p' →
      B.M.htDual B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt B.ξ p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact GlobalTheory.T.dual_lattice_basis_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt B.ξ p') A.Li B.Li j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (B.M.htOm B.t.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt B.ξ, InFibre B.ξ p p' →
      B.M.htW B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt B.ξ p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt B.ξ p') A.Li B.Li j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (B.M.htDual B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (B.M.eigLat B.ρ ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel B.M B.t.PP.L (p ^ A.R p) B.ρ (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull B.ξ h j := by
    intro s
    funext p'
    rw [pull_eq B.ξ h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre B.ξ p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre B.ξ p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show B.M.lat p' ⊓ _ = _
      rw [hlat, pull_eq B.ξ h _ j p' (hsp p')]
      exact GlobalTheory.T.lattice_eigen_field_extension E Ω Ω' i A.Li B.Li j A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext hρj (hreg p')
        (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  refine ⟨j, hext, fun s => Eq.trans ?_ (hV s)⟩
  have he := emb_eq A B h i hdom hf
  show Lat.patch S (B.M.eigLat B.ρ (B.emb s)) (fun p => htLabel B.M B.t.PP.L (p ^ B.R p) B.ρ B.emb s) = _
  rw [he, hR]

end LevelTowerAlt
