import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

section
variable {R : Type} [CommRing R] {F : Shv R}

private theorem res_nsmul' {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul (ModuleCat.Hom.hom (F.obj.map g.op)) n x

private theorem res_sub' {V U : Scheme.{0}} (g : V ⟶ U) (x x' : Sec F U) :
    Sec.res g (x - x') = Sec.res g x - Sec.res g x' := map_sub (ModuleCat.Hom.hom (F.obj.map g.op)) x x'

end

private theorem res_eq_of_range {q : ℕ} {i : ℤ} {U V : Scheme.{0}} (g : V ⟶ U) [Etale g]
    (y G : Sec (tw q i) U) (c : ℕ) (h : Sec.res g y = c • Sec.res g G) {Ω : Type} [Field Ω]
    (x : gp Ω ⟶ U) (hx : pt x ∈ Set.range g) : Sec.res x y = c • Sec.res x G := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := g)
    (IsLocalRing.closedPoint Ω) v hv.symm
  have hE : Etale (pullback.fst x g) := inferInstance
  have hz := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family _ (tw q i) (gp Ω) Unit (fun _ => pullback x g) (fun _ => pullback.fst x g)
    (fun _ => hE) (fun u => ⟨(), t, Subsingleton.elim _ _⟩)).1 (Sec.res x y - c • Sec.res x G) (fun _ => by
      rw [res_sub', res_nsmul', res_res, res_res, pullback.condition, ← res_res, ← res_res, h, res_nsmul', sub_self])
  exact sub_eq_zero.mp hz

theorem secFun_of : PtEx → SecFun := by
  intro hpt q _ i U ζ y
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨-, h2, h3, h4, -, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
  let P : (V : Scheme.{0}) → (V ⟶ U) → Prop :=
    fun V g => ∃ c : ℕ, Sec.res g y = c • Sec.res g (twGen i ζ)
  have hP : ∀ (V W : Scheme) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g) := by
    rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_nsmul', res_res]⟩
  have hloc : Loc U P := by
    obtain ⟨S, hS, hSa⟩ := h2 U ζ y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨c, hc⟩ := hSa V g hg
    exact ⟨c, by rw [hc, h4]⟩
  have hpts := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U P hP).mp hloc
  choose V g hVa hge hgr hc using hpts
  choose c hc using hc
  have key : ∀ (u : U) {Ω : Type} [Field Ω] (x : gp Ω ⟶ U), pt x ∈ Set.range (g u) →
      Sec.res x y = c u • Sec.res x (twGen i ζ) := by
    intro u Ω _ x hx
    haveI := hge u
    exact res_eq_of_range (g u) y (twGen i ζ) (c u) (hc u) x hx
  have uniq : ∀ (u u' : U) {Ω : Type} [Field Ω] (x : gp Ω ⟶ U),
      pt x ∈ Set.range (g u) → pt x ∈ Set.range (g u') → c u % q = c u' % q := by
    intro u u' Ω _ x hx hx'
    have hR : ∀ n : ℕ, n • Sec.res x (twGen i ζ) = 0 → q ∣ n := by
      intro n hn
      rw [h4] at hn
      exact h3 (gp Ω) _ n hn
    have heq : (c u % q) • Sec.res x (twGen i ζ) = (c u' % q) • Sec.res x (twGen i ζ) := by
      rw [← RedExists.nsmul_mod_of, ← RedExists.nsmul_mod_of, ← key u x hx, ← key u' x hx']
    have hlt : ∀ a b : ℕ, a < q → b < q → a ≤ b →
        a • Sec.res x (twGen i ζ) = b • Sec.res x (twGen i ζ) → a = b := by
      intro a b ha hb hab he
      have hs : a • Sec.res x (twGen i ζ) + (b - a) • Sec.res x (twGen i ζ) =
          a • Sec.res x (twGen i ζ) + 0 := by
        rw [← add_nsmul, Nat.add_sub_cancel' hab, add_zero, he]
      have h0 := hR (b - a) (add_left_cancel hs)
      have := Nat.eq_zero_of_dvd_of_lt h0 (by omega)
      omega
    rcases le_total (c u % q) (c u' % q) with hab | hab
    · exact hlt _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) hab heq
    · exact (hlt _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) hab heq.symm).symm
  refine ⟨fun u => ((c u % q : ℕ) : ℤ), ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro u
    refine ⟨Set.range (g u), (g u).isOpenMap.isOpen_range, hgr u, fun u' hu' => ?_⟩
    obtain ⟨Ω, _, _, x, hx⟩ := hpt U u'
    have hx1 : pt x ∈ Set.range (g u) := hx ▸ hu'
    have hx2 : pt x ∈ Set.range (g u') := hx ▸ hgr u'
    simp only [uniq u' u x hx2 hx1]
  · intro Ω _ _ x
    rw [key (pt x) x (hgr (pt x)), natCast_zsmul, ← RedExists.nsmul_mod_of]

end UpperTheory.Gal.TranscendenceTraces
