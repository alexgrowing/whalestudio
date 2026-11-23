import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSumAtPlaceDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem actY_inv_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ}
    (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem perMove (hA : ActY) {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {v : InfinitePlace G.F} {t₀ : D.F →+* ℂ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} {β : G.Cˣ}
    (RD : RDic L v β ρ t₀) (hs : sh G β = β) (y : GlobalTheory.LKCx.grp G β) {Q'' : VQ D →+ (Fin D.g → ℂ)}
    (hQ : IsPerQ L β ρ Q'') (z : GlobalTheory.LKCx.PosV G v β) (hr : RD.rel Q'' z.1) :
    ∃ (Q₁ : VQ D →+ (Fin D.g → ℂ)) (z₁ : GlobalTheory.LKCx.PosV G v β), IsPerQ L β ρ Q₁ ∧
      (∀ w, Q₁ (actY L y w) = Q'' w) ∧ RD.rel Q₁ z₁.1 ∧
      z₁.1 = (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1 := by
  obtain ⟨-, -, h3, h4⟩ := hA p D G L β y
  let Q₁ : VQ D →+ (Fin D.g → ℂ) := Q''.comp (actY L y⁻¹).toAddMonoidHom
  have e : ∀ w, Q₁ (actY L y w) = Q'' w := fun w => by
    show Q'' (actY L y⁻¹ (actY L y w)) = _
    rw [actY_inv_left]
  obtain ⟨z₁, hz₁⟩ := h4 v z hs
  refine ⟨Q₁, z₁, h3 ρ Q'' Q₁ hQ e, e, ?_, hz₁⟩
  rw [hz₁]
  exact RD.equiv y Q'' Q₁ z.1 e hr

private theorem same_mk {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β) (c : ℂ)
    (hc : c ≠ 0) (h1 : b.1.1⁻¹ * B.toAf y * a.1.1 ∈ K) (h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ K')
    (hz : b.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a b := by
  refine ⟨y, ((b.1.1⁻¹ * B.toAf y * a.1.1)⁻¹, (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2)⁻¹), c,
    inv_mem h1, inv_mem h2, hc, ?_, hz⟩
  change b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * _
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul]
    group
  · simp only [Prod.snd_mul]
    group

private theorem same_of_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β)
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K K') = Quot.mk _ b) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b a := by
  have key : ∀ a b : GlobalTheory.LKCx.Dat G v B.β,
      Relation.EqvGen (GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose
        B.trivAf.choose_spec.choose_spec K K') a b →
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b) ∧
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      obtain ⟨g, hg⟩ := (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ x y).1 hxy
      exact ⟨⟨g, hg⟩, ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩
    | refl x => exact ⟨⟨1, one_smul _ _⟩, ⟨1, one_smul _ _⟩⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩⟩ := ih1
      obtain ⟨⟨g2, hg2⟩, ⟨h2, hh2⟩⟩ := ih2
      exact ⟨⟨g2 * g1, by rw [mul_smul, hg1, hg2]⟩, ⟨h1 * h2, by rw [mul_smul, hh2, hh1]⟩⟩
  exact (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ b a).2 (key a b (Quot.eqvGen_exact h)).2

end UpperTheory.Gal.W2

private theorem ext_lemma {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (hj : IsPlace L β D' j) (Q Q₁ : VQ D →+ (Fin D.g → ℂ))
    (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)) (hQ : ∀ u, Q (j u) = h (Q₁ (j u))) :
    ∀ w, Q w = h (Q₁ w) := by
  intro w
  obtain ⟨m, u, hm, hmu⟩ := hj.2.2.1 w
  have key : m • Q w = m • h (Q₁ w) := by
    rw [← map_nsmul Q, hmu, hQ, ← hmu, map_nsmul Q₁, map_nsmul h]
  exact smul_right_injective _ hm key

theorem UpperTheory.Gal.W2.coordIso_of :
    UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.CoordIso := by
  intro hF hI hA p _ D G L v t₀ ρ PD RD N hN hNp D' t P D'' t'' P'' hc hc'' q q'' a a'' j j'' ha ha''
  obtain ⟨hpl, hca, hlp, Q, hQ, hQj, hr⟩ := ha
  obtain ⟨hpl'', hca'', hlp'', Q'', hQ'', hQj'', hr''⟩ := ha''
  constructor
  · rintro ⟨w, h, hw, hPh⟩
    obtain ⟨y, s, hs, hy, hjw⟩ := hF p D G L _ _ D' D'' j j'' hpl hpl'' w.toLinearMap 1 one_pos
      (by intro u u'; rw [_root_.one_mul]; exact hw.1 u u')
    have hjw' : ∀ u, j (w u) = L.rep (y : G.C) (j'' u) := hjw
    have hrel : GlobalTheory.LKCx.Form.Rel (Quot.out q'') (Quot.out q) := by
      refine ⟨y, (s : ℚ)⁻¹, inv_pos.mpr hs, ?_⟩
      rw [hy, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hs), map_one, _root_.one_mul]
    have hq : q'' = q :=
      (Quot.out_eq (q'' : Quot GlobalTheory.LKCx.Form.Rel)).symm.trans
        ((Quot.sound hrel).trans (Quot.out_eq (q : Quot GlobalTheory.LKCx.Form.Rel)))
    subst hq
    let yy : GlobalTheory.LKCx.grp G (Quot.out q'').β := ⟨(y, s), hy, hs⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q'').sym yy hQ'' a''.2 hr''
    have hext : ∃ h' : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ), ∀ w0, Q w0 = h' (Q₁ w0) := by
      refine ⟨h, ext_lemma hpl Q Q₁ h ?_⟩
      intro u
      obtain ⟨u'', rfl⟩ := w.surjective u
      rw [hQj, hPh, ← hQj'', ← hQ₁y, hjw']
      rfl
    obtain ⟨c, hc0, hac⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).1 hext
    have hmem := (hI p D G L (Quot.out q'') (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' yy).2 ⟨w, hw, hjw'⟩
    exact congrArg (Sigma.mk _)
      (Quot.sound (same_mk _ _ _ a'' a yy c hc0 hmem.1 hmem.2 (by rw [hac, hz₁]))).symm
  · intro heq
    obtain ⟨hq, hh⟩ := Sigma.mk.inj heq
    subst hq
    obtain ⟨y, k, c, hk1, hk2, hc0, hk, hz⟩ := same_of_eq _ _ _ a a'' (eq_of_heq hh)
    have hmem1 : a.1.1⁻¹ * (Quot.out q).toAf y * a''.1.1 ∈ L.KN N := by
      have e : a.1.1 = (Quot.out q).toAf y * a''.1.1 * k.1 := congrArg Prod.fst hk
      have e2 : ((Quot.out q).toAf y * a''.1.1 * k.1)⁻¹ * (Quot.out q).toAf y * a''.1.1 = k.1⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk1
    have hmem2 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
      have e : a.1.2 = GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2 := congrArg Prod.snd hk
      have e2 : (GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2)⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y *
          a''.1.2 = k.2⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk2
    obtain ⟨w, hw, hjw⟩ := (hI p D G L (Quot.out q) (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' y).1 ⟨hmem1, hmem2⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q).sym y hQ'' a''.2 hr''
    obtain ⟨h, hh'⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).2 ⟨c, hc0, by rw [hz, hz₁]⟩
    refine ⟨w, h, hw, fun u => ?_⟩
    rw [← hQj, hjw, hh', hQ₁y, hQj'']
