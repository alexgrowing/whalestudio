import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslatePolarisationBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometricStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem exists_isHecke : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.Hecke.heckeSub_finite_free p D R b g k N hk0 hN0 hk hNp S s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    (heckeSub o g N) o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ heckeSub o g N, h ≫ ψ = 1 := fun h hh =>
    comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  have stab : ∀ c' : D.O, ∀ h ∈ heckeSub o g N, h ≫ o.act.act c' ∈ heckeSub o g N := by
    rintro c' _ ⟨x, rfl⟩
    refine ⟨c' • x, ?_⟩
    rw [← o.eta_lin, map_smul, smul_comm]
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A' (heckeSub o g N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨P', hP', r1, r2, hsym, hamp, hker, hros, hpull⟩ :=
    GlobalTheory.T.exists_hecke_translate_polarisation_bundle p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp
  have hgeom := GlobalTheory.T.exists_tateSimilitude_hecke_translate_geometric p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp P' hP' r1 r2 hpull
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (g x) ≫ ψ
      eta_add := fun x y => by rw [map_add, o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (g (c' • x)) ≫ ψ = (o.eta (g x) ≫ ψ) ≫ act'.act c'
        rw [map_smul, o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (mem_heckeSub o g N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp, fun x => rfl, hgal, ⟨hpull⟩, hck⟩

end GlobalTheory.UPel.HT.Hecke
