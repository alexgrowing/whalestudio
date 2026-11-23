import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePreservesEtaleLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.EtLev.HeckeLev

private theorem UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}} {A T : Over S}
    [GrpObj A] (act : OActN D.O A) {I : Ideal (𝓞 D.F)} {n : ℕ} (hn : (n : 𝓞 D.F) ∈ I) (t : T ⟶ A)
    (h : ∀ c ∈ I, t ≫ act.act (algebraMap (𝓞 D.F) D.O c) = 1) : t ^ n = 1 := by
  have := h _ hn
  rwa [map_natCast, act_natCast, MonObj.comp_pow, Category.comp_id] at this

theorem UpperTheory.Gal.FiniteEtaleModels.levTr_holds :
    LevTr := by
  intro q _ D R _ b f c k N 𝔟 hk hq S s o o' ψ lv hT hL
  obtain ⟨e, he⟩ := hq
  obtain ⟨hψ, hact, -, hgal, -, -⟩ := hT
  obtain ⟨hadd, hlin, hkill, hgeo⟩ := hL
  haveI := hψ
  have hnI : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟 := he
  have hkn : k.Coprime (q ^ e) := Nat.Coprime.pow_right e hk
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hkn
    (pow_ne_zero e (Fact.out : q.Prime).ne_zero)
  have hmod : ∀ {Q : Type} [Monoid Q] (z : Q) (n j : ℕ), z ^ n = 1 → z ^ j = z ^ (j % n) := by
    intro Q _ z n j hz
    exact pow_eq_pow_mod j hz
  have hlv0 : lv 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨φ, hφm, hψφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o'.A o.A (heckeSubA o f N) ψ hψ hgal
    (𝟙 o.A ^ k) (isMonHom_idPow o.A k) (fun h hh => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact HeckeAd.pow_eq_one_of_mem o f h hh)
  haveI := hφm
  haveI : Epi ψ := by
    haveI := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact Over.epi_of_epi_left ψ
  have hφψ : φ ≫ ψ = 𝟙 o'.A ^ k := by
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, pow_comp_hom, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hφact : ∀ a : D.O, φ ≫ o.act.act a = o'.act.act a ≫ φ := by
    intro a
    haveI := o.act.hom a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, ← Category.assoc, ← hact a, Category.assoc, hψφ, pow_comp_hom,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [hadd, MonObj.mul_comp]
  · intro a x
    beta_reduce
    rw [hlin, Category.assoc, hact, Category.assoc]
  · intro x hx
    beta_reduce
    rw [hkill x hx, MonObj.one_comp]
  · intro K _ _ x
    obtain ⟨hA, hB⟩ := hgeo K x
    constructor
    · intro y hy
      beta_reduce at hy
      apply hA
      have hPk : (toUnit (Over.mk x) ≫ lv y) ^ k = 1 := by
        calc (toUnit (Over.mk x) ≫ lv y) ^ k = (toUnit (Over.mk x) ≫ lv y) ≫ 𝟙 o.A ^ k := by
              rw [MonObj.comp_pow, Category.comp_id]
          _ = (toUnit (Over.mk x) ≫ lv y ≫ ψ) ≫ φ := by rw [← hψφ]; simp only [Category.assoc]
          _ = 1 := by rw [hy, MonObj.one_comp]
      have hPn : (toUnit (Over.mk x) ≫ lv y) ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o.act hnI _ (fun c hc => by
          rw [Category.assoc, ← hlin,
            hkill _ (Submodule.subset_span ⟨c, by rw [pow_one]; exact hc, y, rfl⟩), MonObj.comp_one])
      calc toUnit (Over.mk x) ≫ lv y = (toUnit (Over.mk x) ≫ lv y) ^ 1 := (pow_one _).symm
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (1 % q ^ e) := hmod _ _ 1 hPn
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m % q ^ e) := by rw [hm]
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m) := (hmod _ _ _ hPn).symm
        _ = 1 := by rw [pow_mul, hPk, one_pow]
    · intro g hg
      have hg0 : ∀ c ∈ 𝔟 ^ 1, (g ≫ φ) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
        intro c hc
        rw [Category.assoc, hφact, ← Category.assoc, hg c hc, MonObj.one_comp]
      obtain ⟨y0, hy0⟩ := hB (g ≫ φ) hg0
      have hgk : g ^ k = toUnit (Over.mk x) ≫ lv y0 ≫ ψ := by
        rw [← Category.assoc, hy0, Category.assoc, hφψ, MonObj.comp_pow, Category.comp_id]
      have hgn : g ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o'.act hnI g (fun c hc => hg c (by rw [pow_one]; exact hc))
      refine ⟨m • y0, ?_⟩
      show toUnit (Over.mk x) ≫ lv (m • y0) ≫ ψ = g
      rw [map_nsmul_pow lv hadd hlv0 m y0, pow_comp_hom, MonObj.comp_pow, ← hgk, ← pow_mul,
        hmod g _ _ hgn, hm, ← hmod g _ 1 hgn, pow_one]
