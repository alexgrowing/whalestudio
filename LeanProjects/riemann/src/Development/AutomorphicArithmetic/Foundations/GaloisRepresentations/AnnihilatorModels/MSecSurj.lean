import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secSurj_of :
    ConstSub → OMod → QuotObj → ObjTri → PullKer → SecSurj := by
  intro hCS hOM hQO hOT hPK
  intro p _ D O _ _ _ _ f b N r w _ hstd M j hj T K _ _ hp x G hGk hGs hGc
  obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N M.X (Sp K) M.s x M.univ
  have hcm : ∀ {X Y Z : Over M.X} [MonObj Z] (e : X ⟶ Y) (u v : Y ⟶ Z), e ≫ (u * v) = (e ≫ u) * (e ≫ v) := by
    intro X Y Z _ e u v
    rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, CartesianMonoidalCategory.comp_lift]
  let eI : Over.mk x ≅ (Over.map x).obj (𝟙_ (Over (Sp K))) := Over.isoMk (Iso.refl _) (by simp)
  let Φ : (𝟙_ (Over (Sp K)) ⟶ o₁.A) →* (Over.mk x ⟶ M.univ.A) :=
    { toFun := fun u => eI.hom ≫ m.ptEquiv _ u
      map_one' := by rw [map_one]; simp [Hom.one_def]
      map_mul' := fun a c => by rw [map_mul]; exact hcm _ _ _ }
  have hΦl : ∀ u, (Φ u).left = u.left ≫ m.φ := fun u => by
    simp [Φ, eI, GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
  have hΦi : Function.Injective Φ := fun a c h => by
    have h2 : m.ptEquiv _ a = m.ptEquiv _ c := by
      simpa [Φ] using congrArg (fun t => eI.inv ≫ t) h
    exact (m.ptEquiv _).injective h2
  have hΦs : Function.Surjective Φ := fun g => ⟨(m.ptEquiv _).symm (eI.inv ≫ g), by simp [Φ]⟩
  have hPK1 := hPK p D O b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m m (𝟙 _) (𝟙 _) (by simp)
  have hkill : ∀ u I, KilledBy o₁ I u ↔ KilledBy M.univ I (Φ u) := fun u I =>
    ((hPK1.1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl u (Φ u) (by simp [hΦl])).2.2 I)
  have hpw : (p : 𝓞 D.F) ∈ w := hstd.ule (GlobalTheory.UPel.HT.ES.p_mem_uIdeal D r)
  have hGO : ∀ g ∈ G, ∀ a : D.O, g ≫ M.univ.act.act a ∈ G := by
    intro g hg a
    obtain ⟨c, y', rfl⟩ := hOM p D hstd.m1 a
    have h1 : g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O (p : 𝓞 D.F)) = 1 := hGk g hg _ hpw
    haveI := M.univ.act.hom y'
    rw [GlobalTheory.UPel.HT.OActN.add, hcm, Algebra.commutes, GlobalTheory.UPel.HT.OActN.mul, ← Category.assoc, h1]
    simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
    rw [← Hom.one_def, _root_.mul_one]
    exact hGs g hg c
  have hcard : Nat.card (G.comap Φ) = Nat.card G :=
    Nat.card_congr ((Subgroup.equivMapOfInjective (G.comap Φ) Φ hΦi).toEquiv.trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective hΦs G)).toEquiv)
  have hne : Nat.card G ≠ 0 := by
    rw [hGc, hstd.norm]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)
  have hfin : Finite (G.comap Φ) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  haveI := o₁.ab
  haveI := IsAbelianScheme.proper (A := o₁.A)
  obtain ⟨G', _, i, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ := hCS K o₁.A inferInstance (G.comap Φ) hfin
  have hΦact : ∀ u a, Φ (u ≫ o₁.act.act a) = Φ u ≫ M.univ.act.act a := fun u a =>
    Over.OverMorphism.ext (by rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act])
  have hks : ∀ (T' : Over (Sp K)) (z : T' ⟶ o₁.A), GlobalTheory.IwLevel.InSub i z → KilledBy o₁ w z := by
    rintro T' z ⟨y0, rfl⟩ a ha
    have h7 : i ≫ o₁.act.act (algebraMap _ _ a) = 1 :=
      hi7 _ (fun u hu => ((hkill u w).2 (hGk _ hu)) a ha)
    rw [Category.assoc, h7]
    simp [Hom.one_def]
  have hstab : ∀ a : D.O, ∃ g, g ≫ i = i ≫ o₁.act.act a := fun a =>
    hi8 _ (fun u hu => by
      rw [Subgroup.mem_comap, hΦact]
      exact hGO _ hu a)
  have hisog : GlobalTheory.IwLevel.IsIsogDeg (toUnit G') (Ideal.absNorm w ^ j) := by
    rw [← hGc, ← hcard]; exact hi5
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h := hstd.card
      rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at h
      exact (not_subsingleton _) h.1
    · exact h0
  have hu : IsUnit (p : Γ(Sp K, ⊤)) := by
    have h0 : IsUnit (p : K) := hp.isUnit
    simpa using h0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨o', ψ, hψ1, hψ2, hψ3⟩ := hQO p D O b N hstd.three hstd.cop hstd.m1 r w j (p ^ (f * j)) inferInstance
    hstd.ule hj ⟨f * j, rfl, fun h => Nat.mul_pos hf0 h⟩ (Sp K) (x ≫ M.s) hu o₁ G' i hi1 hi2 hi3 hi4 hks
    hstab hisog
  obtain ⟨y, ⟨hy, m₀, m₁, hsq⟩, -⟩ := T.univ (Sp K) x o₁ o' m ψ hu hψ1 hψ2
  refine ⟨y, hy, fun g hg => ?_⟩
  obtain ⟨u, rfl⟩ := hΦs g
  have key : m₀.φ ≫ T.ms.φ = m.φ := by
    obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ T.ms
    have hcast : ∀ (f₁ f₂ : Sp K ⟶ M.X) (h : f₁ = f₂) (mm : GlobalTheory.UPel.HT.ObjMap o₁ M.univ f₂),
        ∃ mm' : GlobalTheory.UPel.HT.ObjMap o₁ M.univ f₁, mm'.φ = mm.φ := by
      rintro f₁ f₂ rfl mm
      exact ⟨mm, rfl⟩
    obtain ⟨m', hm'⟩ := hcast _ _ hy m
    rw [← hm', ← hm₂]
    exact (hOT p D O b N hstd.three hstd.cop _ _ _ _ _ _ o₁ M.univ M.univ _ (𝟙 _)).1 m₂ m'
  have h1 : Φ u ∈ G ↔ u ≫ ψ = 1 := by
    rw [← Subgroup.mem_comap, ← hi6, ← hψ3]
    exact ⟨fun h => h.1, fun h => ⟨h, 1, by
      rw [pow_one]
      intro a ha
      exact ((hkill u w).2 hg) a (hstd.ule ha)⟩⟩
  have hPK2 := hPK p D O b N T.Y (Sp K) (T.s ≫ M.s) (x ≫ M.s) y T.o T.o' o₁ o' m₀ m₁ T.ψ ψ hsq
  let eY : Over.mk y ≅ (Over.map y).obj (𝟙_ (Over (Sp K))) := Over.isoMk (Iso.refl _) (by simp)
  let a₀ : Over.mk y ⟶ T.o.A := eY.hom ≫ m₀.ptEquiv _ u
  have hl0 : a₀.left = u.left ≫ m₀.φ := by
    simp [a₀, eY, GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
  constructor
  · intro hK
    have ha0 : a₀ ≫ T.ψ = 1 := hK a₀ (by rw [hl0, Category.assoc, key, hΦl])
    rw [h1]
    exact ((hPK2.1 _ _ rfl u a₀ (by rw [eqToHom_refl, Category.id_comp, hl0])).1).2 ha0
  · intro hG a' ha'
    rw [h1] at hG
    let u' := (m₀.ptEquiv _).symm (eY.inv ≫ a')
    have hu'l : u'.left ≫ m₀.φ = a'.left := by
      rw [← GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
      simp [u', eY]
    have huu : u' = u := hΦi (Over.OverMorphism.ext (by
      rw [hΦl, hΦl, ← key, ← Category.assoc, hu'l, ha', hΦl, key]))
    exact ((hPK2.1 _ _ rfl u a' (by rw [eqToHom_refl, Category.id_comp, ← huu, hu'l])).1).1 hG
