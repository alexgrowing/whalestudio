import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanPureDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pFullOf :
    FullOf := by
  intro p _ D R _ _ gb S s N o k _ _ t J
  have hp : p.Prime := Fact.out
  have hts : t ≫ s = spMap (Spec.preimage (t ≫ s)).hom := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', -⟩ := o.geom k t _ hts
  have hLB : (o.P.pull (Over.Hom.left (lift (𝟙 o.A) (𝟙 o.A)))).IsLB := pull_isLB o.isLB _
  have hpos : ∀ r : ℕ, 0 < p ^ r := fun r => pow_pos hp.pos r
  refine HeckeGen.exists_join (fun c g => g ≫ o.act.act c) _ ?_ ?_ ?_ ?_ ?_ J (fun r => I'.ζ (p ^ r))
    (fun r => I'.ev (p ^ r)) (fun r => I'.ζ_prim _ (hpos r)) ?_ (fun r x y => I'.add _ x y)
    (fun r b x => I'.lin _ b x) (fun r x => I'.ker _ (hpos r) x) (fun r q => I'.onto _ (hpos r) q) ?_
    (fun r x y => I'.isom _ (hpos r) x y)
  · intro c a b
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  · intro n hn g g' hg hg'
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S o.A _ o.ab hLB k t n hn
      (HeckeGen.natCast_ne_zero_of_hom (Spec.preimage (t ≫ s)).hom n hn) g g' hg hg'
    obtain ⟨z, rfl⟩ := HeckeGen.unitOn_bij.2 e
    exact ⟨z, he⟩
  · intro n g g' z z' h1 h2
    exact HeckeGen.unitOn_bij.1 (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab hLB h1 h2)
  · intro n j g g' z h
    have hu : unitOn (z ^ j) = unitOn z ^ j := by
      unfold unitOn
      exact map_pow _ _ _
    rw [hu, Nat.cast_mul]
    exact GlobalTheory.WeilIsogeny.weilIs_pow GlobalTheory.globalFns_holds o.ab hLB j h
  · intro n j g g' z h
    haveI := isMonHom_mulA (A := o.A) j
    have hiso := GlobalTheory.HeckeWeilValue.lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ j
    have e1 : ∀ x : Over.mk t ⟶ o.A, x ≫ Out.mulA o.A j = x ^ j := fun x => by
      rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have h' := h
    rw [← e1, ← e1] at h'
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab hLB hLB (Out.mulA o.A j) hiso h'
    rw [Nat.cast_mul]
    exact this
  · intro r s'
    rw [pow_add]
    exact I'.ζ_pow _ _ (hpos r) (hpos s')
  · intro r s' x
    rw [pow_add]
    exact I'.tower _ _ (hpos r) (hpos s') x
