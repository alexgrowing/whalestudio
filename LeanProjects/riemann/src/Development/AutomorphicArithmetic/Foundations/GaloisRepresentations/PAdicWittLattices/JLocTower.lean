import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsAlgEquivRestrictHomOfAlgebraMapCompat
import Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsIsPullbackGeomFiberBaseChangeTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
import Development.AutomorphicArithmetic.SimultaneousEigenspaces.EtaleCohomologyCorrOpCommPullback
import Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsBasisSimultaneousEigenspaceOfEquivariantBi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct
open UpperTheory.Gal.Seam

private theorem pullTot_bij_of_iso (l : ℕ) [Fact l.Prime] {E E' : Spc} (φ : E ≅ E') :
    Function.Bijective (pullTot l φ.hom) := by
  have h1 : pullTot l φ.hom ∘ₗ pullTot l φ.inv = LinearMap.id := by
    rw [← pullTot_comp, φ.hom_inv_id, pullTot_id]
  have h2 : pullTot l φ.inv ∘ₗ pullTot l φ.hom = LinearMap.id := by
    rw [← pullTot_comp, φ.inv_hom_id, pullTot_id]
  refine Function.bijective_iff_has_inverse.mpr ⟨pullTot l φ.inv, fun x => ?_, fun x => ?_⟩
  · exact LinearMap.congr_fun h2 x
  · exact LinearMap.congr_fun h1 x

private theorem pullTot_bij_of_deg (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E')
    (hf : ∀ n : ℤ, Function.Bijective (pullHQ l f n 0)) :
    Function.Bijective (pullTot l f) := by
  unfold pullTot
  exact ⟨(DirectSum.lmap_injective _).mpr fun n => (hf n).1,
    (DirectSum.lmap_surjective _).mpr fun n => (hf n).2⟩

private theorem bij_bc :
    UpperTheory.Gal.G3.VBcS → ∀ (l : ℕ) [Fact l.Prime] (Ω Ω' : Type) [Field Ω] [Field Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω'] [CharZero Ω] (j : Ω →+* Ω') {X X' : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of Ω)) [IsProper p] [Smooth p] (q : X' ⟶ Spec (CommRingCat.of Ω')) (u : X' ⟶ X), IsPullback u q p (Spec.map (CommRingCat.ofHom j)) → Function.Bijective (pullTot l (sch.map u)) := by
  intro hV l _ Ω Ω' _ _ _ _ _ j X X' p _ _ q u h
  have hl : IsUnit ((l : ℕ) : Ω) :=
    IsUnit.mk0 _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hb : Function.Bijective
      (pullTot l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom j))))) :=
    pullTot_bij_of_deg l _ fun n => hV l Ω Ω' j hl p n 0
  have hu : u = h.isoPullback.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom j)) :=
    (h.isoPullback_hom_fst).symm
  rw [hu, Functor.map_comp, pullTot_comp]
  rw [LinearMap.coe_comp]
  exact (pullTot_bij_of_iso l (sch.mapIso h.isoPullback)).comp hb

theorem UpperTheory.Gal.G3.locTower_of :
    UpperTheory.Gal.G3.VBcS → UpperTheory.Gal.Seam.HopEx → NiceBc → LocTower := by
  intro hV hHop hNice l _ k K Ω Ω' _ _ _ _ _ _ _ _ _ τ j hj H hH L _ _ θ d ρ₀ hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom j.injective
  haveI : CharZero K := charZero_of_injective_ringHom τ.injective
  obtain ⟨r, hr⟩ := UpperTheory.exists_algEquiv_restrict_hom_of_algebraMap_compat k K Ω Ω' τ j hj
  obtain ⟨u, v, hu, hv, hg⟩ := UpperTheory.exists_isPullback_geomFiber_baseChange_tower k K Ω Ω' τ j hj H
  have hH₀ := hH
  obtain ⟨hsm, hpj, hfe⟩ := hH
  haveI : IsProper H.q := GlobalTheory.SchemeWords.isProper_of_isProjOver hpj
  haveI : Smooth H.q := hsm
  have hΦ := bij_bc hV l Ω Ω' j (pullback.snd H.q _) (pullback.snd _ _) u hu
  have hH' := hNice k K τ H hH₀
  have hInt : ∀ g : H.Γ, pullTot l (sch.map u) ∘ₗ hop l H Ω g = hop l (bcAlong H τ) Ω' g ∘ₗ pullTot l (sch.map u) := by
    intro g
    obtain ⟨dg, hd⟩ := hfe g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    have hB : UpperTheory.Gal.G3.BcSplits := UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts) UpperTheory.Gal.G3.pPtsOfSplits)
    obtain ⟨hf, he, -⟩ := hB (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _)
      PEmpty (fun x => x.elim) (fun x => x.elim)
    haveI : IsFinite (H.sΩ Ω g) := hf
    haveI : Etale (H.sΩ Ω g) := he
    exact UpperTheory.etaleCohomology_corrOp_comm_pullback l Ω' (H.sΩ Ω g) (H.tΩ Ω g) ((bcAlong H τ).sΩ Ω' g) ((bcAlong H τ).tΩ Ω' g) (pullback.snd _ _) u (v g) (hv g).1 (hv g).2
      ((UpperTheory.Gal.G3.bcMap_snd _ ((bcAlong H τ).t g) ((bcAlong H τ).comm g)).trans
        (UpperTheory.Gal.G3.bcMap_snd _ ((bcAlong H τ).s g) rfl).symm) _ _ (hHop l k Ω H hH₀ g) (hHop l K Ω' _ hH' g)
  obtain ⟨b, hb⟩ := hM
  obtain ⟨b', hb'⟩ := UpperTheory.exists_basis_simultaneousEigenspace_of_equivariant_bijective l _ _ (pullTot l (sch.map u)) hΦ H.Γ (fun g => hop l H Ω g) (fun g => hop l (bcAlong H τ) Ω' g) hInt L θ d b
  have hgal : ∀ (σ : Ω ≃ₐ[k] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) →
      ∀ x, galV l (bcAlong H τ) Ω' L σ' ((pullTot l (sch.map u)).baseChange L x) = (pullTot l (sch.map u)).baseChange L (galV l H Ω L σ x) := by
    intro σ σ' h x
    have e : galTot l Ω' (bcAlong H τ).q σ' ∘ₗ pullTot l (sch.map u) = pullTot l (sch.map u) ∘ₗ galTot l Ω H.q σ := by
      unfold galTot
      rw [← pullTot_comp, ← pullTot_comp, ← Functor.map_comp, ← Functor.map_comp, hg σ σ' h]
    simp only [galV]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, e]
  refine ⟨ρ₀.comp r, ⟨b', fun σ' i => ?_⟩, fun σ σ' h => ?_⟩
  · refine (congrArg (galV l (bcAlong H τ) Ω' L σ') (hb' i)).trans ?_
    refine (hgal (r σ') σ' (fun x => hr σ' x) _).trans ?_
    refine (congrArg ((pullTot l (sch.map u)).baseChange L) (hb (r σ') i)).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.map_smul]
    exact congrArg (((ρ₀ (r σ') : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) m i • ·) (hb' m).symm
  · have : r σ' = σ := by
      ext x
      apply j.injective
      rw [← hr, h]
    simp [this]
