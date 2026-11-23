import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GaloisActionWeightSpectralE1Apply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOfPf

section Geom

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem geomMap_comp' {X Y Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)}
    {r : Z ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (v : Y ⟶ Z) (hu : u ≫ q = p) (hv : v ≫ r = q)
    (huv : (u ≫ v) ≫ r = p) :
    GlobalTheory.Et.geomMap Ω p u hu ≫ GlobalTheory.Et.geomMap Ω q v hv = GlobalTheory.Et.geomMap Ω p (u ≫ v) huv := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold GlobalTheory.Et.geomMap
    erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    rw [Category.assoc]
  · rw [Category.assoc]
    unfold GlobalTheory.Et.geomMap
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

theorem geomMap_id' {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (h : 𝟙 X ≫ p = p) :
    GlobalTheory.Et.geomMap Ω p (𝟙 X) h = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [GlobalTheory.Et.geomMap]

theorem galMap_geomMap' {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.geomMap Ω p u hu = GlobalTheory.Et.geomMap Ω p u hu ≫ GlobalTheory.Et.galMap Ω q σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.geomMap, pullback.lift_fst, ← Category.assoc,
      GlobalTheory.Et.galMap_fst]
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, GlobalTheory.Et.geomMap, pullback.lift_snd, pullback.lift_snd_assoc,
      GlobalTheory.Et.galMap_snd]

end Geom

theorem toMatrix_map {R : Type*} [CommSemiring R] {M M' N N' : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι R M)
    (b' : Module.Basis κ R N) (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N') (φ : M' →ₗ[R] N') :
    LinearMap.toMatrix (b.map e) (b'.map e') φ =
      LinearMap.toMatrix b b' (e'.symm.toLinearMap ∘ₗ φ ∘ₗ e.toLinearMap) := by
  ext i j
  simp [LinearMap.toMatrix_apply]

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

section Et

theorem etPull_comp {X X' X'' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {q'' : X'' ⟶ Sp ↥K.1}
    {f : X' ⟶ X} {g : X'' ⟶ X'} (hf : f ≫ q = q') (hg : g ≫ q' = q'') (n : ℕ) (x : EtV q n) :
    etPull hg n (etPull hf n x) = etPull (f := g ≫ f) (by rw [Category.assoc, hf, hg]) n x := by
  unfold GlobalTheory.HTLink.etPull
  rw [← LinearMap.comp_apply, ← GlobalTheory.EtC.WSS.pullHQ_map_comp, ← Functor.map_comp, geomMap_comp']

theorem etPull_congr {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f f' : X' ⟶ X}
    (hf : f ≫ q = q') (hf' : f' ≫ q = q') (h : f = f') (n : ℕ) (x : EtV q n) : etPull hf n x = etPull hf' n x := by
  subst h; rfl

theorem etPull_id {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (h : 𝟙 X ≫ q = q) (n : ℕ) (x : EtV q n) :
    etPull (f := 𝟙 X) h n x = x := by
  unfold GlobalTheory.HTLink.etPull
  rw [geomMap_id', CategoryTheory.Functor.map_id, GlobalTheory.EtC.WSS.pullHQ_map_id]
  rfl

theorem etAct_eq {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (σ : ↥(GK K)) :
    etAct q n σ = GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) q
      (IntermediateField.fixingSubgroupEquiv K.1 σ))) n 0 := rfl

theorem etPull_etAct {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X} (hf : f ≫ q = q')
    (n : ℕ) (σ : ↥(GK K)) (x : EtV q n) : etPull hf n (etAct q n σ x) = etAct q' n σ (etPull hf n x) := by
  rw [etAct_eq, etAct_eq]
  unfold GlobalTheory.HTLink.etPull
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← GlobalTheory.EtC.WSS.pullHQ_map_comp, ← GlobalTheory.EtC.WSS.pullHQ_map_comp,
    ← Functor.map_comp, ← Functor.map_comp, galMap_geomMap']

def etEquiv {X Y : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : Y ⟶ Sp ↥K.1} (e : X ≅ Y) (he : e.hom ≫ q' = q) (n : ℕ) :
    EtV q' n ≃ₗ[ℚ_[l]] EtV q n where
  toLinearMap := etPull he n
  invFun := etPull (f := e.inv) (by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]) n
  left_inv x := by
    change etPull (f := e.inv) _ n (etPull he n x) = x
    rw [etPull_comp, etPull_congr _ (Category.id_comp q') e.inv_hom_id, etPull_id]
  right_inv x := by
    change etPull he n (etPull (f := e.inv) _ n x) = x
    rw [etPull_comp, etPull_congr _ (Category.id_comp q) e.hom_inv_id, etPull_id]

theorem etEquiv_apply {X Y : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : Y ⟶ Sp ↥K.1} (e : X ≅ Y) (he : e.hom ≫ q' = q)
    (n : ℕ) (x : EtV q' n) : etEquiv e he n x = etPull he n x := rfl

theorem etEquiv_symm_apply {X Y : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : Y ⟶ Sp ↥K.1} (e : X ≅ Y)
    (he : e.hom ≫ q' = q) (n : ℕ) (x : EtV q n) :
    (etEquiv e he n).symm x = etPull (f := e.inv) (by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]) n x :=
  rfl

end Et

section Hodge

theorem hodgePull_comp' {X X' X'' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {q'' : X'' ⟶ Sp ↥K.1}
    {f : X' ⟶ X} {g : X'' ⟶ X'} (hf : f ≫ q = q') (hg : g ≫ q' = q'') (j b : ℕ) (x : hodgeH q j b) :
    hodgePull hg j b (hodgePull hf j b x) = hodgePull (f := g ≫ f) (by rw [Category.assoc, hf, hg]) j b x :=
  GlobalTheory.HodgeCoh.hodgePull_comp hf hg _ j b x

theorem hodgePull_congr {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f f' : X' ⟶ X}
    (hf : f ≫ q = q') (hf' : f' ≫ q = q') (h : f = f') (j b : ℕ) (x : hodgeH q j b) :
    hodgePull hf j b x = hodgePull hf' j b x := by
  subst h; rfl

def hodgeEquiv {X Y : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : Y ⟶ Sp ↥K.1} (e : X ≅ Y) (he : e.hom ≫ q' = q) (j b : ℕ) :
    hodgeH q' j b ≃ₗ[↥K.1] hodgeH q j b where
  toLinearMap := hodgePull he j b
  invFun := hodgePull (f := e.inv) (by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]) j b
  left_inv x := by
    change hodgePull (f := e.inv) _ j b (hodgePull he j b x) = x
    rw [hodgePull_comp', hodgePull_congr _ (Category.id_comp q') e.inv_hom_id]
    exact GlobalTheory.HodgeCoh.hodgePull_id q' j b x
  right_inv x := by
    change hodgePull he j b (hodgePull (f := e.inv) _ j b x) = x
    rw [hodgePull_comp', hodgePull_congr _ (Category.id_comp q) e.hom_inv_id]
    exact GlobalTheory.HodgeCoh.hodgePull_id q j b x

end Hodge

def trFrame {X Y : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : Y ⟶ Sp ↥K.1} {n : ℕ} (F : Frame (K := K) q n) (e : X ≅ Y)
    (he : e.hom ≫ q' = q) : Frame (K := K) q' n where
  d := F.d
  b := F.b.map (etEquiv e he n).symm
  e := F.e
  c a := (F.c a).map (hodgeEquiv e he a (n - a)).symm

section Tr

variable {A A' X X' : Scheme.{0}} {qA : A ⟶ Sp ↥K.1} {qA' : A' ⟶ Sp ↥K.1} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1}
  {n : ℕ} (F : Frame (K := K) qA n) (F' : Frame (K := K) qA' n) (e : A ≅ X) (he : e.hom ≫ q = qA)
  (e' : A' ≅ X') (he' : e'.hom ≫ q' = qA') {f : X' ⟶ X} (hf : f ≫ q = q') {f₀ : A' ⟶ A} (hf₀ : f₀ ≫ qA = qA')

theorem rho_tr (σ : ↥(GK K)) : (trFrame F e he).rho σ = F.rho σ := by
  have key : (etEquiv e he n).toLinearMap ∘ₗ etAct q n σ ∘ₗ (etEquiv e he n).symm.toLinearMap = etAct qA n σ := by
    refine LinearMap.ext fun x => ?_
    change etPull he n (etAct q n σ ((etEquiv e he n).symm x)) = etAct qA n σ x
    rw [etPull_etAct]
    exact congrArg _ ((etEquiv e he n).apply_symm_apply x)
  change (LinearMap.toMatrix (F.b.map (etEquiv e he n).symm) (F.b.map (etEquiv e he n).symm) (etAct q n σ)).map
      (algebraMap ℚ_[l] ℂ_[l]) = (LinearMap.toMatrix F.b F.b (etAct qA n σ)).map (algebraMap ℚ_[l] ℂ_[l])
  rw [toMatrix_map, LinearEquiv.symm_symm, key]

theorem isHT_tr (Φ : Matrix (Fin F.d) F.Col ℂ_[l]) (h : F.IsHT Φ) : (trFrame F e he).IsHT Φ := by
  refine ⟨h.1, fun σ => ?_⟩
  rw [rho_tr]
  exact h.2 σ

include hf hf₀ in
theorem etMat_tr (h : f₀ ≫ e.hom = e'.hom ≫ f) :
    (trFrame F e he).etMat (trFrame F' e' he') hf = F.etMat F' hf₀ := by
  have key : (etEquiv e' he' n).toLinearMap ∘ₗ etPull hf n ∘ₗ (etEquiv e he n).symm.toLinearMap = etPull hf₀ n := by
    refine LinearMap.ext fun x => ?_
    change etPull he' n (etPull hf n ((etEquiv e he n).symm x)) = etPull hf₀ n x
    rw [etEquiv_symm_apply, etPull_comp, etPull_comp]
    refine etPull_congr _ _ ?_ n x
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  change (LinearMap.toMatrix (F.b.map (etEquiv e he n).symm) (F'.b.map (etEquiv e' he' n).symm) (etPull hf n)).map
      (algebraMap ℚ_[l] ℂ_[l]) = (LinearMap.toMatrix F.b F'.b (etPull hf₀ n)).map (algebraMap ℚ_[l] ℂ_[l])
  rw [toMatrix_map, LinearEquiv.symm_symm, key]

include hf hf₀ in
theorem hodgeMat_tr (h : f₀ ≫ e.hom = e'.hom ≫ f) :
    (trFrame F e he).hodgeMat (trFrame F' e' he') hf = F.hodgeMat F' hf₀ := by
  have key : ∀ a : Fin (n + 1), LinearMap.toMatrix ((F.c a).map (hodgeEquiv e he a (n - a)).symm)
      ((F'.c a).map (hodgeEquiv e' he' a (n - a)).symm) (hodgePull hf a (n - a)) =
      LinearMap.toMatrix (F.c a) (F'.c a) (hodgePull hf₀ a (n - a)) := by
    intro a
    rw [toMatrix_map, LinearEquiv.symm_symm]
    congr 1
    refine LinearMap.ext fun x => ?_
    change hodgePull he' a (n - a) (hodgePull hf a (n - a) (hodgePull (f := e.inv)
      (by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]) a (n - a) x)) = hodgePull hf₀ a (n - a) x
    rw [hodgePull_comp', hodgePull_comp']
    refine hodgePull_congr _ _ ?_ a (n - a) x
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  change (Matrix.blockDiagonal' fun a : Fin (n + 1) => LinearMap.toMatrix ((F.c a).map (hodgeEquiv e he a (n - a)).symm)
      ((F'.c a).map (hodgeEquiv e' he' a (n - a)).symm) (hodgePull hf a (n - a))).map (GlobalTheory.HTLink.toC K) =
    (Matrix.blockDiagonal' fun a : Fin (n + 1) => LinearMap.toMatrix (F.c a) (F'.c a) (hodgePull hf₀ a (n - a))).map
      (GlobalTheory.HTLink.toC K)
  simp only [key]

end Tr

end PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOfPf

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

open CoverOfPf in
theorem coverOf : CoverOf := by
  intro hG l _ K H J ι hcov n
  obtain ⟨hfr, Φ, hHT, hnat⟩ := hG l K n
  obtain ⟨MZ, eZ, ⟨hSm, hd, -⟩, hqZ, hj⟩ := hcov
  obtain ⟨FZ, -⟩ := hfr MZ hSm hd
  refine ⟨trFrame FZ eZ hqZ, Φ MZ hSm hd FZ, isHT_tr FZ eZ hqZ _ (hHT MZ hSm hd FZ), fun j => ?_⟩
  obtain ⟨W, c, G, hG1, hG2, a, I, hI, σ, hgal, hspl, MW, eW, ⟨hSmW, hdW, -⟩, ⟨uc, huc, hc⟩, hi⟩ := hj j
  have hqW : eW.hom ≫ c ≫ H.q = MW.q := by
    rw [← Category.assoc, ← hc, Category.assoc, hqZ, CrystallineSemistableComparison.Model.genMap_q]
  have hσ : ∀ i, (σ i ≫ H.t (ι j)) ≫ H.q = c ≫ H.q := by
    intro i
    obtain ⟨ui, hui, h⟩ := hi i
    rw [← cancel_epi eW.hom, hqW, ← Category.assoc, ← Category.assoc, Category.assoc eW.hom, ← h, Category.assoc, hqZ,
      CrystallineSemistableComparison.Model.genMap_q]
  obtain ⟨FW, -⟩ := hfr MW hSmW hdW
  refine ⟨W, c, G, hG1, hG2, a, I, hI, σ, hσ, hgal, hspl, trFrame FW eW hqW, Φ MW hSmW hdW FW, ?_, fun i => ?_⟩
  · rw [etMat_tr FZ FW eZ hqZ eW hqW rfl (CrystallineSemistableComparison.Model.genMap_q uc huc) hc,
      hodgeMat_tr FZ FW eZ hqZ eW hqW rfl (CrystallineSemistableComparison.Model.genMap_q uc huc) hc]
    exact hnat MZ MW hSm hSmW hd hdW FZ FW uc huc
  · obtain ⟨ui, hui, h⟩ := hi i
    rw [etMat_tr FZ FW eZ hqZ eW hqW (hσ i) (CrystallineSemistableComparison.Model.genMap_q ui hui) h,
      hodgeMat_tr FZ FW eZ hqZ eW hqW (hσ i) (CrystallineSemistableComparison.Model.genMap_q ui hui) h]
    exact hnat MZ MW hSm hSmW hd hdW FZ FW ui hui

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
