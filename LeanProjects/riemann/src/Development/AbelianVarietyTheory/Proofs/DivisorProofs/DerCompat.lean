import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisExtendsToAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoefficientsUniqueAffineOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSAgree

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  show (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) :
    (X.presheaf.map (homOfLE h₂).op).hom.comp (X.presheaf.map (homOfLE h₁).op).hom =
      (X.presheaf.map (homOfLE h₃).op).hom :=
  RingHom.ext (res_res h₁ h₂ h₃)

theorem der_compat {X : Scheme.{0}} (U : X.affineOpens) (f : Γ(X, U.1)) (P : X.Opens)
    (hP : P ≤ X.basicOpen f) (hPU : P ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, X.basicOpen f) Γ(X, X.basicOpen f)) (DP : Derivation ℤ Γ(X, P) Γ(X, P))
    (hW : ∀ r, DW ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom r) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (D r))
    (hD : ∀ r, DP ((X.presheaf.map (homOfLE hPU).op).hom r) = (X.presheaf.map (homOfLE hPU).op).hom (D r)) :
    ∀ r, DP ((X.presheaf.map (homOfLE hP).op).hom r) = (X.presheaf.map (homOfLE hP).op).hom (DW r) := by
  intro r
  obtain ⟨u, r', hu, hb⟩ := GlobalTheory.LogKSLoc.exists_frac U (X.affineBasicOpen f) (X.basicOpen_le f) f rfl r
  have key : ∀ x : Γ(X, U.1), DP ((X.presheaf.map (homOfLE hP).op).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x)) =
      (X.presheaf.map (homOfLE hP).op).hom (DW ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x)) := by
    intro x
    rw [res_res _ _ hPU, hD, hW, res_res _ _ hPU]
  exact GlobalTheory.LogKSLoc.leibniz_frac _ DP (fun x y => by rw [DP.leibniz, smul_eq_mul, smul_eq_mul]) DW hu hb
    (key u) (key r')

theorem dual_alg {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (dualMap r).comp (algebraMap S (DualNumber S)) = (algebraMap S' (DualNumber S')).comp r := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

theorem fst_dual {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap r) = r.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext a <;> (try simp [dualMap]) <;> rfl

theorem dual_eps {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') (c : S) :
    (dualMap r).comp (epsMul c) = (epsMul (r c)).comp (dualMap r) := by
  ext a <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem eps_over {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') :
    spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x' := by
  rw [← hx, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', dual_alg]

def epsHom {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') : tEpsG x' ⟶ tEpsG x :=
  Over.homMk (spMap (dualMap r)) (eps_over r hx)

theorem tan_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t x' (spMap (dualMap r) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, eps_over r hx]
  · have h : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap r) =
        spMap r ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', fst_dual]
    rw [← Category.assoc, h, Category.assoc, hv.2]
    let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap r) hx
    exact congrArg CommaMorphism.left (comp_one k (M := t.G))

theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v cf w) :
    IsCombAtG t x' (fun i => spMap (dualMap r) ≫ v i) (fun i => r (cf i)) (spMap (dualMap r) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let φ : (tEpsG x ⟶ t.G) →* (tEpsG x' ⟶ t.G) :=
    { toFun := fun a => epsHom r hx ≫ a
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (dualMap r) ≫ (u i).left = _
    rw [hu, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', dual_eps, ← GlobalTheory.LogKSLoc.spMap_comp', Category.assoc]
  · have e : (List.ofFn fun i => φ (u i)).prod = φ (List.ofFn u).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [e, ← hw]
    rfl
end Gen

theorem tan_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsTanAtG t (chart U) v → IsTanAtG t (chart W) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v) :=
  fun _ _ _ _ _ _ t U W hW _ hv => tan_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) hv

theorem comb_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (cf : Fin n → Γ(X, U.1)) (w : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsCombAtG t (chart U) v cf w → IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) (fun i => (X.presheaf.map (homOfLE hW).op).hom (cf i)) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ w) :=
  fun _ _ _ _ _ _ t U W hW _ _ _ _ h => comb_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) h

theorem agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∀ (f g : Γ(Y.X, U.1)) (DWf : Derivation ℤ Γ(Y.X, (Y.X.affineBasicOpen f).1) Γ(Y.X, (Y.X.affineBasicOpen f).1)) (DWg : Derivation ℤ Γ(Y.X, (Y.X.affineBasicOpen g).1) Γ(Y.X, (Y.X.affineBasicOpen g).1)), (∀ r, DWf ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom r) = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom (D.1 r)) → (∀ r, DWg ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom r) = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom (D.1 r)) → ∀ (Θf : Matrix (Fin n) (Fin n) Γ(Y.X, (Y.X.affineBasicOpen f).1)) (Θg : Matrix (Fin n) (Fin n) Γ(Y.X, (Y.X.affineBasicOpen g).1)), IsKS Y.t (interior Y) (Y.X.affineBasicOpen f) (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom) ≫ v i) DWf Θf → IsKS Y.t (interior Y) (Y.X.affineBasicOpen g) (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom) ≫ v i) DWg Θg → (Y.X.presheaf.map (homOfLE (inf_le_left : Y.X.basicOpen f ⊓ Y.X.basicOpen g ≤ Y.X.basicOpen f)).op).hom.mapMatrix Θf = (Y.X.presheaf.map (homOfLE (inf_le_right : Y.X.basicOpen f ⊓ Y.X.basicOpen g ≤ Y.X.basicOpen g)).op).hom.mapMatrix Θg := by
  intro E _ _ _ H Dw l Xo c Y h1 h2 h3 h4 U n v A hv hb hA D f g DWf DWg hDf hDg Θf Θg hKf hKg
  let P : Y.X.affineOpens := ⟨Y.X.basicOpen f ⊓ Y.X.basicOpen g, by
    rw [← Scheme.basicOpen_mul]; exact (Y.X.affineBasicOpen (f * g)).2⟩
  have hPU : P.1 ≤ U.1 := inf_le_left.trans (Y.X.basicOpen_le f)
  have hPf : P.1 ≤ (Y.X.affineBasicOpen f).1 := inf_le_left
  have hPg : P.1 ≤ (Y.X.affineBasicOpen g).1 := inf_le_right
  have hPf' : P.1 = Y.X.basicOpen ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom g) :=
    (Scheme.basicOpen_res _ _ _).symm
  have hPg' : P.1 = Y.X.basicOpen ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom f) := by
    rw [Scheme.basicOpen_res]; exact inf_comm _ _
  have hPUf : P.1 = Y.X.basicOpen (f * g) := (Scheme.basicOpen_mul _ _ _).symm
  obtain ⟨DP, hDPmem, hDP⟩ := GlobalTheory.LogDerLoc.exists_logDer_basicOpen Y.X _ Y.s _ U P hPU (f * g) hPUf D.1 D.2
  have cf := der_compat U f P.1 hPf hPU D.1 DWf DP hDf hDP
  have cg := der_compat U g P.1 hPg hPU D.1 DWg DP hDg hDP
  have kf := GlobalTheory.LogKSLoc.isKS_basicOpen E H Y.X Y.t (interior Y) _ P hPf _ hPf' n _ DWf DP Θf cf hKf
  have kg := GlobalTheory.LogKSLoc.isKS_basicOpen E H Y.X Y.t (interior Y) _ P hPg _ hPg' n _ DWg DP Θg cg hKg
  have fr : ∀ {V : Y.X.Opens} (hV : V ≤ U.1) (hPV : P.1 ≤ V) (i : Fin n),
      spMap (dualMap (Y.X.presheaf.map (homOfLE hPV).op).hom) ≫
        spMap (dualMap (Y.X.presheaf.map (homOfLE hV).op).hom) ≫ v i =
      spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i := by
    intro V hV hPV i
    rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp', res_comp]
  rw [show (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPf).op).hom) ≫
      spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom) ≫ v i) =
      fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i from funext (fr _ hPf)] at kf
  rw [show (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPg).op).hom) ≫
      spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom) ≫ v i) =
      fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i from funext (fr _ hPg)] at kg
  exact GlobalTheory.T.rigid_chart_dual_number_deformation E H Dw l Xo c Y h1 h2 h3 h4 P n _ (fun a => (Y.X.presheaf.map (homOfLE hPU).op).hom.mapMatrix (A a))
    (fun i => tan_res E H Y.X Y.t U P hPU _ (hv i))
    (fun w hw => by
      obtain ⟨cf, hcf⟩ := GlobalTheory.T.tangent_basis_extends_to_affine_open E H Y.X Y.t U P hPU (f * g) hPUf n v hv hb w hw
      exact ⟨cf, hcf, fun cf' h => GlobalTheory.T.tangent_coefficients_unique_affine_open E H Y.X Y.t U P hPU (f * g) hPUf n v hv hb cf' cf w h hcf⟩)
    (fun a i => by
      have := comb_res E H Y.X Y.t U P hPU n v (A a i) _ (hA a i)
      rw [Category.assoc]; exact this)
    ⟨DP, hDPmem⟩ _ _ kf kg

end GlobalTheory.KSAgree
