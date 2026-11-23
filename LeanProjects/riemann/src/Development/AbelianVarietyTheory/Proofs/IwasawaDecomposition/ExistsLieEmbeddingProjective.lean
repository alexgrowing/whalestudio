import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCoverStatement
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open GlobalTheory.FactorDepth GlobalTheory.Points

namespace GlobalTheory.LieEmb

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Bas

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R}

theorem comb_mulVec (hu : ∀ j, IsTanAtG t x (u j)) {m : ℕ} {w : Fin m → Tn t R} {A : Matrix (Fin n) (Fin m) R}
    {N : Fin m → R} {w' : Tn t R} (h1 : ∀ i, IsCombAtG t x u (fun j => A j i) (w i))
    (h2 : IsCombAtG t x w N w') : IsCombAtG t x u (A.mulVec N) w' := by
  have hw : w = fun i => (combT x (fun j => ovT (hu j)) (fun j => A j i)).left :=
    funext fun i => ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 (h1 i)).symm
  subst hw
  rw [isCombAtG_iff, combT_combT x _ (fun j => smT_zero_ovT (hu j))] at h2
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 h2

theorem comb_unit (hu : ∀ j, IsTanAtG t x (u j)) (j : Fin n) : IsCombAtG t x u (Pi.single j 1) (u j) :=
  (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 (by
    rw [combT_single x _ (fun j => smT_zero_ovT (hu j))]; rfl)

variable (x u) in

def Bas : Prop := (∀ j, IsTanAtG t x (u j)) ∧ ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x u a w

open Classical in
variable (x u) in

def co (w : Tn t R) : Fin n → R := if h : ∃ a, IsCombAtG t x u a w then h.choose else 0

theorem Bas.co_spec (h : Bas x u) {w : Tn t R} (hw : IsTanAtG t x w) : IsCombAtG t x u (co x u w) w := by
  have e := (h.2 w hw).exists
  rw [co, dif_pos e]
  exact e.choose_spec

theorem Bas.co_eq (h : Bas x u) {w : Tn t R} {a : Fin n → R} (ha : IsCombAtG t x u a w) : co x u w = a :=
  have hw := comb_tan t h.1 ha
  (h.2 w hw).unique (h.co_spec hw) ha

theorem Bas.co_inj (h : Bas x u) {w w' : Tn t R} (hw : IsTanAtG t x w) (hw' : IsTanAtG t x w')
    (e : co x u w = co x u w') : w = w' :=
  comb_unique t h.1 (h.co_spec hw) (e ▸ h.co_spec hw')

theorem Bas.co_self (h : Bas x u) (j : Fin n) : co x u (u j) = Pi.single j 1 := h.co_eq (comb_unit h.1 j)

variable (x u) in

def mat {m : ℕ} (w : Fin m → Tn t R) : Matrix (Fin n) (Fin m) R := Matrix.of fun a b => co x u (w b) a

theorem Bas.co_comb (h : Bas x u) {m : ℕ} {w : Fin m → Tn t R} (hw : ∀ j, IsTanAtG t x (w j)) {N : Fin m → R}
    {w' : Tn t R} (h2 : IsCombAtG t x w N w') : co x u w' = (mat x u w).mulVec N :=
  h.co_eq (comb_mulVec h.1 (fun i => h.co_spec (hw i)) h2)

theorem Bas.mat_self (h : Bas x u) : mat x u u = 1 := by
  ext a b
  rw [mat, Matrix.of_apply, h.co_self, Matrix.one_apply, Pi.single_apply]

theorem Bas.mat_mul (h : Bas x u) {m : ℕ} {w : Fin m → Tn t R} (hw : Bas x w) {l : ℕ} {z : Fin l → Tn t R}
    (hz : ∀ j, IsTanAtG t x (z j)) : mat x u w * mat x w z = mat x u z := by
  ext a b
  exact (congrFun (h.co_comb hw.1 (hw.co_spec (hz b))) a).symm

theorem Bas.co_map {R' : Type} [CommRing R'] (ψ : R →+* R') (h : Bas x u)
    (h' : Bas (spMap ψ ≫ x) fun j => spMap (dualMap ψ) ≫ u j) {w : Tn t R} (hw : IsTanAtG t x w) :
    co (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ u j) (spMap (dualMap ψ) ≫ w) = ψ ∘ co x u w :=
  h'.co_eq (GlobalTheory.LatDRFree.comb_map t ψ (h.co_spec hw))

theorem bc_bc {R' R'' : Type} [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') (w : Tn t R) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  have e : (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  rw [← Category.assoc, spMap_comp', e]

theorem stab_bas (h : StabBasis t x u) {R' : Type} [CommRing R'] (φ : R →+* R') :
    Bas (spMap φ ≫ x) fun j => spMap (dualMap φ) ≫ u j :=
  ⟨fun j => isTanAtG_map t φ (h.1 j), h.2 R' φ⟩

theorem stab_map (h : StabBasis t x u) {R' : Type} [CommRing R'] (φ : R →+* R') :
    StabBasis t (spMap φ ≫ x) fun j => spMap (dualMap φ) ≫ u j := by
  refine ⟨fun j => isTanAtG_map t φ (h.1 j), fun R'' _ ψ => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, spMap_comp']
  exact h.2 R'' (ψ.comp φ)

end Bas

section At

variable {U : X.Opens} {n : ℕ} (v : Fin n → Tn t Γ(X, U)) {R : Type} [CommRing R]

def vAt (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) : Fin n → Tn t R := fun j => spMap (dualMap (valMap x U h).hom) ≫ v j

theorem le_comp {R' : Type} [CommRing R'] (ψ : R →+* R') {x : Sp R ⟶ X} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U := le_preimage_comp _ x h (le_preimage_top _)

theorem vAt_comp {R' : Type} [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) : vAt v (spMap ψ ≫ x) h' = fun j => spMap (dualMap ψ) ≫ vAt v x h j := by
  funext j
  have e : (valMap (spMap ψ ≫ x) U h').hom = ψ.comp (valMap x U h).hom := RingHom.ext fun f => by
    rw [← valR_eq, valR_spMap_comp ψ x U h, valR_eq x U h]; rfl
  rw [vAt, vAt, e]
  exact (bc_bc _ _ _).symm

variable {v}

theorem stab_vAt (hU : IsAffineOpen U) (hv : StabBasis t hU.fromSpec v) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    StabBasis t x (vAt v x h) := by
  have := stab_map hv (valMap x U h).hom
  have e : spMap (valMap x U h).hom ≫ hU.fromSpec = x := specMap_valMap_fromSpec hU x h
  rw [e] at this
  exact this

theorem bas_vAt (hU : IsAffineOpen U) (hv : StabBasis t hU.fromSpec v) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Bas x (vAt v x h) := by
  have := stab_bas hv (valMap x U h).hom
  have e : spMap (valMap x U h).hom ≫ hU.fromSpec = x := specMap_valMap_fromSpec hU x h
  rw [e] at this
  exact this

theorem co_vAt_map (hU : IsAffineOpen U) (hv : StabBasis t hU.fromSpec v) {R' : Type} [CommRing R'] (ψ : R →+* R')
    (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) {w : Tn t R} (hw : IsTanAtG t x w) :
    co (spMap ψ ≫ x) (vAt v _ h') (spMap (dualMap ψ) ≫ w) = ψ ∘ co x (vAt v x h) w := by
  rw [vAt_comp v ψ x h h']
  exact (bas_vAt hU hv x h).co_map ψ (stab_bas (stab_vAt hU hv x h) ψ) hw

theorem le_fromSpec {W : X.Opens} (hW : IsAffineOpen W) (e : W ≤ U) (φ : Γ(X, W) →+* R) :
    ⊤ ≤ (spMap φ ≫ hW.fromSpec) ⁻¹ᵁ U :=
  le_preimage_mono _ e (le_preimage_specMap_fromSpec hW (CommRingCat.ofHom φ))

theorem le_fromSpec' {W : X.Opens} (hW : IsAffineOpen W) (e : W ≤ U) : ⊤ ≤ hW.fromSpec ⁻¹ᵁ U :=
  le_preimage_mono (C := Γ(X, W)) _ e hW.fromSpec_preimage_self.ge

theorem valR_fromSpec {W : X.Opens} (hW : IsAffineOpen W) (φ : Γ(X, W) →+* R) :
    valR (spMap φ ≫ hW.fromSpec) W = φ := by
  funext f
  rw [valR_eq _ _ (le_fromSpec hW le_rfl φ)]
  exact congrArg (fun g => g.hom f) (valMap_specMap_fromSpec hW (CommRingCat.ofHom φ) _)

variable (v) in

def trM {U' : X.Opens} {n' : ℕ} (v' : Fin n' → Tn t Γ(X, U')) (hW : IsAffineOpen (U ⊓ U')) :
    Matrix (Fin n) (Fin n') Γ(X, U ⊓ U') :=
  mat (R := Γ(X, U ⊓ U')) hW.fromSpec (vAt v _ (le_fromSpec' hW inf_le_left)) (vAt v' _ (le_fromSpec' hW inf_le_right))

theorem trM_val (hU : IsAffineOpen U) (hv : StabBasis t hU.fromSpec v) {U' : X.Opens} {n' : ℕ}
    {v' : Fin n' → Tn t Γ(X, U')} (hU' : IsAffineOpen U') (hv' : StabBasis t hU'.fromSpec v')
    (hW : IsAffineOpen (U ⊓ U')) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ U') :
    (trM v v' hW).map (valR x _) = mat x (vAt v x h) (vAt v' x h') := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := fun z hz => ⟨h hz, h' hz⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X, U ⊓ U') →+* R, x = spMap ψ ≫ hW.fromSpec :=
    ⟨(valMap x _ hx).hom, (specMap_valMap_fromSpec hW x hx).symm⟩
  rw [valR_fromSpec]
  ext a b
  have k := co_vAt_map (R := Γ(X, U ⊓ U')) hU hv ψ hW.fromSpec (le_fromSpec' hW inf_le_left) h
    ((bas_vAt (R := Γ(X, U ⊓ U')) hU' hv' hW.fromSpec (le_fromSpec' hW inf_le_right)).1 b)
  have k' := congrFun (vAt_comp (R := Γ(X, U ⊓ U')) v' ψ hW.fromSpec (le_fromSpec' hW inf_le_right) h') b
  rw [← k'] at k
  exact (congrFun k a).symm

end At

theorem exists_isLieEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (t : SAB H X), IsProjOver s → ∃ (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd := by
  intro E _ _ _ H O _ _ X _ s t hs
  have hp : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hs
    have := isProper_str O N
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from s]
    infer_instance
  choose U n v hxU hv using GlobalTheory.T.exists_affine_stable_tangent_basis E H X t
  have hW : ∀ j j', IsAffineOpen ((U j).1 ⊓ (U j').1) := fun j j' => (U j).2.inf (U j').2
  have hb : ∀ {R : Type} [CommRing R] j (x : Sp R ⟶ X) h, Bas x (vAt (v j) x h) :=
    fun j x h => bas_vAt (U j).2 (hv j) x h
  have hG : ∀ {k : Type} [Field k] j j' (x : Sp k ⟶ X) h h',
      (trM (v j) (v j') (hW j j')).map (valF x _) = mat x (vAt (v j) x h) (vAt (v j') x h') :=
    fun j j' x h h' => trM_val (U j).2 (hv j) (U j').2 (hv j') (hW j j') x h h'
  obtain ⟨L, M, σ, A, B, aff, hle, hBA, htr⟩ := GlobalTheory.T.cocycle_trivial_on_projective_cover O X s X (fun j => (U j).1) n
    (fun j j' => trM (v j) (v j') (hW j j')) hs (fun x => ⟨x, hxU x⟩)
    (fun k _ w j h => (hG j j w h h).trans (hb j w h).mat_self)
    (fun k _ w j j' j'' h h' h'' => by
      rw [hG j j' w h h', hG j' j'' w h' h'', hG j j'' w h h'']
      exact (hb j w h).mat_mul (hb j' w h') (hb j'' w h'').1)
  have hBA' : ∀ i (R : Type) [CommRing R] (φ : Γ(X, L.U i) →+* R) (a : Fin (n (σ i)) → R),
      ((B i).map φ).mulVec (((A i).map φ).mulVec a) = a := fun i R _ φ a => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  refine ⟨L, aff, M, fun i R _ φ w => ((A i).map φ).mulVec (co (spMap φ ≫ (aff i).fromSpec)
    (vAt (v (σ i)) _ (le_fromSpec (aff i) (hle i) φ)) w), ?_, ?_, ?_, ?_, ?_⟩
  · intro i R _ φ m u cf w hu hw
    rw [(hb _ _ _).co_comb hu hw]
    simp only [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext a
    simp [Matrix.mulVec, dotProduct, mat, mul_comm]
  · intro i R _ φ w w' hw hw' e
    refine (hb (σ i) _ (le_fromSpec (aff i) (hle i) φ)).co_inj hw hw' ?_
    have := congrArg ((B i).map φ).mulVec e
    simpa only [hBA'] using this
  · intro i R R' _ _ φ ψ w hw
    have k := co_vAt_map (U (σ i)).2 (hv _) ψ _ (le_fromSpec (aff i) (hle i) φ)
      (le_comp ψ (le_fromSpec (aff i) (hle i) φ)) hw
    have e : spMap (ψ.comp φ) ≫ (aff i).fromSpec = spMap ψ ≫ spMap φ ≫ (aff i).fromSpec := by
      rw [← Category.assoc, spMap_comp']
    have k2 : ∀ (y : Sp R' ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ (U (σ i)).1), y = spMap ψ ≫ spMap φ ≫ (aff i).fromSpec →
        co y (vAt (v (σ i)) y hy) (spMap (dualMap ψ) ≫ w) =
          ψ ∘ co (spMap φ ≫ (aff i).fromSpec) (vAt (v (σ i)) _ (le_fromSpec (aff i) (hle i) φ)) w := by
      rintro _ hy rfl
      exact k
    simp only [k2 _ _ e]
    funext r
    simp [Matrix.mulVec, dotProduct]
  · intro i i' k _ φ φ' w e hw
    have h1 := le_fromSpec (aff i) le_rfl φ
    have h2 := le_fromSpec (aff i') le_rfl φ'
    have a1 : (A i).map φ = (A i).map (valF (spMap φ ≫ (aff i).fromSpec) _) :=
      congrArg _ (valR_fromSpec (aff i) φ).symm
    have a2 : (A i').map φ' = (A i').map (valF (spMap φ' ≫ (aff i').fromSpec) _) :=
      congrArg _ (valR_fromSpec (aff i') φ').symm
    have h3 := le_fromSpec (aff i) (hle i) φ
    have h4 := le_fromSpec (aff i') (hle i') φ'
    show ((A i).map φ).mulVec (co (spMap φ ≫ (aff i).fromSpec) (vAt _ _ h3) w) =
      _ • ((A i').map φ').mulVec (co (spMap φ' ≫ (aff i').fromSpec) (vAt _ _ h4) w)
    rw [a1, a2]
    generalize spMap φ' ≫ (aff i').fromSpec = y at *
    generalize spMap φ ≫ (aff i).fromSpec = x at *
    subst e
    rw [htr k x i i' h1 h2, hG _ _ x h4 h3, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      ← (hb _ x h4).co_comb (hb _ x h3).1 ((hb _ x h3).co_spec hw)]
  · intro i
    have e : spMap (RingHom.id Γ(X, L.U i)) ≫ (aff i).fromSpec = (aff i).fromSpec := by
      have : spMap (RingHom.id Γ(X, L.U i)) = 𝟙 _ := Spec.map_id _
      rw [this]; exact Category.id_comp _
    have h := le_fromSpec (aff i) (hle i) (RingHom.id _)
    refine ⟨n (σ i), vAt (v (σ i)) _ h, B i, ?_, fun z z' => ?_⟩
    · have := stab_vAt (U (σ i)).2 (hv _) _ h
      exact (congrArg (fun y => StabBasis t y (vAt (v (σ i)) _ h)) e).mp this
    · have k := congrFun (hBA' i _ (RingHom.id _) (Pi.single z' 1)) z
      simp only [(hb _ _ _).co_self]
      refine k.trans ?_
      rw [Pi.single_apply]
      congr

end GlobalTheory.LieEmb
