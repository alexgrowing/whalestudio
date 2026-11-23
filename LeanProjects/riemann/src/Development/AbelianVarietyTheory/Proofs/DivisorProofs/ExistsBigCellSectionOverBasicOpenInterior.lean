import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellPointEqOfBaseAndCellCoordinatesEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellSection

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Basic

variable {X : Scheme.{0}} {S : Type} [CommRing S]

theorem le_basicOpen_of_isUnit (x : Sp S ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U))
    (ha : IsUnit (ev x U h a)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e : (x.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (ev x U h a) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _).symm
  have hu : IsUnit ((x.appLE U ⊤ h).hom a) := e ▸ ha.map _
  have h1 := Scheme.basicOpen_appLE x ⊤ U h a
  have h2 := Scheme.basicOpen_of_isUnit (Sp S) hu
  exact h2.symm.le.trans (h1.le.trans inf_le_right)

theorem isUnit_of_mem_basicOpen {K : Type} [Field K] (x : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U))
    (p : Sp K) (hp : x p ∈ X.basicOpen a) : IsUnit (ev x U h a) := by
  refine IsUnit.mk0 _ fun h0 => ?_
  have e : (x.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (ev x U h a) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _).symm
  rw [h0, map_zero] at e
  have h1 := Scheme.basicOpen_appLE x ⊤ U h a
  have h2 : p ∈ (Sp K).basicOpen ((x.appLE U ⊤ h).hom a) := h1.ge ⟨trivial, hp⟩
  rw [e, Scheme.basicOpen_zero] at h2
  exact h2

end Basic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Model

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Type} [CommRing S] [Algebra c.F S]

theorem exists_frPt_of_basis (M : MChart Y) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {x : Sp S ⟶ Y.X} (hx : y ≫ Y.j = x)
    (hM : ⊤ ≤ x ⁻¹ᵁ M.U) (f : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → TanM x Y.t.G) (h1 : ∀ σ i, f σ i ∈ eigLie c x σ)
    (h2 : ∀ σ, ∀ w ∈ eigLie c x σ, ∃! a : Fin (Dw.mult σ) → S, ∑ i, a i • f σ i = w) :
    ∃ (P : FrPt Xo c S) (hP : frX P ≫ Y.j = x), ∀ σ i, frVec Y P hP σ i = f σ i := by
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U hM) y hy
    (hx.trans (spMap_ev x M.hU hM).symm)
  let u : ∀ σ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult σ)) S := fun σ j i => (vec M x hM).symm (f σ i) j
  have hu : ∀ σ i, vec M x hM (fun j => u σ j i) = f σ i := fun σ i => (vec M x hM).apply_symm_apply _
  have hs : ∀ σ (a : Fin (Dw.mult σ) → S), vec M x hM ((u σ).mulVec a) = ∑ i, a i • f σ i := fun σ a => by
    simp only [← hu, ← map_smul, ← map_sum]
    congr 1
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
  obtain ⟨Q, -, Λ', hQ, -⟩ := exists_frPt_tie GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c O β Y M S _ _ Λ u
    (fun σ i => (vec_mem_eigLie M x hM σ _).1 (by rw [hu]; exact h1 σ i))
    (fun σ cv h => by
      obtain ⟨a, ha, hu'⟩ := h2 σ _ ((vec_mem_eigLie M x hM σ cv).2 h)
      exact ⟨a, (vec M x hM).injective ((hs σ a).trans ha),
        fun b hb => hu' b ((hs σ b).symm.trans (congrArg _ hb))⟩)
  have hQx : frX Q ≫ Y.j = x := by
    rw [← eq_frX Q Λ'.xF_fst Λ'.xF_snd, Λ'.xF_j, spMap_ev]
  exact ⟨Q, hQx, fun σ i => ((vec_iff_toModel hM Λ' (eq_frX Q Λ'.xF_fst Λ'.xF_snd) (frX_fst Q) hQx _
    (Q.tan σ i)).1 (hQ σ i)).trans (hu σ i)⟩

theorem eq_ptY_of_initSpan_eq (X : FlagCover Y) {P : FrPt Xo c S} {x : Sp S ⟶ Y.X} (hPx : frX P ≫ Y.j = x)
    {z : Sp S ⟶ X.YY} (hx : z ≫ X.π = x) {k : X.F.J} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    (h : ∀ σ i, initSpan S (frVec Y P hPx σ) i = initSpan S (X.F.vecAt k z hz hx σ) i) : z = X.ptY P := by
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (frX_snd P) (hx.trans hPx.symm) k hz
  have hQx := hQ.over.trans hx
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hPx σ i = ∑ j, b j i • frVec Y Q hQx σ j := fun σ => by
    rw [hQ.frVec_eq hx]
    exact exists_tri_of_eq (X.F.linearIndependent_vecAt k z hz hx σ) (h σ)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hPx.trans hQx.symm)]
  have hB : ∃ t, FrBor t Q P := by
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec (X.F.inM hz hx) hQx hPx
      (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact FlagCover.eq_ptY (hQ.lies.frBor ht)

end Model

theorem existsUnique_of_isUnit_det {R : Type} [CommRing R] {m : ℕ} {M : Type} [AddCommGroup M] [Module R M]
    (T : Matrix (Fin m) (Fin m) R) (hT : IsUnit T.det) (f : Fin m → M) (w : M)
    (h : ∃! a : Fin m → R, ∑ i, a i • f i = w) : ∃! a : Fin m → R, ∑ i, a i • ∑ j, T i j • f j = w := by
  have key : ∀ a : Fin m → R, ∑ i, a i • ∑ j, T i j • f j = ∑ j, Matrix.vecMul a T j • f j := fun a => by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  obtain ⟨a, ha, hu⟩ := h
  refine ⟨Matrix.vecMul a T⁻¹, ?_, fun b hb => ?_⟩
  · beta_reduce
    rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hT, Matrix.vecMul_one, ha]
  · rw [← hu _ ((key b).symm.trans hb), Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hT, Matrix.vecMul_one]

variable (TF : TorFlag Xo c) {U : TF.Y.X.affineOpens} {n : ℕ} {e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n}
  {v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)}

def valV (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] (x : Sp S ⟶ TF.Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (m : Fin n) :
    TanM x TF.Y.t.G := GlobalTheory.LieMet.tanOf (GlobalTheory.LieMet.isTan_map _ (spMap_ev x U.2 hU) (hv.1 m))

theorem valV_left (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] (x : Sp S ⟶ TF.Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (m : Fin n) : (tv (valV TF hv x hU m)).left = spMap (dualMap (ev x U.1 hU)) ≫ v m := rfl

theorem tanPull_valV (hv : IsEigBasis TF U e v) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {x : Sp S ⟶ TF.Y.X} {x' : Sp S' ⟶ TF.Y.X} (h : spMap φ ≫ x = x') (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (hU' : ⊤ ≤ x' ⁻¹ᵁ U.1)
    (m : Fin n) : tanPull φ h (valV TF hv x hU m) = valV TF hv x' hU' m := by
  subst h
  apply tan_ext_left
  rw [tanPull_left, valV_left, valV_left, ev_spMap φ x U.1 hU, FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

theorem valV_block (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (hs : x ≫ TF.Y.s = spMap (algebraMap c.F S)) (σ : E →+* ℂ) :
    (∀ j, valV TF hv x hU (e ⟨σ, j⟩) ∈ eigLie c x σ) ∧
      ∀ w ∈ eigLie c x σ, ∃! a : Fin (Dw.mult σ) → S, ∑ j, a j • valV TF hv x hU (e ⟨σ, j⟩) = w := by
  have hxψ : spMap (ev x U.1 hU) ≫ LogKS.chart U = x := spMap_ev _ U.2 hU
  obtain ⟨-, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange TF.Y.t (ev x U.1 hU) (LogKS.chart U) n v hv.1 hv.2.1
  rw [hxψ] at b2
  have hφ : (ev (x ≫ TF.Y.s) ⊤ le_top).comp (toΓ c.F) = algebraMap c.F S :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_ev_top _).trans hs))
  have hφψ : ∀ r : c.F, ev x U.1 hU (algX TF.Y.s U.1 r) = algebraMap c.F S r := fun r =>
    (ev_appLE x TF.Y.s (by simp) hU le_top (toΓ c.F r)).trans (RingHom.congr_fun hφ r)
  let V := valV TF hv x hU
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      actR TF.Y.t.act a (V (e ⟨τ, j⟩)) = algebraMap c.F S (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H TF.Y.X TF.Y.t _ S (ev x U.1 hU) (LogKS.chart U) _ hxψ).2
      n v _ _ (hv.2.2 a τ j)
    have e1 : (fun i => ev x U.1 hU
        ((Pi.single (e ⟨τ, j⟩) (algX TF.Y.s U.1 (embK c τ a)) : Fin n → Γ(TF.Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (algebraMap c.F S (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [hi]
    rw [e1] at h
    have e2 : spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨τ, j⟩) ≫ (TF.Y.t.act.act a).left =
        (tv (actR TF.Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (actR TF.Y.t.act) (embK c z.1) (V (e z)) := fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  exact ⟨fun j a => hV σ j a, fun w hw =>
    GlobalTheory.FlagEmb.EigSpread.block_basis (GlobalTheory.FlagEmb.EigSpread.splits (E := E) c) (fun z => V (e z)) hu hb' σ w hw⟩

theorem exists_frPt_mul (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] (x : Sp S ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (hI : ⊤ ≤ x ⁻¹ᵁ LogKS.interior TF.Y) (M : MChart TF.Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U)
    (T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (hT : ∀ σ, IsUnit (T σ).det) :
    ∃ (_ : Algebra c.F S) (P : FrPt Xo c S) (hP : frX P ≫ TF.Y.j = x),
      ∀ σ i, frVec TF.Y P hP σ i = ∑ j, T σ i j • valV TF hv x hU (e ⟨σ, j⟩) := by
  have hr : Set.range x ⊆ Set.range TF.Y.j := by
    rintro _ ⟨s, rfl⟩; exact hI (Set.mem_univ s)
  obtain ⟨y, hy⟩ : ∃ y, y ≫ TF.Y.j = x := ⟨_, IsOpenImmersion.lift_fac TF.Y.j x hr⟩
  letI : Algebra c.F S := ((ev (y ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  have hy2 : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := (spMap_ev_top _).symm
  have hs : x ≫ TF.Y.s = spMap (algebraMap c.F S) := by
    rw [← hy, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc TF.Y.jQ, TF.Y.jQ_over,
      ← Category.assoc, hy2]
    exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
  exact ⟨inferInstance, exists_frPt_of_basis M hy2 hy hM _
    (fun σ i => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((valV_block TF hv x hU hs σ).1 j))
    fun σ w hw => existsUnique_of_isUnit_det (T σ) (hT σ) _ w ((valV_block TF hv x hU hs σ).2 w hw)⟩

def Carries (Z : Comp Xo c) (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z)
    (x : Sp S ⟶ TF.Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) : Prop :=
  ∃ (_ : Algebra c.F S) (P : FrPt Xo c S) (hP : frX P ≫ TF.Y.j = x), z ≫ inc₀ TF.X Z = TF.X.ptY P ∧
    ∀ σ i, frVec TF.Y P hP σ i = ∑ j, T σ i j • valV TF hv x hU (e ⟨σ, j⟩)

theorem exists_carries (Z : Comp Xo c) (hv : IsEigBasis TF U e v) {S : Type} [CommRing S] (x : Sp S ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (hI : ⊤ ≤ x ⁻¹ᵁ LogKS.interior TF.Y) (hB : ⊤ ≤ x ⁻¹ᵁ barComp TF.Y Z) (M : MChart TF.Y)
    (hM : ⊤ ≤ x ⁻¹ᵁ M.U) (T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S)
    (hT : ∀ σ, IsUnit (T σ).det) :
    ∃ z : Sp S ⟶ Y₀ TF.X Z, z ≫ toBase TF Z = x ∧ Carries TF Z hv z x hU T := by
  obtain ⟨inst, P, hP, hvec⟩ := exists_frPt_mul TF hv x hU hI M hM T hT
  have hπ : TF.X.ptY P ≫ TF.X.π = x := (TF.X.lies_ptY P).1.trans hP
  have hY : ⊤ ≤ TF.X.ptY P ⁻¹ᵁ (TF.X.π ⁻¹ᵁ barComp TF.Y Z) := by
    rw [← Scheme.Hom.comp_preimage, hπ]; exact hB
  have hr : Set.range (TF.X.ptY P) ⊆ Set.range (inc₀ TF.X Z) := by
    rintro _ ⟨s, rfl⟩; exact ⟨⟨_, hY (Set.mem_univ s)⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z ≫ inc₀ TF.X Z = TF.X.ptY P := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  exact ⟨z, by rw [← Category.assoc, hz, hπ], inst, P, hP, hz, hvec⟩

variable {TF} {Z : Comp Xo c} {hv : IsEigBasis TF U e v}

theorem Carries.map {S S' : Type} [CommRing S] [CommRing S'] {z : Sp S ⟶ Y₀ TF.X Z} {x : Sp S ⟶ TF.Y.X}
    {hU : ⊤ ≤ x ⁻¹ᵁ U.1} {T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S}
    (h : Carries TF Z hv z x hU T) (ψ : S →+* S') {x' : Sp S' ⟶ TF.Y.X} (hx' : spMap ψ ≫ x = x')
    (hU' : ⊤ ≤ x' ⁻¹ᵁ U.1) : Carries TF Z hv (spMap ψ ≫ z) x' hU' fun σ => (T σ).map ψ := by
  obtain ⟨inst, P, hP, hz, hvec⟩ := h
  obtain ⟨inst', χ, rfl⟩ : ∃ (_ : Algebra c.F S') (χ : S →ₐ[c.F] S'), χ.toRingHom = ψ := by
    letI : Algebra c.F S' := (ψ.comp (algebraMap c.F S)).toAlgebra
    exact ⟨inferInstance, { ψ with commutes' := fun _ => rfl }, rfl⟩
  obtain ⟨P', hPP⟩ := exists_frMap χ P
  have hP' : frX P' ≫ TF.Y.j = x' := by
    rw [← frX_frMap hPP, Category.assoc, hP]; exact hx'
  refine ⟨inst', P', hP', ?_, fun σ i => ?_⟩
  · rw [Category.assoc, hz]; exact TF.X.ptY_frMap hPP
  · rw [← tanPull_frVec hPP hP hP' hx' σ i, hvec, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smulₛₗ, tanPull_valV TF hv _ hx' hU hU']
      rfl

variable {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
  {L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)}

theorem Carries.exists_lower (hC : IsCell TF Z U e v W k L N) {S : Type} [CommRing S] {z : Sp S ⟶ Y₀ TF.X Z}
    (hW : ⊤ ≤ z ⁻¹ᵁ W) {hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1}
    {T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S}
    (h : Carries TF Z hv z (z ≫ toBase TF Z) hU T) (σ : E →+* ℂ) :
    ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧
      ∀ i j, T σ i j = ∑ m, b i m * ev z W hW ((L σ * N σ) m j) := by
  obtain ⟨_, P, hP, hpt, hvec⟩ := h
  obtain ⟨B, hB0, -, hBc⟩ := frVec_cell_comb E H Dw l Xo c TF Z U n e v hv W k L N hC S P _ hW _ hP hU hpt
  refine ⟨B σ, hB0 σ, fun i j => ?_⟩
  have h1 := (GlobalTheory.LieMet.isComb_iff (fun j => valV TF hv _ hU (e ⟨σ, j⟩)) _ _).2 (hvec σ i)
  exact congrFun (cell_eigComb_coeff_unique E H Dw l Xo c TF Z U n e v hv W k L N hC S _ hW _ rfl hU σ _ _ _ h1
    (hBc σ i)) j

theorem Carries.eq_of_cell (hC : IsCell TF Z U e v W k L N) {S : Type} [CommRing S] {z zw : Sp S ⟶ Y₀ TF.X Z}
    (hW : ⊤ ≤ zw ⁻¹ᵁ W) {hU : ⊤ ≤ (zw ≫ toBase TF Z) ⁻¹ᵁ U.1}
    (h : Carries TF Z hv z (zw ≫ toBase TF Z) hU fun σ => (N σ).map (ev zw W hW)) : z = zw := by
  obtain ⟨-, -, hWk, hLz, hLu, -, -, hcomb⟩ := hC
  obtain ⟨_, P, hP, hpt, hvec⟩ := h
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hW hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have heq : zw ≫ inc₀ TF.X Z = TF.X.ptY P := by
    refine eq_ptY_of_initSpan_eq TF.X hP hxx hk fun σ i => Eq.symm ?_
    refine CellMono.initSpan_eq_of_lowerTri (A := (L σ).map (ev zw W hW)) (fun i j h => ?_)
      (fun i => (hLu σ i).map (ev zw W hW)) (fun i => ?_) i
    · show ev zw W hW (L σ i j) = 0
      rw [hLz σ i j h, map_zero]
    · rw [(GlobalTheory.LieMet.isComb_iff (fun j => valV TF hv _ hU (e ⟨σ, j⟩)) _ _).1 (hcomb S zw hW hU hk hxx σ i)]
      simp only [hvec, Finset.smul_sum, smul_smul, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul,
        Matrix.map_apply]
      exact Finset.sum_comm
  rw [← cancel_mono (inc₀ TF.X Z), hpt, heq]

def univN (Dw : Datum H) (A : Type) [CommRing A] (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (MvPolynomial (VIx Dw) A) := fun i j =>
  if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0

theorem isUnit_det_univN {A B : Type} [CommRing A] [CommRing B] (f : MvPolynomial (VIx Dw) A →+* B) (σ : E →+* ℂ) :
    IsUnit ((univN Dw A σ).map f).det := by
  rw [Matrix.det_of_upperTriangular (M := (univN Dw A σ).map f) (fun i j (h : j < i) => by
    rw [Matrix.map_apply, univN, dif_neg (not_lt.2 h.le), if_neg h.ne', map_zero])]
  refine IsUnit.prod_univ_iff.2 fun i => ?_
  rw [Matrix.map_apply, univN, dif_neg (lt_irrefl i), if_pos rfl, map_one]
  exact isUnit_one

theorem eval₂Hom_univN {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : C →+* B)
    (N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) C) (h0 : ∀ σ i j, j < i → N σ i j = 0)
    (h1 : ∀ σ i, N σ i i = 1) (σ : E →+* ℂ) (i j : Fin (Dw.mult σ)) :
    MvPolynomial.eval₂Hom f (fun a => g (cellCoord N a)) (univN Dw A σ i j) = g (N σ i j) := by
  rw [univN]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dif_pos h]; exact MvPolynomial.eval₂Hom_X' _ _ _
  · rw [dif_neg (lt_irrefl i), if_pos rfl, h1, map_one, map_one]
  · rw [dif_neg (not_lt.2 h.le), if_neg h.ne', h0 σ i j h, map_zero, map_zero]

theorem Carries.nonempty (hC : IsCell TF Z U e v W k L N) (a : Γ(TF.Y.X, U.1)) {S : Type} [CommRing S]
    [Algebra (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S]
    [IsLocalization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S] {z : Sp S ⟶ Y₀ TF.X Z}
    {x : Sp S ⟶ TF.Y.X} {hU : ⊤ ≤ x ⁻¹ᵁ U.1}
    (hρ : ∀ r, ev x U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S (MvPolynomial.C r))
    (h : Carries TF Z hv z x hU fun σ => (univN Dw Γ(TF.Y.X, U.1) σ).map (algebraMap _ S))
    {K : Type} [Field K] (zw : Sp K ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (p : Sp K)
    (hp : (zw ≫ toBase TF Z) p ∈ TF.Y.X.basicOpen a) : ∃ q, z q ∈ W := by
  have hUw : ⊤ ≤ (zw ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hC.2.1 (hzw hp)
  have hau : IsUnit (ev (zw ≫ toBase TF Z) U.1 hUw a) := isUnit_of_mem_basicOpen _ hUw a p hp
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀, ψ₀ = MvPolynomial.eval₂Hom (ev (zw ≫ toBase TF Z) U.1 hUw)
    fun i : VIx Dw => ev zw W hzw (cellCoord N i) := ⟨_, rfl⟩
  have hψC : ∀ r, ψ₀ (MvPolynomial.C r) = ev (zw ≫ toBase TF Z) U.1 hUw r := fun r => by
    rw [hψ₀, MvPolynomial.eval₂Hom_C]
  have hψa : IsUnit (ψ₀ (MvPolynomial.C a)) := by rw [hψC]; exact hau
  obtain ⟨ψ, hψ⟩ : ∃ ψ : S →+* K, ∀ r, ψ (algebraMap _ S r) = ψ₀ r :=
    ⟨IsLocalization.Away.lift (MvPolynomial.C a) hψa, fun r => IsLocalization.Away.lift_eq _ hψa r⟩
  have hx' : spMap ψ ≫ x = zw ≫ toBase TF Z := by
    have e1 : ψ.comp (ev x U.1 hU) = ev (zw ≫ toBase TF Z) U.1 hUw :=
      RingHom.ext fun r => by rw [RingHom.comp_apply, hρ, hψ, hψC]
    rw [← spMap_ev x U.2 hU, ← Category.assoc, spMap_comp', e1]
    exact spMap_ev _ U.2 hUw
  have h1 := h.map ψ hx' hUw
  have hTN : (fun σ => ((univN Dw Γ(TF.Y.X, U.1) σ).map (algebraMap _ S)).map ψ) =
      fun σ => (N σ).map (ev zw W hzw) := by
    funext σ
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hψ, hψ₀]
    exact eval₂Hom_univN _ _ N hC.2.2.2.2.2.1 hC.2.2.2.2.2.2.1 σ i j
  rw [hTN] at h1
  have hzz := h1.eq_of_cell hC hzw
  refine ⟨spMap ψ p, ?_⟩
  have h2 : (spMap ψ ≫ z) p ∈ W := by rw [hzz]; exact hzw (Set.mem_univ p)
  exact h2

theorem exists_section (hv : IsEigBasis TF U e v) (hC : IsCell TF Z U e v W k L N) (a : Γ(TF.Y.X, U.1))
    (ha : TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U) (S : Type) [CommRing S]
    [Algebra (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S]
    [IsLocalization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S] :
    ∃ (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧
      (∀ r, ev (z ≫ toBase TF Z) U.1 hU r =
        algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S (MvPolynomial.C r)) ∧
      Carries TF Z hv z (z ≫ toBase TF Z) hU fun σ => (univN Dw Γ(TF.Y.X, U.1) σ).map (algebraMap _ S) := by
  obtain ⟨x, hU, hρ⟩ : ∃ (x : Sp S ⟶ TF.Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1), ev x U.1 hU =
      (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) S).comp MvPolynomial.C :=
    ⟨spMap _ ≫ tau U.2, le_preimage_comp _ (tau_le U.2 le_rfl), ev_spMap_tau U.2 _ _⟩
  have hxa : ⊤ ≤ x ⁻¹ᵁ TF.Y.X.basicOpen a := le_basicOpen_of_isUnit x hU a (by
    rw [hρ]
    exact IsLocalization.Away.algebraMap_isUnit (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)))
  have hI := le_preimage_mono (ha.trans (inf_le_left.trans inf_le_left)) hxa
  have hB := le_preimage_mono (ha.trans (inf_le_left.trans inf_le_right)) hxa
  have hM := le_preimage_mono (ha.trans inf_le_right) hxa
  obtain ⟨z, rfl, hz⟩ := exists_carries TF Z hv x hU hI hB (TF.X.F.M k).toMChart hM
    (fun σ => (univN Dw Γ(TF.Y.X, U.1) σ).map (algebraMap _ S)) fun σ => isUnit_det_univN _ σ
  exact ⟨z, hU, fun p hp => hI hp, fun r => RingHom.congr_fun hρ r, hz⟩

theorem exists_section_props (hv : IsEigBasis TF U e v) (hC : IsCell TF Z U e v W k L N) (a : Γ(TF.Y.X, U.1))
    (ha : TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U)
    (hw : ∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) (A : Type) [CommRing A]
    [Algebra (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) A]
    [IsLocalization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) A] :
    ∃ z : Sp A ⟶ Y₀ TF.X Z, ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r,
      ev (z ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) A (MvPolynomial.C r)) ∧
      ((z ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp A)).Nonempty ∧
      ∀ (S : Type) [CommRing S] (ψ : A →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z) ⁻¹ᵁ W) (σ : E →+* ℂ),
        ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧
          ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) A
            (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) =
              ∑ m, b i m * ev (spMap ψ ≫ z) W hW ((L σ * N σ) m j) := by
  obtain ⟨w, hwW, -, hwa⟩ := hw
  obtain ⟨z, hU, hO, hρ, hz⟩ := exists_section hv hC a ha A
  refine ⟨z, hO, ⟨hU, hρ⟩, ?_, fun S _ ψ hW σ => ?_⟩
  · obtain ⟨K, _, zw, hpt⟩ : ∃ (K : Type) (_ : Field K) (zw : Sp K ⟶ Y₀ TF.X Z), ∀ p, zw p = w :=
      ⟨(Y₀ TF.X Z).residueField w, inferInstance, (Y₀ TF.X Z).fromSpecResidueField w,
        Scheme.fromSpecResidueField_apply w⟩
    have hzw : ⊤ ≤ zw ⁻¹ᵁ W := fun p _ => show zw p ∈ W from (hpt p).symm ▸ hwW
    obtain ⟨p⟩ : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
    have hp : (zw ≫ toBase TF Z) p ∈ TF.Y.X.basicOpen a := by
      rw [Scheme.Hom.comp_apply, hpt]; exact hwa
    obtain ⟨q, hq⟩ := hz.nonempty hC a hρ zw hzw _ hp
    exact ⟨q, hq⟩
  · have hU' : ⊤ ≤ ((spMap ψ ≫ z) ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hC.2.1 (hW hp)
    have h1 := hz.map ψ (Category.assoc (spMap ψ) z (toBase TF Z)).symm hU'
    obtain ⟨b, hb, h⟩ := h1.exists_lower hC hW σ
    refine ⟨b, hb, fun i j => Eq.trans ?_ (h i j)⟩
    rw [Matrix.map_apply, Matrix.map_apply, univN]

end GlobalTheory.LogPole.CellSection

namespace GlobalTheory.LogPole

open GlobalTheory.FlagMod

theorem exists_cell_section_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (a : Γ(TF.Y.X, U.1)), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U → (∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) → ∃ z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ⟶ Y₀ TF.X Z, ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z₁ ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r, ev (z₁ ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) (MvPolynomial.C r)) ∧ ((z₁ ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))))).Nonempty ∧ ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (σ : E →+* ℂ), ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧ ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _ (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) = ∑ m, b i m * ev (spMap ψ ≫ z₁) W hW ((L σ * N σ) m j) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N hC a ha hw
  exact CellSection.exists_section_props hv hC a ha hw
    (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)))

end GlobalTheory.LogPole
