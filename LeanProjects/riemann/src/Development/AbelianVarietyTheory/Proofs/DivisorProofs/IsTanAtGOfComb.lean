import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm GlobalTheory.HtGen GlobalTheory.RootFrameB
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] GlobalTheory.CompHt.algPadicInt GlobalTheory.CompHt.algPadicField GlobalTheory.CompHt.towerPadic GlobalTheory.CompHt.factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open scoped Classical

namespace GlobalTheory.RootFrameB.EigTie

open GlobalTheory.FlatModel GlobalTheory.FlatModel.RetractionModules GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.CompHt

theorem omega_combLie {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] (f : omega G) :
    ∀ (m : ℕ) (cf : Fin m → O) (xs : Fin m → LieG G), f.1 (combLie G m cf xs) = ∑ i, cf i * f.1 (xs i)
  | 0, _, _ => by simp [combLie, omega_lieZero]
  | m + 1, cf, xs => by
    rw [combLie, omega_lieAdd, omega_lieScale, omega_combLie f m, Fin.sum_univ_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem isTanAtG_of_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i)) {cf : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v cf w) : IsTanAtG t x w := by
  rw [← (GlobalTheory.FrameTangent.isCombAtG_iff t x (fun j => GlobalTheory.FrameTangent.ovT (hv j)) cf w).1 h]
  refine GlobalTheory.FrameTangent.isTanAtG_of _ ?_
  rw [GlobalTheory.FrameTangent.combT, GlobalTheory.TangentLinear.smT_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [GlobalTheory.FrameTangent.smT_smT, zero_mul]
  exact GlobalTheory.FrameTangent.smT_zero_ovT (hv j)

variable {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {Q : PtP E p} {yb : Sp 𝓞_ℂ_[p] ⟶ X} {π : Q.G.left ⟶ t.G.left}

theorem eq_combLie (hπ : IsGrpPullback Q.G t.G yb π) {m : ℕ} {u : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)}
    {v : Fin m → LieG Q.Gt} (hv : ∀ i, ITie Q π (v i) (u i)) {cf : Fin m → 𝓞_ℂ_[p]}
    {w : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left} (hw : IsCombAtG t yb u cf w) {x : LieG Q.Gt} (hx : ITie Q π x w) :
    x = combLie Q.Gt m cf v := by
  choose xG hxc hxG using hv
  obtain ⟨y, hy, hwu⟩ := hw
  obtain ⟨yG, hyc, hyG⟩ := hx
  have h1 : ((List.ofFn y).prod).left =
      ((List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod).left ≫ π :=
    prod_left_comp hπ (T := specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]))
      (fun i => ptMap (dualScale (cf i)) ≫ (xG i).1) y fun i => by
      rw [hy i, Over.comp_left, Category.assoc, hxG i]
      rfl
  have h2 : yG.1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod :=
    hom_ext_pb hπ (hyG.trans (hwu.symm.trans h1))
  have h3 : Corr Q (combLie Q.Gt m cf v).1 yG.1 := by
    rw [combLie_val, h2]
    exact corr_prod _ _ fun i => (hxc i).comp (dualScale (cf i))
  exact Subtype.ext (corr_left_unique hyc h3)

theorem iTie_act (hact : ∀ a, (Q.oG.act a).left ≫ π = π ≫ (t.act.act a).left) {x : LieG Q.Gt}
    {u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left} (h : ITie Q π x u) (a : 𝓞 E) :
    ITie Q π (AvDefs.lieAct Q.Gt Q.oGt a x) (u ≫ (t.act.act a).left) := by
  obtain ⟨xG, hc, hu⟩ := h
  refine ⟨AvDefs.lieAct Q.G Q.oG a xG, corr_act hc a, ?_⟩
  change (xG.1 ≫ Q.oG.act a).left ≫ π = _
  rw [Over.comp_left, Category.assoc, hact, ← Category.assoc, hu]

theorem sum_al₀_actT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (Q : GlobalTheory.FlatModel.PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : Q.G.left ⟶ t.G.left), IsGrpPullback Q.G t.G yb π → (∀ a, (Q.oG.act a).left ≫ π = π ≫ (t.act.act a).left) → ∀ (ε : 𝓞_ℂ_[p] ≃+* ↥(intO ℂ_[p])), (intO ℂ_[p]).subtype.comp ε.toRingHom = algebraMap 𝓞_ℂ_[p] ℂ_[p] → ∀ (x : Sp ↥(intO ℂ_[p]) ⟶ X), spMap ε.toRingHom ≫ yb = x → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (v : Fin g → LieG Q.Gt) (u : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)), (∀ i, GlobalTheory.FlatModel.ITie Q π (v i) (u i)) → (∀ i, spMap (dualMap ε.toRingHom) ≫ u i = e i) → IsTanBasis t x e → ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left) (σ : 𝓞 E →+* ℂ_[p]), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) cf w → GlobalTheory.FlatModel.IsEigG t σ w → ∀ (o : 𝓞 E) (s : Q.T), ∑ i, cf i * algebraMap 𝓞_ℂ_[p] ℂ_[p] ((Q.al₀ (Q.actT (star o) s)).1 (v i)) = σ o * ∑ i, cf i * algebraMap 𝓞_ℂ_[p] ℂ_[p] ((Q.al₀ s).1 (v i)) := by
  intro E _ _ _ H X t p _ _ Q yb π hπ hact ε hε x hx g e v u hvu hue he cf w σ hw hσ o s
  have e₁ : spMap (intO ℂ_[p]).subtype ≫ x = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb := by
    rw [← hx, GlobalTheory.FlatModel.sp_sp, hε]
  obtain rfl : bcV t ε.toRingHom u = e := funext hue
  have e₂ : (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ bcV t ε.toRingHom u i) =
      fun i => spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ u i := by
    have := GlobalTheory.FlatModel.bcV_bcV (t := t) ε.toRingHom (intO ℂ_[p]).subtype u
    rw [hε] at this
    exact this
  rw [e₁, e₂] at hw
  have hid : ε.symm.toRingHom.comp ε.toRingHom = RingHom.id _ := by
    ext1 s
    simp
  have h1 : spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id 𝓞_ℂ_[p])) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hu : IsTanBasis t yb u := by
    have h := isTanBasis_bc he ε.symm.toRingHom
    have h4 : bcV t (RingHom.id 𝓞_ℂ_[p]) u = u := funext fun i => by rw [bcV, h3, Category.id_comp]
    rwa [bcV_bcV, ← hx, GlobalTheory.FlatModel.sp_sp, hid, h1, Category.id_comp, h4] at h
  have hU : ∀ w, IsTanAtG t yb w → ∃ a, IsCombAtG t yb u a w := fun w hw => by
    have h := hu.2 _ (RingHom.id _) w
    simp only [h1, h3, Category.id_comp] at h
    exact (h hw).exists
  choose M hM using fun i => hU _ (GlobalTheory.ActMatrix.isTanAtG_act t yb o (hu.1 i))
  have hT := (isTanBasis_bc hu (algebraMap 𝓞_ℂ_[p] ℂ_[p])).1
  haveI := t.act.hom o
  have c1 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ hT _ (Matrix.of fun j i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (M i j)) cf _
    (fun i => GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (hM i))
    (GlobalTheory.PushChart.isCombAtG_comp (t.act.act o) _ (fun i => (Category.assoc _ _ _).symm) hw)
  have c2 := GlobalTheory.DetHT.Bridge.isCombAtG_scale hw (σ o)
  rw [← hσ o] at c2
  have key := (hu.2 _ (algebraMap 𝓞_ℂ_[p] ℂ_[p]) _ (isTanAtG_of_comb hT c1)).unique c1 c2
  have hv : ∀ i, (Q.al₀ (Q.actT (star o) s)).1 (v i) = ∑ j, M i j * (Q.al₀ s).1 (v j) := fun i => by
    rw [Q.al₀_act, omegaAct_apply, star_star, eq_combLie hπ hvu (hM i) (iTie_act hact (hvu i) o), omega_combLie]
  simp only [hv, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have k := congrFun key j
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at k
  rw [← _root_.mul_assoc, ← k, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.RootFrameB.EigTie

end
