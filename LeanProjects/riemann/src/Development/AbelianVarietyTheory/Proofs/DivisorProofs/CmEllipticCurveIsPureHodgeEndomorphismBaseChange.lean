import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.PureLift GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.GrpTangent
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

theorem eq_epsScale_of_isLieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {c : Fin 1 → R}
    {v : Fin 1 → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb c v w) : w = epsScale (c 0) ≫ v 0 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : (List.ofFn u).prod = u 0 := by simp
  rw [h1]
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact hu 0

theorem push_sub_smul_mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : LieExact A)
    {v : Fin 1 → (epsR R ⟶ A)} (hv : IsLieBasis v) (W : A ⟶ A) [IsMonHom W] {s : Fin 1 → R}
    (e : IsLieComb s v (v 0 ≫ W)) (y : HdR A) : push (dp0 R) (𝟙 _) W y - s 0 • y ∈ Fil A := by
  obtain ⟨u, hu⟩ := (hA.1 y).exists
  obtain ⟨c, hc, -⟩ := hv.2 u hu.1
  have hu' : u = epsScale (c 0) ≫ v 0 := eq_epsScale_of_isLieComb hc
  have hW : v 0 ≫ W = epsScale (s 0) ≫ v 0 := eq_epsScale_of_isLieComb e
  have key : u ≫ W = epsScale (s 0) ≫ u := by
    rw [hu', Category.assoc, hW, epsScale_mul_assoc, epsScale_mul_assoc, mul_comm]
  have h1 := hu.push W
  rw [key] at h1
  exact h1.sub_mem (hu.smul (s 0))

theorem exists_isPolForm (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨hall, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨z, hz⟩ : ∃ z, IsChern (dp0 R) (A.hom ≫ 𝟙 (Sp R)) L z :=
    GlobalTheory.Cris.ChernExists.exists_isChern L hL
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hmem : ∀ x, x ∈ prim (dp0 R) (𝟙 (Sp R)) A := fun x => by
    rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hall]
    exact Submodule.mem_top
  refine ⟨_, n, fun k => ⟨a k, hmem _⟩, fun k => ⟨b k, hmem _⟩, ?_, rfl⟩
  have hz' : z = ∑ k, cup _ (a k) (b k) := by
    rw [← e.apply_symm_apply z, ← hab, map_sum]
    exact Finset.sum_congr rfl fun k _ => he _ _
  rw [hz'] at hz
  exact hz

private theorem pGen_pull_refl {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (F : Y ⟶ X) :
    PGen (⟨fun p => (L.pull F).g p.1 p.2⟩ : LB.Iso (L.pull F) (L.pull F)) := by
  intro Z f y j j' k k' h1 h2 h3 h4
  unfold gw
  dsimp only
  have e1 : (f ≫ F) y ∈ L.U j := h1
  have e2 : (f ≫ F) y ∈ L.U j' := h2
  have e3' : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 h3
  have e3 : (f ≫ F) y ∈ L.U (k PUnit.unit) := e3'
  have e4' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 h4
  have e4 : (f ≫ F) y ∈ L.U (k' PUnit.unit) := e4'
  rw [gm_pull_g L F f y (fun _ => j) k (mem_pull.2 h1) h3, gm_pull_g L F f y k k' h3 h4,
    gm_pull_g L F f y (fun _ => j') k' (mem_pull.2 h2) h4]
  have c1 := gm_cocycle hL (f ≫ F) y e1 e2 e4
  have c2 := gm_cocycle hL (f ≫ F) y e1 e4 e3
  have c3 := gm_cocycle hL (f ≫ F) y e3 e4 e3
  have c4 := gm_cocycle hL (f ≫ F) y e3 e3 e3
  have hkk : (gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit))) (L.g (k PUnit.unit) (k PUnit.unit)) = 1 := by
    have h := congrArg (· * ((gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit)))
      (L.g (k PUnit.unit) (k PUnit.unit)))⁻¹) c4
    simpa using h
  have hinv := eq_inv_of_mul_eq_one_right (c3.trans hkk)
  rw [← c2, ← c1, hinv, mul_right_comm]

theorem isPureBC_ell : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω),
    IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  intro hP E _ _ _ H S _ ω C
  unfold IsPureBC
  intro R _ f A _ φ hpb W' _ hW'

  haveI : IsCommMonObj A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback C.P.isAb hpb
  have hgG : SmoothOfRelativeDimension 1 C.P.A.hom := by
    have h := C.P.smoothDim
    rw [C.dim] at h
    exact h
  have hgA : SmoothOfRelativeDimension 1 A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb.1 hgG
  have hLie : LieExact A := (hP.2.1 R A 1 hA hgA).1

  haveI := hgG
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange S R f C.P.A A φ hpb
    (SmoothOfRelativeDimension.smooth 1 C.P.A.hom) 1 ![C.v] C.basis
  have hu : ∀ i, (v' i).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (![C.v] i).left := hv'φ
  have hw : (v' 0 ≫ W').left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (C.v ≫ C.act.act (GlobalTheory.CM.wK H)).left := by
    rw [Over.comp_left, Category.assoc, hW', ← Category.assoc, hu 0, Over.comp_left, Category.assoc]
    rfl
  have e : IsLieComb (fun i => f (![ω] i)) v' (v' 0 ≫ W') :=
    GlobalTheory.ArcQ.NormalForm.isLieComb_baseChange hpb hu hw C.eig
  have hquot : ∀ y : HdR A, push (dp0 R) (𝟙 _) W' y - f ω • y ∈ Fil A :=
    fun y => push_sub_smul_mem_Fil hLie hv' W' e y

  have hL' : (C.P.L.pull φ).IsLB := pull_isLB C.P.isLB φ
  obtain ⟨ψ, hψ⟩ := exists_isPolForm hP.1 hA hgA hL'
  obtain ⟨hiso, hperf⟩ := hP.2.2.2.2 R A 1 hA hgA (C.P.L.pull φ) hL' ψ hψ
  have hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A (C.P.L.pull φ) :=
    kTriv_pull hpb C.P.isLB hL' (pGen_pull_refl C.P.L C.P.isLB φ) C.P.ktriv
  haveI := hperf hK

  obtain ⟨o', ho'⟩ := GlobalTheory.CM.ellPull_exists_oAct hpb C.act
  haveI := o'.hom (GlobalTheory.CM.wK H)
  haveI := o'.hom (1 - GlobalTheory.CM.wK H)
  have hWo : o'.act (GlobalTheory.CM.wK H) = W' := by
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [ho', hW']
    · rw [Over.w, Over.w]

  have hb : ((1 - GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.bar ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) := by
    rw [show ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.w0 from rfl, GlobalTheory.CM.kform_bar_w0]
    push_cast
    rfl
  have HG : LBIso (cubeLB C.P.A ![fst C.P.A C.P.A ≫ C.act.act (GlobalTheory.CM.wK H), snd C.P.A C.P.A] C.P.L)
      (cubeLB C.P.A ![fst C.P.A C.P.A, snd C.P.A C.P.A ≫ C.act.act (1 - GlobalTheory.CM.wK H)] C.P.L) := by
    have h := C.adj (GlobalTheory.CM.wK H) (1 - GlobalTheory.CM.wK H) hb
    unfold GlobalTheory.CM.LamEq at h
    simpa only [Category.comp_id] using h
  have HA := GlobalTheory.PolAdjoint.lbIso_cube hpb C.P.L hW' (ho' (1 - GlobalTheory.CM.wK H)) HG
  have hadj : ∀ x y : HdR A, ψ (push (dp0 R) (𝟙 _) W' x) y =
      ψ x (push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y) :=
    GlobalTheory.PolAdjoint.adjoint_of_lbIso hP.1 hA hgA hL' hψ W' (o'.act (1 - GlobalTheory.CM.wK H)) HA
  have hpushb : ∀ y : HdR A, push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y = y - push (dp0 R) (𝟙 _) W' y := by
    intro y
    have h1 : GlobalTheory.DeRham.act (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H) = 1 - push (dp0 R) (𝟙 _) W' := by
      rw [map_sub, map_one, GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (GlobalTheory.CM.wK H),
        push_congr (dp0 R) (𝟙 _) hWo]
    rw [← GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H), h1]
    rfl

  have hfil : ∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W' x = f (1 - ω) • x := by
    intro x hx
    have hlie : ∀ y : HdR A, ψ x (push (dp0 R) (𝟙 _) W' y) = f ω * ψ x y := by
      intro y
      have h0 := hiso x hx _ (hquot y)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have key : ψ (push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x) = 0 := by
      ext y
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hadj, hpushb, map_sub, hlie, map_sub, map_one,
        smul_eq_mul, LinearMap.zero_apply]
      ring
    have hinj := (LinearMap.IsPerfPair.bijective_left ψ).1
    have h0 : push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x = 0 := hinj (by rw [key, map_zero])
    exact sub_eq_zero.mp h0
  exact ⟨hfil, hquot⟩

end GlobalTheory.PureLift
