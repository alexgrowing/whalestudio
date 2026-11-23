import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfTangentEqStatement

noncomputable section

namespace GlobalTheory.LevelFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem eta_injective (Xo : Moduli Dw l) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (β : KA l →+* k)
    (hx : x ≫ Xo.s = spMap β) (a : Dw.La) (h : toUnit (Over.mk x) ≫ Xo.univ.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom k x β hx
  have htop : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) = ⊤ := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [htop]; trivial
  obtain ⟨a₂, h₂, a₁, h₁, rfl⟩ := Submodule.mem_sup.1 ha
  have e : toUnit (Over.mk x) ≫ Xo.univ.eta (a₂ + a₁) = toUnit (Over.mk x) ≫ Xo.univ.eta a₁ := by
    rw [Xo.univ.eta_add, Xo.univ.eta_ker a₂ h₂, _root_.one_mul]
  have e₁ : I.ev l.M a₁ = 1 := (hI a₁ h₁).symm.trans (e.symm.trans h)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨b, rfl⟩ := (I.ker l.M hM a₁).1 e₁
  have hMm : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact hle this
  refine Submodule.add_mem _ h₂ ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hMm trivial

section Bridge

abbrev fib {X Y : Scheme.{0}} (G : Over X) (x : Y ⟶ X) : Over Y := (Over.pullback x).obj G

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def pushAt {ρ : X ⟶ X} {F : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (T : Over X) (c : T.left ⟶ X)
    (e : T.hom ≫ ρ = c) : (T ⟶ G) →* (Over.mk c ⟶ G) :=
  MonoidHom.mk' (fun u => Over.homMk (u.left ≫ F) (by
      subst e
      show (u.left ≫ F) ≫ G.hom = T.hom ≫ ρ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u])) (fun a b => by
    subst e
    exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm)

theorem one_left_congr {T : Scheme.{0}} {c c' : T ⟶ X} (h : c = c') :
    (1 : Over.mk c ⟶ G).left = (1 : Over.mk c' ⟶ G).left := by
  subst h; rfl

end Bridge

theorem sections_eq {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) [IsProper G.hom]
    {ρ ρ' : X ⟶ X} {F F' : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (h' : IsGrpPullback G G ρ' F')
    {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x ≫ ρ')
    (ht : ∀ w : overAt x (DualNumber k) ⟶ G, smT x 0 w = 1 → w.left ≫ F = w.left ≫ F')
    (s : Over.mk x ⟶ G) : s.left ≫ F = s.left ≫ F' := by
  have pA : IsGrpPullback (fib G x) G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have pB : IsGrpPullback (fib G (x ≫ ρ)) G (x ≫ ρ) (pullback.fst G.hom (x ≫ ρ)) := isGrpPullback_pullback G (x ≫ ρ)
  have c₁ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F) := IsGrpPullback.comp pA h
  have c₂ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F') := hx ▸ IsGrpPullback.comp pA h'
  let f : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F) (pullback.snd G.hom x) c₁.1.w) (pullback.lift_snd _ _ _)
  let f' : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F') (pullback.snd G.hom x) c₂.1.w) (pullback.lift_snd _ _ _)
  have ef : f.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F := pullback.lift_fst _ _ _
  have ef' : f'.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F' := pullback.lift_fst _ _ _
  haveI : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pB (𝟙 G) f (by simpa using ef)
  haveI : IsMonHom f' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₂ pB (𝟙 G) f' (by simpa using ef')
  have hA : IsAbelianScheme (fib G x) := by
    haveI : IsProper (fib G x).hom := inferInstanceAs (IsProper (pullback.snd G.hom x))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback x G hG)
  have hB : IsAbelianScheme (fib G (x ≫ ρ)) := by
    haveI : IsProper (fib G (x ≫ ρ)).hom := inferInstanceAs (IsProper (pullback.snd G.hom (x ≫ ρ)))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback (x ≫ ρ) G hG)
  haveI : IsCommMonObj (fib G x) := hA.comm
  haveI : IsCommMonObj (fib G (x ≫ ρ)) := hB.comm
  have key : f = f' := by
    refine GlobalTheory.T.abelianScheme_hom_eq_of_tangent_eq k _ _ hA hB f f' fun v hv => ?_
    let w : overAt x (DualNumber k) ⟶ G := Over.homMk (v.left ≫ pullback.fst G.hom x) (by
      have e := Over.w v
      show (v.left ≫ pullback.fst G.hom x) ≫ G.hom = spMap (algebraMap k (DualNumber k)) ≫ x
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have e' : v.left ≫ pullback.snd G.hom x = spMap (algebraMap k (DualNumber k)) ≫ 𝟙 (Sp k) := e
      rw [e', Category.comp_id])
    have hw : smT x 0 w = 1 := by
      apply Over.OverMorphism.ext
      have e₁ : (smT x 0 w).left = (smT (𝟙 (Sp k)) 0 v).left ≫ pullback.fst G.hom x := by
        simp only [smT_left, w, Over.homMk_left, Category.assoc]
      rw [e₁, hv]
      have e₂ := congrArg (fun z => z.left) (map_one (pushHom pA (overAt (𝟙 (Sp k)) (DualNumber k))))
      refine e₂.trans (one_left_congr ?_)
      simp
    have e := ht w hw
    apply Over.OverMorphism.ext
    refine pB.1.hom_ext ?_ ?_
    · simp only [Over.comp_left, Category.assoc]
      rw [ef, ef']
      simpa [w] using e
    · rw [Over.w, Over.w]
  let a : Over.mk (𝟙 (Sp k)) ⟶ fib G x := Over.homMk (pullback.lift s.left (𝟙 _) (by simpa using Over.w s)) (pullback.lift_snd _ _ _)
  have ea : a.left ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
  have e1 : a.left ≫ f.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F := by
    rw [ef, ← Category.assoc, ea]
  have e2 : a.left ≫ f'.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F' := by
    rw [ef', ← Category.assoc, ea]
  rw [← e1, ← e2, key]

theorem move_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (g g' : Gam Dw l), levR (lift g, LinearMap.id) y y' → levR (lift g', LinearMap.id) y y' → g = g' := by
  intro E _ _ _ H Dw l Xo c _ _ lift hl k _ _ _ y y' g g' h h'
  obtain ⟨ρ, ν, -, hm, hf⟩ := h
  obtain ⟨ρ', ν', -, hm', hf'⟩ := h'
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
  have hx : y.x ≫ ρ = y.x ≫ ρ' := hf.1.symm.trans hf'.1
  have hu : ∀ τ i, y.u τ i ≫ ν.φ = y.u τ i ≫ ν'.φ := fun τ i => (hf.2.1 τ i).symm.trans (hf'.2.1 τ i)
  have ht : ∀ w : overAt y.x (DualNumber k) ⟶ Xo.univ.t.G, smT y.x 0 w = 1 → w.left ≫ ν.φ = w.left ≫ ν'.φ := by
    intro w hw
    have hT : IsTanAt y.x w.left := isTanAtG_of (t := Xo.univ.t) w hw
    obtain ⟨a, ⟨u, hu1, hu2⟩, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan.frTanBasis_holds Xo c k y w.left hT
    let P := pushAt ν.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ) rfl
    let P' := pushAt ν'.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ)
      (by simp only [Over.mk_hom, Category.assoc, hx])
    have e₁ : ∀ i, P (u i) = P' (u i) := fun i => by
      apply Over.OverMorphism.ext
      show (u i).left ≫ ν.φ = (u i).left ≫ ν'.φ
      rw [hu1, Category.assoc, Category.assoc, hu]
    have e₂ : P (List.ofFn u).prod = P' (List.ofFn u).prod := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 2
      exact funext e₁
    have e₃ := congrArg (fun z => z.left) e₂
    have e₄ : ((List.ofFn u).prod).left ≫ ν.φ = ((List.ofFn u).prod).left ≫ ν'.φ := e₃
    rw [hu2] at e₄
    exact e₄
  have hs := sections_eq Xo.univ.t.semi ν.cart ν'.cart y.x hx ht
  have tl : (toUnit (Over.mk y.x)).left = y.x := by simpa using Over.w (toUnit (Over.mk y.x))
  have hη : ∀ a, toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) = toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a) := by
    intro a
    have e₁ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a)).left ≫ ν.φ = y.x ≫ ρ ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm.2.1 a]
    have e₂ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)).left ≫ ν'.φ = y.x ≫ ρ' ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm'.2.1 a]
    apply Over.OverMorphism.ext
    refine ν.cart.1.hom_ext ?_ ?_
    · rw [e₁, hs, e₂, ← Category.assoc, ← Category.assoc, hx]
    · rw [Over.w, Over.w]
  have hz : ∀ a, lift g a - lift g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    intro a
    refine eta_injective Xo y.x ((algebraMap c.F k).comp (IntermediateField.inclusion c.le).toRingHom) y.x_over _ ?_
    have e : toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) =
        (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a - lift g' a)) * (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)) := by
      rw [← MonObj.comp_mul, ← Xo.univ.eta_add, sub_add_cancel]
    rw [hη a] at e
    exact (mul_eq_right.1 e.symm)
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e₁ := LinearMap.congr_fun (hl g) a
  have e₂ := LinearMap.congr_fun (hl g') a
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at e₁ e₂
  rw [← e₁, ← e₂]
  exact (Submodule.Quotient.eq _).2 (hz a)

end GlobalTheory.LevelFree
