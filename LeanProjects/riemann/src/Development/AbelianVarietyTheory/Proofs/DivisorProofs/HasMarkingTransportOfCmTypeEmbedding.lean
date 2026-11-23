import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpaceStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.GoodTransport

theorem exists_equiv_of_lattices {La : Type} [AddCommGroup La] {g : ℕ} (P P' : La →+ (Fin g → ℂ))
    (hi : Function.Injective P) (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range) (hs' : Submodule.span ℝ (Set.range P') = ⊤) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ a, φ (P a) = P' a := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  let L' : Submodule ℤ (Fin g → ℂ) := LinearMap.range P'.toIntLinearMap
  haveI : DiscreteTopology L := hd
  haveI : DiscreteTopology L' := hd'
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ L' := ⟨hs'⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hi
  let e' : La ≃ₗ[ℤ] L' := LinearEquiv.ofInjective P'.toIntLinearMap hi'
  let b := Module.Free.chooseBasis ℤ L
  let b₀ := b.map e.symm
  let b' := b₀.map e'
  let φ := (b.ofZLatticeBasis ℝ L).equiv (b'.ofZLatticeBasis ℝ L') (Equiv.refl _)
  have key : (φ.toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap = P'.toIntLinearMap := by
    refine b₀.ext fun k => ?_
    have h1 : P (b₀ k) = b.ofZLatticeBasis ℝ L k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (b k))
    have h2 : P' (b₀ k) = b'.ofZLatticeBasis ℝ L' k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      rfl
    change φ (P (b₀ k)) = P' (b₀ k)
    rw [h1, h2, Module.Basis.equiv_apply]
    rfl
  exact ⟨φ, fun a => LinearMap.congr_fun key a⟩

theorem ex_eq_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z w : Fin g → ℂ) :
    u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [← u.ker, this]
  exact mul_eq_right

def imHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (herm Hm z w).im)
    (fun _ _ _ => by simp [herm])
    (fun r z w => by
      rw [herm, herm, smul_dotProduct, Complex.smul_im])
    (fun _ _ _ => by simp [herm, Matrix.mulVec_add])
    (fun r z w => by
      rw [herm, herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, star_trivial])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem fibre_marks {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X}
    (hy : y₀ = Fu.u i P) {s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) → (Fin g → ℂ))
    (hh : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) :
    (∀ (a : 𝓞 E) z, u.ex (h z) ≫ o.t.act.act a = u.ex (h fun k => ty k (a : E) * z k)) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        o.eta a = u.ex (h ((l.M : ℂ)⁻¹ • P (Fu.t i a)))) ∧
      ∀ a, o.etaA a = u.ex (h ((l.A : ℂ)⁻¹ • P (Fu.t i a))) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y :=
    fun x y h => Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨fun a z => inj _ _ ?_, fun a ha => inj _ _ ?_, fun a => inj _ _ ?_⟩
  · rw [hh, Fu.ex_lin i P hP, Over.comp_left, Over.comp_left, ← hh, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · rw [hh, ← Fu.ex_eta i P hP a ha]
    exact m.eta a
  · rw [hh, ← Fu.ex_etaA i P hP a]
    exact m.etaA a

theorem exists_eta_eq (a : D.La) : ∃ a₁ ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta a = o.eta a₁ := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, fun o => ?_⟩
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  conv_lhs => rw [this]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hx trivial), _root_.one_mul]

theorem exists_transport {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {κ : u.Λ → ℂ} {κ' : u'.Λ → ℂ}
    (hAH : u.IsAH Hm κ) (hAH' : u'.IsAH Hm' κ') : ∃ φ, IsTransport o o' u u' Hm Hm' φ := by
  obtain ⟨h, hex, hΛ, hE, -⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P y₀ s o m g u Hm κ hP hy hAH
  obtain ⟨h', hex', hΛ', hE', -⟩ :=
    FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P' y₀' s' o' m' g' u' Hm' κ' hP' hy' hAH'
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

theorem hasTransport_of_goodEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  intro E _ _ _ H D l Xo c O _ β Y U e B io hU hio hr hs hpq he y y' hy hy' hyU hyU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm'
    κ κ' hAH hAH'
  let e₀ : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c e (e₀ j).1) hpq he hty
  have ov : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ toF Xo c = spMap e →
      (x ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun x hx => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, DetExtendZero.spMap_comp]
  obtain ⟨i, P, hP, hu⟩ := Fu.onto _ (ov y hy)
  obtain ⟨i', P', hP', hu'⟩ := Fu.onto _ (ov y' hy')
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e _ _ Fu i i' P P' y y' B io hU hio hr hs hy hy' hyU hyU'
    hP hP' hu.symm hu'.symm
  exact exists_transport Fu i hP hP' hu.symm hu'.symm m m' u u' hAH hAH'

end GlobalTheory.DetLine.GoodTransport
